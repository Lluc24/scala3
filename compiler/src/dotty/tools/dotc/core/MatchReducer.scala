package dotty.tools
package dotc
package core


import Types.*, Contexts.*, Symbols.*, Flags.*, Names.*, NameOps.*, Denotations.*
import Decorators.*
import Phases.{gettersPhase, elimByNamePhase}
import StdNames.nme
import TypeOps.refineUsingParent
import collection.mutable
import util.{Stats, NoSourcePosition, EqHashMap}
import config.Config
import config.Feature.{migrateTo3, sourceVersion}
import config.Printers.{subtyping, gadts, matchTypes, capt, noPrinter}
import config.SourceVersion
import TypeErasure.{erasedLub, erasedGlb}
import TypeApplications.*
import Variances.{Variance, variancesConform}
import Constants.Constant
import scala.util.control.NonFatal
import typer.ProtoTypes.constrained
import typer.Applications.productSelectorTypes
import reporting.trace
import annotation.constructorOnly
import cc.*
import Capabilities.Capability
import NameKinds.WildcardParamName
import MatchTypes.isConcrete
import reporting.Message.Note
import scala.util.boundary, boundary.break

/** Implements match type reduction.
 *
 *  A match type has the form `S match { case P1 => T1 ... case Pn => Tn }` where `S` is the scrutinee,
 *  and each case has a pattern `Pi` and corresponding body `Ti`.
 */
object MatchReducer:
  import printing.*, Texts.*

  /** Result of attempting to match a scrutinee against a single case pattern. */
  enum MatchResult extends Showable:
    /** Pattern matched successfully; reduce to the given type. */
    case Reduced(tp: Type)
    /** Pattern is provably disjoint from scrutinee; try next case. */
    case Disjoint
    /** Pattern matched but is also disjoint (indicates empty scrutinee); do not reduce. */
    case ReducedAndDisjoint
    /** Cannot determine if pattern matches; do not reduce. */
    case Stuck
    /** Pattern matched but type captures could not be instantiated specifically enough. */
    case NoInstance(fails: List[(Name, TypeBounds)])

    def toText(p: Printer): Text = this match
      case Reduced(tp)        => "Reduced(" ~ p.toText(tp) ~ ")"
      case Disjoint           => "Disjoint"
      case ReducedAndDisjoint => "ReducedAndDisjoint"
      case Stuck              => "Stuck"
      case NoInstance(fails)  => "NoInstance(" ~ Text(fails.map(p.toText(_) ~ p.toText(_)), ", ") ~ ")"

/** Reduces match types by attempting to match a scrutinee against case patterns.
 *
 *  This class delegates subtyping and type equality checks to the provided `typeComparer`,
 *  and extends `ConstraintHandling` to manage type constraints during reduction.
 *
 *  @param typeComparer The type comparer used for subtyping and equality checks.
 */
class MatchReducer(typeComparer: TypeComparer) extends ConstraintHandling {
  import MatchReducer.*

  protected var state: TyperState = compiletime.uninitialized
  def constraint: Constraint = typeComparer.constraint
  def constraint_=(c: Constraint): Unit = typeComparer.constraint = c

  override protected def isSame(tp1: Type, tp2: Type)(using Context): Boolean = typeComparer.isSameType(tp1, tp2)

  override protected def isSub(tp1: Type, tp2: Type)(using Context): Boolean = typeComparer.isSubType(tp1, tp2)

  /** Reduces a match type by sequentially trying to match the scrutinee against each case.
   *
   *  The reduction follows these rules:
   *  - If a case matches and is not disjoint, reduce to that case's body.
   *  - If a case is provably disjoint, skip it and try the next case.
   *  - If a case matches but is also disjoint (empty scrutinee), do not reduce.
   *  - If a case cannot be determined to match or be disjoint, do not reduce (stuck).
   *  - If no cases match, do not reduce.
   *
   *  Reduction is performed with a frozen constraint to prevent side effects on the type comparer's state.
   *
   *  @param scrut The scrutinee type to match against.
   *  @param cases The list of case specifications to try in order.
   *  @return The reduced type if reduction succeeds, or `NoType` if reduction fails or gets stuck.
   */
  def matchCases(scrut: Type, cases: List[MatchTypeCaseSpec])(using Context): Type = {
    // a reference for the type parameters poisoned during matching
    // for use during the reduction step
    var poisoned: Set[TypeParamRef] = Set.empty

    def paramInstances(canApprox: Boolean) = new TypeAccumulator[Array[Type]]:
      def apply(insts: Array[Type], t: Type) = t match
        case param @ TypeParamRef(b, n) if b eq caseLambda =>
          insts(n) =
            if canApprox then
              typeComparer.approximation(param, fromBelow = variance >= 0, Int.MaxValue).simplified
            else typeComparer.constraint.entry(param) match
              case entry: TypeBounds =>
                val lo = typeComparer.fullLowerBound(param)
                val hi = typeComparer.fullUpperBound(param)
                if !poisoned(param) && typeComparer.isSubType(hi, lo) then lo.simplified else Range(lo, hi)
              case inst =>
                assert(inst.exists, i"param = $param\nconstraint = ${typeComparer.constraint}")
                if !poisoned(param) then inst.simplified else Range(inst, inst)
          insts
        case _ =>
          foldOver(insts, t)

    def instantiateParams(insts: Array[Type]) = new ApproximatingTypeMap {
      variance = 0

      override def range(lo: Type, hi: Type): Type =
        if variance == 0 && (lo eq hi) then
          // override the default `lo eq hi` test, which removes the Range
          // which leads to a Reduced result, instead of NoInstance
          Range(lower(lo), upper(hi))
        else super.range(lo, hi)

      def apply(t: Type) = t match {
        case t @ TypeParamRef(b, n) if b `eq` caseLambda => insts(n)
        case t: LazyRef => apply(t.ref)
        case _ => mapOver(t)
      }
    }

    def instantiateParamsSpec(insts: Array[Type], caseLambda: HKTypeLambda) = new TypeMap {
      variance = 0

      def apply(t: Type) = t match {
        case t @ TypeParamRef(b, n) if b `eq` caseLambda => insts(n)
        case t: LazyRef => apply(t.ref)
        case _ => mapOver(t)
      }
    }

    /** Attempts to match a single case against the scrutinee. */
    def matchCase(cas: MatchTypeCaseSpec): MatchResult = trace(i"$scrut match ${MatchTypeTrace.caseText(cas)}", matchTypes, show = true) {
      cas match
        case cas: MatchTypeCaseSpec.SubTypeTest     => matchSubTypeTest(cas)
        case cas: MatchTypeCaseSpec.SpeccedPatMat   => matchSpeccedPatMat(cas)
        case cas: MatchTypeCaseSpec.LegacyPatMat    => matchLegacyPatMat(cas)
        case cas: MatchTypeCaseSpec.MissingCaptures => matchMissingCaptures(cas)
    }

    /** Matches a simple subtype test case without type captures.
     *
     *  Checks if the scrutinee is a necessary subtype of the pattern, and whether they are disjoint.
     */
    def matchSubTypeTest(spec: MatchTypeCaseSpec.SubTypeTest): MatchResult =
      val disjoint = typeComparer.provablyDisjoint(scrut, spec.pattern)
      if typeComparer.necessarySubType(scrut, spec.pattern) then
        if disjoint then
          MatchResult.ReducedAndDisjoint
        else
          MatchResult.Reduced(spec.body)
      else if disjoint then
        MatchResult.Disjoint
      else
        MatchResult.Stuck
    end matchSubTypeTest

    /** Matches a case using the spec-compliant pattern matching algorithm.
     *
     *  This algorithm handles type captures and follows the semantics described in
     *  https://docs.scala-lang.org/sips/match-types-spec.html#matching
     *
     *  The algorithm:
     *  1. Recursively matches the pattern against the scrutinee, computing type capture instantiations.
     *  2. Checks that instantiations are specific enough (not abstract type bounds in variant positions).
     *  3. Verifies that the scrutinee is a subtype of the instantiated pattern.
     *  4. If successful, reduces to the instantiated body.
     */
    def matchSpeccedPatMat(spec: MatchTypeCaseSpec.SpeccedPatMat): MatchResult =
      val instances = Array.fill[Type](spec.captureCount)(NoType)
      val noInstances = mutable.ListBuffer.empty[(TypeName, TypeBounds)]

      /** Recursively matches a pattern against the scrutinee.
       *
       *  @param pattern The pattern to match.
       *  @param scrut The scrutinee type.
       *  @param variance The variance position: 1 for covariant, -1 for contravariant, 0 for invariant.
       *  @param scrutIsWidenedAbstract Whether the scrutinee has been widened from an abstract type.
       *  @return `true` if the pattern matches, `false` otherwise.
       */
      def rec(pattern: MatchTypeCasePattern, scrut: Type, variance: Int, scrutIsWidenedAbstract: Boolean): Boolean =
        pattern match
          case MatchTypeCasePattern.Capture(num, /* isWildcard = */ true) =>
            // instantiate the wildcard in a way that the subtype test always succeeds
            instances(num) = variance match
              case 1  => scrut.hiBound // actually important if we are not in a class type constructor
              case -1 => scrut.loBound
              case 0  => scrut
            !instances(num).isError

          case MatchTypeCasePattern.Capture(num, /* isWildcard = */ false) =>
            def failNotSpecific(bounds: TypeBounds): TypeBounds =
              noInstances += spec.origMatchCase.paramNames(num) -> bounds
              bounds

            instances(num) = scrut match
              case scrut: TypeBounds =>
                if scrutIsWidenedAbstract then
                  failNotSpecific(scrut)
                else
                  variance match
                    case 1  => scrut.hi
                    case -1 => scrut.lo
                    case 0  => failNotSpecific(scrut)
              case _ =>
                if scrutIsWidenedAbstract && variance != 0 then
                  // fail as not specific
                  // the Nothing and Any bounds are used so that they are not displayed; not for themselves in particular
                  if variance > 0 then failNotSpecific(TypeBounds(defn.NothingType, scrut))
                  else failNotSpecific(TypeBounds(scrut, defn.AnyType))
                else
                  scrut
            !instances(num).isError

          case MatchTypeCasePattern.TypeTest(tpe) =>
            // The actual type test is handled by `scrut <:< instantiatedPat`
            true

          case MatchTypeCasePattern.BaseTypeTest(classType, argPatterns, needsConcreteScrut) =>
            val cls = classType.classSymbol.asClass
            scrut.baseType(cls) match
              case base @ AppliedType(baseTycon, baseArgs) =>
                // #19445 Don't check the prefix of baseTycon here; it is handled by `scrut <:< instantiatedPat`.
                val innerScrutIsWidenedAbstract =
                  scrutIsWidenedAbstract
                    || (needsConcreteScrut && !isConcrete(scrut)) // no point in checking concreteness if it does not need to be concrete
                matchArgs(argPatterns, baseArgs, classType.typeParams, innerScrutIsWidenedAbstract)
              case _ =>
                false

          case MatchTypeCasePattern.AbstractTypeConstructor(tycon, argPatterns) =>
            scrut.dealias match
              case scrutDealias @ AppliedType(scrutTycon, args) if scrutTycon =:= tycon =>
                matchArgs(argPatterns, args, tycon.typeParams, scrutIsWidenedAbstract)
              case _ =>
                false

          case MatchTypeCasePattern.CompileTimeS(argPattern) =>
            typeComparer.natValue(scrut) match
              case Some(scrutValue) if scrutValue > 0 =>
                rec(argPattern, ConstantType(Constant(scrutValue - 1)), variance, scrutIsWidenedAbstract)
              case _ =>
                false

          case MatchTypeCasePattern.TypeMemberExtractor(typeMemberName, capture) =>
            /** Attempts to remove references to a skolem type by following aliases and singletons.
             *
             *  When extracting a type member from a skolem type (used to represent non-singleton scrutinees),
             *  we try to eliminate references to the skolem from the member's type by:
             *  - Following type aliases to their right-hand sides
             *  - Following singleton term references to their underlying types
             *
             *  If any reference to the skolem remains after this process, `refersToSkolem` is set to true.
             */
            class DropSkolemMap(skolem: SkolemType) extends TypeMap:
              var refersToSkolem = false
              def apply(tp: Type): Type =
                if refersToSkolem then
                  return tp
                tp match
                  case `skolem` =>
                    refersToSkolem = true
                    tp
                  case tp: NamedType =>
                    val pre1 = apply(tp.prefix)
                    if refersToSkolem then
                      tp match
                        case tp: TermRef => tp.info.widenExpr.dealias match
                          case info: SingletonType =>
                            refersToSkolem = false
                            apply(info)
                          case _ =>
                            tp.derivedSelect(pre1)
                        case tp: TypeRef => tp.info match
                          case info: AliasingBounds =>
                            refersToSkolem = false
                            apply(info.alias)
                          case _ =>
                            tp.derivedSelect(pre1)
                    else
                      tp.derivedSelect(pre1)
                  case tp: LazyRef =>
                    // By default, TypeMap maps LazyRefs lazily. We need to
                    // force it for `refersToSkolem` to be correctly set.
                    apply(tp.ref)
                  case _ =>
                    mapOver(tp)
            end DropSkolemMap

            /** Attempts to remove references to a skolem type from the given type.
             *
             *  @param u The type to process.
             *  @param skolem The skolem type to remove.
             *  @return The type with skolem references removed, or `NoType` if references remain.
             */
            def dropSkolem(u: Type, skolem: SkolemType): Type =
              val dmap = DropSkolemMap(skolem)
              val res = dmap(u)
              if dmap.refersToSkolem then NoType else res

            val stableScrut: SingletonType = scrut match
              case scrut: SingletonType => scrut
              case _                    => SkolemType(scrut)

            stableScrut.member(typeMemberName) match
              case denot: SingleDenotation if denot.exists =>
                val info = stableScrut match
                  case skolem: SkolemType =>
                    /* If it is a skolem type, we cannot have class selections nor
                     * abstract type selections. If it is an alias, we try to remove
                     * any reference to the skolem from the right-hand-side. If that
                     * succeeds, we take the result, otherwise we fail as not-specific.
                     */

                    def adaptToTriggerNotSpecific(info: Type): Type = info match
                      case info: TypeBounds => info
                      case _                => RealTypeBounds(info, info)

                    denot.info match
                      case denotInfo: AliasingBounds =>
                        val alias = denotInfo.alias
                        dropSkolem(alias, skolem).orElse(adaptToTriggerNotSpecific(alias))
                      case ClassInfo(prefix, cls, _, _, _) =>
                        // for clean error messages
                        adaptToTriggerNotSpecific(prefix.select(cls))
                      case denotInfo =>
                        adaptToTriggerNotSpecific(denotInfo)

                  case _ =>
                    // The scrutinee type is truly stable. We select the type member directly on it.
                    stableScrut.select(typeMemberName)
                end info

                rec(capture, info, variance = 0, scrutIsWidenedAbstract)

              case _ =>
                // The type member was not found; no match
                false
      end rec

      /** Matches argument patterns against argument types in the correct variance positions. */
      def matchArgs(argPatterns: List[MatchTypeCasePattern], args: List[Type], tparams: List[TypeParamInfo], scrutIsWidenedAbstract: Boolean): Boolean =
        if argPatterns.isEmpty then
          true
        else
          rec(argPatterns.head, args.head, tparams.head.paramVarianceSign, scrutIsWidenedAbstract)
            && matchArgs(argPatterns.tail, args.tail, tparams.tail, scrutIsWidenedAbstract)

      // This might not be needed
      val constrainedCaseLambda = constrained(spec.origMatchCase, ast.tpd.EmptyTree)._1.asInstanceOf[HKTypeLambda]

      val disjoint =
        val defn.MatchCase(origPattern, _) = constrainedCaseLambda.resultType: @unchecked
        typeComparer.provablyDisjoint(scrut, origPattern)

      def tryDisjoint: MatchResult =
        if disjoint then
          MatchResult.Disjoint
        else
          MatchResult.Stuck

      if rec(spec.pattern, scrut, variance = 1, scrutIsWidenedAbstract = false) then
        if noInstances.nonEmpty then
          MatchResult.NoInstance(noInstances.toList)
        else
          val defn.MatchCase(instantiatedPat, reduced) =
            instantiateParamsSpec(instances, constrainedCaseLambda)(constrainedCaseLambda.resultType): @unchecked
          if scrut <:< instantiatedPat then
            if disjoint then
              MatchResult.ReducedAndDisjoint
            else
              MatchResult.Reduced(reduced)
          else
            tryDisjoint
      else
        tryDisjoint
    end matchSpeccedPatMat

    /** Matches a case using the legacy pattern matching algorithm.
     *
     *  This algorithm is used for code compiled with `-source:3.3` and below, or when the
     *  pattern cannot be converted to the spec-compliant representation.
     *
     *  The legacy algorithm uses constraint-based matching with type variable instantiation.
     */
    def matchLegacyPatMat(spec: MatchTypeCaseSpec.LegacyPatMat): MatchResult =
      val caseLambda = constrained(spec.origMatchCase, ast.tpd.EmptyTree)._1.asInstanceOf[HKTypeLambda]
      this.caseLambda = caseLambda

      val defn.MatchCase(pat, body) = caseLambda.resultType: @unchecked

      def matches(canWidenAbstract: Boolean): Boolean =
        val saved = this.canWidenAbstract
        val savedPoisoned = this.poisoned
        this.canWidenAbstract = canWidenAbstract
        this.poisoned = Set.empty
        try typeComparer.necessarySubType(scrut, pat)
        finally
          poisoned = this.poisoned
          this.poisoned = savedPoisoned
          this.canWidenAbstract = saved

      val disjoint = typeComparer.provablyDisjoint(scrut, pat)

      def redux(canApprox: Boolean): MatchResult =
        val instances = paramInstances(canApprox)(Array.fill(caseLambda.paramNames.length)(NoType), pat)
        instantiateParams(instances)(body) match
          case Range(lo, hi) =>
            MatchResult.NoInstance {
              caseLambda.paramNames.zip(instances).collect {
                case (name, Range(lo, hi)) => (name, TypeBounds(lo, hi))
              }
            }
          case redux =>
            if disjoint then
              MatchResult.ReducedAndDisjoint
            else
              MatchResult.Reduced(redux)

      if matches(canWidenAbstract = false) then
        redux(canApprox = true)
      else if matches(canWidenAbstract = true) then
        redux(canApprox = false)
      else if (disjoint)
        // We found a proof that `scrut` and `pat` are incompatible.
        // The search continues.
        MatchResult.Disjoint
      else
        MatchResult.Stuck
    end matchLegacyPatMat

    /** Handles cases where type captures are missing from the pattern.
     *
     *  This occurs when earlier substitutions cause pattern type parameters to disappear.
     *  Always returns `Stuck` since the case cannot be properly matched.
     */
    def matchMissingCaptures(spec: MatchTypeCaseSpec.MissingCaptures): MatchResult =
      MatchResult.Stuck

    /** Recursively tries to match remaining cases in order. */
    def recur(remaining: List[MatchTypeCaseSpec]): Type = remaining match
      case (cas: MatchTypeCaseSpec.LegacyPatMat) :: _ if sourceVersion.isAtLeast(SourceVersion.`3.4`) =>
        val errorText = MatchTypeTrace.illegalPatternText(scrut, cas)
        ErrorType(reporting.MatchTypeLegacyPattern(errorText))
      case cas :: remaining1 =>
        matchCase(cas) match
          case MatchResult.Disjoint =>
            recur(remaining1)
          case MatchResult.Stuck =>
            MatchTypeTrace.stuck(scrut, cas, remaining1)
            NoType
          case MatchResult.NoInstance(fails) =>
            MatchTypeTrace.noInstance(scrut, cas, fails)
            NoType
          case MatchResult.Reduced(tp) =>
            tp.simplified
          case MatchResult.ReducedAndDisjoint =>
            // Empty types break the basic assumption that if a scrutinee and a
            // pattern are disjoint it's OK to reduce passed that pattern. Indeed,
            // empty types viewed as a set of value is always a subset of any other
            // types. As a result, if a scrutinee both matches a pattern and is
            // probably disjoint from it, we prevent reduction.
            // See `tests/neg/6570.scala` and `6570-1.scala` for examples that
            // exploit emptiness to break match type soundness.
            MatchTypeTrace.emptyScrutinee(scrut)
            NoType
      case Nil =>
        /* TODO warn ? then re-enable warn/12974.scala:26
        val noCasesText = MatchTypeTrace.noMatchesText(scrut, cases)
        report.warning(reporting.MatchTypeNoCases(noCasesText), pos = ???)
        */
        MatchTypeTrace.noMatches(scrut, cases)
        NoType

    inFrozenConstraint(recur(cases))
  }
}