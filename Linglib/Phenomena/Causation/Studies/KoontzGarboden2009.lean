import Linglib.Theories.Semantics.Causation.Morphological
import Linglib.Theories.Semantics.Lexical.Verb.EventStructure
import Linglib.Theories.Morphology.Core.Monotonicity
import Linglib.Fragments.Spanish.Predicates
import Linglib.Core.Alternation

/-!
# @cite{koontz-garboden-2009} — Anticausativization

Koontz-Garboden, Andrew. 2009. Anticausativization.
*Natural Language & Linguistic Theory* 27(1): 77–138.

## Core thesis

Anticausativization is semantically a **reflexivization** operation:
the reflexive clitic (*se*, *sich*, *-da*, *-wa*) takes the two-place
causative denotation and identifies the EFFECTOR with the THEME.
Derived inchoatives **retain CAUSE** in their lexical semantic
representation, contra the deletion analysis (Grimshaw 1982;
@cite{krejci-2012}).

## Key formal apparatus

- ⟦*se*⟧ = λℜλx[ℜ(x,x)] — the reflexivization operator
- ⟦*romper*⟧ = λxλyλsλe[∃v[CAUSE(v,e) ∧ EFFECTOR(v,y) ∧
  BECOME(e,s) ∧ THEME(s,x) ∧ not-whole(s)]]
- ⟦*romperse*⟧ = ⟦*se*⟧(⟦*romper*⟧) = λxλsλe[∃v[CAUSE(v,e) ∧
  EFFECTOR(v,x) ∧ BECOME(e,s) ∧ THEME(s,x) ∧ not-whole(s)]]

## Predictions

1. Only verbs with underspecified causers (EFFECTOR) anticausativize.
   Verbs with specified causers (AGENT) yield reflexive-only readings.
2. Causative does NOT entail inchoative (the inchoative requires the
   single argument to be both EFFECTOR and THEME).
3. Derived inchoatives license *por sí solo* / *by itself* (because
   CAUSE is in their denotation).
4. Internally caused COS verbs (*empeorar*, *crecer*) lack CAUSE in
   their LSR and reject *por sí solo*.

## Monotonicity Hypothesis

The Monotonicity Hypothesis (MH) states that word formation operations
do not remove operators from lexical semantic representations. The
reflexivization analysis preserves the MH; the deletion analysis violates
it. Evidence from *por sí solo*, negation scope, NPI licensing, and the
Albanian "feel like" construction independently confirms that derived
inchoatives have CAUSE.

## Bridges

- `CauserSpec` (Spanish fragment) — EFFECTOR vs AGENT verb taxonomy
- `CausationType.hasCauseInLSR` — internally vs externally caused distinction
- `IntransitivizationType` — competing structural analysis (@cite{krejci-2012})
- `reflexivization` / `decausativization` — valency alternation types
- `AnticausativeAnalysis` — parameterization of competing analyses
-/

namespace Phenomena.Causation.Studies.KoontzGarboden2009

open Fragments.Spanish.Predicates
open Semantics.Causation.Morphological
open Semantics.Lexical.Verb.EventStructure
open Theories.Morphology.Core.Monotonicity
open Minimalism (VerbHead)
open Core.Alternation

-- ════════════════════════════════════════════════════
-- § 1. Competing Analyses of Anticausativization (§5)
-- ════════════════════════════════════════════════════

/-- Competing analyses of the semantic impact of anticausativization.

    @cite{koontz-garboden-2009} §5 reviews four families of analysis.
    The choice determines whether derived inchoatives have CAUSE in
    their denotation, which in turn predicts:
    - licensing of *por sí solo* / *by itself* (CAUSE required)
    - scope of negation over CAUSE (§4.3)
    - NPI licensing in negated inchoatives (§4.3)
    - acceptability in the Albanian "feel like" construction (§4.2) -/
inductive AnticausativeAnalysis where
  /-- Anticausativization deletes CAUSE + external argument.
      Result: [BECOME [x STATE]]. Grimshaw 1982; @cite{krejci-2012}. -/
  | deletion
  /-- Anticausativization reflexivizes the causative denotation.
      CAUSE retained. @cite{koontz-garboden-2009}; @cite{chierchia-2004}. -/
  | reflexivization
  /-- Existential binding of the external argument
      (@cite{levin-hovav-1995} Ch. 3). -/
  | existentialBinding
  /-- Both forms derived from a more abstract root.
      Doron 2003; Alexiadou et al. 2006. -/
  | leastCommonDenominator
  deriving DecidableEq, Repr

/-- Does this analysis predict that derived inchoatives retain CAUSE? -/
def AnticausativeAnalysis.retainsCause : AnticausativeAnalysis → Bool
  | .reflexivization => true
  | .existentialBinding => true
  | .deletion => false
  | .leastCommonDenominator => false

/-- Does this analysis preserve the Monotonicity Hypothesis? -/
def AnticausativeAnalysis.preservesMH : AnticausativeAnalysis → Bool
  | .deletion => false
  | _ => true

-- ════════════════════════════════════════════════════
-- § 2. The Reflexivization Operator (§2.2)
-- ════════════════════════════════════════════════════

/-! The reflexivization operator (eq. 11) = λℜλx[ℜ(x,x)].
    It takes a relation as an argument, setting both arguments
    of the relation to be the same.

    In set-theoretic terms: if a relation is a set of pairs,
    reflexivization restricts it to those pairs whose members are
    identical. -/

/-- Reflexivization of a two-place relation over entities.
    ⟦*se*⟧ = λℜλx[ℜ(x,x)] -/
def reflexivize {Entity : Type} (R : Entity → Entity → Prop) :
    Entity → Prop :=
  fun x => R x x

/-- Reflexivization of a Boolean two-place predicate. -/
def reflexivizeBool {Entity : Type} (R : Entity → Entity → Bool) :
    Entity → Bool :=
  fun x => R x x

-- ════════════════════════════════════════════════════
-- § 3. Verb Denotation Taxonomy (§§2.1, 3.1–3.2)
-- ════════════════════════════════════════════════════

/-! The critical distinction between verbs that anticausativize (*romper*)
    and those that do not (*asesinar*) reduces to the thematic specification
    of the participant in the causing subevent.

    `CauserSpec` from the Spanish fragment encodes this.
    The prediction: `reflexivize` applied to an EFFECTOR verb yields
    an anticausative reading; applied to an AGENT verb, a reflexive-only
    reading. -/

/-- Reflexivization of an EFFECTOR verb: the single argument becomes
    both the undergoer (THEME) and the underspecified causer (EFFECTOR).
    Because EFFECTOR carries no agent entailments, the result is
    compatible with inanimate subjects → anticausative reading.

    Reflexivization of an AGENT verb: the single argument must be both
    undergoer and AGENT. AGENT entails volition/sentience → the result
    requires an animate, agentive subject → reflexive reading only. -/
def reflexivizationYieldsAnticausative : CauserSpec → Bool
  | .effector => true
  | .agent => false

-- ════════════════════════════════════════════════════
-- § 3b. Reduction to Proto-Role Entailments
-- ════════════════════════════════════════════════════

/-! K-G's EFFECTOR/AGENT distinction (@cite{van-valin-wilkins-1996})
    partially reduces to @cite{dowty-1991}'s proto-role entailments.

    The reduction: EFFECTOR verbs entail causation but NOT volition
    for their subject. AGENT verbs entail both. Volition is the
    discriminating feature.

    Where it reduces: for every Spanish verb with a `causerSpec`,
    checking `volition` in the subject's entailment profile yields
    the same classification. The alternation prediction chains:
    entailment profile → CauserSpec → anticausativization.

    Where it doesn't reduce conceptually: K-G's EFFECTOR is defined
    by what the verb LACKS (thematic specification of the causer),
    while Dowty's system specifies what the verb ENTAILS (individual
    proto-role features). These are different theoretical objects that
    happen to align for the causative alternation. A hypothetical verb
    entailing sentience but not volition for its causer would be
    classified as EFFECTOR by `toCauserSpec` — correctly, since it
    would still admit non-agentive causers — but its EFFECTOR status
    would carry more structure than K-G's underspecification account
    predicts. -/

open Semantics.Lexical.Verb.EntailmentProfile

/-- Derive `CauserSpec` from a proto-role entailment profile.
    Volition is the discriminating feature:
    - volition → AGENT (thematically specified causer)
    - causation without volition → EFFECTOR (underspecified causer)
    - neither → not a causer at all -/
def toCauserSpec (p : EntailmentProfile) : Option CauserSpec :=
  if p.volition then some .agent
  else if p.causation then some .effector
  else none

/-- The derivation matches the stipulated `causerSpec` for every
    Spanish verb that has both fields populated. -/
theorem causerSpec_matches_profile :
    (allVerbs.filter (fun v => v.causerSpec.isSome && v.subjectEntailments.isSome)).all
      (fun v => v.subjectEntailments.bind toCauserSpec == v.causerSpec) = true := by
  native_decide

/-- Volition is the discriminating feature: all EFFECTOR verbs have
    `volition = false` in their subject profile. -/
theorem effector_lacks_volition :
    (allVerbs.filter (fun v => v.causerSpec == some .effector)).all
      (fun v => v.subjectEntailments.map (·.volition) == some false) = true := by
  native_decide

/-- All AGENT verbs have `volition = true` in their subject profile. -/
theorem agent_has_volition :
    (allVerbs.filter (fun v => v.causerSpec == some .agent)).all
      (fun v => v.subjectEntailments.map (·.volition) == some true) = true := by
  native_decide

/-- Both EFFECTOR and AGENT verbs satisfy `isEffector` (movement ∨ IE
    with causation). This is why `isEffector` alone cannot distinguish
    them — it's a necessary but not sufficient condition for K-G's
    EFFECTOR. The AGENT/EFFECTOR split requires checking volition. -/
theorem both_satisfy_causation :
    (allVerbs.filter (fun v => v.causerSpec.isSome)).all
      (fun v => v.subjectEntailments.map (·.causation) == some true) = true := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 4. The Main Prediction (§§3.1–3.2)
-- ════════════════════════════════════════════════════

/-! The central empirical prediction: a verb anticausativizes iff its
    causer is underspecified (EFFECTOR). This is validated against the
    Spanish fragment data. -/

/-- All EFFECTOR verbs in the Spanish fragment alternate. -/
theorem effector_verbs_alternate :
    (allVerbs.filter (fun v => v.causerSpec == some .effector)).all
      (·.causativeAlternation) = true := by native_decide

/-- No AGENT verb in the Spanish fragment alternates. -/
theorem agent_verbs_dont_alternate :
    (allVerbs.filter (fun v => v.causerSpec == some .agent)).all
      (!·.causativeAlternation) = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 5. Non-Entailment of Inchoative by Causative (§3.5)
-- ════════════════════════════════════════════════════

/-! Contrary to the received wisdom (from @cite{lakoff-1965}), the
    reflexivization analysis predicts that causative does NOT entail
    inchoative for derived inchoatives.

    Causative *romper*: ∃v[CAUSE(v,e) ∧ EFFECTOR(v,y) ∧ ...]
      — the effector y and undergoer x can be DISTINCT participants.
    Inchoative *romperse*: ∃v[CAUSE(v,e) ∧ EFFECTOR(v,x) ∧ ...]
      — the effector and undergoer MUST be the SAME participant.

    A causative event where the effector and undergoer are distinct
    satisfies the causative but not the inchoative. The Spanish data
    in exx. 56–57 confirm this: a causative can be true while the
    derived inchoative is denied.

    We model this with a minimal 2-entity domain. -/

/-- A minimal 2-entity domain for the non-entailment model. -/
inductive SmallEntity where
  | glass   -- el vaso (the glass)
  | juan    -- Juan (the external causer)
  deriving DecidableEq, Repr

/-- A causative relation R(effector, undergoer) representing a
    specific breaking event: Juan broke the glass.
    Only the pair (Juan, glass) satisfies the relation. -/
def breakRelation : SmallEntity → SmallEntity → Bool
  | .juan, .glass => true
  | _, _          => false

/-- The causative is satisfied: Juan broke the glass. -/
theorem causative_satisfied :
    breakRelation .juan .glass = true := rfl

/-- The inchoative denotation is the reflexivization of the causative
    (§2.2, eq. 19): ⟦*se*⟧(⟦*romper*⟧) restricts to the diagonal.
    The glass is not its own effector in this scenario. -/
theorem inchoative_not_satisfied :
    reflexivizeBool breakRelation .glass = false := rfl

/-- Non-entailment derived from reflexivization: there exists a
    model where the causative is true but the inchoative is false.
    This follows from the reflexivization operator restricting R to
    its diagonal — a point (Juan, glass) off the diagonal satisfies
    the causative but the diagonal point (glass, glass) does not.
    (exx. 56–57) -/
theorem causative_does_not_entail_inchoative :
    breakRelation .juan .glass = true ∧
    reflexivizeBool breakRelation .glass = false := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 6. Por Sí Solo / By Itself Diagnostic (§§3.4, 4.1)
-- ════════════════════════════════════════════════════

/-! *por sí solo* 'by itself' requires a CAUSE operator in the
    denotation of the verb it modifies. It is:
    - Acceptable with derived inchoatives (*romperse*, *abrirse*)
    - Unacceptable with passives (*fue hundido* 'was sunk')
    - Unacceptable with statives (*saber* 'know', *ser rojo* 'be red')
    - Unacceptable with internally caused COS verbs (*empeorar*, *crecer*)

    This diagnostic independently confirms that derived inchoatives
    retain CAUSE. -/

/-- Externally caused COS verbs have CAUSE in their LSR and
    license *por sí solo*. -/
theorem external_has_cause :
    CausationType.hasCauseInLSR .external = true := rfl

/-- Internally caused COS verbs lack CAUSE and reject *por sí solo*. -/
theorem internal_no_cause :
    CausationType.hasCauseInLSR .internal = false := rfl

/-- The Albanian "feel like" construction (§4.2) provides independent
    evidence: its "unintended cause" reading (Kallulli 2006b) is
    available only for verbs with CAUSE in their LSR. COS verbs
    like *break* get the reading; non-causative verbs like *eat* do not.
    This is the same structural property that `hasCauseInLSR` tests. -/
theorem feel_like_requires_cause :
    CausationType.hasCauseInLSR .external = true ∧
    CausationType.hasCauseInLSR .internal = false := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 7. Monotonicity Hypothesis (§1, §4)
-- ════════════════════════════════════════════════════

/-! The Monotonicity Hypothesis (MH): word formation operations do not
    remove operators from lexical semantic representations. This is a
    constraint on the FORM of word formation rules, not on their output.

    @cite{koontz-garboden-2009} argues that anticausativization is the
    strongest apparent counterexample to the MH, since the deletion
    analysis requires removing the CAUSE operator. The reflexivization
    analysis resolves this: no operator is deleted, the relation is
    simply reflexivized. -/

/-- On the reflexivization analysis, anticausativization is the
    identity on operator lists — it satisfies the MH. -/
theorem reflexivization_satisfiesMH_verbHead :
    satisfiesMH (identityOp (Op := VerbHead)) :=
  identityOp_satisfiesMH

/-- On the deletion analysis, anticausativization removes vCAUSE —
    it does not satisfy the MH. -/
theorem deletion_of_cause_not_satisfiesMH :
    ¬ satisfiesMH (deleteOp VerbHead.vCAUSE) :=
  deleteOp_not_satisfiesMH _

/-- Concrete instance: the inchoative operator list [vCAUSE, vGO, vBE]
    is monotonically preserved by reflexivization. -/
theorem reflexivization_monotonic :
    isMonotonic
      [VerbHead.vCAUSE, .vGO, .vBE]
      [VerbHead.vCAUSE, .vGO, .vBE] = true := by native_decide

/-- Concrete instance: deleting vCAUSE from the inchoative list
    breaks monotonicity. -/
theorem deletion_not_monotonic :
    isMonotonic
      [VerbHead.vCAUSE, .vGO, .vBE]
      [VerbHead.vGO, .vBE] = false := by native_decide

-- ════════════════════════════════════════════════════
-- § 8. Bridge: Reflexivization ↔ ValencyAlternation
-- ════════════════════════════════════════════════════

/-! @cite{koontz-garboden-2009}'s core claim is that what @cite{creissels-2025}
    calls `decausativization` (A suppressed from participant structure) is
    semantically `reflexivization` (A and P cumulated). The structural
    effect looks like decausativization — the derived construction is
    intransitive with a single S argument — but the semantic operation
    is reflexivization of the causative denotation.

    On Creissels' framework, reflexivization and decausativization are
    distinct: reflexivization cumulates A and P, while decausativization
    suppresses A. K-G argues the surface decausativization in languages
    with SE-marking is semantically reflexivization. -/

/-- Decausativization suppresses A; reflexivization cumulates A and P. -/
theorem structural_distinction :
    decausativization.fateOfA = .suppressed ∧
    reflexivization.fateOfA = .cumulated := ⟨rfl, rfl⟩

/-- K-G's claim: the SE-marked form is semantically reflexivization
    (cumulation of A and P), not decausativization (suppression of A).
    The surface effect looks like valency decrease, but the underlying
    operation is cumulation — both arguments are still semantically
    present, identified with each other. -/
theorem reflexivization_is_cumulation :
    reflexivization.involvesCumulation = true ∧
    decausativization.involvesCumulation = false := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 9. Bridge: IntransitivizationType
-- ════════════════════════════════════════════════════

/-! @cite{krejci-2012}'s `IntransitivizationType.anticausative` says the
    external cause is removed (monoeventive). @cite{koontz-garboden-2009}
    says it is retained via reflexivization (bieventive). These are
    competing analyses.

    The library now records both. On K-G's analysis, what Krejci calls
    "anticausative" is actually a special case of "reflexive" where the
    EFFECTOR underspecification makes the reflexive reading look like
    an anticausative. -/

/-- On Krejci's analysis, anticausatives are monoeventive. -/
theorem krejci_anticausative_monoeventive :
    IntransitivizationType.isBieventive .anticausative = false := rfl

/-- On Krejci's analysis, reflexives are bieventive. -/
theorem krejci_reflexive_bieventive :
    IntransitivizationType.isBieventive .reflexive = true := rfl

/-- K-G's claim: anticausativization IS reflexivization. The
    "anticausative" reading arises from EFFECTOR underspecification,
    not from a structurally distinct operation. -/
theorem kg_anticausative_is_reflexivization :
    AnticausativeAnalysis.retainsCause .reflexivization = true ∧
    AnticausativeAnalysis.preservesMH .reflexivization = true := ⟨rfl, rfl⟩

/-- The deletion analysis fails the MH. -/
theorem deletion_violates_mh :
    AnticausativeAnalysis.preservesMH .deletion = false := rfl

-- ════════════════════════════════════════════════════
-- § 10. Cross-Linguistic Morphological Evidence (§3.3)
-- ════════════════════════════════════════════════════

/-! Haspelmath (1990): in 9 of 13 languages with anticausative markers,
    the same marker also serves as a reflexive marker. This is the
    expected state of affairs if anticausativization IS reflexivization,
    and would be a remarkable coincidence on any other analysis. -/

/-- Cross-linguistic anticausative/reflexive marker syncretism data
    from Haspelmath 1990, cited in @cite{koontz-garboden-2009} (35). -/
structure MarkerSyncretismDatum where
  language : String
  hasReflexiveUse : Bool
  hasAnticausativeUse : Bool
  deriving Repr, BEq

def haspelmathData : List MarkerSyncretismDatum :=
  [ { language := "Tigre",         hasReflexiveUse := true,  hasAnticausativeUse := true }
  , { language := "Motu",          hasReflexiveUse := true,  hasAnticausativeUse := true }
  , { language := "O'odham",       hasReflexiveUse := true,  hasAnticausativeUse := true }
  , { language := "Mod. Greek",    hasReflexiveUse := true,  hasAnticausativeUse := true }
  , { language := "Kanuri",        hasReflexiveUse := true,  hasAnticausativeUse := true }
  , { language := "Margi",         hasReflexiveUse := true,  hasAnticausativeUse := true }
  , { language := "Uigur",         hasReflexiveUse := false, hasAnticausativeUse := true }
  , { language := "Udmurt",        hasReflexiveUse := true,  hasAnticausativeUse := true }
  , { language := "Nimboran",      hasReflexiveUse := false, hasAnticausativeUse := true }
  , { language := "Danish",        hasReflexiveUse := false, hasAnticausativeUse := true }
  , { language := "Latin (r)",     hasReflexiveUse := true,  hasAnticausativeUse := true }
  , { language := "Latin (esse)",  hasReflexiveUse := true,  hasAnticausativeUse := true }
  , { language := "Mwera",         hasReflexiveUse := false, hasAnticausativeUse := true }
  ]

/-- 9 of 13 languages have syncretism (marker serves both functions). -/
theorem syncretism_majority :
    (haspelmathData.filter (fun d => d.hasReflexiveUse && d.hasAnticausativeUse)).length = 9 := by
  native_decide

/-- All 13 languages have anticausative use (selection criterion). -/
theorem all_have_anticausative :
    haspelmathData.all (·.hasAnticausativeUse) = true := by native_decide

end Phenomena.Causation.Studies.KoontzGarboden2009
