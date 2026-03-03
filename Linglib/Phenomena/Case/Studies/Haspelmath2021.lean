import Linglib.Core.Prominence
import Linglib.Core.FormFrequency
import Linglib.Core.Discourse.InformationStructure
import Linglib.Phenomena.Case.Studies.Aissen2003
import Linglib.Phenomena.Case.Studies.DeHoopMalchukov2008
import Linglib.Phenomena.Alignment.Typology

/-!
# @cite{haspelmath-2021}: Explaining Argument-Coding Splits @cite{haspelmath-2021}

Explaining argument-coding splits with role-reference associations.
Linguistics 59(5): 1231–1270.

## Overview

Haspelmath proposes a single meta-universal — the **Role-Reference
Association Universal** (Universal 1) — that subsumes differential object
marking, split ergativity, ditransitive splits, and person-scenario splits
under one generalization: deviations from the usual associations of role
rank and referential prominence tend to be coded by longer grammatical forms.

The paper further argues that this universal itself reduces to a
**form-frequency correspondence** (§10.2): the "usual" associations ARE the
frequent ones, and frequent expressions get shorter forms (Zipf).

## The Paper's 14 Universals

The paper states 14 numbered universals organized hierarchically
(Figure 1, §11.1):

### Meta-universals (§2)
- **Universal 1**: Role-Reference Association Universal — deviations from
  usual role-prominence associations get longer coding
- **Universal 2**: Usual role-reference associations — A/R tend to be
  prominent, P/T tend to be non-prominent

### Single-argument coding splits (§3–5)
- **Universal 3**: Single-argument coding universal (general)
- **Universal 4**: Split P flagging / DOM (§4.1)
- **Universal 5**: Scenario coding universal (§3, §6)
- **Universal 6**: Split A flagging / DSM (§4.2)
- **Universal 7**: Split R flagging (§5)
- **Universal 8**: Split T flagging (§5)

### Scenario and voice splits (§6–9)
- **Universal 9**: Monotransitive scenario splits (§6)
- **Universal 10**: Ditransitive person-role splits (§7)
- **Universal 11**: Relative scenario splits (§8)
- **Universal 12**: Inverse (§9)
- **Universal 13**: Passive (§9)
- **Universal 14**: Dative alternation (§9)

## What We Formalize

This file captures Universals 1–9 using existing linglib infrastructure.
Universals 4 and 6 are already proven in `Aissen2003.lean` and
`DeHoopMalchukov2008.lean` respectively — we re-export those results.
Universals 10–14 (ditransitive scenarios, inverse, passive, dative
alternation) are noted but require additional infrastructure.

-/

namespace Phenomena.Case.Studies.Haspelmath2021

open Core.Prominence
open Core.FormFrequency
open Core.ConstraintEvaluation
open Phenomena.Case.Studies.Aissen2003
open Phenomena.Case.Studies.DeHoopMalchukov2008
open Phenomena.Alignment.Typology

-- ============================================================================
-- § 1: Universal 1 — The Role-Reference Association Universal
-- ============================================================================

/-! **Universal 1** (@cite{haspelmath-2021}, §2, statement (5)):

    "Deviations from the usual associations of role rank and referential
    prominence tend to be coded by longer grammatical forms (if the coding
    is asymmetric)."

    This is the paper's central claim — a single meta-universal that
    subsumes all 13 other universals. It is formalized here as the
    conjunction of two properties: (a) the direction of differential
    marking matches the role's default prominence zone, and (b) the
    form-frequency correspondence assigns higher frequency to the
    usual (default) zone. -/

/-- Universal 1: The Role-Reference Association Universal holds for all
    monotransitive and ditransitive roles. For each role, the direction of
    differential marking matches the deviation from the usual association.

    - P/T: prominent end is unusual → differential marking targets prominent
    - A/R: non-prominent end is unusual → differential marking targets
      non-prominent -/
theorem universal1_role_reference_association :
    -- P: prominent end is unusual → marked
    differentialTargetsProminent .P = true ∧
    -- T: prominent end is unusual → marked (like P)
    differentialTargetsProminent .T = true ∧
    -- A: non-prominent end is unusual → marked
    differentialTargetsProminent .A = false ∧
    -- R: non-prominent end is unusual → marked (like A)
    differentialTargetsProminent .R = false := ⟨rfl, rfl, rfl, rfl⟩

/-- Universal 1 is grounded by the form-frequency correspondence (§10.2):
    the frequency proxy assigns higher frequency to the "usual" (default)
    zone for every role. Usual = frequent = short coding. -/
theorem universal1_frequency_grounding (role : ArgumentRole)
    (a : AnimacyLevel) (d : DefinitenessLevel) :
    (isDefaultZone role a d = true) →
    (frequencyProxy role a d ≥ 3) :=
  frequency_proxy_matches_default role a d

-- ============================================================================
-- § 2: Universal 2 — Usual Role-Reference Associations
-- ============================================================================

/-! **Universal 2** (@cite{haspelmath-2021}, §2, statement (6)):

    "Arguments with higher-ranked roles tend to be more referentially
    prominent, and vice versa."

    This defines the *baseline* for Universal 1: A/R arguments (higher role
    rank) tend to be human, definite, topical. P/T arguments (lower role
    rank) tend to be inanimate, indefinite, new-information.

    Formalized as: high-rank roles have high default prominence, low-rank
    roles have low default prominence. -/

/-- Universal 2: Role rank determines default prominence direction.
    A and R are high-default (expect prominent referents).
    P and T are low-default (expect non-prominent referents). -/
theorem universal2_usual_associations :
    ArgumentRole.A.highDefault = true ∧
    ArgumentRole.R.highDefault = true ∧
    ArgumentRole.P.lowDefault = true ∧
    ArgumentRole.T.lowDefault = true := ⟨rfl, rfl, rfl, rfl⟩

/-- Universal 2 is consistent with role rank: A > R > S > T > P.
    Higher role rank → higher default prominence expectation. -/
theorem universal2_role_rank_ordering :
    ArgumentRole.A.roleRank > ArgumentRole.R.roleRank ∧
    ArgumentRole.R.roleRank > ArgumentRole.S.roleRank ∧
    ArgumentRole.S.roleRank > ArgumentRole.T.roleRank ∧
    ArgumentRole.T.roleRank > ArgumentRole.P.roleRank := by decide

-- ============================================================================
-- § 3: Universal 3 — Single-Argument Coding Universal
-- ============================================================================

/-! **Universal 3** (@cite{haspelmath-2021}, §3, statement (13)):

    "The single-argument flagging universal: If a language has an asymmetric
    single-argument flagging split depending on some prominence scale, then
    the coding is longer for prominent P/T-arguments or for non-prominent
    A/R-arguments."

    This is the general form from which Universals 4, 6, 7, 8 follow as
    specific cases for each argument role. It applies to both flagging and
    indexing (statement (15)). -/

/-- Universal 3: The monotonicity direction is determined by role type.
    For P/T (low-default roles), differential marking targets the
    prominent end (upper set / monotone). For A/R (high-default roles),
    it targets the non-prominent end (lower set / anti-monotone).

    This subsumes both flagging and indexing channels. -/
theorem universal3_single_argument_coding :
    differentialTargetsProminent .P = true ∧
    differentialTargetsProminent .T = true ∧
    differentialTargetsProminent .A = false ∧
    differentialTargetsProminent .R = false := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 4: Universal 4 — Split P Flagging (DOM)
-- ============================================================================

/-! **Universal 4** (@cite{haspelmath-2021}, §4.1, statement (14)):

    "Split P flagging (Differential Object Marking): If a language has an
    asymmetric split in P flagging depending on some prominence scale, then
    the special flag is used on the prominent P-argument."

    This is @cite{aissen-2003}'s core result: the OT factorial typology generates
    only monotone DOM patterns — marking always starts from the prominent
    end of the animacy/definiteness scale. -/

/-- Universal 4: All OT-generated animacy DOM patterns are monotone
    (prominent Ps marked before non-prominent Ps).
    Re-exported from @cite{aissen-2003}. -/
theorem universal4_split_P_flagging : animOptima.all (λ opts =>
    opts.all (λ c =>
      (if c.an then c.hu else true) &&
      (if c.inan then c.an else true))) = true :=
  animacy_all_monotone

-- ============================================================================
-- § 5: Universal 5 — Scenario Coding Universal
-- ============================================================================

/-! **Universal 5**:

    The scenario coding universal: if a language has an asymmetric scenario
    split, then the coding is longest for upstream scenarios (P more
    prominent than A), shortest for downstream scenarios (A more prominent
    than P), and intermediate for balanced scenarios.

    This is the second major branch under Universal 1 (alongside Universal
    3). While Universal 3 conditions coding on the prominence of a single
    argument, Universal 5 conditions it on the *combination* of A-person
    and P-person. -/

/-- Downstream scenario: SAP acts on 3rd (A more prominent than P). -/
def downstreamScenario : Scenario := ⟨.first, .third⟩

/-- Upstream scenario: 3rd acts on SAP (P more prominent than A). -/
def upstreamScenario : Scenario := ⟨.third, .first⟩

/-- Balanced scenario: both 3rd person (same prominence level). -/
def balancedScenario : Scenario := ⟨.third, .third⟩

/-- Local scenario: 1st acts on 2nd (both SAP; downstream sub-case). -/
def localScenario : Scenario := ⟨.first, .second⟩

theorem downstream_is_downstream : downstreamScenario.isDownstream = true := rfl
theorem upstream_is_upstream : upstreamScenario.isUpstream = true := rfl
theorem balanced_is_balanced : balancedScenario.isBalanced = true := rfl
theorem local_is_local : localScenario.isLocal = true := rfl

/-- Universal 5: Downstream scenarios have higher A-person rank than
    upstream. Higher A-person rank = more "usual" = predicted shorter
    coding. -/
theorem universal5_downstream_shorter :
    downstreamScenario.aPerson.rank > upstreamScenario.aPerson.rank := by decide

/-- Universal 5: The downstream/upstream/balanced trichotomy is exhaustive
    for all 9 person-pair scenarios. -/
theorem universal5_trichotomy_exhaustive :
    Scenario.all.all (λ s =>
      s.isDownstream || s.isUpstream || s.isBalanced) = true := by native_decide

-- ============================================================================
-- § 6: Universal 6 — Split A Flagging (DSM)
-- ============================================================================

/-! **Universal 6** (@cite{haspelmath-2021}, §4.2, statement (21)):

    "Split A flagging (Differential Subject Marking): If a language has an
    asymmetric split in A flagging depending on some prominence scale, then
    the special flag is used on the non-prominent A-argument."

    The mirror image of Universal 4. Verified via @cite{de-hoop-malchukov-2008} Distinguish constraint: weak (non-prominent) subjects get overt
    ergative marking. -/

/-- Universal 6: Under Distinguish, weak subjects are marked (Fore pattern).
    Re-exported from @cite{de-hoop-malchukov-2008}. -/
theorem universal6_split_A_flagging :
    superoptimal allPairs (profileFor [distinguishSubj, economy])
    = [(CaseForm.zero, Strength.strong), (CaseForm.overt, Strength.weak)] :=
  dsm_distinguish

-- ============================================================================
-- § 7: Universals 7–8 — Ditransitive Splits (R and T flagging)
-- ============================================================================

/-! **Universal 7** (@cite{haspelmath-2021}, §5, statement (26)):

    "Split R flagging: If a language has an asymmetric split in R flagging
    depending on some prominence scale, then the special flag is used on
    the non-prominent R-argument."

    R behaves like A: both are high-rank roles whose differential marking
    targets the non-prominent end.

    **Universal 8** (@cite{haspelmath-2021}, §5, statement (27)):

    "Split T flagging: If a language has an asymmetric split in T flagging
    depending on some prominence scale, then the special flag is used on
    the prominent T-argument."

    T behaves like P: both are low-rank roles whose differential marking
    targets the prominent end. -/

/-- Universal 7: R targets the non-prominent end (like A). -/
theorem universal7_R_like_A :
    differentialTargetsProminent .R = differentialTargetsProminent .A :=
  rfl

/-- Universal 8: T targets the prominent end (like P). -/
theorem universal8_T_like_P :
    differentialTargetsProminent .T = differentialTargetsProminent .P :=
  rfl

/-- R monotonicity uses the same direction as A monotonicity. -/
theorem R_monotone_like_A (profile : DifferentialMarkingProfile) :
    ({ profile with role := .R } : DifferentialMarkingProfile).isMonotone =
    ({ profile with role := .A } : DifferentialMarkingProfile).isMonotone :=
  rfl

/-- T monotonicity uses the same direction as P monotonicity. -/
theorem T_monotone_like_P (profile : DifferentialMarkingProfile) :
    ({ profile with role := .T } : DifferentialMarkingProfile).isMonotone =
    ({ profile with role := .P } : DifferentialMarkingProfile).isMonotone :=
  rfl

-- ============================================================================
-- § 8: Universal 9 — Monotransitive Scenario Splits
-- ============================================================================

/-! **Universal 9**: Monotransitive scenario splits.

    When argument coding depends on the person combination (A-person ×
    P-person), coding is longest for upstream scenarios (3→SAP) and
    shortest for downstream (SAP→3). Local scenarios (SAP↔SAP) tend
    to get short coding as both arguments are highly prominent. -/

/-- Universal 9: Local scenarios have SAP in both slots — the most
    prominent combination. -/
theorem universal9_local_both_SAP :
    localScenario.aPerson.isSAP = true ∧
    localScenario.pPerson.isSAP = true := ⟨rfl, rfl⟩

/-- Universal 9: Direct (SAP→3) scenarios are downstream. -/
theorem universal9_direct_is_downstream :
    (⟨.first, .third⟩ : Scenario).isDirect = true ∧
    (⟨.first, .third⟩ : Scenario).isDownstream = true := ⟨rfl, rfl⟩

/-- Universal 9: Inverse (3→SAP) scenarios are upstream. -/
theorem universal9_inverse_is_upstream :
    (⟨.third, .first⟩ : Scenario).isInverse = true ∧
    (⟨.third, .first⟩ : Scenario).isUpstream = true := ⟨rfl, rfl⟩

-- ============================================================================
-- § 9: Ditransitive Alignment Parallels
-- ============================================================================

/-! The parallel between monotransitive and ditransitive alignment is a
    structural consequence of the role-rank hierarchy (Universal 2):

    - Indirective (R marked, T = P) parallels accusative (P marked, A = S)
    - Secundative (T marked, R = P) parallels ergative (A marked, P = S)

    This follows from Universals 7–8: R behaves like A, T behaves like P. -/

/-- Ditransitive alignment parallels monotransitive alignment:
    indirective marks R (the high-rank role), secundative marks T
    (the low-rank role). -/
theorem ditransitive_parallels_monotransitive :
    DitransitiveAlignment.indirective.marksR = true ∧
    DitransitiveAlignment.indirective.marksT = false ∧
    DitransitiveAlignment.secundative.marksT = true ∧
    DitransitiveAlignment.secundative.marksR = false := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 10: DOM ↔ Accusative, DSM ↔ Ergative (@cite{de-hoop-malchukov-2008})
-- ============================================================================

/-! The correlation between DOM and accusative alignment, and between DSM
    and ergative alignment, is independently derived in @cite{de-hoop-malchukov-2008} via the PaIP (Primary Actant Immunity Principle). @cite{haspelmath-2021} discusses this as background but does not number it as one of
    his 14 universals.

    This theorem re-exports the De Hoop & Malchukov result for reference. -/

/-- DOM ↔ accusative, DSM ↔ ergative (@cite{de-hoop-malchukov-2008}, not a
    numbered Haspelmath universal — included for cross-reference). -/
theorem alignment_correlation_deHoopMalchukov :
    -- Nom-acc: DOM possible, DSM blocked by PaIP
    markingPattern [identify, economy] = ⟨.overt, .zero⟩ ∧
    markingPattern [paip, identify] = ⟨.zero, .zero⟩ ∧
    -- Ergative: DSM possible, DOM blocked by PaIP
    markingPattern [distinguishSubj, economy] = ⟨.zero, .overt⟩ ∧
    markingPattern [paip, distinguishObj] = ⟨.zero, .zero⟩ :=
  alignment_correlation

-- ============================================================================
-- § 11: Bridge — Usual Discourse Status (@cite{haspelmath-2021}, §9)
-- ============================================================================

open Core.InformationStructure

/-- Usual discourse-status association:
    A/R tend to be given (topical); P/T tend to be new (focal).
    This bridges ArgumentRole (Prominence) and DiscourseStatus
    (InformationStructure) in the study file to keep Core loosely coupled. -/
def usualDiscourseStatus : ArgumentRole → DiscourseStatus
  | .A | .R | .S => .given
  | .P | .T      => .new

-- ============================================================================
-- § 12: Universal 10 — Ditransitive Person-Role Constraint (§7)
-- ============================================================================

/-! **Universal 10**:

    "If a language has a person-role constraint in its ditransitive
    construction, it is restricted to T=SAP, R=3."

    Reuse `Scenario` for R×T pairs (aPerson = R, pPerson = T). When T is
    SAP and R is 3rd (upstream ditransitive), coding is longer — predicted
    by the role-reference association (R is high-rank, so R=3rd is unusual;
    T is low-rank, so T=SAP is unusual). -/

/-- Upstream ditransitive scenario: R=3rd, T=SAP (both deviate from usual). -/
def ditransUpstream : Scenario := ⟨.third, .first⟩

theorem universal10_ditrans_person_role :
    ditransUpstream.isUpstream = true ∧
    ditransUpstream.frequencyClass = 0 := ⟨rfl, rfl⟩

/-- Downstream ditransitive: R=SAP, T=3rd (both match usual). -/
def ditransDownstream : Scenario := ⟨.first, .third⟩

theorem universal10_ditrans_downstream :
    ditransDownstream.isDownstream = true ∧
    ditransDownstream.frequencyClass = 2 := ⟨rfl, rfl⟩

-- ============================================================================
-- § 13: Universal 11 — Relative Scenario Splits (§8)
-- ============================================================================

/-! **Universal 11**:

    "If a language has a relative scenario split, then the coding of
    upstream scenarios is longer (or at least not shorter) than the
    coding of downstream scenarios."

    Frequency class decreases monotonically: downstream > balanced > upstream.
    By the form-frequency correspondence, coding length increases in the
    same order. -/

theorem universal11_relative_scenario :
    downstreamScenario.frequencyClass > balancedScenario.frequencyClass ∧
    balancedScenario.frequencyClass > upstreamScenario.frequencyClass := by decide

-- ============================================================================
-- § 14: Universal 12 — Inverse (§9)
-- ============================================================================

/-! **Universal 12**:

    "Inverse verb forms (marking upstream scenarios) tend to be
    morphologically more complex than direct verb forms."

    Upstream = unusual = lower frequency class = predicted longer by FFC. -/

theorem universal12_inverse :
    upstreamScenario.frequencyClass < downstreamScenario.frequencyClass := by decide

-- ============================================================================
-- § 15: Universal 13 — Passive (§9)
-- ============================================================================

/-! **Universal 13**:

    "Passive voice is preferred when A is non-given (unusual for A) and/or
    P is non-new (unusual for P)."

    Active voice is the "usual" frame where A=given, P=new. Passive is
    preferred when discourse statuses deviate from these defaults. -/

/-- Passive is preferred when A's or P's discourse status deviates from
    the usual association. -/
def passivePreferred (aStatus pStatus : DiscourseStatus) : Bool :=
  aStatus != usualDiscourseStatus .A ||
  pStatus != usualDiscourseStatus .P

theorem universal13_passive :
    passivePreferred .new .given = true ∧   -- deviant → passive
    passivePreferred .given .new = false     -- usual → active
    := ⟨rfl, rfl⟩

-- ============================================================================
-- § 16: Universal 14 — Dative Alternation (§9)
-- ============================================================================

/-! **Universal 14**:

    "The prepositional dative (longer form) is preferred when R is non-given
    and/or T is non-new."

    The double-object construction is the shorter form, preferred when
    discourse statuses match the usual associations (R=given, T=new). -/

/-- PP-dative (longer) is preferred when R's or T's discourse status
    deviates from the usual association. -/
def ppDativePreferred (rStatus tStatus : DiscourseStatus) : Bool :=
  rStatus != usualDiscourseStatus .R ||
  tStatus != usualDiscourseStatus .T

theorem universal14_dative_alternation :
    ppDativePreferred .new .given = true ∧   -- deviant → PP-dative
    ppDativePreferred .given .new = false     -- usual → DOC
    := ⟨rfl, rfl⟩

-- ============================================================================
-- § 17: Form-Frequency Unification
-- ============================================================================

/-! **Form-frequency unification** (@cite{haspelmath-2021}, §10.2, statement 68):

    All 14 universals reduce to Zipf's form-frequency correspondence.
    The scenario-level check: for every pair of scenarios where one is
    downstream and the other upstream, the downstream one has a strictly
    higher frequency class. -/

theorem scenario_frequency_consistent :
    Scenario.all.all (λ s1 =>
      Scenario.all.all (λ s2 =>
        if s1.isDownstream && s2.isUpstream
        then s1.frequencyClass > s2.frequencyClass
        else true)) = true := by native_decide

end Phenomena.Case.Studies.Haspelmath2021
