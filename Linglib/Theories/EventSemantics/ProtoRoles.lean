/-
# Dowty (1991) Proto-Roles and Argument Selection

Dowty (1991) "Thematic Proto-Roles and Argument Selection" replaces discrete
thematic roles (agent, patient, etc.) with **cluster concepts**: Proto-Agent
and Proto-Patient are each defined by a list of independent entailments.
Argument selection follows from *counting* which argument has more P-Agent
vs P-Patient entailments.

## Key results

- **Argument Selection Principle (ASP)**: The argument with the most P-Agent
  entailments is lexicalized as subject; the argument with the most P-Patient
  entailments is lexicalized as object.
- **Corollary 1**: Equal scores → alternation allowed (buy/sell, like/please).
- **Corollary 2**: Intransitive subjects with predominantly P-Patient
  entailments are unaccusative (arrive, die).
- **Role hierarchy**: Agent > Instrument/Experiencer > Patient, derived from
  entailment counting rather than stipulated.

## Bridges

- Cruse (1973) agentivity features derived from P-Agent entailments (§5)
- ThetaRole (Fragment enum) mapped to canonical profiles (§6)
- Krifka (1998) SINC = P-Patient entailment (b) incrementalTheme (§7)
- ChangeOfState/CoSType = P-Patient entailment (a) changeOfState (§8)
- CausativeBuilder = P-Agent entailment (c) causation (§9)
- VerbEntry.unaccusative prediction from entailment counting (§10)

## References

- Dowty, D. (1991). Thematic Proto-Roles and Argument Selection.
  Language 67(3), 547–619.
- Levin, B. (2022). Proto-roles at 30. In *Thematic Roles*, 337–367.
- Rappaport Hovav, M. & Levin, B. (2024). The landscape of verb classes.
- Beavers, J. (2010). The structure of lexical meaning. Language 86(4).
-/

import Linglib.Theories.EventSemantics.Agentivity
import Linglib.Theories.EventSemantics.Krifka1998
import Linglib.Theories.IntensionalSemantics.Causative.Builder
import Linglib.Theories.TruthConditional.Verb.ChangeOfState.Theory
import Linglib.Fragments.English.Predicates.Verbal

namespace Theories.EventSemantics.ProtoRoles

open Theories.EventSemantics.Agentivity
open Theories.EventSemantics.Krifka1998
open Theories.NadathurLauer2020.Builder
open TruthConditional.Verb.ChangeOfState
open Fragments.English.Predicates.Verbal

-- ════════════════════════════════════════════════════
-- § 1. Entailment Profile (Dowty 1991 pp.572–573)
-- ════════════════════════════════════════════════════

/-- The 10 independent entailments defining Proto-Agent and Proto-Patient
    (Dowty 1991 pp.572–573).

    Proto-Agent entailments (a)–(e):
    - volition, sentience, causation, movement, independent existence

    Proto-Patient entailments (a)–(e):
    - change of state, incremental theme, causally affected, stationary,
      dependent existence -/
structure EntailmentProfile where
  -- Proto-Agent entailments
  /-- (a) volitional involvement in the event -/
  volition            : Bool
  /-- (b) sentience/perception -/
  sentience           : Bool
  /-- (c) causing an event or change of state in another participant -/
  causation           : Bool
  /-- (d) movement (relative to another participant) -/
  movement            : Bool
  /-- (e) exists independently of the event named by the verb -/
  independentExistence : Bool
  -- Proto-Patient entailments
  /-- (a) undergoes change of state -/
  changeOfState       : Bool
  /-- (b) incremental theme (Krifka's SINC) -/
  incrementalTheme    : Bool
  /-- (c) causally affected by another participant -/
  causallyAffected    : Bool
  /-- (d) stationary relative to another participant -/
  stationary          : Bool
  /-- (e) does not exist independently of the event -/
  dependentExistence  : Bool
  deriving DecidableEq, Repr, BEq

-- ════════════════════════════════════════════════════
-- § 2. Entailment Counting
-- ════════════════════════════════════════════════════

/-- Count of Proto-Agent entailments that hold for this profile. -/
def EntailmentProfile.pAgentScore (p : EntailmentProfile) : Nat :=
  p.volition.toNat + p.sentience.toNat + p.causation.toNat +
  p.movement.toNat + p.independentExistence.toNat

/-- Count of Proto-Patient entailments that hold for this profile. -/
def EntailmentProfile.pPatientScore (p : EntailmentProfile) : Nat :=
  p.changeOfState.toNat + p.incrementalTheme.toNat +
  p.causallyAffected.toNat + p.stationary.toNat +
  p.dependentExistence.toNat

-- ════════════════════════════════════════════════════
-- § 3. Argument Selection Principle (Dowty 1991 p.576)
-- ════════════════════════════════════════════════════

/-- Dowty's ASP: "In predicates with grammatical subject and object, the
    argument for which the predicate entails the greatest number of
    Proto-Agent properties will be lexicalized as the subject." -/
def selectsSubject (p : EntailmentProfile) : Bool :=
  p.pAgentScore > p.pPatientScore

/-- The argument with the most P-Patient entailments → object. -/
def selectsObject (p : EntailmentProfile) : Bool :=
  p.pPatientScore > p.pAgentScore

/-- Corollary 1 (Dowty 1991 p.579): When subject and object have equal
    P-Agent scores and equal P-Patient scores, alternation is predicted
    (buy/sell, like/please). -/
def allowsAlternation (subj obj : EntailmentProfile) : Bool :=
  subj.pAgentScore == obj.pAgentScore &&
  subj.pPatientScore == obj.pPatientScore

-- ════════════════════════════════════════════════════
-- § 4. Canonical Verb Profiles (Meaning Postulates)
-- ════════════════════════════════════════════════════

-- Each verb's argument gets an EntailmentProfile. These are meaning
-- postulates: the entailments a verb's truth conditions impose on
-- each argument position.

/-- "kick" subject: V+S+C+M+IE (prototypical agent, 5 P-Ag) -/
def kickSubjectProfile : EntailmentProfile :=
  ⟨true, true, true, true, true, false, false, false, false, false⟩

/-- "kick" object: CoS+CA+St (3 P-Pat) -/
def kickObjectProfile : EntailmentProfile :=
  ⟨false, false, false, false, false, true, false, true, true, false⟩

/-- "build" subject: V+S+C+M+IE (5 P-Ag) -/
def buildSubjectProfile : EntailmentProfile :=
  ⟨true, true, true, true, true, false, false, false, false, false⟩

/-- "build" object: CoS+IT+CA+DE (4 P-Pat, incremental theme, dependent existence) -/
def buildObjectProfile : EntailmentProfile :=
  ⟨false, false, false, false, false, true, true, true, false, true⟩

/-- "see" subject: S+IE (experiencer, 2 P-Ag) -/
def seeSubjectProfile : EntailmentProfile :=
  ⟨false, true, false, false, true, false, false, false, false, false⟩

/-- "run" subject: V+S+M+IE (4 P-Ag, unergative) -/
def runSubjectProfile : EntailmentProfile :=
  ⟨true, true, false, true, true, false, false, false, false, false⟩

/-- "arrive" subject: M+IE+CoS (2 P-Ag, 1 P-Pat — unaccusative) -/
def arriveSubjectProfile : EntailmentProfile :=
  ⟨false, false, false, true, true, true, false, false, false, false⟩

/-- "die" subject: CoS+CA+DE (0 P-Ag, 3 P-Pat — unaccusative) -/
def dieSubjectProfile : EntailmentProfile :=
  ⟨false, false, false, false, false, true, false, true, false, true⟩

/-- "eat" subject: V+S+C+M+IE (5 P-Ag) -/
def eatSubjectProfile : EntailmentProfile :=
  ⟨true, true, true, true, true, false, false, false, false, false⟩

/-- "eat" object: CoS+IT+CA (3 P-Pat, incremental theme) -/
def eatObjectProfile : EntailmentProfile :=
  ⟨false, false, false, false, false, true, true, true, false, false⟩

-- Per-verb ASP verification theorems

theorem kickSubjectIsSubject :
    selectsSubject kickSubjectProfile = true := by native_decide

theorem kickObjectIsObject :
    selectsObject kickObjectProfile = true := by native_decide

theorem buildSubjectIsSubject :
    selectsSubject buildSubjectProfile = true := by native_decide

theorem buildObjectIsObject :
    selectsObject buildObjectProfile = true := by native_decide

theorem seeSubjectIsSubject :
    selectsSubject seeSubjectProfile = true := by native_decide

theorem runSubjectIsSubject :
    selectsSubject runSubjectProfile = true := by native_decide

theorem eatSubjectIsSubject :
    selectsSubject eatSubjectProfile = true := by native_decide

theorem eatObjectIsObject :
    selectsObject eatObjectProfile = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 5. Bridge to Cruse (1973): Features Derived from Entailments
-- ════════════════════════════════════════════════════

/-- Cruse's do-test, reformulated over Dowty entailments.

    The do-test passes iff at least one of {volition, causation, movement}
    holds — these are the P-Agent entailments that correspond to Cruse's
    four features:
    - Cruse's volitive  ≈ Dowty's volition
    - Cruse's effective ≈ Dowty's causation
    - Cruse's agentive_ ≈ Dowty's movement + volition
    - Cruse's initiative ≈ Dowty's causation + volition -/
def passesDoTestFromProfile (p : EntailmentProfile) : Bool :=
  p.volition || p.causation || p.movement

/-- Passing the do-test (from entailment profile) is equivalent to having
    at least one P-Agent entailment from {volition, causation, movement}. -/
theorem doTest_from_profile_iff_hasAgentEntailment
    (p : EntailmentProfile) :
    passesDoTestFromProfile p = true ↔
    (p.volition = true ∨ p.causation = true ∨ p.movement = true) := by
  simp [passesDoTestFromProfile, Bool.or_eq_true, or_assoc]

/-- Kick subject passes the do-test (has volition + causation + movement). -/
theorem kick_subject_passes_doTest :
    passesDoTestFromProfile kickSubjectProfile = true := by native_decide

/-- Die subject does NOT pass the do-test (no volition, causation, or movement). -/
theorem die_subject_fails_doTest :
    passesDoTestFromProfile dieSubjectProfile = false := by native_decide

/-- Arrive subject passes the do-test (has movement). -/
theorem arrive_subject_passes_doTest :
    passesDoTestFromProfile arriveSubjectProfile = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 6. Bridge to Traditional Roles (ThetaRole → EntailmentProfile)
-- ════════════════════════════════════════════════════

/-- Map each ThetaRole to its canonical entailment profile.

    This derives the discrete role labels from the underlying entailment
    space: each traditional role name is a cluster of typical entailments. -/
def ThetaRole.canonicalProfile : ThetaRole → EntailmentProfile
  | .agent       => ⟨true, true, true, true, true,     false, false, false, false, false⟩
  | .patient     => ⟨false, false, false, false, false, true, false, true, true, false⟩
  | .theme       => ⟨false, false, false, false, true,  false, false, false, true, false⟩
  | .experiencer => ⟨false, true, false, false, true,   false, false, false, false, false⟩
  | .instrument  => ⟨false, false, true, false, true,   false, false, false, false, false⟩
  | .stimulus    => ⟨false, false, true, false, true,   false, false, false, false, false⟩
  | .goal        => ⟨false, false, false, false, true,  false, false, false, false, false⟩
  | .source      => ⟨false, false, false, false, true,  false, false, false, false, false⟩

/-- Role hierarchy (Dowty 1991 p.576): Agent outscores Instrument/Experiencer
    in P-Agent entailments. -/
theorem agent_outscores_instrument :
    (ThetaRole.canonicalProfile .agent).pAgentScore >
    (ThetaRole.canonicalProfile .instrument).pAgentScore := by native_decide

theorem agent_outscores_experiencer :
    (ThetaRole.canonicalProfile .agent).pAgentScore >
    (ThetaRole.canonicalProfile .experiencer).pAgentScore := by native_decide

/-- Instrument and Experiencer have equal P-Agent scores (both = 2). -/
theorem instrument_experiencer_equal :
    (ThetaRole.canonicalProfile .instrument).pAgentScore =
    (ThetaRole.canonicalProfile .experiencer).pAgentScore := by native_decide

/-- Patient has 0 P-Agent entailments. -/
theorem patient_zero_pAgent :
    (ThetaRole.canonicalProfile .patient).pAgentScore = 0 := by native_decide

/-- Agent has 0 P-Patient entailments. -/
theorem agent_zero_pPatient :
    (ThetaRole.canonicalProfile .agent).pPatientScore = 0 := by native_decide

/-- Agent is predicted as subject (P-Agent > P-Patient). -/
theorem agent_selects_subject :
    selectsSubject (ThetaRole.canonicalProfile .agent) = true := by native_decide

/-- Patient is predicted as object (P-Patient > P-Agent). -/
theorem patient_selects_object :
    selectsObject (ThetaRole.canonicalProfile .patient) = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 7. Bridge to Krifka (1998) SINC
-- ════════════════════════════════════════════════════

/-- Dowty's P-Patient entailment (b) "incremental theme" is precisely
    Krifka's (1998) Strict Incrementality (SINC). The `incrementalTheme`
    Bool field marks that a verb's object role satisfies SINC.

    Bridge: `build` has `incrementalTheme = true`, connecting to
    `VerbIncrementality.build_sinc` in Krifka1998.lean. -/
theorem buildObject_is_incrementalTheme :
    buildObjectProfile.incrementalTheme = true := by native_decide

/-- `eat` object is also an incremental theme (SINC). -/
theorem eatObject_is_incrementalTheme :
    eatObjectProfile.incrementalTheme = true := by native_decide

/-- `kick` object is NOT an incremental theme (kick doesn't "use up" the patient). -/
theorem kickObject_not_incrementalTheme :
    kickObjectProfile.incrementalTheme = false := by native_decide

-- ════════════════════════════════════════════════════
-- § 8. Bridge to ChangeOfState / CoSType
-- ════════════════════════════════════════════════════

/-- Dowty's P-Patient entailment (a) "undergoes change of state" connects
    to the existing `CoSType` infrastructure. Any participant with
    `changeOfState = true` undergoes a state transition formalized by
    `cosSemantics` in ChangeOfState/Theory.lean. -/
theorem kickObject_changeOfState :
    kickObjectProfile.changeOfState = true := by native_decide

theorem buildObject_changeOfState :
    buildObjectProfile.changeOfState = true := by native_decide

theorem dieSubject_changeOfState :
    dieSubjectProfile.changeOfState = true := by native_decide

/-- Arrive involves change of state (change of location). -/
theorem arriveSubject_changeOfState :
    arriveSubjectProfile.changeOfState = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 9. Bridge to CausativeBuilder
-- ════════════════════════════════════════════════════

/-- Dowty's P-Agent entailment (c) "causing an event" is precisely what
    `CausativeBuilder` formalizes for periphrastic causatives (make, cause,
    force). Any argument with `causation = true` has at least 1 P-Agent point. -/
theorem causation_entailment_implies_pAgent_ge_one
    (p : EntailmentProfile) (h : p.causation = true) :
    p.pAgentScore ≥ 1 := by
  simp [EntailmentProfile.pAgentScore, h]
  omega

/-- Kick subject has the causation entailment (consistent with CausativeBuilder). -/
theorem kickSubject_has_causation :
    kickSubjectProfile.causation = true := by native_decide

/-- Build subject has the causation entailment. -/
theorem buildSubject_has_causation :
    buildSubjectProfile.causation = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 10. Unaccusativity (Dowty 1991 Corollary 2)
-- ════════════════════════════════════════════════════

/-- Dowty's Corollary 2: intransitive subjects with predominantly P-Patient
    entailments are unaccusative. -/
def predictsUnaccusative (p : EntailmentProfile) : Bool :=
  p.pPatientScore > p.pAgentScore

/-- Dowty's complement: intransitive subjects with predominantly P-Agent
    entailments are unergative. -/
def predictsUnergative (p : EntailmentProfile) : Bool :=
  p.pAgentScore > p.pPatientScore

-- die: 0 P-Ag, 3 P-Pat → unaccusative
theorem die_unaccusative :
    predictsUnaccusative dieSubjectProfile = true := by native_decide

-- arrive: 2 P-Ag, 1 P-Pat → unergative by counting (but arrive IS
-- unaccusative on other diagnostics). Dowty notes that arrive's subject
-- has movement + IE (P-Agent) but also CoS (P-Patient). The ASP
-- prediction is marginal; the VerbEntry annotation captures the
-- distributional fact.
theorem arrive_asp_prediction :
    predictsUnaccusative arriveSubjectProfile = false := by native_decide

/-- Bridge: arrive's lexical annotation records it as unaccusative. -/
theorem arrive_verb_unaccusative :
    Fragments.English.Predicates.Verbal.arrive.unaccusative = true := rfl

-- run: 4 P-Ag, 0 P-Pat → unergative
theorem run_unergative :
    predictsUnergative runSubjectProfile = true := by native_decide

theorem run_not_unaccusative :
    predictsUnaccusative runSubjectProfile = false := by native_decide

/-- Bridge: run's lexical annotation records it as NOT unaccusative. -/
theorem run_verb_not_unaccusative :
    Fragments.English.Predicates.Verbal.run.unaccusative = false := rfl

/-- Agreement: Dowty's unergative prediction for run matches the
    lexical annotation (both say "not unaccusative"). -/
theorem run_unaccusative_agrees :
    predictsUnaccusative runSubjectProfile =
    Fragments.English.Predicates.Verbal.run.unaccusative := by native_decide

-- ════════════════════════════════════════════════════
-- § 11. Alternation Examples (Dowty 1991 Corollary 1)
-- ════════════════════════════════════════════════════

/-- "buy" subject: V+S+C+IE (4 P-Ag) -/
def buySubjectProfile : EntailmentProfile :=
  ⟨true, true, true, false, true, false, false, false, false, false⟩

/-- "sell" subject: V+S+C+IE (same as buy — 4 P-Ag) -/
def sellSubjectProfile : EntailmentProfile :=
  ⟨true, true, true, false, true, false, false, false, false, false⟩

/-- Buy/sell subjects have the same entailment profile → alternation
    predicted (Dowty's Corollary 1). -/
theorem buy_sell_alternation :
    allowsAlternation buySubjectProfile sellSubjectProfile = true := by
  native_decide

/-- Buy and sell subjects have identical P-Agent scores. -/
theorem buy_sell_equal_pAgent :
    buySubjectProfile.pAgentScore = sellSubjectProfile.pAgentScore := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 12. Variable Agentivity (Rappaport Hovav & Levin 2024)
-- ════════════════════════════════════════════════════

/-- "sweep" basic-sense subject: M+IE (movement + independent existence).
    Underspecified for volition — agentivity is pragmatically resolved.
    Rappaport Hovav & Levin (2024) §3.2: the event structure is
    "x moves across surface y while x imparts force to y through contact". -/
def sweepBasicSubjectProfile : EntailmentProfile :=
  ⟨false, false, false, true, true, false, false, false, false, false⟩

/-- "sweep" broom-sense subject: V+S+C+M+IE (obligatory agent, 5 P-Ag).
    Instrument lexicalization forces volition, sentience, causation. -/
def sweepBroomSubjectProfile : EntailmentProfile :=
  ⟨true, true, true, true, true, false, false, false, false, false⟩

/-- Variable agentivity = the broom sense has strictly more P-Agent
    entailments than the basic sense (Rappaport Hovav & Levin 2024 §4). -/
theorem sweep_broom_more_agentive :
    sweepBroomSubjectProfile.pAgentScore >
    sweepBasicSubjectProfile.pAgentScore := by native_decide

/-- Basic sweep passes the do-test (movement alone suffices). -/
theorem sweep_basic_passes_doTest :
    passesDoTestFromProfile sweepBasicSubjectProfile = true := by native_decide

/-- Broom sweep obligatorily passes the do-test (volition alone suffices). -/
theorem sweep_broom_passes_doTest :
    passesDoTestFromProfile sweepBroomSubjectProfile = true := by native_decide

/-- Bridge: basic sweep subject theta is underspecified (none). -/
theorem sweep_basic_underspecified :
    Fragments.English.Predicates.Verbal.sweep_basic.subjectTheta = none := rfl

/-- Bridge: broom sweep subject theta is agent (obligatory agentivity). -/
theorem sweep_broom_agentive :
    Fragments.English.Predicates.Verbal.sweep_broom.subjectTheta = some .agent := rfl

-- ════════════════════════════════════════════════════
-- § 13. Effector / Force Recipient (Rappaport Hovav & Levin 2024)
-- ════════════════════════════════════════════════════

/-- An effector (Van Valin & Wilkins 1996; Rappaport Hovav & Levin 2024
    principle 45) is a self-energetic force bearer: it has movement and
    exists independently. Effectors are realized as external arguments. -/
def isEffector (p : EntailmentProfile) : Bool :=
  p.movement && p.independentExistence

/-- A force recipient (Rappaport Hovav & Levin 2024 principle 44) is
    causally affected or stationary. Force recipients are realized as
    internal arguments. -/
def isForceRecipient (p : EntailmentProfile) : Bool :=
  p.causallyAffected || p.stationary

/-- Effectors have at least 2 P-Agent entailments (movement + IE). -/
theorem effector_has_pAgent (p : EntailmentProfile) (h : isEffector p = true) :
    p.pAgentScore ≥ 2 := by
  simp [isEffector, Bool.and_eq_true] at h
  obtain ⟨hm, hie⟩ := h
  simp [EntailmentProfile.pAgentScore, hm, hie]

/-- Wind as effector: movement + independent existence. -/
theorem wind_is_effector :
    isEffector sweepBasicSubjectProfile = true := by native_decide

/-- Kick object is a force recipient (causally affected + stationary). -/
theorem kickObject_is_forceRecipient :
    isForceRecipient kickObjectProfile = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 14. Modern Extensions (comment only)
-- ════════════════════════════════════════════════════

/-
## Future extensions (Beavers 2010, Rappaport Hovav & Levin 2024)

Beavers (2010) "The structure of lexical meaning" generalizes Dowty's
discrete entailments (a) changeOfState and (b) incrementalTheme into a
unified **scalar change** framework. Under this view:
- changeOfState = change along a 2-point property scale
- incrementalTheme = change measured by a path/extent scale

To integrate: add `scaleType : Option ScaleType` to EntailmentProfile,
where ScaleType refines the Bool fields with scalar structure. The Bool
fields remain as the decidable "does this entailment hold?" projection,
while ScaleType captures the finer-grained scalar geometry.
-/

end Theories.EventSemantics.ProtoRoles
