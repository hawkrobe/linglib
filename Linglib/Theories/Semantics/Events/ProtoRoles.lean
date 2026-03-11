import Linglib.Theories.Semantics.Events.EntailmentProfile
import Linglib.Theories.Semantics.Events.Agentivity
import Linglib.Theories.Semantics.Events.AgentivityLattice
import Linglib.Theories.Semantics.Events.Krifka1998
import Linglib.Theories.Semantics.Causation.Builder
import Linglib.Theories.Semantics.Lexical.Verb.ChangeOfState.Theory
import Linglib.Core.RootDimensions

/-!
# @cite{dowty-1991} Proto-Roles: Theory Bridges and Canonical Profiles
@cite{levin-2022}

Pure theory file connecting the entailment profile theory
(`EntailmentProfile.lean`) to other semantic modules: @cite{cruse-1973}
agentivity, @cite{krifka-1998} SINC, change-of-state, causation, and
@cite{levin-1993} meaning components.

Verb-specific entailment profiles (canonical instances of `EntailmentProfile`)
are defined here as theory-level constants. Bridge theorems connecting these
profiles to English Fragment entries live in study files under `Phenomena/`.
-/

namespace Semantics.Events.ProtoRoles

open Semantics.Events.Agentivity
open Semantics.Events.Krifka1998
open NadathurLauer2020.Builder
open Semantics.Lexical.Verb.ChangeOfState

-- ════════════════════════════════════════════════════
-- § 1. ASP Verification (lattice-based)
-- ════════════════════════════════════════════════════

/-- Kick: subject outranks object (lattice: {V,S,C,M,IE} ⊃ {}). -/
theorem kick_subject_outranks :
    outranksForSubject kickSubjectProfile kickObjectProfile = true := by native_decide

/-- Build: subject outranks object. -/
theorem build_subject_outranks :
    outranksForSubject buildSubjectProfile buildObjectProfile = true := by native_decide

/-- Eat: subject outranks object. -/
theorem eat_subject_outranks :
    outranksForSubject eatSubjectProfile eatObjectProfile = true := by native_decide

/-- Buy/sell subjects have identical profiles → alternation. -/
theorem buy_sell_alternation :
    allowsAlternation buySubjectProfile sellSubjectProfile = true := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 3. Unaccusativity Verification (priority-based)
-- ════════════════════════════════════════════════════

/-- die: no volition, no causation, 3 P-Pat → unaccusative. -/
theorem die_unaccusative :
    predictsUnaccusative dieSubjectProfile = true := by native_decide

/-- arrive: no volition, no causation, 1 P-Pat → unaccusative.
    This FIXES the anomaly in @cite{dowty-1991}'s flat counting, which
    predicted unergative because pAgentScore (2) > pPatientScore (1). -/
theorem arrive_unaccusative :
    predictsUnaccusative arriveSubjectProfile = true := by native_decide

/-- run: has volition, 0 P-Pat → unergative. -/
theorem run_unergative :
    predictsUnergative runSubjectProfile = true := by native_decide

theorem run_not_unaccusative :
    predictsUnaccusative runSubjectProfile = false := by native_decide

-- ════════════════════════════════════════════════════
-- § 4. Bridge to @cite{cruse-1973}: Features Derived from Entailments
-- ════════════════════════════════════════════════════

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
-- § 5. Bridge to @cite{krifka-1998} SINC
-- ════════════════════════════════════════════════════

theorem buildObject_is_incrementalTheme :
    buildObjectProfile.incrementalTheme = true := by native_decide

theorem eatObject_is_incrementalTheme :
    eatObjectProfile.incrementalTheme = true := by native_decide

theorem kickObject_not_incrementalTheme :
    kickObjectProfile.incrementalTheme = false := by native_decide

-- ════════════════════════════════════════════════════
-- § 6. Bridge to ChangeOfState / CoSType
-- ════════════════════════════════════════════════════

theorem kickObject_changeOfState :
    kickObjectProfile.changeOfState = true := by native_decide

theorem buildObject_changeOfState :
    buildObjectProfile.changeOfState = true := by native_decide

theorem dieSubject_changeOfState :
    dieSubjectProfile.changeOfState = true := by native_decide

theorem arriveSubject_changeOfState :
    arriveSubjectProfile.changeOfState = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 7. Bridge to CausativeBuilder
-- ════════════════════════════════════════════════════

theorem causation_entailment_implies_pAgent_ge_one
    (p : EntailmentProfile) (h : p.causation = true) :
    p.pAgentScore ≥ 1 := by
  simp [EntailmentProfile.pAgentScore, h]
  omega

theorem kickSubject_has_causation :
    kickSubjectProfile.causation = true := by native_decide

theorem buildSubject_has_causation :
    buildSubjectProfile.causation = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 8. Variable Agentivity (@cite{rappaport-hovav-levin-2024})
-- ════════════════════════════════════════════════════

/-- Variable agentivity = the broom sense has strictly more P-Agent
    entailments than the basic sense. -/
theorem sweep_instr_more_agentive :
    sweepBroomSubjectProfile.pAgentScore >
    sweepBasicSubjectProfile.pAgentScore := by native_decide

theorem sweep_passes_doTest :
    passesDoTestFromProfile sweepBasicSubjectProfile = true := by native_decide

theorem sweep_instr_passes_doTest :
    passesDoTestFromProfile sweepBroomSubjectProfile = true := by native_decide

/-- Wind as effector: movement + independent existence. -/
theorem wind_is_effector :
    isEffector sweepBasicSubjectProfile = true := by native_decide

/-- Kick object is a force recipient (causally affected + stationary). -/
theorem kickObject_is_forceRecipient :
    isForceRecipient kickObjectProfile = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 9. Bridge to @cite{levin-1993} Meaning Components
-- ════════════════════════════════════════════════════

/-! @cite{levin-1993}'s meaning components are a coarse-grained projection of
    Dowty's entailment profiles. Three of the four components correspond
    to specific Dowty entailments:

    | Levin component | Dowty entailment | Argument |
    |---|---|---|
    | `causation` | P-Agent (c) `causation` | Subject |
    | `changeOfState` | P-Patient (a) `changeOfState` | Object / unacc. subject |
    | `motion` | P-Agent (d) `movement` | Subject |
    | `contact` | — (no direct Dowty counterpart) | — |

    The key divergence: Levin's `causation` is *narrow* — it diagnoses
    specifically causation of a change of state (via the causative/inchoative
    alternation). Dowty's `causation` is *broad* — any event where one
    participant causes something in another. -/

def levinSubjectPrediction (mc : MeaningComponents) : Bool × Bool :=
  (mc.causation, mc.motion)

def levinPatientPrediction (mc : MeaningComponents) : Bool × Bool :=
  (mc.changeOfState, mc.causation)

theorem break_class_subject_causation :
    (levinSubjectPrediction LevinClass.break_.meaningComponents).1 = true := rfl

theorem break_class_patient_cos :
    (levinPatientPrediction LevinClass.break_.meaningComponents).1 = true := rfl

theorem hit_class_no_levin_causation :
    (levinSubjectPrediction LevinClass.hit.meaningComponents).1 = false := rfl

theorem hit_class_patient_no_cos :
    (levinPatientPrediction LevinClass.hit.meaningComponents).1 = false := rfl

theorem kick_dowty_vs_levin_causation :
    kickSubjectProfile.causation = true
    ∧ LevinClass.hit.meaningComponents.causation = false := ⟨rfl, rfl⟩

theorem motion_class_subject_movement :
    (levinSubjectPrediction LevinClass.mannerOfMotion.meaningComponents).2 = true
    ∧ (levinSubjectPrediction LevinClass.inherentlyDirectedMotion.meaningComponents).2 = true
    := ⟨rfl, rfl⟩

theorem stative_class_no_dynamics :
    levinSubjectPrediction LevinClass.exist.meaningComponents = ⟨false, false⟩
    ∧ levinSubjectPrediction LevinClass.admire.meaningComponents = ⟨false, false⟩
    := ⟨rfl, rfl⟩

theorem levin_causation_subsumes :
    ∀ (mc : MeaningComponents), mc.causation = true →
    (levinSubjectPrediction mc).1 = true :=
  fun _ h => h

theorem dowty_causation_not_subsumes :
    kickSubjectProfile.causation = true
    ∧ LevinClass.hit.meaningComponents.causation = false := ⟨rfl, rfl⟩

theorem levin_causation_implies_both (mc : MeaningComponents)
    (h : mc.causation = true) :
    (levinSubjectPrediction mc).1 = true
    ∧ (levinPatientPrediction mc).2 = true := ⟨h, h⟩

-- ════════════════════════════════════════════════════
-- § 10. Well-Formedness Verification
-- ════════════════════════════════════════════════════

/-- All canonical verb profiles satisfy the internal well-formedness
    constraint (volition → sentience). -/
theorem kick_wellformed :
    kickSubjectProfile.wellFormedInternal = true := by native_decide

theorem die_wellformed :
    dieSubjectProfile.wellFormedInternal = true := by native_decide

theorem arrive_wellformed :
    arriveSubjectProfile.wellFormedInternal = true := by native_decide

theorem sweep_basic_wellformed :
    sweepBasicSubjectProfile.wellFormedInternal = true := by native_decide

/-- Kick satisfies the causation↔CoS paired constraint but NOT the
    IE↔DE constraint (the ball exists independently of the kicking). -/
theorem kick_pair_causation_cos :
    (!kickSubjectProfile.causation || kickObjectProfile.changeOfState) = true ∧
    (!kickSubjectProfile.independentExistence || kickObjectProfile.dependentExistence) = false :=
  ⟨rfl, rfl⟩

/-- Build satisfies causation↔CoS and IE↔DE, but NOT movement↔stationary
    (the thing being built is not stationary relative to the builder). -/
theorem build_pair_partial :
    (!buildSubjectProfile.causation || buildObjectProfile.changeOfState) = true ∧
    (!buildSubjectProfile.independentExistence || buildObjectProfile.dependentExistence) = true ∧
    (!buildSubjectProfile.movement || buildObjectProfile.stationary) = false :=
  ⟨rfl, rfl, rfl⟩

/-- Eat satisfies causation↔CoS but NOT movement↔stationary or IE↔DE
    (food exists independently and is not stationary). -/
theorem eat_pair_partial :
    (!eatSubjectProfile.causation || eatObjectProfile.changeOfState) = true ∧
    (!eatSubjectProfile.movement || eatObjectProfile.stationary) = false ∧
    (!eatSubjectProfile.independentExistence || eatObjectProfile.dependentExistence) = false :=
  ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 11. Bridge to @cite{grimm-2011} Agentivity Lattice
-- ════════════════════════════════════════════════════

/-! @cite{grimm-2011}'s agentivity lattice reformulates proto-role entailments
    as privative features with lattice structure. This section connects the
    entailment profiles to Grimm's lattice, combining results from multiple
    theory bridges (@cite{cruse-1973} agentivity, @cite{krifka-1998} SINC). -/

open Semantics.Events.AgentivityLattice

/-- Cross-theory: kick subject passes the do-test (@cite{cruse-1973}),
    has maximal agentivity on @cite{grimm-2011}'s lattice (⊤), and maps
    to NOM in an accusative system. Three theories converge. -/
theorem kick_cruse_grimm_consistent :
    passesDoTestFromProfile kickSubjectProfile = true ∧
    AgentivityNode.fromEntailmentProfile kickSubjectProfile = ⊤ ∧
    (GrimmNode.fromSubjectProfile kickSubjectProfile).toCaseRegion.toAccusativeCase
      = .nom :=
  ⟨by native_decide, rfl, by native_decide⟩

/-- Cross-theory: die subject fails the do-test, has zero agentivity (⊥),
    and maps to ABS in an ergative system. -/
theorem die_cruse_grimm_consistent :
    passesDoTestFromProfile dieSubjectProfile = false ∧
    AgentivityNode.fromEntailmentProfile dieSubjectProfile = ⊥ ∧
    (GrimmNode.fromObjectProfile dieSubjectProfile).toCaseRegion.toErgativeCase
      = .abs :=
  ⟨by native_decide, rfl, by native_decide⟩

/-- Cross-theory: build object is an incremental theme (@cite{krifka-1998}),
    maps to exPersEnd on @cite{grimm-2011}'s persistence scale (creation),
    and falls OUTSIDE the canonical ACC region — creation verb objects are
    non-prototypically transitive. -/
theorem build_krifka_grimm_consistent :
    buildObjectProfile.incrementalTheme = true ∧
    PersistenceLevel.fromPatientProfile buildObjectProfile = .exPersEnd ∧
    (GrimmNode.fromObjectProfile buildObjectProfile).toCaseRegion ≠ .accAbs :=
  ⟨by native_decide, by native_decide, by native_decide⟩

/-- Cross-theory: arrive subject has movement but not instigation →
    Grimm's lattice places it outside the NOM/ERG region, consistent with
    the priority-based ASP predicting unaccusative. -/
theorem arrive_asp_grimm_consistent :
    predictsUnaccusative arriveSubjectProfile = true ∧
    (GrimmNode.fromSubjectProfile arriveSubjectProfile).toCaseRegion ≠ .nomErg :=
  ⟨by native_decide, by native_decide⟩

end Semantics.Events.ProtoRoles
