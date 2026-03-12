import Linglib.Theories.Semantics.Events.ThematicRoles
import Linglib.Fragments.English.Predicates.Verbal

/-!
# Thematic Role Grounding

Bridge theorems connecting Fragment-layer verb entries (kick, give,)
to Theory-layer thematic role infrastructure. These verify that the
theta role annotations in the lexicon correctly map to ThematicFrame
fields via `ThetaRole.toRel`.

Separated from `ThematicRoles.lean` to keep the Theory layer free of
Fragment imports (Theories → Fragments dependency discipline).
-/

namespace Semantics.Events.ThematicRoles.Grounding

open Semantics.Events
open Semantics.Events.ThematicRoles
open Core.Time
open Fragments.English.Predicates.Verbal

-- ════════════════════════════════════════════════════
-- § 1. Per-Verb Role Verification (via entailment profiles)
-- ════════════════════════════════════════════════════

/-- "kick" has agent as subject role (derived from entailment profile). -/
theorem kick_subject_agent : kick.toVerbCore.subjectRole = some .agent := by native_decide

/-- "kick" has patient as object role (derived from entailment profile). -/
theorem kick_object_patient : kick.toVerbCore.objectRole = some .patient := by native_decide

/-- "see" has experiencer subject (derived from entailment profile). -/
theorem see_subject_experiencer : see.toVerbCore.subjectRole = some .experiencer := by native_decide

-- ════════════════════════════════════════════════════
-- § 2. ThetaRole.toRel Bridge Verification
-- ════════════════════════════════════════════════════

/-- "kick"'s subject role maps to the agent relation in any frame. -/
theorem subjectRole_toRel_kick {Entity Time : Type*} [LE Time]
    (frame : ThematicFrame Entity Time) :
    kick.toVerbCore.subjectRole.map (ThetaRole.toRel · frame) = some frame.agent := rfl

/-- "kick"'s object role maps to the patient relation in any frame. -/
theorem objectRole_toRel_kick {Entity Time : Type*} [LE Time]
    (frame : ThematicFrame Entity Time) :
    kick.toVerbCore.objectRole.map (ThetaRole.toRel · frame) = some frame.patient := rfl

-- ════════════════════════════════════════════════════
-- § 3. Concrete Example (Toy model)
-- ════════════════════════════════════════════════════

/-- A toy entity type for examples. -/
inductive Person where
  | john | mary | bill
  deriving DecidableEq, Repr, BEq

/-- A toy thematic frame for the kicking example. -/
def exampleFrame : ThematicFrame Person ℤ where
  agent      := λ x e => x = .john ∧ e = exampleRun
  patient    := λ x e => x = .mary ∧ e = exampleRun
  theme      := λ _ _ => False
  experiencer := λ _ _ => False
  goal       := λ _ _ => False
  source     := λ _ _ => False
  instrument := λ _ _ => False
  stimulus   := λ _ _ => False
  holder     := λ _ _ => False

/-- A toy "kick" event predicate. -/
def kickPred : EvPred ℤ := λ e => e = exampleRun

/-- "John kicked Mary" is true in the example model:
    ∃e. kick(e) ∧ Agent(john, e) ∧ Patient(mary, e). -/
theorem john_kicked_mary :
    transitiveLogicalForm kickPred exampleFrame .john .mary := by
  exact ⟨exampleRun, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

end Semantics.Events.ThematicRoles.Grounding
