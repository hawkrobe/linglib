import Linglib.Theories.Semantics.Events.ThematicRoles
import Linglib.Fragments.English.Predicates.Verbal

/-!
# Thematic Role Grounding

Bridge theorems connecting Fragment-layer verb entries (kick, give, see)
to Theory-layer thematic role infrastructure. These verify that the
theta role annotations in the lexicon correctly map to ThematicFrame
fields via `ThetaRole.toRel`.

Separated from `ThematicRoles.lean` to keep the Theory layer free of
Fragment imports (Theories → Fragments dependency discipline).
-/

namespace EventSemantics.ThematicRoles.Grounding

open EventSemantics
open EventSemantics.ThematicRoles
open Core.Time
open Fragments.English.Predicates.Verbal

-- ════════════════════════════════════════════════════
-- § 1. Per-Verb Role Verification
-- ════════════════════════════════════════════════════

/-- "kick" has agent as subject theta role. -/
theorem kick_subject_agent : kick.subjectTheta = some .agent := rfl

/-- "kick" has patient as object theta role. -/
theorem kick_object_patient : kick.objectTheta = some .patient := rfl

/-- "give" has agent subject, theme direct object, goal indirect object. -/
theorem give_roles :
    give.subjectTheta = some .agent ∧
    give.objectTheta = some .theme ∧
    give.object2Theta = some .goal :=
  ⟨rfl, rfl, rfl⟩

/-- "see" has experiencer subject and stimulus object. -/
theorem see_roles :
    see.subjectTheta = some .experiencer ∧
    see.objectTheta = some .stimulus :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 2. ThetaRole.toRel Bridge Verification
-- ════════════════════════════════════════════════════

/-- "kick"'s subject theta role maps to the agent relation in any frame. -/
theorem subjectTheta_toRel_kick {Entity Time : Type*} [LE Time]
    (frame : ThematicFrame Entity Time) :
    kick.subjectTheta.map (ThetaRole.toRel · frame) = some frame.agent := rfl

/-- "kick"'s object theta role maps to the patient relation in any frame. -/
theorem objectTheta_toRel_kick {Entity Time : Type*} [LE Time]
    (frame : ThematicFrame Entity Time) :
    kick.objectTheta.map (ThetaRole.toRel · frame) = some frame.patient := rfl

/-- "give"'s subject theta role maps to the agent relation. -/
theorem subjectTheta_toRel_give {Entity Time : Type*} [LE Time]
    (frame : ThematicFrame Entity Time) :
    give.subjectTheta.map (ThetaRole.toRel · frame) = some frame.agent := rfl

/-- "give"'s object theta role maps to the theme relation. -/
theorem objectTheta_toRel_give {Entity Time : Type*} [LE Time]
    (frame : ThematicFrame Entity Time) :
    give.objectTheta.map (ThetaRole.toRel · frame) = some frame.theme := rfl

/-- "give"'s indirect object theta role maps to the goal relation. -/
theorem object2Theta_toRel_give {Entity Time : Type*} [LE Time]
    (frame : ThematicFrame Entity Time) :
    give.object2Theta.map (ThetaRole.toRel · frame) = some frame.goal := rfl

/-- "see"'s subject theta role maps to the experiencer relation. -/
theorem subjectTheta_toRel_see {Entity Time : Type*} [LE Time]
    (frame : ThematicFrame Entity Time) :
    see.subjectTheta.map (ThetaRole.toRel · frame) = some frame.experiencer := rfl

/-- "see"'s object theta role maps to the stimulus relation. -/
theorem objectTheta_toRel_see {Entity Time : Type*} [LE Time]
    (frame : ThematicFrame Entity Time) :
    see.objectTheta.map (ThetaRole.toRel · frame) = some frame.stimulus := rfl

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

end EventSemantics.ThematicRoles.Grounding
