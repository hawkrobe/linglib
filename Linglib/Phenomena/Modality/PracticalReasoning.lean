import Linglib.Theories.Semantics.Modality.Kratzer

/-!
# Practical Reasoning — Kratzer 2012 §2.8

Teleological modality: "To get to Harlem, you have to take the A train."

The scenario illustrates how goal-directed reasoning arises from Kratzer's
ordering source. The circumstantial modal base includes all four worlds;
the goal ordering restricts to worlds where the goal is achieved. Since
every goal-reaching world involves the A train, taking the A train is a
teleological necessity.

| World | ReachesGoal | TakesATrain | Notes              |
|-------|-------------|-------------|--------------------|
| w0    | yes         | yes         | A train, no delay  |
| w1    | yes         | yes         | A train, with delay|
| w2    | no          | no          | Takes bus           |
| w3    | no          | no          | Stays home          |

Reference: Kratzer, A. (2012). Modals and Conditionals. OUP. Ch. 2 §2.8.
-/

namespace Phenomena.Modality.PracticalReasoning

open Semantics.Attitudes.Intensional (World allWorlds)
open Semantics.Modality.Kratzer
open Core.ModalLogic (ModalFlavor)

/-! ## Propositions -/

/-- The agent reaches Harlem (the goal). -/
def reachesGoal : BProp World := λ w =>
  match w with | .w0 => true | .w1 => true | .w2 => false | .w3 => false

/-- The agent takes the A train. -/
def takesATrain : BProp World := λ w =>
  match w with | .w0 => true | .w1 => true | .w2 => false | .w3 => false

/-- No delay (distinguishes w0 from w1). -/
def noDelay : BProp World := λ w =>
  match w with | .w0 => true | .w1 => false | .w2 => true | .w3 => true

/-! ## Conversational backgrounds -/

/-- Circumstantial modal base: all worlds accessible (empty fact set). -/
def circumstantialBase : ModalBase := emptyBackground

/-- Goal ordering source: ranks worlds by whether the goal is reached. -/
def goalOrdering : OrderingSource := λ _ => [reachesGoal]

/-- Efficiency ordering: ranks by goal AND no-delay. w0 > w1. -/
def efficiencyOrdering : OrderingSource := λ _ => [reachesGoal, noDelay]

/-! ## Teleological flavor structure -/

/-- Harlem scenario as a Kratzer teleological flavor. -/
def harlemTeleological : TeleologicalFlavor where
  circumstances := circumstantialBase
  goals := goalOrdering

/-! ## Theory-neutral facts -/

/-- Every world that reaches the goal also takes the A train. -/
theorem goal_worlds_all_take_a :
    allWorlds.all (λ w => !reachesGoal w || takesATrain w) = true := by native_decide

/-! ## Derivation theorems -/

/-- **Teleological necessity**: Given the goal ordering, the A train is necessary.
    Best worlds = {w0, w1} (goal-reaching), both take the A train. -/
theorem teleological_necessity (w : World) :
    necessity circumstantialBase goalOrdering takesATrain w = true := by
  cases w <;> native_decide

/-- **Without goal restriction, A train is not necessary.**
    With empty ordering, all worlds are best, and w2/w3 don't take the A train. -/
theorem unrestricted_not_necessary (w : World) :
    necessity circumstantialBase emptyBackground takesATrain w = false := by
  cases w <;> native_decide

/-- **Efficiency refines**: Adding a no-delay criterion still yields necessity.
    Best worlds = {w0} (goal + no delay), and w0 takes the A train. -/
theorem efficiency_refines (w : World) :
    necessity circumstantialBase efficiencyOrdering takesATrain w = true := by
  cases w <;> native_decide

/-- **Teleological uses circumstantial flavor tag.** -/
theorem harlem_uses_teleological :
    TeleologicalFlavor.flavorTag = ModalFlavor.circumstantial := rfl

end Phenomena.Modality.PracticalReasoning
