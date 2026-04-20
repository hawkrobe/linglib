import Linglib.Theories.Semantics.Modality.Kratzer.Flavor
import Linglib.Theories.Semantics.Attitudes.Intensional

/-!
# Practical Reasoning — @cite{kratzer-2012} §2.8

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

namespace Phenomena.Modality.PracticalReasoningBridge

open Semantics.Attitudes.Intensional (World allWorlds)
open Semantics.Modality.Kratzer
open Core.Modality (ModalFlavor)

/-! ## Propositions -/

/-- The agent reaches Harlem (the goal). -/
def reachesGoal : World → Prop := λ w =>
  match w with | .w0 => True | .w1 => True | .w2 => False | .w3 => False

instance : DecidablePred reachesGoal :=
  fun w => by cases w <;> unfold reachesGoal <;> infer_instance

/-- The agent takes the A train. -/
def takesATrain : World → Prop := λ w =>
  match w with | .w0 => True | .w1 => True | .w2 => False | .w3 => False

instance : DecidablePred takesATrain :=
  fun w => by cases w <;> unfold takesATrain <;> infer_instance

/-- No delay (distinguishes w0 from w1). -/
def noDelay : World → Prop := λ w =>
  match w with | .w0 => True | .w1 => False | .w2 => True | .w3 => True

instance : DecidablePred noDelay :=
  fun w => by cases w <;> unfold noDelay <;> infer_instance

/-! ## Conversational backgrounds -/

/-- Circumstantial modal base: all worlds accessible (empty fact set). -/
def circumstantialBase : ModalBase World := emptyBackground

/-- Goal ordering source: ranks worlds by whether the goal is reached. -/
def goalOrdering : OrderingSource World := λ _ => [reachesGoal]

/-- Efficiency ordering: ranks by goal AND no-delay. w0 > w1. -/
def efficiencyOrdering : OrderingSource World := λ _ => [reachesGoal, noDelay]

/-! ## Teleological flavor structure -/

/-- Harlem scenario as a Kratzer teleological flavor. -/
def harlemTeleological : TeleologicalFlavor World where
  circumstances := circumstantialBase
  goals := goalOrdering

/-! ## Theory-neutral facts -/

/-- Every world that reaches the goal also takes the A train. -/
theorem goal_worlds_all_take_a :
    ∀ w ∈ allWorlds, reachesGoal w → takesATrain w := by decide

/-! ## Derivation theorems -/

/-- Every world is accessible under the (empty) circumstantial base. -/
private theorem all_accessible (w w' : World) :
    w' ∈ accessibleWorlds circumstantialBase w := by
  show w' ∈ accessibleWorlds emptyBackground w
  rw [empty_base_universal_access]
  exact Set.mem_univ _

/-- **Teleological necessity**: Given the goal ordering, the A train is necessary.
    Best worlds = {w0, w1} (goal-reaching), both take the A train. -/
theorem teleological_necessity (w : World) :
    necessity circumstantialBase goalOrdering takesATrain w := by
  rw [necessity_iff_all]
  intro w' hw'
  obtain ⟨_, hBest⟩ := hw'
  have hReachW0 : reachesGoal .w0 := by decide
  have hReachW' : reachesGoal w' :=
    hBest .w0 (all_accessible w .w0) reachesGoal
      (by simp [goalOrdering]) hReachW0
  cases w' with
  | w0 => decide
  | w1 => decide
  | w2 => exact hReachW'.elim
  | w3 => exact hReachW'.elim

/-- **Without goal restriction, A train is not necessary.**
    With empty ordering, all worlds are best, and w2/w3 don't take the A train. -/
theorem unrestricted_not_necessary (w : World) :
    ¬ necessity circumstantialBase emptyBackground takesATrain w := by
  rw [necessity_iff_all]
  intro h
  have hBestW2 : (.w2 : World) ∈ bestWorlds circumstantialBase emptyBackground w := by
    rw [empty_ordering_emptyBackground]
    exact all_accessible w .w2
  exact (h .w2 hBestW2).elim

/-- **Efficiency refines**: Adding a no-delay criterion still yields necessity.
    Best worlds = {w0} (goal + no delay), and w0 takes the A train. -/
theorem efficiency_refines (w : World) :
    necessity circumstantialBase efficiencyOrdering takesATrain w := by
  rw [necessity_iff_all]
  intro w' hw'
  obtain ⟨_, hBest⟩ := hw'
  have hReachW0 : reachesGoal .w0 := by decide
  have hNoDelayW0 : noDelay .w0 := by decide
  have hReachW' : reachesGoal w' :=
    hBest .w0 (all_accessible w .w0) reachesGoal
      (by simp [efficiencyOrdering]) hReachW0
  have hNoDelayW' : noDelay w' :=
    hBest .w0 (all_accessible w .w0) noDelay
      (by simp [efficiencyOrdering]) hNoDelayW0
  cases w' with
  | w0 => decide
  | w1 => exact hNoDelayW'.elim
  | w2 => exact hReachW'.elim
  | w3 => exact hReachW'.elim

/-- **Teleological uses circumstantial flavor tag.** -/
theorem harlem_uses_teleological :
    TeleologicalFlavor.flavorTag = ModalFlavor.circumstantial := rfl

end Phenomena.Modality.PracticalReasoningBridge
