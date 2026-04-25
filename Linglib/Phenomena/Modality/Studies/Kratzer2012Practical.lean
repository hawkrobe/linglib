import Linglib.Theories.Semantics.Modality.Kratzer.Flavor
import Mathlib.Data.Fin.Basic

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

abbrev World := Fin 4

def allWorlds : List World := [0, 1, 2, 3]

open Semantics.Modality.Kratzer
open Core.Modality (ModalFlavor)

/-! ## Propositions -/

/-- The agent reaches Harlem (the goal). -/
def reachesGoal : World → Prop
  | 0 => True
  | 1 => True
  | 2 => False
  | 3 => False

instance : DecidablePred reachesGoal := fun w =>
  match w with
  | 0 => inferInstanceAs (Decidable True)
  | 1 => inferInstanceAs (Decidable True)
  | 2 => inferInstanceAs (Decidable False)
  | 3 => inferInstanceAs (Decidable False)

/-- The agent takes the A train. -/
def takesATrain : World → Prop
  | 0 => True
  | 1 => True
  | 2 => False
  | 3 => False

instance : DecidablePred takesATrain := fun w =>
  match w with
  | 0 => inferInstanceAs (Decidable True)
  | 1 => inferInstanceAs (Decidable True)
  | 2 => inferInstanceAs (Decidable False)
  | 3 => inferInstanceAs (Decidable False)

/-- No delay (distinguishes w0 from w1). -/
def noDelay : World → Prop
  | 0 => True
  | 1 => False
  | 2 => True
  | 3 => True

instance : DecidablePred noDelay := fun w =>
  match w with
  | 0 => inferInstanceAs (Decidable True)
  | 1 => inferInstanceAs (Decidable False)
  | 2 => inferInstanceAs (Decidable True)
  | 3 => inferInstanceAs (Decidable True)

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
  have hReachW0 : reachesGoal (0 : World) := by decide
  have hReachW' : reachesGoal w' :=
    hBest (0 : World) (all_accessible w (0 : World)) reachesGoal
      (by simp [goalOrdering]) hReachW0
  match w' with
  | 0 => decide
  | 1 => decide
  | 2 => exact hReachW'.elim
  | 3 => exact hReachW'.elim

/-- **Without goal restriction, A train is not necessary.**
    With empty ordering, all worlds are best, and w2/w3 don't take the A train. -/
theorem unrestricted_not_necessary (w : World) :
    ¬ necessity circumstantialBase emptyBackground takesATrain w := by
  rw [necessity_iff_all]
  intro h
  have hBestW2 : ((2 : World) : World) ∈ bestWorlds circumstantialBase emptyBackground w := by
    rw [empty_ordering_emptyBackground]
    exact all_accessible w (2 : World)
  exact (h (2 : World) hBestW2).elim

/-- **Efficiency refines**: Adding a no-delay criterion still yields necessity.
    Best worlds = {w0} (goal + no delay), and w0 takes the A train. -/
theorem efficiency_refines (w : World) :
    necessity circumstantialBase efficiencyOrdering takesATrain w := by
  rw [necessity_iff_all]
  intro w' hw'
  obtain ⟨_, hBest⟩ := hw'
  have hReachW0 : reachesGoal (0 : World) := by decide
  have hNoDelayW0 : noDelay (0 : World) := by decide
  have hReachW' : reachesGoal w' :=
    hBest (0 : World) (all_accessible w (0 : World)) reachesGoal
      (by simp [efficiencyOrdering]) hReachW0
  have hNoDelayW' : noDelay w' :=
    hBest (0 : World) (all_accessible w (0 : World)) noDelay
      (by simp [efficiencyOrdering]) hNoDelayW0
  match w' with
  | 0 => decide
  | 1 => exact hNoDelayW'.elim
  | 2 => exact hReachW'.elim
  | 3 => exact hReachW'.elim

/-- **Teleological uses circumstantial flavor tag.** -/
theorem harlem_uses_teleological :
    TeleologicalFlavor.flavorTag = ModalFlavor.circumstantial := rfl

end Phenomena.Modality.PracticalReasoningBridge
