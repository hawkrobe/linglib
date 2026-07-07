/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Fintype.Prod
import Linglib.Semantics.Modality.Kratzer.Operators

/-!
# Kratzer 1981: The Notional Category of Modality

[kratzer-1981]'s practical-inference example (her §7): *I want to
become mayor; I will become mayor only if I go to the pub regularly.*
The circumstances contribute the modal base, the desires the ordering
source, and the ordering source's two ideals — becoming mayor, not
going to the pub — pull in opposite directions, so the induced
ordering is non-connected by construction: her clause (c), "If v ∈ A
and z ∈ B, then neither v ≤ z nor z ≤ v."

Her verdicts: conclusions one ("must go to the pub"), two ("must not
go"), and three ("possible to become mayor without going") are
faulty; four ("possible to go") and five ("possible not to go") are
correct. The example also fixes the form of `bestWorlds`: under the
dominance reading (at least as good as *every* accessible world) the
best set here is empty and all five conclusions would come out
trivially, so her verdicts require the minimality reading
(`dominance_best_empty`, `best_nonempty`).
-/

namespace Kratzer1981

open Semantics.Modality.Kratzer

/-- A world: does the speaker become mayor, and go to the pub regularly? -/
abbrev World := Bool × Bool

/-- The evaluation world (arbitrary; the backgrounds are constant). -/
def w₀ : World := (false, false)

/-- Circumstances: I will become mayor only if I go to the pub regularly. -/
def circumstances : ModalBase World :=
  fun _ => [fun w => w.1 = true → w.2 = true]

/-- Desires: to become mayor, and not to go to the pub. -/
def desires : OrderingSource World :=
  fun _ => [fun w => w.1 = true, fun w => w.2 = false]

private lemma mem_acc_iff (w : World) :
    w ∈ accessibleWorlds circumstances w₀ ↔ (w.1 = true → w.2 = true) := by
  simp [accessibleWorlds, circumstances, Intensional.Premise.propIntersection]

private lemma agag_iff (a b : World) :
    atLeastAsGoodAs (desires w₀) a b ↔
      ((b.1 = true → a.1 = true) ∧ (b.2 = false → a.2 = false)) := by
  constructor
  · intro h
    exact ⟨h _ List.mem_cons_self, h _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  · rintro ⟨h1, h2⟩ q hq hqb
    cases hq with
    | head => exact h1 hqb
    | tail _ hq =>
      cases hq with
      | head => exact h2 hqb
      | tail _ hq => cases hq

/-- Her clause (c): the mayor-ideal world and the no-pub-ideal world are
incomparable — the ordering is non-connected by construction. -/
theorem mayor_pub_incomparable :
    ¬ atLeastAsGoodAs (desires w₀) (true, true) (false, false) ∧
    ¬ atLeastAsGoodAs (desires w₀) (false, false) (true, true) := by
  constructor <;> rw [agag_iff] <;> decide

private lemma mem_best_iff (w : World) :
    w ∈ bestWorlds circumstances desires w₀ ↔
      (w.1 = true → w.2 = true) ∧
      ∀ v : World, (v.1 = true → v.2 = true) →
        ((w.1 = true → v.1 = true) ∧ (w.2 = false → v.2 = false)) →
        ((v.1 = true → w.1 = true) ∧ (v.2 = false → w.2 = false)) := by
  constructor
  · rintro ⟨hacc, hmin⟩
    refine ⟨(mem_acc_iff w).mp hacc, fun v hv hle => ?_⟩
    exact (agag_iff w v).mp (hmin ((mem_acc_iff v).mpr hv) ((agag_iff v w).mpr hle))
  · rintro ⟨hacc, hmin⟩
    refine ⟨(mem_acc_iff w).mpr hacc, fun v hv hle => ?_⟩
    exact (agag_iff w v).mpr
      (hmin v ((mem_acc_iff v).mp hv) ((agag_iff v w).mp hle))

/-- The best worlds are exactly the two ideal-realizing ones: become
mayor and go, or stay home and skip the pub. -/
theorem best_eq :
    ∀ w : World, w ∈ bestWorlds circumstances desires w₀ ↔
      (w = (true, true) ∨ w = (false, false)) := by
  intro w
  rw [mem_best_iff]
  revert w
  decide

/-- Conclusion one is faulty: it is not necessary to go to the pub. -/
theorem conclusion_one_faulty :
    ¬ necessity circumstances desires (fun w => w.2 = true) w₀ := by
  intro h
  exact absurd (h (false, false) ((best_eq _).mpr (Or.inr rfl))) (by decide)

/-- Conclusion two is faulty: it is not necessary to skip the pub. -/
theorem conclusion_two_faulty :
    ¬ necessity circumstances desires (fun w => w.2 = false) w₀ := by
  intro h
  exact absurd (h (true, true) ((best_eq _).mpr (Or.inl rfl))) (by decide)

/-- Conclusion three is faulty: becoming mayor without the pub is not
even accessible. -/
theorem conclusion_three_faulty :
    ¬ possibility circumstances desires (fun w => w.1 = true ∧ w.2 = false) w₀ := by
  rintro ⟨w, hw, h1, h2⟩
  have := ((best_eq w).mp hw)
  rcases this with rfl | rfl <;> simp_all

/-- Conclusion four is correct: going to the pub is possible. -/
theorem conclusion_four_correct :
    possibility circumstances desires (fun w => w.2 = true) w₀ :=
  ⟨(true, true), (best_eq _).mpr (Or.inl rfl), rfl⟩

/-- Conclusion five is correct: skipping the pub is possible. -/
theorem conclusion_five_correct :
    possibility circumstances desires (fun w => w.2 = false) w₀ :=
  ⟨(false, false), (best_eq _).mpr (Or.inr rfl), rfl⟩

/-! ### The example fixes the form of `bestWorlds` -/

/-- Under the dominance reading of "best" — at least as good as every
accessible world — the best set of her example is empty: the two
ideal-realizing worlds disqualify each other. -/
theorem dominance_best_empty :
    {w : World | w ∈ accessibleWorlds circumstances w₀ ∧
      ∀ v ∈ accessibleWorlds circumstances w₀,
        atLeastAsGoodAs (desires w₀) w v} = ∅ := by
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hacc h
  have h1 := (agag_iff w (true, true)).mp
    (h (true, true) ((mem_acc_iff _).mpr (by decide)))
  have h2 := (agag_iff w (false, false)).mp
    (h (false, false) ((mem_acc_iff _).mpr (by decide)))
  have hw := (mem_acc_iff w).mp hacc
  obtain ⟨a, b⟩ := w
  revert h1 h2 hw
  cases a <;> cases b <;> decide

/-- The minimality reading leaves the best set nonempty, as her verdicts
require. -/
theorem best_nonempty :
    (bestWorlds circumstances desires w₀).Nonempty :=
  ⟨(true, true), (best_eq _).mpr (Or.inl rfl)⟩

end Kratzer1981
