/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Fintype.Pi
import Linglib.Core.Computability.Bimachine
import Linglib.Core.Computability.Subsequential

/-!
# Elgot–Mezei composition

Feeding a right-to-left transducer the output of a left-to-right one gives a bimachine:
the left automaton is the first machine, and the right automaton carries the *map* taking
a state of the first machine to the state the second reaches over the image of the
suffix. We show that a right-subsequential function after a left-subsequential one is
bimachine-computable as soon as the composite preserves the empty word — the composition
half of [elgot-mezei-1965]'s decomposition theorem ([sakarovitch-2009], Cor. V.2.5). The
decomposition half, that every rational function factors this way ([sakarovitch-2009],
Th. V.2.2), is not formalized here.

## Main definitions

* `SubsequentialTransducer.rightComp`: the bimachine running `T₂` right-to-left over the
  output of `T₁`

## Implementation notes

The empty-word hypothesis is not an artifact of the construction: `Bimachine.run [] = []`,
so a composite whose flushes emit anything on the empty input is computed by no bimachine
at all.

[UPSTREAM] candidate: `Mathlib.Computability.Bimachine`.

## TODO

* The decomposition half: every bimachine-computable function is a right-subsequential
  function after a left-subsequential one.
* The letter-to-letter refinement: `Mealy` after `Mealy` gives a length-preserving
  bimachine (`IsLengthPreservingBimachineComputable`).
-/

variable {α β γ σ₁ σ₂ : Type*}

namespace SubsequentialTransducer

variable (T₂ : SubsequentialTransducer σ₂ β γ) (T₁ : SubsequentialTransducer σ₁ α β)

/-- `T₂.rightComp T₁` is the bimachine reading `T₁` left to right and `T₂` right to left
over `T₁`'s output. Its right state is the map sending the `T₁`-state entering the suffix
to the `T₂`-state over the image of that suffix, `T₁`'s flush already consumed; the two
flags mark the ends of the input, where `T₂`'s flush and the image of `T₁`'s flush are
emitted. -/
@[simps]
def rightComp : Bimachine (Bool × σ₁) (Bool × (σ₁ → σ₂)) α γ where
  lInit := (true, T₁.start)
  lStep l a := (false, T₁.step l.2 a)
  rInit := (true, fun s => T₂.stateAfter T₂.start (T₁.finalOutput s).reverse)
  rStep r a := (false, fun s => T₂.stateAfter (r.2 (T₁.step s a)) (T₁.output s a).reverse)
  output l a r :=
    (if l.1 then T₂.runFrom (r.2 (T₁.step l.2 a)) (T₁.output l.2 a).reverse
      else T₂.emitted (r.2 (T₁.step l.2 a)) (T₁.output l.2 a).reverse).reverse
      ++ (if r.1 then (T₂.emitted T₂.start (T₁.finalOutput (T₁.step l.2 a)).reverse).reverse
        else [])

@[simp] theorem rightComp_rState_fst (suf : List α) :
    ((T₂.rightComp T₁).rState suf).1 = suf.isEmpty := by
  cases suf <;> rfl

@[simp] theorem rightComp_rState_snd (suf : List α) (s : σ₁) :
    ((T₂.rightComp T₁).rState suf).2 s
      = T₂.stateAfter T₂.start (T₁.runFrom s suf).reverse := by
  induction suf generalizing s <;> simp [stateAfter_append, *]

/-- Each cell emits the reverse of what `T₂` produces over the reversed image of the
input: its whole run at the left end, its emission alone — no flush — elsewhere. -/
theorem rightComp_runFrom (b : Bool) (s : σ₁) (a : α) (xs : List α) :
    (T₂.rightComp T₁).runFrom (b, s) (a :: xs)
      = (if b then T₂.runFrom T₂.start (T₁.runFrom s (a :: xs)).reverse
          else T₂.emitted T₂.start (T₁.runFrom s (a :: xs)).reverse).reverse := by
  induction xs generalizing b s a <;>
    cases b <;> simp [runFrom, emitted_append, stateAfter_append, *]

/-- The bimachine computes the composite on every nonempty input — the empty word is the
only obstruction. -/
theorem rightComp_run_cons (a : α) (xs : List α) :
    (T₂.rightComp T₁).run (a :: xs) = T₂.runRight (T₁.run (a :: xs)) := by
  rw [Bimachine.run, rightComp_lInit, rightComp_runFrom]
  simp [runRight, run]

/-- The bimachine computes `T₂.runRight ∘ T₁.run`, given that the composite preserves the
empty word. -/
theorem rightComp_run (h : T₂.runRight (T₁.run []) = []) :
    (T₂.rightComp T₁).run = T₂.runRight ∘ T₁.run := by
  funext xs
  cases xs with
  | nil => simpa [Bimachine.run] using h.symm
  | cons a xs => exact T₂.rightComp_run_cons T₁ a xs

end SubsequentialTransducer

/-- **Elgot–Mezei composition**: a right-subsequential function after a left-subsequential
one is bimachine-computable, as soon as the composite preserves the empty word (as every
bimachine-computable function does). -/
theorem IsRightSubsequential.isBimachineComputable_comp {f : List α → List β}
    {g : List β → List γ} (hg : IsRightSubsequential g) (hf : IsLeftSubsequential f)
    (hnil : g (f []) = []) : IsBimachineComputable (g ∘ f) := by
  classical
  obtain ⟨σ₂, _, T₂, rfl⟩ := isRightSubsequential_iff.mp hg
  obtain ⟨σ₁, _, T₁, rfl⟩ := hf
  exact ⟨_, inferInstance, _, inferInstance, T₂.rightComp T₁, T₂.rightComp_run T₁ hnil⟩

/-- The synchronous case: a `Mealy` machine run right to left over the output of another
is a bimachine, with no side condition since both passes preserve the empty word. -/
theorem Mealy.isBimachineComputable_runRight_comp [Fintype σ₁] [Fintype σ₂]
    (T₂ : Mealy σ₂ β γ) (T₁ : Mealy σ₁ α β) :
    IsBimachineComputable (T₂.runRight ∘ T₁.run) := by
  refine IsRightSubsequential.isBimachineComputable_comp ?_
    T₁.isMealyComputable.isLeftSubsequential rfl
  rw [isRightSubsequential_iff_left_reverse]
  simpa using T₂.isMealyComputable.isLeftSubsequential

