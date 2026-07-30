/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Vector

/-!
# Finiteness of bounded-length lists

Over a finite alphabet, the lists of length at most `n` form a finite type — the state
space of window-based transducers.
-/

/-- The "lists of length at most `n`" subtype is finite when `α` is: it is a surjective
image of `Σ m : Fin (n + 1), List.Vector α m`. Uses `classical` for the `DecidableEq`
side condition rather than imposing it on consumers. -/
noncomputable instance List.fintypeSubtypeLengthLE {α : Type*} [Fintype α] (n : ℕ) :
    Fintype {l : List α // l.length ≤ n} := by
  classical
  exact Fintype.ofSurjective
    (fun (s : Σ m : Fin (n + 1), List.Vector α m) =>
      (⟨s.snd.toList, by
        rw [List.Vector.toList_length]
        exact Nat.lt_succ_iff.mp s.fst.isLt⟩ :
        {l : List α // l.length ≤ n}))
    (fun l => ⟨⟨⟨l.val.length, Nat.lt_succ_iff.mpr l.property⟩,
                  ⟨l.val, rfl⟩⟩, rfl⟩)
