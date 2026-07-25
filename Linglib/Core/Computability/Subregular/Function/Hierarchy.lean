/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.Function.ISL
import Linglib.Core.Computability.Subregular.Function.OSL
import Linglib.Core.Computability.Mealy
import Linglib.Core.Computability.Subregular.Function.Subsequential
import Linglib.Core.Computability.Subregular.Function.SideDeterminacy
import Linglib.Core.Computability.Subregular.Function.Bimachine

/-!
# The subregular function hierarchy

Inclusions among the directionality classes of the transducer substrate — strictly local
(`ISLRule`, `OSLRule`), synchronous (`Mealy`) and bimachine (`Bimachine`):

  `single-symbol ISL/OSL ⊆ IsMealyComputable ⊆ IsBimachineWeaklyDeterministic ⊆ IsBimachineComputable`

A synchronous transducer is the degenerate bimachine whose right automaton is trivial, so
its cell output is a *one-sided* rule — non-interacting.

Each file states the facts internal to its own classes; this one holds only the edges
between them. The properness of `IsBimachineWeaklyDeterministic ⊆ IsBimachineComputable`
is in `Bimachine.lean`, with the machine conversions in `Subsequential.lean`.

## Main theorems

* `IsMealyComputable.isLeftSubsequential`: synchronous ⊆ block subsequential
* `IsBimachineWeaklyDeterministic.of_mealyComputable`: synchronous ⊆ weakly deterministic
* `IsBimachineComputable.of_weaklyDeterministic`: weakly deterministic ⊆ regular
* `isMealyComputable_of_ISLRule`, `isMealyComputable_of_OSLRule`: the single-symbol
  (length-preserving) fragment of the strictly-local classes is synchronous
* `Mealy.leftDetermined`, `Mealy.isRightMyopic`: a synchronous map is prefix-determined at
  every coordinate, hence has no look-ahead

## TODO

* `IsLeftSubsequential ⊊ IsBimachineWeaklyDeterministic`. No witness is formalized here.
  Note that non-myopia refutes only *synchronous* computability, via
  `IsMealyComputable.isRightMyopic`: a block transducer may delay its output, so its
  coordinate `i` is not fixed by the prefix, and excluding one takes the bounded-delay
  route (`IsLeftSubsequential.bounded_delay`) instead.
-/

namespace Subregular

section MealyBlock

variable {α β : Type*}

/-- **Synchronous ⊆ block subsequential**, via the `Mealy.toSFST` view. -/
theorem IsMealyComputable.isLeftSubsequential {f : List α → List β}
    (hf : IsMealyComputable f) : IsLeftSubsequential f := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  exact T.toSFST_run ▸ T.toSFST.isLeftSubsequential

end MealyBlock

/-! ### Mealy-computable maps have no look-ahead

Output coordinate `i` of a synchronous machine depends only on the input prefix
`[0..i]`. The *block* class `IsLeftSubsequential` lacks this: a length-preserving block
transducer can delay output (emit `[]` then `[x, y]`), so its output coordinate `0` can
depend on input position `1`. -/

section Footprint

variable {σ α β : Type*}

/-- A synchronous machine is left-determined at every coordinate — output `i` depends only
on the prefix `{k | k ≤ i}`. Finiteness is irrelevant, so this is stated for the machine. -/
theorem Mealy.leftDetermined (T : Mealy σ α β) (i : ℕ) : LeftDetermined T.run i := by
  intro u v hlen hag
  simp only [Set.mem_setOf_eq] at hag
  rw [T.getElem?_run u, T.getElem?_run v, hag i le_rfl,
    take_eq_of_agree fun k hk => hag k hk.le]

/-- A synchronous machine is right-myopic: it has no look-ahead. -/
theorem Mealy.isRightMyopic (T : Mealy σ α β) : IsMyopicTowards T.run .right :=
  IsMyopicTowards.right_of_leftDetermined T.leftDetermined

/-- A Mealy-computable map is left-determined at every coordinate. -/
theorem IsMealyComputable.leftDetermined {f : List α → List β}
    (hf : IsMealyComputable f) (i : ℕ) : LeftDetermined f i := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  exact T.leftDetermined i

/-- A Mealy-computable map is right-myopic: it has no look-ahead. -/
theorem IsMealyComputable.isRightMyopic {f : List α → List β}
    (hf : IsMealyComputable f) : IsMyopicTowards f .right :=
  IsMyopicTowards.right_of_leftDetermined hf.leftDetermined

end Footprint

variable {α : Type*} [DecidableEq α]

/-- **Synchronous ⊆ weakly deterministic.** A Mealy-computable function is computed by a
non-interacting bimachine: the left automaton *is* the transducer, the right automaton is
trivial, so the cell output is a one-sided rule (`ωR` is the identity). -/
theorem IsBimachineWeaklyDeterministic.of_mealyComputable {f : List α → List α}
    (h : IsMealyComputable f) : IsBimachineWeaklyDeterministic f := by
  obtain ⟨σ, _, T, rfl⟩ := h
  let B : Bimachine σ Unit α α :=
    { lInit := T.initial, lStep := T.step,
      rInit := (), rStep := fun _ _ => (), out := fun l a _ => T.output l a }
  have hrun : B.run = T.run :=
    funext fun xs => List.ext_getElem? fun i => by
      rw [Bimachine.run_getElem?, T.getElem?_run]; rfl
  exact hrun ▸ isBimachineWeaklyDeterministic B
    ⟨T.output, fun _ a => a, fun l a r => (unite_right_self _ _).symm⟩

/-- **Weakly deterministic ⊆ regular.** A non-interacting bimachine is a bimachine. -/
theorem IsBimachineComputable.of_weaklyDeterministic {f : List α → List α}
    (h : IsBimachineWeaklyDeterministic f) : IsBimachineComputable f := by
  obtain ⟨L, R, _, _, B, rfl, _⟩ := h
  exact isBimachineComputable B

/-! ### The strictly-local lower end: single-symbol ISL/OSL ⊆ synchronous

The ISL/OSL classes are block-output (length-changing) in general, so they sit outside the
length-preserving lattice. Their **single-symbol** (length-preserving) fragment embeds: the
bounded window that makes `toFinSFST` finite-state serves as the `Mealy` state, with the
lone output symbol as the letter. This extends the chain to
`single-symbol ISL/OSL ⊆ synchronous ⊆ WD ⊆ regular`. -/

/-- **Single-symbol left-ISL ⊆ synchronous**: the bounded input window that makes
`ISLRule.toFinSFST` finite-state is already the `Mealy` state. -/
theorem isMealyComputable_of_ISLRule {α β : Type*} {k : ℕ} [Fintype α] (r : ISLRule k α β)
    (hs : ∀ w x, (r.windowOutput w x).length = 1) : IsMealyComputable r.apply :=
  r.toFinSFST_run_eq_apply ▸ r.toFinSFST.isMealyComputable (fun w x => hs w.val x) fun _ => rfl

/-- **Single-symbol left-OSL ⊆ synchronous**, with the bounded output window as the state. -/
theorem isMealyComputable_of_OSLRule {α β : Type*} {k : ℕ} [Fintype β] (r : OSLRule k α β)
    (hs : ∀ w x, (r.windowOutput w x).length = 1) : IsMealyComputable r.apply :=
  r.toFinSFST_run_eq_apply ▸ r.toFinSFST.isMealyComputable (fun w x => hs w.val x) fun _ => rfl

/-- **Single-symbol left-ISL ⊆ WD** — extends the lattice down through the synchronous
class. -/
theorem IsBimachineWeaklyDeterministic.of_ISLRule {α : Type*} {k : ℕ} [Fintype α] [DecidableEq α]
    (r : ISLRule k α α) (hs : ∀ w x, (r.windowOutput w x).length = 1) :
    IsBimachineWeaklyDeterministic r.apply :=
  .of_mealyComputable (isMealyComputable_of_ISLRule r hs)

/-- **Single-symbol left-OSL ⊆ WD**. -/
theorem IsBimachineWeaklyDeterministic.of_OSLRule {α : Type*} {k : ℕ} [Fintype α] [DecidableEq α]
    (r : OSLRule k α α) (hs : ∀ w x, (r.windowOutput w x).length = 1) :
    IsBimachineWeaklyDeterministic r.apply :=
  .of_mealyComputable (isMealyComputable_of_OSLRule r hs)

end Subregular
