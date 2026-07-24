/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Fintype.EquivFin
import Linglib.Core.Computability.Mealy
import Linglib.Core.Computability.Subregular.Function.SideDeterminacy

/-!
# Synchronous (letter) left-subsequential functions

`IsLetterLeftSubsequential f` states that `f` is computed by a finite-state `Mealy`
machine. Output coordinate `i` of such a function depends only on the input prefix
`[0..i]`, so the class is characterized by its dependency footprint
(`OutputDependsOn`): letter-left-subsequential functions are prefix-determined at
every coordinate, hence have no look-ahead.

The *block* class `IsLeftSubsequential` lacks this characterization: a
length-preserving block transducer can delay output (emit `[]` then `[x, y]`), so its
output coordinate `0` can depend on input position `1`. The synchronous restriction is
what makes the dependency-footprint view coincide with the machine view.

## Main definitions

* `IsLetterLeftSubsequential f`: `f` is computed by some finite-state `Mealy`

## Main theorems

* `IsLetterLeftSubsequential.leftDetermined`, `.isRightMyopic`:
  letter-left-subsequential functions are prefix-determined, hence right-myopic
* `isLetterLeftSubsequential_of_stateSummary`: the sufficiency half of Myhill–Nerode —
  a finite left-congruent state summary determining the output yields a machine

## Implementation notes

In the transducer literature [mohri-1997] a *subsequential* machine additionally
carries a state-final output emitted at the end of the input; `Mealy` has none, so
strictly it computes the letter-to-letter *sequential* class. Length preservation
forces the final output to be empty, so the two classes coincide here; the name keeps
the parallel with the block class `IsLeftSubsequential`.

## TODO

* Instantiate `isLetterLeftSubsequential_of_stateSummary` at the natural Nerode prefix
  congruence, and prove the necessity direction: a letter-left-subsequential function
  has a prefix congruence of finite index [choffrut-1977].
* Composition closure (state-product machine) and the right-scan mirror
  `IsLetterRightSubsequential` via reverse conjugation.
-/

namespace Subregular

variable {α β : Type*}

/-- The synchronous left-subsequential class: computed by a finite-state `Mealy`. -/
def IsLetterLeftSubsequential (f : List α → List β) : Prop :=
  ∃ (σ : Type) (_ : Fintype σ) (T : Mealy σ α β), T.run = f

/-- Every finite-state `Mealy` witnesses `IsLetterLeftSubsequential` for its `run`.
The state `σ` is accepted at arbitrary `Type*` and brought down to
`Fin (Fintype.card σ) : Type 0` via `Mealy.reindex` and `Fintype.equivFin`, so
bounded-window states at the alphabet's universe can witness the predicate (mirrors
`SFST.isLeftSubsequential`). -/
theorem Mealy.isLetterLeftSubsequential {σ : Type*} [Fintype σ]
    (T : Mealy σ α β) : IsLetterLeftSubsequential T.run :=
  ⟨Fin (Fintype.card σ), inferInstance, Mealy.reindex (Fintype.equivFin σ) T,
   T.run_reindex _⟩

/-- A letter-left-subsequential map is left-determined at every coordinate — output `i`
depends only on the prefix `{k | k ≤ i}`. (The *block* `IsLeftSubsequential` lacks
this, by delayed output.) -/
theorem IsLetterLeftSubsequential.leftDetermined {f : List α → List β}
    (hf : IsLetterLeftSubsequential f) (i : ℕ) : LeftDetermined f i := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  intro u v hlen hag
  rw [T.getElem?_run u, T.getElem?_run v, hag i (Set.mem_setOf.mpr le_rfl),
    take_eq_of_agree fun k hk => hag k (Set.mem_setOf.mpr hk.le)]

/-- A synchronous left-subsequential map is right-myopic: it has no look-ahead. -/
theorem IsLetterLeftSubsequential.isRightMyopic {f : List α → List β}
    (hf : IsLetterLeftSubsequential f) : IsMyopicTowards f .right :=
  IsMyopicTowards.right_of_leftDetermined hf.leftDetermined

/-! ### Myhill–Nerode: the sufficiency direction

`f` is letter-left-subsequential as soon as it admits a *finite-state, left-congruent
summary that determines its output*. The finite `state` plays the role of the
prefix-congruence's quotient; `δ`/`out` are the induced transition and output. (The
natural Nerode congruence, when of finite index, is one such summary — that
instantiation, and the necessity direction, are the TODO above.) -/

/-- A length-preserving `f` with a finite `state : List α → σ` that is left-congruent
(`hδ`) and determines `f`'s output at each position (`hout`) is
letter-left-subsequential — the sufficiency half of Myhill–Nerode. -/
theorem isLetterLeftSubsequential_of_stateSummary
    {f : List α → List β} {σ : Type} [Fintype σ]
    (state : List α → σ) (δ : σ → α → σ) (out : σ → α → β)
    (hδ : ∀ u x, state (u ++ [x]) = δ (state u) x)
    (hout : ∀ u x w, (f (u ++ x :: w))[u.length]? = some (out (state u) x))
    (hlen : ∀ xs, (f xs).length = xs.length) :
    IsLetterLeftSubsequential f := by
  refine ⟨σ, inferInstance, ⟨state [], fun s x => (δ s x, out s x)⟩, ?_⟩
  set T : Mealy σ α β := ⟨state [], fun s x => (δ s x, out s x)⟩
  have hstate : ∀ ps : List α, T.stateAfter T.initial ps = state ps := by
    intro ps
    induction ps using List.reverseRecOn with
    | nil => rfl
    | append_singleton ps x ih => rw [T.stateAfter_append, ih, hδ]; rfl
  funext xs
  apply List.ext_getElem?
  intro i
  rw [T.getElem?_run xs i, hstate]
  rcases lt_or_ge i xs.length with hi | hi
  · have key := hout (xs.take i) xs[i] (xs.drop (i + 1))
    rw [List.length_take_of_le hi.le, ← List.drop_eq_getElem_cons hi,
      List.take_append_drop] at key
    rw [List.getElem?_eq_getElem hi, Option.map_some, key]
  · rw [List.getElem?_eq_none hi, List.getElem?_eq_none (by rw [hlen]; exact hi)]
    simp

/-- Non-vacuity: the identity is letter-left-subsequential via a one-state summary. -/
example : IsLetterLeftSubsequential (id : List α → List α) :=
  isLetterLeftSubsequential_of_stateSummary
    (fun _ => ()) (fun _ _ => ()) (fun _ x => x)
    (fun _ _ => rfl) (fun _ _ _ => by simp) (fun _ => rfl)

end Subregular
