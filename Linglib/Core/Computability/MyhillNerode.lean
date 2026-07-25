/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range
import Linglib.Core.Computability.Mealy

/-!
# Myhill–Nerode theorem for Mealy machines

This file characterizes the Mealy-computable (sequential) functions by their residuals,
in the style of `Mathlib.Computability.MyhillNerode` (which treats the language case).

Given `f : List α → List β` and a word `u`, the *residual* of `f` by `u` is the
function `v ↦ (f (u ++ v)).drop u.length` — what `f` appends after reading `u`. A
function is Mealy-computable if and only if it is length-preserving,
prefix-preserving, and has finitely many residuals — the Myhill–Nerode argument for the
minimal sequential machine of [holcombe-1982].

## Main definitions

* `residual f u`: the residual of `f` by the word `u`

## Main theorems

* `isMealyComputable_of_stateSummary`: a finite left-congruent state summary
  determining the output yields a machine
* `isMealyComputable_iff_residual`: `f` is Mealy-computable if and only if it is
  length-preserving, prefix-preserving, and `Set.range (residual f)` is finite

[UPSTREAM] candidate: `Mathlib.Computability.MyhillNerode` (as a Mealy section of the
existing file, with `residual` beside `Language.leftQuotient`).
-/

namespace Subregular

variable {α β : Type*} (f : List α → List β)

/-- The *residual* of `f` by `u` is what `f` appends after reading `u` — the analogue
for string functions of `Language.leftQuotient`. -/
def residual (u : List α) : List α → List β :=
  fun v => (f (u ++ v)).drop u.length

@[simp] theorem residual_nil : residual f [] = f := by
  funext v; simp [residual]

theorem residual_append (u v : List α) :
    residual f (u ++ v) = residual (residual f u) v := by
  funext w; simp [residual]

theorem residual_append_singleton (u : List α) (x : α) :
    residual f (u ++ [x]) = fun v => (residual f u (x :: v)).drop 1 := by
  funext v; simp [residual]

/-- Residuals of a machine's run factor through its states. -/
theorem Mealy.residual_run {σ : Type*} (T : Mealy σ α β) (u : List α) :
    residual T.run u = T.runFrom (T.stateAfter T.initial u) := by
  funext v
  simp only [residual, Mealy.run, Mealy.runFrom_append]
  rw [show u.length = (T.runFrom T.initial u).length from (T.length_runFrom _ _).symm,
    List.drop_left]

/-! ### Necessity -/

theorem IsMealyComputable.length_eq {f : List α → List β} (hf : IsMealyComputable f)
    (xs : List α) : (f xs).length = xs.length := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  exact T.length_run xs

theorem IsMealyComputable.isPrefix {f : List α → List β} (hf : IsMealyComputable f)
    (u v : List α) : f u <+: f (u ++ v) := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  exact ⟨_, (T.runFrom_append T.initial u v).symm⟩

theorem IsMealyComputable.finite_range_residual {f : List α → List β}
    (hf : IsMealyComputable f) : (Set.range (residual f)).Finite := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  exact Set.Finite.subset (Set.finite_range T.runFrom)
    (Set.range_subset_iff.mpr fun u => ⟨_, (T.residual_run u).symm⟩)

/-! ### Sufficiency -/

/-- A length-preserving `f` with a finite `state : List α → σ` that is left-congruent
(`hδ`) and determines `f`'s output at each position (`hout`) is Mealy-computable. -/
theorem isMealyComputable_of_stateSummary
    {f : List α → List β} {σ : Type*} [Fintype σ]
    (state : List α → σ) (δ : σ → α → σ) (out : σ → α → β)
    (hδ : ∀ u x, state (u ++ [x]) = δ (state u) x)
    (hout : ∀ u x w, (f (u ++ x :: w))[u.length]? = some (out (state u) x))
    (hlen : ∀ xs, (f xs).length = xs.length) :
    IsMealyComputable f := by
  refine isMealyComputable_iff.mpr ⟨σ, inferInstance, ⟨state [], δ, out⟩, ?_⟩
  set T : Mealy σ α β := ⟨state [], δ, out⟩
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
  · rw [List.getElem?_eq_none hi, List.getElem?_eq_none ((hlen xs).le.trans hi),
      Option.map_none]

/-- The identity is Mealy-computable, via a one-state summary. -/
theorem isMealyComputable_id : IsMealyComputable (id : List α → List α) :=
  isMealyComputable_of_stateSummary
    (fun _ => ()) (fun _ _ => ()) (fun _ x => x)
    (fun _ _ => rfl) (fun _ _ _ => by simp) (fun _ => rfl)

/-- A length-preserving, prefix-preserving function with finitely many residuals is
Mealy-computable: the residuals themselves are the states. -/
theorem isMealyComputable_of_residual {f : List α → List β}
    (hlen : ∀ xs, (f xs).length = xs.length)
    (hpre : ∀ u v, f u <+: f (u ++ v))
    (hfin : (Set.range (residual f)).Finite) :
    IsMealyComputable f := by
  have := Set.Finite.fintype hfin
  have hne : ∀ (r : Set.range (residual f)) (x : α), r.val [x] ≠ [] := by
    rintro ⟨_, u, rfl⟩ x
    exact List.ne_nil_of_length_pos (by simp [residual, hlen])
  refine isMealyComputable_of_stateSummary
    (fun u => ⟨residual f u, Set.mem_range_self u⟩)
    (fun r x => ⟨fun v => (r.val (x :: v)).drop 1, by
      obtain ⟨u, hu⟩ := r.prop
      exact ⟨u ++ [x], by rw [residual_append_singleton, hu]⟩⟩)
    (fun r x => (r.val [x]).head (hne r x))
    (fun u x => Subtype.ext (residual_append_singleton f u x))
    (fun u x w => ?_) hlen
  obtain ⟨t, ht⟩ := hpre (u ++ [x]) w
  rw [List.append_assoc, List.singleton_append] at ht
  rw [← ht, List.getElem?_append_left (by rw [hlen]; simp), ← List.head?_drop,
    show (f (u ++ [x])).drop u.length = residual f u [x] from rfl,
    List.head?_eq_some_head]

/-- **Myhill–Nerode for Mealy machines**: a function is Mealy-computable if and only
if it is length-preserving, prefix-preserving, and has finitely many residuals. -/
theorem isMealyComputable_iff_residual {f : List α → List β} :
    IsMealyComputable f
      ↔ (∀ xs, (f xs).length = xs.length) ∧ (∀ u v, f u <+: f (u ++ v))
        ∧ (Set.range (residual f)).Finite :=
  ⟨fun hf => ⟨hf.length_eq, hf.isPrefix, hf.finite_range_residual⟩,
   fun h => isMealyComputable_of_residual h.1 h.2.1 h.2.2⟩

end Subregular
