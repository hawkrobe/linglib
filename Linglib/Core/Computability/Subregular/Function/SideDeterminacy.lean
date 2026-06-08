/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic
import Linglib.Core.Computability.Subregular.Function.Direction

/-!
# Side-determinacy: myopia and unbounded circumambience

Locality predicates on string functions, used to classify phonological maps in the
function-level subregular hierarchy. The kernel `OutputDependsOn f i K` says output
coordinate `i` of `f` is fixed by the input positions in `K`.

The two phonological notions both papers in this line center are instances:

* **Myopia** ([wilson-2006]; the "no look-ahead" generalisation): a side's influence
  on the output is *bounded*.
* **Unbounded circumambience** ([mccollum-bakovic-mai-meinhardt-2020] def. 13): some
  target depends on input *arbitrarily far on both sides at once*.

## Main definitions

* `OutputDependsOn` — output coord `i` determined by input positions in `K`.
* `UnboundedDependence f s` — for every distance `d`, some output flips under a
  perturbation strictly beyond `d` on side `s`.
* `IsMyopicTowards f s` — the negation: dependence on side `s` is bounded.
* `IsUnboundedCircumambient` — co-located form of def. 13: for every `d`, ONE base
  word with a target that flips under both a far-left and a far-right perturbation.

## Implementation notes

The predicates are **distance-based** (`∀ d, ∃ word + target`), not fixed-index. A
fixed target index has only finitely many positions to its left, so a fixed-index
"unbounded left dependence" is unsatisfiable; the unbounded distance must be witnessed
by ever-longer words. The co-located `IsUnboundedCircumambient` keeps both
perturbations on a single shared base (so any computing automaton hits one context
where neither side alone fixes the output) — the hook for the deferred
"circumambient ⟹ non-deterministic" classification.

## Todo

* The machine-level `IsUnboundedCircumambient f → ¬ IsWeaklyDeterministic f` theorem
  (the bridge to `Function/WeaklyDeterministic.lean`; needs bimachine substrate, with
  the co-located base as its automaton-context witness).
-/

namespace Core.Computability.Subregular.Function

open Core (Direction)

variable {α β : Type*}

/-- Output coordinate `i` of `f` is determined by the input positions in `K`:
equal-length inputs agreeing on `K` agree at output `i`. Monotone in `K`. -/
def OutputDependsOn (f : List α → List β) (i : ℕ) (K : Set ℕ) : Prop :=
  ∀ u v : List α, u.length = v.length →
    (∀ k ∈ K, u[k]? = v[k]?) → (f u)[i]? = (f v)[i]?

theorem OutputDependsOn.mono {f : List α → List β} {i : ℕ} {K K' : Set ℕ}
    (hKK' : K ⊆ K') (h : OutputDependsOn f i K) : OutputDependsOn f i K' :=
  fun u v hl hag => h u v hl fun k hk => hag k (hKK' hk)

/-- `u` and `v` agree at every index `≥ j`. -/
def AgreeFrom (u v : List α) (j : ℕ) : Prop := ∀ k, j ≤ k → u[k]? = v[k]?
/-- `u` and `v` agree at every index `≤ j`. -/
def AgreeUpto (u v : List α) (j : ℕ) : Prop := ∀ k, k ≤ j → u[k]? = v[k]?

/-- **Unbounded dependence on side `s`**: for every distance `d`, some target output
position flips under a perturbation strictly beyond `d` on side `s` (the perturbed
input agrees on the near window + the whole opposite side). -/
def UnboundedDependence (f : List α → List β) : Direction → Prop
  | .left  => ∀ d, ∃ (u v : List α) (i : ℕ), u.length = v.length ∧ i < u.length ∧
                AgreeFrom u v (i - d) ∧ (f u)[i]? ≠ (f v)[i]?
  | .right => ∀ d, ∃ (u v : List α) (i : ℕ), u.length = v.length ∧ i < u.length ∧
                AgreeUpto u v (i + d) ∧ (f u)[i]? ≠ (f v)[i]?

/-- **Myopia towards `s`** ([wilson-2006]): dependence on side `s` is bounded. -/
def IsMyopicTowards (f : List α → List β) (s : Direction) : Prop :=
  ¬ UnboundedDependence f s

/-- **Unbounded circumambience** ([mccollum-bakovic-mai-meinhardt-2020] def. 13),
co-located: for every `d`, one base word with a target `i` whose output flips under
BOTH a far-left perturbation (agreeing from `i - d`) and a far-right one (agreeing up
to `i + d`). Co-location keeps both flips on a single base (one automaton context). -/
def IsUnboundedCircumambient (f : List α → List β) : Prop :=
  ∀ d, ∃ (base : List α) (i : ℕ), i < base.length ∧
    (∃ uL : List α, uL.length = base.length ∧ AgreeFrom base uL (i - d) ∧
      (f base)[i]? ≠ (f uL)[i]?) ∧
    (∃ uR : List α, uR.length = base.length ∧ AgreeUpto base uR (i + d) ∧
      (f base)[i]? ≠ (f uR)[i]?)

/-- Co-located circumambience yields unbounded dependence on the left. -/
theorem IsUnboundedCircumambient.left {f : List α → List β}
    (h : IsUnboundedCircumambient f) : UnboundedDependence f .left := by
  intro d
  obtain ⟨base, i, hi, ⟨uL, hlen, hag, hne⟩, _⟩ := h d
  exact ⟨base, uL, i, hlen.symm, hi, hag, hne⟩

/-- …and on the right. -/
theorem IsUnboundedCircumambient.right {f : List α → List β}
    (h : IsUnboundedCircumambient f) : UnboundedDependence f .right := by
  intro d
  obtain ⟨base, i, hi, _, ⟨uR, hlen, hag, hne⟩⟩ := h d
  exact ⟨base, uR, i, hlen.symm, hi, hag, hne⟩

/-- **Circumambient ⟹ not myopic** (either side): a real consequence, since
circumambience exhibits unbounded dependence on each side. -/
theorem IsUnboundedCircumambient.not_myopic {f : List α → List β}
    (h : IsUnboundedCircumambient f) (s : Direction) : ¬ IsMyopicTowards f s := by
  cases s with
  | left => exact not_not_intro h.left
  | right => exact not_not_intro h.right

/-- `f` is non-myopic towards `s` exactly when it has unbounded dependence there
(`IsMyopicTowards` is by definition the negation of `UnboundedDependence`). -/
@[simp] theorem not_isMyopicTowards_iff {f : List α → List β} {s : Direction} :
    ¬ IsMyopicTowards f s ↔ UnboundedDependence f s := not_not

end Core.Computability.Subregular.Function
