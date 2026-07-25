/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic
import Linglib.Core.Computability.Mealy
import Linglib.Core.Computability.Subregular.Function.Defs

/-!
# How far an output coordinate depends on its input

Dependence predicates on string functions. The kernel `OutputDependsOn f i K` says
output coordinate `i` of `f` is fixed by the input positions in `K`. Two notions are
instances:

* **Bounded dependence** on a side: that side's influence on the output reaches only a
  bounded distance, so a transducer scanning from it needs no unbounded context.
* **Two-sided unbounded dependence**: some target is swayed from *either* side,
  arbitrarily far away — each side alone suffices to change it.

## Main definitions

* `OutputDependsOn` — output coord `i` determined by input positions in `K`.
* `UnboundedDependence f s` — for every distance `d`, some output flips under a
  perturbation strictly beyond `d` on side `s`.
* `BoundedDependence f s` — the negation: dependence on side `s` is bounded.
* `TwoSidedUnboundedDependence` — co-located form: for every `d`, ONE base word with a
  target that flips under a far-left perturbation and under a far-right one.

## Main theorems

* `Mealy.boundedDependence_right`, `IsMealyComputable.boundedDependence_right` — a
  sequential machine is prefix-determined at every coordinate, so nothing to its right
  influences it.

## Implementation notes

The predicates are **distance-based** (`∀ d, ∃ word + target`), not fixed-index. A
fixed target index has only finitely many positions to its left, so a fixed-index
"unbounded left dependence" is unsatisfiable; the unbounded distance must be witnessed
by ever-longer words. The co-located `TwoSidedUnboundedDependence` keeps both
perturbations on a single shared base, so any computing automaton hits one context
where neither side alone fixes the output.

`TwoSidedUnboundedDependence` is *not* the weak-determinism boundary: a map can satisfy
it yet be weakly deterministic (a two-sided *union* is perturbed at one output by either
side, but neither side alone reverts it). The not-weakly-deterministic classification is
driven by the strictly stronger `RequiresBothSides` (in `Bimachine.lean`), where
perturbing either far side reverts the target to the identity — *both* sides are needed
at once, which is the boundary.

The name is deliberately descriptive rather than borrowed. Being changeable from either
side is compatible with every individual output coordinate still being fixed by a single
side, so this predicate separates neither of the two standard classes on its own: it is
implied by needing both sides at once, and is also satisfied by maps that never do.
-/

namespace Subregular


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

/-- Prefixes agreeing below `i` have equal `i`-truncations. -/
theorem take_eq_of_agree {u v : List α} {i : ℕ} (h : ∀ k, k < i → u[k]? = v[k]?) :
    u.take i = v.take i := by
  apply List.ext_getElem?
  intro k
  rcases lt_or_ge k i with hk | hk
  · simpa only [List.getElem?_take_of_lt hk] using h k hk
  · simp [List.getElem?_take_eq_none hk]

/-- Lists agreeing from `i` upward have equal `i`-suffixes. -/
theorem drop_eq_of_agree {u v : List α} {i : ℕ} (h : ∀ k, i ≤ k → u[k]? = v[k]?) :
    u.drop i = v.drop i := by
  apply List.ext_getElem?
  intro k
  simpa only [List.getElem?_drop] using h (i + k) (Nat.le_add_right i k)

/-- Agreement up to `j` transports truncations: `h.take_eq` for `h : AgreeUpto u v j`. -/
theorem AgreeUpto.take_eq {u v : List α} {j : ℕ} (h : AgreeUpto u v j) {i : ℕ}
    (hij : i ≤ j + 1) : u.take i = v.take i :=
  take_eq_of_agree fun k hk => h k (by omega)

/-- Agreement from `j` transports suffixes: `h.drop_eq` for `h : AgreeFrom u v j`. -/
theorem AgreeFrom.drop_eq {u v : List α} {j : ℕ} (h : AgreeFrom u v j) {i : ℕ}
    (hij : j ≤ i) : u.drop i = v.drop i :=
  drop_eq_of_agree fun k hk => h k (by omega)

/-- **Unbounded dependence on side `s`**: for every distance `d`, some target output
position flips under a perturbation strictly beyond `d` on side `s` (the perturbed
input agrees on the near window + the whole opposite side). -/
def UnboundedDependence (f : List α → List β) : Direction → Prop
  | .left  => ∀ d, ∃ (u v : List α) (i : ℕ), u.length = v.length ∧ i < u.length ∧
                AgreeFrom u v (i - d) ∧ (f u)[i]? ≠ (f v)[i]?
  | .right => ∀ d, ∃ (u v : List α) (i : ℕ), u.length = v.length ∧ i < u.length ∧
                AgreeUpto u v (i + d) ∧ (f u)[i]? ≠ (f v)[i]?

/-- Dependence on side `s` is bounded: no target is swayed from arbitrarily far away on
that side. -/
def BoundedDependence (f : List α → List β) (s : Direction) : Prop :=
  ¬ UnboundedDependence f s

/-- An equal-length variant of `base` differing only beyond the `d`-margin of target
`i` on side `s` — the far perturbation of the two-sided diagnostics. -/
def IsFarPerturbation (base u : List α) (i d : ℕ) (s : Direction) : Prop :=
  u.length = base.length ∧
    match s with
    | .left => AgreeFrom base u (i - d)
    | .right => AgreeUpto base u (i + d)

/-- Two-sided unbounded dependence, co-located: for every `d`, one base word with a
target `i` whose output flips under a far perturbation on either side. Co-location keeps
both flips on a single base (one automaton context). Each side alone sways the target, so
this is weaker than needing both at once (`RequiresBothSides`). -/
def TwoSidedUnboundedDependence (f : List α → List β) : Prop :=
  ∀ d, ∃ (base : List α) (i : ℕ), i < base.length ∧
    ∀ s, ∃ u, IsFarPerturbation base u i d s ∧ (f base)[i]? ≠ (f u)[i]?

/-- Co-located two-sided dependence yields unbounded dependence on the left. -/
theorem TwoSidedUnboundedDependence.left {f : List α → List β}
    (h : TwoSidedUnboundedDependence f) : UnboundedDependence f .left := by
  intro d
  obtain ⟨base, i, hi, hw⟩ := h d
  obtain ⟨uL, ⟨hlen, hag⟩, hne⟩ := hw .left
  exact ⟨base, uL, i, hlen.symm, hi, hag, hne⟩

/-- …and on the right. -/
theorem TwoSidedUnboundedDependence.right {f : List α → List β}
    (h : TwoSidedUnboundedDependence f) : UnboundedDependence f .right := by
  intro d
  obtain ⟨base, i, hi, hw⟩ := h d
  obtain ⟨uR, ⟨hlen, hag⟩, hne⟩ := hw .right
  exact ⟨base, uR, i, hlen.symm, hi, hag, hne⟩

/-- A map with two-sided unbounded dependence has bounded dependence on neither side,
since it exhibits unbounded dependence on each. -/
theorem TwoSidedUnboundedDependence.not_boundedDependence {f : List α → List β}
    (h : TwoSidedUnboundedDependence f) (s : Direction) : ¬ BoundedDependence f s := by
  cases s with
  | left => exact not_not_intro h.left
  | right => exact not_not_intro h.right

/-- `f` fails bounded dependence towards `s` exactly when it has unbounded dependence there
(`BoundedDependence` is by definition the negation of `UnboundedDependence`). -/
@[simp] theorem not_boundedDependence_iff {f : List α → List β} {s : Direction} :
    ¬ BoundedDependence f s ↔ UnboundedDependence f s := not_not

/-- Output coordinate `i` is fixed by the prefix `{k | k ≤ i}`, the footprint shape of a
left-to-right transducer. -/
def LeftDetermined (f : List α → List β) (i : ℕ) : Prop := OutputDependsOn f i {k | k ≤ i}

/-- A map whose every output coordinate is fixed by its prefix `{k | k ≤ i}` depends
boundedly on the right — trivially so, since nothing to the right matters at all. -/
theorem BoundedDependence.right_of_leftDetermined {f : List α → List β}
    (h : ∀ i, LeftDetermined f i) : BoundedDependence f .right := by
  intro hunb
  obtain ⟨u, v, i, hlen, _, hag, hne⟩ := hunb 0
  exact hne (h i u v hlen fun k hk => hag k (by simp only [Set.mem_setOf_eq] at hk; omega))

/-- A map whose every output coordinate is fixed by the input's *strict* prefix
`{k | k < i}` depends boundedly on the right; the canonical left-to-right scan has this
shape. The strict hypothesis is the stronger one, so this follows by
`OutputDependsOn.mono`. -/
theorem BoundedDependence.right_of_prefixDetermined {f : List α → List β}
    (h : ∀ i, OutputDependsOn f i {k | k < i}) : BoundedDependence f .right :=
  BoundedDependence.right_of_leftDetermined fun i => (h i).mono fun _ hk => Nat.le_of_lt hk

/-! ### Sequential machines do not depend on the right

Output coordinate `i` of a `Mealy` machine is fixed by the input prefix `[0..i]`, so the
sequential class depends boundedly on the right. Machines emitting blocks need not: one
that delays output, emitting `[]` and then `[x, y]`, has its coordinate `0` depend on
input position `1`. -/

section Synchronous

variable {σ : Type*}

/-- A sequential machine is left-determined at every coordinate: output `i` depends only
on the input prefix `{k | k ≤ i}`. -/
theorem Mealy.leftDetermined (T : Mealy σ α β) (i : ℕ) : LeftDetermined T.run i := by
  intro u v hlen hag
  simp only [Set.mem_setOf_eq] at hag
  rw [T.getElem?_run u, T.getElem?_run v, hag i le_rfl,
    take_eq_of_agree fun k hk => hag k hk.le]

/-- A sequential machine's output never depends on input to its right. -/
theorem Mealy.boundedDependence_right (T : Mealy σ α β) : BoundedDependence T.run .right :=
  BoundedDependence.right_of_leftDetermined T.leftDetermined

/-- A Mealy-computable map is left-determined at every coordinate. -/
theorem IsMealyComputable.leftDetermined {f : List α → List β}
    (hf : IsMealyComputable f) (i : ℕ) : LeftDetermined f i := by
  obtain ⟨σ, _, T, rfl⟩ := hf
  exact T.leftDetermined i

/-- A Mealy-computable map's output never depends on input to its right. -/
theorem IsMealyComputable.boundedDependence_right {f : List α → List β}
    (hf : IsMealyComputable f) : BoundedDependence f .right :=
  BoundedDependence.right_of_leftDetermined hf.leftDetermined

end Synchronous

end Subregular
