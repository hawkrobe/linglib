/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic
import Linglib.Core.Computability.Subregular.Function.Subsequential
import Linglib.Core.Data.List.DependsOn
import Linglib.Core.Data.List.EqOn

/-!
# Side dependence for string functions

A lattice of side-dependence predicates over `OutputDependsOn`:
`UnboundedDependence f s` says that input beyond any distance bound on side `s` can
still flip an output, `TwoSidedUnboundedDependence` places one target under the
influence of both sides, and `RequiresBothSides` demands both sides at once.
`flankWord` is the witness family instantiating them: a target buried in a filler run
between two independently editable flanks.

## Main definitions

* `UnboundedDependence f s`, `BoundedDependence f s`: whether input arbitrarily far
  away on side `s` can flip an output
* `TwoSidedUnboundedDependence f`: for every `d`, one base word carries a target
  flipped by far perturbations on either side
* `RequiresBothSides f`: the target is changed, and either far perturbation alone
  reverts it
* `flankWord x fill y n`: a target buried in a filler run with editable flanks

## Main theorems

* `RequiresBothSides.of_flanks`: the three-map witness template — a map is excluded
  by three images at the target coordinate
* `IsLeftSubsequential.boundedDependence_right`: a length-preserving left-subsequential
  function depends boundedly on the right
* `Mealy.leftDetermined`, `Mealy.boundedDependence_right`: a sequential machine is
  prefix-determined at every coordinate

## Implementation notes

The unboundedness predicates are distance-based (`∀ d, ∃ word + target`) rather than
fixed-index: a fixed target has only finitely many positions to its left, so a
fixed-index unbounded left dependence would be unsatisfiable.
-/

namespace Subregular

open Set

variable {α β : Type*} {f : List α → List β}

/-! ### The dependence lattice -/

/-- An equal-length variant of `base` differing only beyond the `d`-margin of target
`i` on side `s`. -/
def IsFarPerturbation (base u : List α) (i d : ℕ) (s : Direction) : Prop :=
  u.length = base.length ∧
    match s with
    | .left => EqOn (base[·]?) (u[·]?) (Ici (i - d))
    | .right => EqOn (base[·]?) (u[·]?) (Iic (i + d))

/-- `f` depends unboundedly on side `s` when for every distance `d` some target output
position flips under a far perturbation on that side. -/
def UnboundedDependence (f : List α → List β) (s : Direction) : Prop :=
  ∀ d, ∃ (u v : List α) (i : ℕ), i < u.length ∧ IsFarPerturbation u v i d s ∧
    (f u)[i]? ≠ (f v)[i]?

/-- Dependence on side `s` is bounded: no output flips under perturbations arbitrarily
far away on that side. -/
def BoundedDependence (f : List α → List β) (s : Direction) : Prop :=
  ¬ UnboundedDependence f s

/-- `f` fails bounded dependence towards `s` exactly when it has unbounded dependence
there. -/
@[simp] theorem not_boundedDependence_iff {s : Direction} :
    ¬ BoundedDependence f s ↔ UnboundedDependence f s := not_not

/-- A map whose every output coordinate is fixed by its prefix `Set.Iic i` depends
boundedly on the right. -/
theorem BoundedDependence.right_of_leftDetermined (h : ∀ i, LeftDetermined f i) :
    BoundedDependence f .right := by
  rintro hunb
  obtain ⟨u, v, i, hi, ⟨hlen, hag⟩, hne⟩ := hunb 0
  exact hne (h i hlen.symm (hag.mono (Iic_subset_Iic.mpr (by omega))))

/-- A map whose every output coordinate is fixed by the input's strict prefix
`Set.Iio i` depends boundedly on the right. -/
theorem BoundedDependence.right_of_prefixDetermined
    (h : ∀ i, OutputDependsOn f i (Iio i)) : BoundedDependence f .right :=
  BoundedDependence.right_of_leftDetermined fun i => (h i).mono Iio_subset_Iic_self

/-- For every `d`, one base word carries a target whose output flips under a far
perturbation on either side. -/
def TwoSidedUnboundedDependence (f : List α → List β) : Prop :=
  ∀ d, ∃ (base : List α) (i : ℕ), i < base.length ∧
    ∀ s, ∃ u, IsFarPerturbation base u i d s ∧ (f base)[i]? ≠ (f u)[i]?

/-- Co-located two-sided dependence yields unbounded dependence on either side. -/
theorem TwoSidedUnboundedDependence.unboundedDependence
    (h : TwoSidedUnboundedDependence f) (s : Direction) : UnboundedDependence f s :=
  fun d =>
    have ⟨base, i, hi, hw⟩ := h d
    have ⟨u, hp, hne⟩ := hw s
    ⟨base, u, i, hi, hp, hne⟩

/-- A map with two-sided unbounded dependence has bounded dependence on neither side. -/
theorem TwoSidedUnboundedDependence.not_boundedDependence
    (h : TwoSidedUnboundedDependence f) (s : Direction) : ¬ BoundedDependence f s :=
  not_not_intro (h.unboundedDependence s)

/-- `f` requires both sides when some target changes under `f` yet perturbing either
far side reverts it to the identity. -/
def RequiresBothSides (f : List α → List α) : Prop :=
  ∀ d, ∃ (base : List α) (i : ℕ), i < base.length ∧ (f base)[i]? ≠ base[i]? ∧
    ∀ s, ∃ u, IsFarPerturbation base u i d s ∧ u[i]? = base[i]? ∧ (f u)[i]? = u[i]?

/-- Requiring both sides strengthens two-sided unbounded dependence. -/
theorem RequiresBothSides.twoSidedUnboundedDependence {f : List α → List α}
    (hf : RequiresBothSides f) : TwoSidedUnboundedDependence f := fun d =>
  have ⟨base, i, hi, hchange, hw⟩ := hf d
  ⟨base, i, hi, fun s =>
    have ⟨u, hp, hsym, hrev⟩ := hw s
    ⟨u, hp, fun h => hchange (h.trans (hrev.trans hsym))⟩⟩

section FlankWitness

variable {x fill y a : α} {n k : ℕ} {p : α → Bool}

/-! ### The flank-witness template

The recurring witness family for two-sided unboundedness: a target buried in a filler
run, with independently editable flanks. `RequiresBothSides.of_flanks` packages the
whole assembly — a map is excluded by exhibiting only three images, those of the base
and of the two single-flank perturbations, at the target coordinate. -/

/-- The word `x`, then `n` copies of `fill`, then `y`. -/
def flankWord (x fill y : α) (n : ℕ) : List α := x :: (List.replicate n fill ++ [y])

@[simp] theorem length_flankWord :
    (flankWord x fill y n).length = n + 2 := by
  simp [flankWord]

theorem getElem?_flankWord :
    (flankWord x fill y n)[k]? = if k = 0 then some x else if k = n + 1 then some y
      else if k < n + 2 then some fill else none := by
  simp only [flankWord, List.getElem?_cons, List.getElem?_append, List.getElem?_replicate,
    List.length_replicate, List.getElem?_nil]
  split_ifs <;> first | rfl | omega

@[simp] theorem getElem?_flankWord_zero :
    (flankWord x fill y n)[0]? = some x := rfl

@[simp] theorem getElem?_flankWord_last :
    (flankWord x fill y n)[n + 1]? = some y := by
  rw [getElem?_flankWord]; simp

theorem getElem?_flankWord_mid (h₁ : 0 < k) (h₂ : k ≤ n) :
    (flankWord x fill y n)[k]? = some fill := by
  rw [getElem?_flankWord]
  split_ifs <;> first | rfl | exact ‹False›.elim | omega

/-- A non-filler value sits only on a flank. -/
theorem getElem?_flankWord_eq_some_iff {j : ℕ} (hfill : fill ≠ a) :
    (flankWord x fill y n)[j]? = some a ↔ j = 0 ∧ x = a ∨ j = n + 1 ∧ y = a := by
  rw [getElem?_flankWord]
  split_ifs <;> simp_all

/-- The window up to the filler run is the left flank and part of the run. -/
theorem take_flankWord (hk : k ≤ n) :
    (flankWord x fill y n).take (k + 1) = x :: List.replicate k fill := by
  rw [flankWord, List.take_succ_cons, List.take_append_of_le_length (by simp; omega),
    List.take_replicate, Nat.min_eq_left hk]

/-- The window past the left flank is the rest of the run and the right flank. -/
theorem drop_flankWord (hk : k ≤ n) :
    (flankWord x fill y n).drop (k + 1) = List.replicate (n - k) fill ++ [y] := by
  rw [flankWord, List.drop_succ_cons, List.drop_append_of_le_length (by simp; omega),
    List.drop_replicate]

/-- A window reaching at most the filler run hits `a` iff the left flank is `a`. -/
theorem exists_le_flankWord_eq_some_iff (hfill : fill ≠ a) (hk : k ≤ n) :
    (∃ j ≤ k, (flankWord x fill y n)[j]? = some a) ↔ x = a := by
  simp [getElem?_flankWord_eq_some_iff hfill, and_or_left, exists_or,
    eq_false (by omega : ¬ (n + 1 ≤ k))]

/-- A window past the left flank hits `a` iff the right flank is `a`. -/
theorem exists_ge_flankWord_eq_some_iff (hfill : fill ≠ a) (h0 : 0 < k)
    (hk : k ≤ n + 1) : (∃ j ≥ k, (flankWord x fill y n)[j]? = some a) ↔ y = a := by
  simp [getElem?_flankWord_eq_some_iff hfill, and_or_left, exists_or,
    eq_false (by omega : ¬ (k ≤ 0)), hk]

/-- A window reaching at most the filler run contains `a` iff the left flank is `a`. -/
theorem mem_take_flankWord_iff (hfill : fill ≠ a) (h0 : 0 < k) (hk : k ≤ n + 1) :
    a ∈ (flankWord x fill y n).take k ↔ x = a := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [take_flankWord (by omega)]
  simp [List.mem_replicate, eq_comm, hfill]

/-- A window past the left flank contains `a` iff the right flank is `a`. -/
theorem mem_drop_flankWord_iff (hfill : fill ≠ a) (h0 : 0 < k) (hk : k ≤ n + 1) :
    a ∈ (flankWord x fill y n).drop k ↔ y = a := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [drop_flankWord (by omega)]
  simp [List.mem_replicate, eq_comm, hfill]

/-- A flag over a window reaching at most the filler run reads the left flank. -/
theorem any_take_flankWord (hfill : p fill = false) (h0 : 0 < k) (hk : k ≤ n + 1) :
    ((flankWord x fill y n).take k).any p = p x := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [take_flankWord (by omega)]
  simp [hfill]

/-- A flag over a window past the left flank reads the right flank. -/
theorem any_drop_flankWord (hfill : p fill = false) (h0 : 0 < k) (hk : k ≤ n + 1) :
    ((flankWord x fill y n).drop k).any p = p y := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [drop_flankWord (by omega)]
  simp [hfill]

/-- Flank words differing only on the left agree off position `0`. -/
theorem flankWord_congr_left {x' : α} (h : k ≠ 0) :
    (flankWord x fill y n)[k]? = (flankWord x' fill y n)[k]? := by
  simp only [getElem?_flankWord, if_neg h]

/-- Flank words differing only on the right agree off the last position. -/
theorem flankWord_congr_right {y' : α} (h : k ≠ n + 1) :
    (flankWord x fill y n)[k]? = (flankWord x fill y' n)[k]? := by
  simp only [getElem?_flankWord, if_neg h]

/-- A `d`-indexed family of flank words whose target sits `d`-far from both flanks,
changed to `on` in the base and reverted by flipping either flank alone, requires both
sides. -/
theorem RequiresBothSides.of_flanks {f : List α → List α}
    {fill on xOn yOn xOff yOff : α} {n t : ℕ → ℕ} (hne : on ≠ fill)
    (hmargin : ∀ d, d < t d ∧ t d + d < n d + 1)
    (hchange : ∀ d, (f (flankWord xOn fill yOn (n d)))[t d]? = some on)
    (hrevL : ∀ d, (f (flankWord xOff fill yOn (n d)))[t d]? = some fill)
    (hrevR : ∀ d, (f (flankWord xOn fill yOff (n d)))[t d]? = some fill) :
    RequiresBothSides f := by
  intro d
  obtain ⟨hm₁, hm₂⟩ := hmargin d
  have hmid : ∀ x y : α, (flankWord x fill y (n d))[t d]? = some fill := fun x y =>
    getElem?_flankWord_mid (by omega) (by omega)
  refine ⟨flankWord xOn fill yOn (n d), t d, by rw [length_flankWord]; omega,
    by rw [hchange, hmid]; simpa using hne, fun s => ?_⟩
  match s with
  | .left =>
    exact ⟨flankWord xOff fill yOn (n d),
      ⟨by simp, fun k (hk : t d - d ≤ k) => flankWord_congr_left (by omega)⟩,
      by rw [hmid, hmid],
      by rw [hrevL, hmid]⟩
  | .right =>
    exact ⟨flankWord xOn fill yOff (n d),
      ⟨by simp, fun k (hk : k ≤ t d + d) => flankWord_congr_right (by omega)⟩,
      by rw [hmid, hmid],
      by rw [hrevR, hmid]⟩

end FlankWitness

/-! ### Machines bound dependence

A length-preserving left-subsequential function depends boundedly on the right: the
delay bound of `IsLeftSubsequential.exists_getElem?_append_eq` is the dependence bound.
Sequential machines are the zero-delay case — prefix-determined at every coordinate
(`Mealy.leftDetermined`), which is strictly stronger than bounded right dependence. -/

section Machines

variable {σ : Type*}

/-- A length-preserving left-subsequential function depends boundedly on the right. -/
theorem IsLeftSubsequential.boundedDependence_right
    (hlen : ∀ w, (f w).length = w.length) (hf : IsLeftSubsequential f) :
    BoundedDependence f .right := by
  obtain ⟨N, hN⟩ := hf.exists_getElem?_append_eq
  rintro hunb
  obtain ⟨u, v, i, hi, ⟨hl, hag⟩, hne⟩ := hunb N
  rcases lt_or_ge u.length (i + N + 1) with hle | hlt
  · exact hne (congrArg (·[i]?) (congrArg f (List.ext_getElem? fun k => by
      rcases lt_or_ge k (i + N + 1) with hk | hk
      · exact hag.getElem?_eq (mem_Iic.mpr (by omega))
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)])))
  · have hp : u.take (i + N + 1) = v.take (i + N + 1) := hag.take_eq (by omega)
    have key : ∀ w : List α, w.length = u.length →
        (f (w.take (i + N + 1)))[i]? = (f w)[i]? := fun w hw => by
      conv_rhs => rw [← List.take_append_drop (i + N + 1) w]
      exact hN _ _ i (by rw [hlen, List.length_take]; omega)
    rw [← key u rfl, hp, key v hl] at hne
    exact hne rfl

/-- A sequential machine is left-determined at every coordinate. -/
theorem Mealy.leftDetermined (T : Mealy σ α β) (i : ℕ) : LeftDetermined T.run i := by
  intro u v hlen hag
  rw [T.getElem?_run u, T.getElem?_run v, hag.getElem?_eq (mem_Iic.mpr le_rfl),
    List.take_eq_of_agree fun k hk => hag.getElem?_eq (mem_Iic.mpr hk.le)]

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

end Machines

end Subregular
