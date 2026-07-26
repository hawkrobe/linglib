/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Restrict
import Linglib.Core.Computability.Subregular.Function.Subsequential
import Linglib.Core.Data.List.EqOn

/-!
# Side dependence for string functions

`OutputDependsOn f i K` states that output coordinate `i` of the string function `f`
is determined by the input positions in `K`: equal-length inputs agreeing on `K` agree
at output `i`. It is the length-stratified sibling of `Function.DependsOn`, with the
same congruence form as primary definition and the same factor-through
characterization (`outputDependsOn_iff_factorsThrough`).

A lattice of side-dependence predicates sits over it: `BoundedDependence f s` says a
single margin caps the influence of side `s` at every output coordinate,
`TwoSidedUnboundedDependence` places one target under the influence of both sides,
and `RequiresBothSides` demands both sides at once. `flankWord` is the witness family
instantiating the negative side: a target buried in a filler run between two
independently editable flanks.

## Main definitions

* `OutputDependsOn f i K`: output coordinate `i` is determined by input positions `K`
* `LeftDetermined f i`: output coordinate `i` is fixed by the prefix `Set.Iic i`
* `BoundedDependence f s`, `UnboundedDependence f s`: whether one margin caps the
  influence of side `s` at every output coordinate
* `TwoSidedUnboundedDependence f`: for every `d`, one base word carries a target
  flipped by far perturbations on either side
* `RequiresBothSides f`: the target is changed, and either far perturbation alone
  reverts it
* `flankWord x fill y n`: a target buried in a filler run with editable flanks

## Main theorems

* `unboundedDependence_iff`: every margin fails at some output coordinate
* `RequiresBothSides.of_flanks`: the three-map witness template — a map is excluded
  by three target-cell observations
* `IsLeftSubsequential.boundedDependence_right`: a length-preserving left-subsequential
  function depends boundedly on the right
* `Mealy.leftDetermined`, `Mealy.boundedDependence_right`: a sequential machine is
  prefix-determined at every coordinate

## Implementation notes

The output coordinate and the input window are indexed separately, which is
informative for length-preserving functions; for block-emitting transducers the two
drift apart. `BoundedDependence` is the positive primitive; `unboundedDependence_iff` recovers
the margin-indexed witness form, and unpacking `¬ OutputDependsOn` yields word-pair
witnesses. The forms are margin-indexed rather than fixed-index because a fixed
target has only finitely many positions to its left.
The predicates place no in-range guard on target coordinates: for length-preserving
maps an out-of-range coordinate is `none` on both sides of any perturbation.
-/

namespace Subregular

open Set

variable {α β : Type*} {f : List α → List β}

/-! ### Coordinate dependence -/

/-- Output coordinate `i` of `f` is determined by the input positions in `K`:
equal-length inputs agreeing on `K` agree at output `i`. -/
def OutputDependsOn (f : List α → List β) (i : ℕ) (K : Set ℕ) : Prop :=
  ∀ ⦃u v : List α⦄, u.length = v.length → EqOn (u[·]?) (v[·]?) K →
    (f u)[i]? = (f v)[i]?

theorem OutputDependsOn.mono {i : ℕ} {K K' : Set ℕ}
    (hKK' : K ⊆ K') (h : OutputDependsOn f i K) : OutputDependsOn f i K' :=
  fun _ _ hl hag => h hl (hag.mono hKK')

/-- Coordinate `i` of the output factors through the input's length and its
restriction to `K`. -/
theorem outputDependsOn_iff_factorsThrough {i : ℕ} {K : Set ℕ} :
    OutputDependsOn f i K ↔
      Function.FactorsThrough (fun u => (f u)[i]?)
        (fun u : List α => (u.length, K.restrict (u[·]?))) := by
  constructor
  · intro h u v huv
    rw [Prod.mk.injEq] at huv
    exact h huv.1 fun k hk => congrFun huv.2 ⟨k, hk⟩
  · intro h u v hlen hag
    exact h (Prod.ext hlen (funext fun k => hag k.2))

/-- Output coordinate `i` is fixed by the prefix `Set.Iic i`. -/
def LeftDetermined (f : List α → List β) (i : ℕ) : Prop := OutputDependsOn f i (Iic i)

/-! ### The dependence lattice -/

/-- An equal-length variant of `base` differing only beyond the `d`-margin of target
`i` on side `s`. -/
def IsFarPerturbation (base u : List α) (i d : ℕ) (s : Direction) : Prop :=
  u.length = base.length ∧ EqOn (base[·]?) (u[·]?) (s.window i d)

/-- `f` depends boundedly on side `s`: a single margin caps, at every output
coordinate, how far input on side `s` can matter. -/
def BoundedDependence (f : List α → List β) (s : Direction) : Prop :=
  ∃ N, ∀ i, OutputDependsOn f i (s.window i N)

/-- `f` depends unboundedly on side `s`. -/
def UnboundedDependence (f : List α → List β) (s : Direction) : Prop :=
  ¬ BoundedDependence f s

/-- `f` fails unbounded dependence on side `s` exactly when its dependence there is
bounded. -/
@[simp] theorem not_unboundedDependence_iff {s : Direction} :
    ¬ UnboundedDependence f s ↔ BoundedDependence f s := not_not

/-- Unbounded dependence coordinate-wise: every margin fails at some output
coordinate. -/
theorem unboundedDependence_iff {s : Direction} :
    UnboundedDependence f s ↔ ∀ N, ∃ i, ¬ OutputDependsOn f i (s.window i N) := by
  simp [UnboundedDependence, BoundedDependence]

/-- A map whose every output coordinate is fixed by its prefix `Set.Iic i` depends
boundedly on the right. -/
theorem BoundedDependence.right_of_leftDetermined (h : ∀ i, LeftDetermined f i) :
    BoundedDependence f .right := ⟨0, h⟩

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
  unboundedDependence_iff.mpr fun N =>
    have ⟨_, i, _, hw⟩ := h N
    have ⟨_, ⟨hlen, hag⟩, hne⟩ := hw s
    ⟨i, fun hOD => hne (hOD hlen.symm hag)⟩

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
whole assembly — a map is excluded by three target-cell observations: the base image
leaves the filler, and either single-flank perturbation restores it. -/

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

/-- A window reaching at most the filler run contains `a` iff the left flank is `a`. -/
theorem mem_take_flankWord_iff (hfill : fill ≠ a) (hk : k ≤ n) :
    a ∈ (flankWord x fill y n).take (k + 1) ↔ x = a := by
  rw [take_flankWord hk]
  simp [List.mem_replicate, eq_comm, hfill]

/-- A window past the left flank contains `a` iff the right flank is `a`. -/
theorem mem_drop_flankWord_iff (hfill : fill ≠ a) (hk : k ≤ n) :
    a ∈ (flankWord x fill y n).drop (k + 1) ↔ y = a := by
  rw [drop_flankWord hk]
  simp [List.mem_replicate, eq_comm, hfill]

/-- A flag over a window reaching at most the filler run reads the left flank. -/
theorem any_take_flankWord (hfill : p fill = false) (hk : k ≤ n) :
    ((flankWord x fill y n).take (k + 1)).any p = p x := by
  rw [take_flankWord hk]
  simp [hfill]

/-- A flag over a window past the left flank reads the right flank. -/
theorem any_drop_flankWord (hfill : p fill = false) (hk : k ≤ n) :
    ((flankWord x fill y n).drop (k + 1)).any p = p y := by
  rw [drop_flankWord hk]
  simp [hfill]

/-- Changing only the left flank perturbs beyond the `d`-margin of a target past it. -/
theorem IsFarPerturbation.flankWord_left {i d : ℕ} (x' : α) (h : d < i) :
    IsFarPerturbation (flankWord x fill y n) (flankWord x' fill y n) i d .left :=
  ⟨by simp, fun k hk => by grind [getElem?_flankWord]⟩

/-- Changing only the right flank perturbs beyond the `d`-margin of a target
`d`-clear of the last position. -/
theorem IsFarPerturbation.flankWord_right {i d : ℕ} (y' : α) (h : i + d ≤ n) :
    IsFarPerturbation (flankWord x fill y n) (flankWord x fill y' n) i d .right :=
  ⟨by simp, fun k hk => by grind [getElem?_flankWord]⟩

/-- A `d`-indexed family of flank words whose target sits `d`-far from both flanks,
changed in the base and reverted by flipping either flank alone, requires both sides. -/
theorem RequiresBothSides.of_flanks {f : List α → List α}
    {fill xOn yOn xOff yOff : α} {n t : ℕ → ℕ}
    (ht : ∀ d, d < t d) (hn : ∀ d, t d + d ≤ n d)
    (hchange : ∀ d, (f (flankWord xOn fill yOn (n d)))[t d]? ≠ some fill)
    (hrevL : ∀ d, (f (flankWord xOff fill yOn (n d)))[t d]? = some fill)
    (hrevR : ∀ d, (f (flankWord xOn fill yOff (n d)))[t d]? = some fill) :
    RequiresBothSides f := by
  intro d
  have h₁ := ht d; have h₂ := hn d
  have hmid : ∀ x y : α, (flankWord x fill y (n d))[t d]? = some fill := fun _ _ =>
    getElem?_flankWord_mid (by omega) (by omega)
  refine ⟨flankWord xOn fill yOn (n d), t d, by rw [length_flankWord]; omega,
    fun h => hchange d (h.trans (hmid _ _)), fun s => ?_⟩
  match s with
  | .left => exact ⟨_, .flankWord_left xOff (ht d),
      (hmid _ _).trans (hmid _ _).symm, (hrevL d).trans (hmid _ _).symm⟩
  | .right => exact ⟨_, .flankWord_right yOff (hn d),
      (hmid _ _).trans (hmid _ _).symm, (hrevR d).trans (hmid _ _).symm⟩

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
  refine ⟨N, fun i => ?_⟩
  rw [Direction.window_right]
  intro u v hl hag
  rcases lt_or_ge u.length (i + N + 1) with hle | hlt
  · exact congrArg (·[i]?) (congrArg f (List.ext_getElem? fun k => by
      rcases lt_or_ge k (i + N + 1) with hk | hk
      · exact hag.getElem?_eq (mem_Iic.mpr (by omega))
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]))
  · have hp : u.take (i + N + 1) = v.take (i + N + 1) := hag.take_eq (by omega)
    have key : ∀ w : List α, w.length = u.length →
        (f (w.take (i + N + 1)))[i]? = (f w)[i]? := fun w hw => by
      conv_rhs => rw [← List.take_append_drop (i + N + 1) w]
      exact hN _ _ i (by rw [hlen, List.length_take]; omega)
    rw [← key u rfl, hp, key v hl.symm]

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
