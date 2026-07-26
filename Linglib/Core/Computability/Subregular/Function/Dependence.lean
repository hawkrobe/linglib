/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Basic
import Linglib.Core.Computability.Mealy
import Linglib.Core.Computability.Subregular.Function.Defs
import Linglib.Core.Logic.FactorsThroughOn

/-!
# Dependence predicates for string functions

`OutputDependsOn f i K` states that output coordinate `i` of the string function `f`
is determined by the input positions in `K`: equal-length inputs agreeing on `K` agree
at output `i`. `UnboundedDependence f s` says that input beyond any distance bound on
side `s` can still flip an output of `f`, and `BoundedDependence` is its negation.
`TwoSidedUnboundedDependence` and the stronger `RequiresBothSides` place a single
target under the influence of both sides at once, and `flankWord` is the witness
family instantiating them: a target buried in a filler run between two independently
editable flanks.

## Main definitions

* `OutputDependsOn f i K`: output coordinate `i` is fixed by the input positions in `K`
* `UnboundedDependence f s`, `BoundedDependence f s`: whether input arbitrarily far
  away on side `s` can flip an output
* `TwoSidedUnboundedDependence f`: for every `d`, one base word carries a target
  flipped by far perturbations on either side
* `RequiresBothSides f`: the target is changed, and either far perturbation alone
  reverts it
* `flankWord x fill y n`: a target buried in a filler run with editable flanks

## Main theorems

* `outputDependsOn_iff_factorsThroughOn`: dependence on `K` is a factor-through of the
  input's restriction to `K`
* `RequiresBothSides.of_flanks`: the three-map witness template of [yolyan-2025] §5.3
* `Mealy.boundedDependence_right`, `IsMealyComputable.boundedDependence_right`: a
  sequential machine is prefix-determined at every coordinate, so nothing to its
  right influences it

## Implementation notes

The unboundedness predicates are distance-based (`∀ d, ∃ word + target`) rather than
fixed-index: a fixed target has only finitely many positions to its left, so a
fixed-index unbounded left dependence would be unsatisfiable.
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

/-- `OutputDependsOn` is a factor-through condition: coordinate `i` of the output factors
through the restriction of the input to `K`, on each set of inputs of a fixed length.
This is the same shape the language side uses for its locality classes, which are stated
directly as `Function.FactorsThrough` of membership through a bounded window. -/
theorem outputDependsOn_iff_factorsThroughOn {f : List α → List β} {i : ℕ} {K : Set ℕ} :
    OutputDependsOn f i K ↔
      ∀ n, Function.FactorsThroughOn (fun u => (f u)[i]?)
        (fun u : List α => K.restrict fun k => u[k]?) {u : List α | u.length = n} := by
  constructor
  · intro h n u v hu hv hres
    exact h u v (hu.trans hv.symm) fun k hk => congrFun hres ⟨k, hk⟩
  · intro h u v hlen hag
    exact h u.length (rfl : u.length = u.length) hlen.symm (funext fun k => hag k.1 k.2)

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

/-- `f` depends unboundedly on side `s` when for every distance `d` some target output
position flips under a perturbation strictly beyond `d` on that side (the perturbed
input agrees on the near window and the whole opposite side). -/
def UnboundedDependence (f : List α → List β) : Direction → Prop
  | .left  => ∀ d, ∃ (u v : List α) (i : ℕ), u.length = v.length ∧ i < u.length ∧
                AgreeFrom u v (i - d) ∧ (f u)[i]? ≠ (f v)[i]?
  | .right => ∀ d, ∃ (u v : List α) (i : ℕ), u.length = v.length ∧ i < u.length ∧
                AgreeUpto u v (i + d) ∧ (f u)[i]? ≠ (f v)[i]?

/-- Dependence on side `s` is bounded: no output flips under perturbations arbitrarily
far away on that side. -/
def BoundedDependence (f : List α → List β) (s : Direction) : Prop :=
  ¬ UnboundedDependence f s

/-- An equal-length variant of `base` differing only beyond the `d`-margin of target
`i` on side `s` — the far perturbation of the two-sided diagnostics. -/
def IsFarPerturbation (base u : List α) (i d : ℕ) (s : Direction) : Prop :=
  u.length = base.length ∧
    match s with
    | .left => AgreeFrom base u (i - d)
    | .right => AgreeUpto base u (i + d)

/-- For every `d`, one base word carries a target whose output flips under a far
perturbation on either side. Co-location keeps both flips on a single base (one
automaton context); each side alone flips the target, so this is weaker than needing
both at once (`RequiresBothSides`). -/
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

section FlankWitness

variable {x fill y a : α} {n k : ℕ} {p : α → Bool}

/-! ### The flank-witness template

The recurring witness family for two-sided unboundedness: a target buried in a filler
run, with independently editable flanks. `RequiresBothSides.of_flanks` packages the
whole assembly — a map is excluded by exhibiting only three images, those of the base
and of the two single-flank perturbations, at the target coordinate. -/

/-- The word `x`, then `n` copies of `fill`, then `y` — a target buried in a filler
run, with independently editable flanks. -/
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
  rw [flankWord, List.take_succ_cons, List.take_append_of_le_length (by simp; omega),
    List.take_replicate]
  simp [List.mem_replicate, eq_comm, hfill]

/-- A window past the left flank contains `a` iff the right flank is `a`. -/
theorem mem_drop_flankWord_iff (hfill : fill ≠ a) (h0 : 0 < k) (hk : k ≤ n + 1) :
    a ∈ (flankWord x fill y n).drop k ↔ y = a := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [flankWord, List.drop_succ_cons, List.drop_append_of_le_length (by simp; omega),
    List.drop_replicate]
  simp [List.mem_replicate, eq_comm, hfill]

/-- A flag over a window reaching at most the filler run reads the left flank — the
`ofFlags` counterpart of `exists_le_flankWord_eq_some_iff`. -/
theorem any_take_flankWord (hfill : p fill = false) (h0 : 0 < k) (hk : k ≤ n + 1) :
    ((flankWord x fill y n).take k).any p = p x := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [flankWord, List.take_succ_cons, List.take_append_of_le_length (by simp; omega),
    List.take_replicate]
  simp [hfill]

/-- A flag over a window past the left flank reads the right flank. -/
theorem any_drop_flankWord (hfill : p fill = false) (h0 : 0 < k) (hk : k ≤ n + 1) :
    ((flankWord x fill y n).drop k).any p = p y := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [flankWord, List.drop_succ_cons, List.drop_append_of_le_length (by simp; omega),
    List.drop_replicate]
  simp [hfill]

/-- Flank words differing only on the left agree off position `0`. -/
theorem flankWord_congr_left {x' : α} (h : k ≠ 0) :
    (flankWord x fill y n)[k]? = (flankWord x' fill y n)[k]? := by
  simp only [getElem?_flankWord, if_neg h]

/-- Flank words differing only on the right agree off the last position. -/
theorem flankWord_congr_right {y' : α} (h : k ≠ n + 1) :
    (flankWord x fill y n)[k]? = (flankWord x fill y' n)[k]? := by
  simp only [getElem?_flankWord, if_neg h]

/-- `f` requires both sides when some target changes under `f` yet perturbing either
far side reverts it to the identity. Unlike `TwoSidedUnboundedDependence`, a two-sided
union never satisfies this — removing one trigger leaves the other, so the output stays
changed. -/
def RequiresBothSides (f : List α → List α) : Prop :=
  ∀ d, ∃ (base : List α) (i : ℕ), i < base.length ∧ (f base)[i]? ≠ base[i]? ∧
    ∀ s, ∃ u, IsFarPerturbation base u i d s ∧ u[i]? = base[i]? ∧ (f u)[i]? = u[i]?

/-- A `d`-indexed family of flank words whose target sits `d`-far from both flanks,
changed to `on` in the base and reverted by flipping either flank alone, requires both
sides — the three-map template of [yolyan-2025] §5.3. -/
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
      ⟨by simp, fun k hk => flankWord_congr_left (by omega)⟩, by rw [hmid, hmid],
      by rw [hrevL, hmid]⟩
  | .right =>
    exact ⟨flankWord xOn fill yOff (n d),
      ⟨by simp, fun k hk => flankWord_congr_right (by omega)⟩, by rw [hmid, hmid],
      by rw [hrevR, hmid]⟩

/-- Requiring both sides strengthens two-sided unbounded dependence: a reverted target is
in particular a flipped one. The converse fails (a two-sided union has the dependence but
reverts under neither side alone). -/
theorem RequiresBothSides.twoSidedUnboundedDependence {f : List α → List α}
    (hf : RequiresBothSides f) : TwoSidedUnboundedDependence f := fun d =>
  have ⟨base, i, hi, hchange, hw⟩ := hf d
  ⟨base, i, hi, fun s =>
    have ⟨u, hp, hsym, hrev⟩ := hw s
    ⟨u, hp, fun h => hchange (h.trans (hrev.trans hsym))⟩⟩

end FlankWitness

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
