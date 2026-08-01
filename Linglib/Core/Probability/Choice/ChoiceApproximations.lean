import Linglib.Core.Probability.Choice.RationalAction

/-!
# Just noticeable differences and the trace

This file formalizes the algebraic approximations of [luce-1959] (§1.G,
pp. 34–37). A jnd threshold `π ∈ (1/2, 1)` splits pairwise choice into a
discriminable-preference relation `L(π)` and an indistinguishability relation
`I(π)` (Definition 3). We show that the pair satisfies Luce's semiorder
axioms (Theorem 5) and that the trace ordering (Definition 4) is a weak order
coinciding with the ratio-scale order (Theorem 6).

## Main definitions

* `jndL`, `jndI`: the relations `L(π)` and `I(π)`.
* `traceGe`: the trace ordering `x ≥_T y`.

## References

* [R. D. Luce, *Individual Choice Behavior*][luce-1959]
-/

namespace Core

open Real BigOperators Finset

variable {A : Type*}

-- The pairwise kernel `pairwiseProb` and its lemma suite live in
-- `Core.Probability.Choice.RationalAction` (imported above).

/-! ### Just noticeable differences (Definition 3, p. 34) -/

/-- The `L(π)` relation (Definition 3, [luce-1959], p. 34):
    `x L(π) y` iff `P(x, {x,y}) > π`.

    This means `x` is **discriminably preferred** to `y` at threshold `π`:
    the observer can reliably tell that `x` is "better" than `y`. The
    threshold `π` must satisfy `1/2 < π < 1`; it represents the minimum
    probability that constitutes a "noticeable difference." -/
def jndL (v : A → ℝ) (thr : ℝ) (x y : A) : Prop :=
  thr < pairwiseProb v x y

/-- The `I(π)` relation (Definition 3, [luce-1959], p. 34):
    `x I(π) y` iff `1 - π ≤ P(x, {x,y}) ≤ π`.

    This means `x` and `y` are **indistinguishable** at threshold `π`:
    neither is reliably discriminated from the other. By complementarity,
    `x I(π) y` iff `1 - π ≤ P(x,y) ≤ π` iff `1 - π ≤ P(y,x) ≤ π`,
    so `I` is symmetric. -/
def jndI (v : A → ℝ) (thr : ℝ) (x y : A) : Prop :=
  1 - thr ≤ pairwiseProb v x y ∧ pairwiseProb v x y ≤ thr

/-!
### Semiorder axioms (Theorem 5, p. 35)

[luce-1959] defines a **semiordering** of a set `U` as a pair
`(L, I)` of relations satisfying, for all `x, y, z, w ∈ U`:

(i) **Trichotomy**: exactly one of `xLy`, `yLx`, or `xIy` holds
(ii) **I-reflexivity**: `xIx`
(iii) **Interval condition**: `xLy ∧ yIz ∧ zLw → xLw`
(iv) **No sandwiching**: `xLy ∧ yLz → ¬(xIw ∧ wIz)`

Theorem 5 proves these hold for `(L(π), I(π))` under Axiom 1.
-/

/-- I(π) is symmetric: if `x` and `y` are indistinguishable, so are `y` and
    `x`. -/
theorem jndI_symm (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ) (x y : A)
    (h : jndI v thr x y) : jndI v thr y x := by
  simp only [jndI] at *
  have hc := pairwiseProb_complement (hv x) (hv y)
  constructor <;> linarith [h.1, h.2]

/-- **I-reflexivity**: `x I(π) x`. -/
theorem jndI_refl (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ)
    (hthr_lower : 1 / 2 < thr) (_hthr_upper : thr < 1) (x : A) :
    jndI v thr x x := by
  simp only [jndI, pairwiseProb_self (hv x)]
  constructor <;> linarith

/-- **Trichotomy**: for any `x, y`, exactly one of `xLy`, `yLx`, or `xIy`
    holds. -/
theorem jnd_trichotomy (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ)
    (hthr_lower : 1 / 2 < thr) (_hthr_upper : thr < 1) (x y : A) :
    (jndL v thr x y ∧ ¬jndL v thr y x ∧ ¬jndI v thr x y) ∨
    (jndL v thr y x ∧ ¬jndL v thr x y ∧ ¬jndI v thr x y) ∨
    (jndI v thr x y ∧ ¬jndL v thr x y ∧ ¬jndL v thr y x) := by
  have hc := pairwiseProb_complement (hv x) (hv y)
  unfold jndL jndI
  by_cases h₁ : thr < pairwiseProb v x y
  · left; exact ⟨h₁, fun h => by linarith, fun ⟨_, h⟩ => by linarith⟩
  · push Not at h₁
    by_cases h₂ : thr < pairwiseProb v y x
    · right; left; exact ⟨h₂, fun h => by linarith, fun ⟨h, _⟩ => by linarith⟩
    · push Not at h₂
      right; right; exact ⟨⟨by linarith, h₁⟩, fun h => by linarith, fun h => by linarith⟩

/-- **Interval condition**: `xLy ∧ yIz ∧ zLw → xLw`. -/
theorem jndL_interval (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ)
    (_hthr_lower : 1 / 2 < thr) (_hthr_upper : thr < 1) (x y z w : A)
    (hxy : jndL v thr x y) (hyz : jndI v thr y z) (hzw : jndL v thr z w) :
    jndL v thr x w := by
  simp only [jndL, jndI, pairwiseProb] at *
  have hvx := hv x; have hvy := hv y; have hvz := hv z; have hvw := hv w
  rw [lt_div_iff₀ (add_pos hvx hvy)] at hxy
  obtain ⟨hyz_lo, _⟩ := hyz
  rw [le_div_iff₀ (add_pos hvy hvz)] at hyz_lo
  rw [lt_div_iff₀ (add_pos hvz hvw)] at hzw
  rw [lt_div_iff₀ (add_pos hvx hvw)]
  -- hxy: thr * v(y) < (1-thr) * v(x)
  -- hyz_lo: (1-thr) * v(z) ≤ thr * v(y)
  -- hzw: thr * v(w) < (1-thr) * v(z)
  -- Chain: thr * v(w) < (1-thr) * v(z) ≤ thr * v(y) < (1-thr) * v(x)
  linarith

/-- **No sandwiching**: `xLy ∧ yLz → ¬(xIw ∧ wIz)` — no `w` can be
    indistinguishable from both endpoints of a discriminable chain. -/
theorem jndL_no_sandwich (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ)
    (hthr_lower : 1 / 2 < thr) (hthr_upper : thr < 1) (x y z w : A)
    (hxy : jndL v thr x y) (hyz : jndL v thr y z) :
    ¬(jndI v thr x w ∧ jndI v thr w z) := by
  intro ⟨hxw, hwz⟩
  simp only [jndL, jndI, pairwiseProb] at *
  have hvx := hv x; have hvy := hv y; have hvz := hv z; have hvw := hv w
  -- From xLy: thr*(v y) < (1-thr)*(v x)
  rw [lt_div_iff₀ (add_pos hvx hvy)] at hxy
  -- From yLz: thr*(v z) < (1-thr)*(v y)
  rw [lt_div_iff₀ (add_pos hvy hvz)] at hyz
  -- From xIw: (1-thr)*(v(x)+v(w)) ≤ v(x) and v(x) ≤ thr*(v(x)+v(w))
  obtain ⟨hxw_lo, hxw_hi⟩ := hxw
  rw [le_div_iff₀ (add_pos hvx hvw)] at hxw_lo
  rw [div_le_iff₀ (add_pos hvx hvw)] at hxw_hi
  -- From wIz: (1-thr)*(v(w)+v(z)) ≤ v(w) and v(w) ≤ thr*(v(w)+v(z))
  obtain ⟨hwz_lo, hwz_hi⟩ := hwz
  rw [le_div_iff₀ (add_pos hvw hvz)] at hwz_lo
  rw [div_le_iff₀ (add_pos hvw hvz)] at hwz_hi
  -- xIw gives: (1-thr)*v(x) ≤ thr*v(w) (from hxw_hi expanded)
  -- wIz gives: (1-thr)*v(w) ≤ thr*v(z) (from hwz_hi expanded)
  -- xLy gives: thr*v(y) < (1-thr)*v(x) (from hxy expanded)
  -- yLz gives: thr*v(z) < (1-thr)*v(y) (from hyz expanded)
  -- Chain via nlinarith: multiply inequalities to get contradiction
  nlinarith [mul_le_mul_of_nonneg_right hxw_hi (le_of_lt hvw),
             mul_le_mul_of_nonneg_right hwz_hi (le_of_lt hvx),
             mul_lt_mul_of_pos_right hxy (hv z),
             mul_lt_mul_of_pos_right hyz (hv x)]

/-- **L-transitivity**: `xLy ∧ yLz → xLz`. Not one of the semiorder axioms —
    it follows from the interval condition instantiated at `z := y`, via
    I-reflexivity. -/
theorem jndL_trans (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ)
    (hthr_lower : 1 / 2 < thr) (hthr_upper : thr < 1) (x y z : A)
    (hxy : jndL v thr x y) (hyz : jndL v thr y z) :
    jndL v thr x z :=
  jndL_interval v hv thr hthr_lower hthr_upper x y y z hxy
    (jndI_refl v hv thr hthr_lower hthr_upper y) hyz

/-! ### The trace (Definition 4 and Theorem 6, p. 37) -/

/-- The trace relation (Definition 4, [luce-1959], p. 37):
    `x ≥_T y` iff `P(x, z) ≥ P(y, z)` for all `z`.

    The trace extracts the "underlying" preference ordering by requiring
    that `x` is at least as preferred as `y` in **every** pairwise
    comparison against a common reference `z`. This is a stronger condition
    than just `P(x, y) ≥ 1/2`. -/
def traceGe (v : A → ℝ) (x y : A) : Prop :=
  ∀ z : A, pairwiseProb v y z ≤ pairwiseProb v x z

/-- **Theorem 6**: the trace relation is equivalent to the scale ordering
    `v(y) ≤ v(x)`. -/
theorem trace_iff_scale_ge (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (x y : A) :
    traceGe v x y ↔ v y ≤ v x := by
  simp only [traceGe]
  constructor
  · intro h
    -- Take z = y: P(y,y) ≤ P(x,y), i.e. 1/2 ≤ P(x,y)
    have := h y
    rwa [pairwiseProb_mono_iff (hv x) (hv y) (hv y)] at this
  · intro hle z
    rwa [pairwiseProb_mono_iff (hv x) (hv y) (hv z)]

/-- Corollary: `x ≥_T y` iff `P(x, y) ≥ 1/2`. -/
theorem trace_iff_pairwiseProb_ge_half (v : A → ℝ) (hv : ∀ a : A, 0 < v a)
    (x y : A) :
    traceGe v x y ↔ 1 / 2 ≤ pairwiseProb v x y := by
  rw [trace_iff_scale_ge v hv, pairwiseProb_ge_half_iff (hv x) (hv y)]

/-- The trace is reflexive: `x ≥_T x`. -/
theorem traceGe_refl (v : A → ℝ) (x : A) : traceGe v x x :=
  λ _ => le_refl _

/-- The trace is transitive: `x ≥_T y ∧ y ≥_T z → x ≥_T z`. -/
theorem traceGe_trans (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (x y z : A)
    (hxy : traceGe v x y) (hyz : traceGe v y z) :
    traceGe v x z := by
  rw [trace_iff_scale_ge v hv] at *
  linarith

/-- The trace is total: for any `x, y`, either `x ≥_T y` or `y ≥_T x`.
    With `traceGe_refl` and `traceGe_trans`, the trace is a **weak order**
    (total preorder). -/
theorem traceGe_total (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (x y : A) :
    traceGe v x y ∨ traceGe v y x := by
  rw [trace_iff_scale_ge v hv, trace_iff_scale_ge v hv]
  exact le_total (v y) (v x)

/-- The trace agrees with L: if `xLy` for any `π`, then `x ≥_T y`. -/
theorem traceGe_of_jndL (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ)
    (hthr : 1 / 2 < thr) (x y : A) (h : jndL v thr x y) :
    traceGe v x y := by
  rw [trace_iff_scale_ge v hv]
  rw [jndL, pairwiseProb] at h
  have hD := add_pos (hv x) (hv y)
  have := (lt_div_iff₀ hD).mp h
  nlinarith

end Core
