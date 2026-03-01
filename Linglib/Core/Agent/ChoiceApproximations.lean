import Linglib.Core.Agent.RationalAction

/-!
# Algebraic Approximations (Luce 1959, §1.G, pp. 34–37) @cite{luce-1959}

Luce (1959, §1.G) develops the connection between choice probabilities and
ordinal preference structures via **just noticeable differences** (jnds).

When stimuli are "close" in value, subjects cannot reliably discriminate
between them — the choice probability `P(x, {x,y})` is near `1/2`. A jnd
threshold `π ∈ (1/2, 1)` defines two relations on the alternative set:

- **L(π)**: `x` is discriminably preferred to `y` (Definition 3)
- **I(π)**: `x` and `y` are indistinguishable (Definition 3)

## Key results

1. **Semiorder** (Theorem 5): Under Axiom 1 with imperfect discrimination,
   `(L(π), I(π))` satisfies the semiorder axioms — trichotomy, I-reflexivity,
   L-transitivity, and the interval condition `xLy ∧ yIz ∧ zLw → xLw`.

2. **Trace** (Definition 4): `x ≥_T y` iff `P(x, z) ≥ P(y, z)` for all `z`.
   The trace extracts the "underlying" preference by requiring dominance in
   all pairwise comparisons against any third alternative.

3. **Weak order** (Theorem 6): Under Axiom 1, the trace is a weak order
   (total preorder), and `x ≥_T y` iff `v(x) ≥ v(y)` iff `P(x, y) ≥ 1/2`.

## Connection to the choice axiom

The semiorder captures the *observable* preference structure (what a subject
can discriminate), while the trace recovers the *latent* ratio scale ordering.
Theorem 6 shows that Axiom 1 forces these to align: the trace is exactly the
ordering induced by the scale values `v`.
-/

namespace Core

open Real BigOperators Finset

variable {A : Type*} [DecidableEq A]

-- ============================================================================
-- §1. Pairwise Choice Probabilities
-- ============================================================================

/-- The pairwise choice probability `P(x, {x,y})` under a ratio scale `v`:
    `P(x, y) = v(x) / (v(x) + v(y))`.

    This is the Luce model prediction for binary forced choice.
    The function is symmetric in the sense that `P(x,y) + P(y,x) = 1`. -/
noncomputable def pairwiseProb (v : A → ℝ) (x y : A) : ℝ :=
  v x / (v x + v y)

/-- Pairwise probabilities are non-negative for positive scales. -/
theorem pairwiseProb_nonneg (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (x y : A) :
    0 ≤ pairwiseProb v x y :=
  div_nonneg (le_of_lt (hv x)) (le_of_lt (add_pos (hv x) (hv y)))

/-- Pairwise probabilities are at most 1 for positive scales. -/
theorem pairwiseProb_le_one (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (x y : A) :
    pairwiseProb v x y ≤ 1 := by
  simp only [pairwiseProb]
  rw [div_le_one (add_pos (hv x) (hv y))]
  linarith [hv y]

/-- Complementarity: `P(x, y) + P(y, x) = 1` for positive scales. -/
theorem pairwiseProb_complement (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (x y : A) :
    pairwiseProb v x y + pairwiseProb v y x = 1 := by
  simp only [pairwiseProb]
  have hne : v x + v y ≠ 0 := ne_of_gt (add_pos (hv x) (hv y))
  rw [show v y + v x = v x + v y from by ring, ← add_div, div_self hne]

/-- `P(x, x) = 1/2` for positive scales (indifference with self). -/
theorem pairwiseProb_self (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (x : A) :
    pairwiseProb v x x = 1 / 2 := by
  simp only [pairwiseProb]
  have hne : v x ≠ 0 := ne_of_gt (hv x)
  field_simp
  ring

/-- `P(x, y) > 1/2` iff `v(x) > v(y)`: the higher-scale alternative is
    chosen more than half the time. -/
theorem pairwiseProb_gt_half_iff (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (x y : A) :
    1 / 2 < pairwiseProb v x y ↔ v y < v x := by
  simp only [pairwiseProb]
  rw [lt_div_iff₀ (add_pos (hv x) (hv y))]
  constructor <;> intro h <;> nlinarith

/-- `P(x, y) ≥ 1/2` iff `v(x) ≥ v(y)`. -/
theorem pairwiseProb_ge_half_iff (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (x y : A) :
    1 / 2 ≤ pairwiseProb v x y ↔ v y ≤ v x := by
  simp only [pairwiseProb]
  rw [le_div_iff₀ (add_pos (hv x) (hv y))]
  constructor <;> intro h <;> nlinarith

/-- Monotonicity: `P(x, z) ≥ P(y, z)` iff `v(x) ≥ v(y)`.

    The function `t ↦ t/(t+c)` is monotone increasing for `c > 0`,
    so the ordering of pairwise probabilities against any fixed `z`
    mirrors the ordering of scale values. -/
theorem pairwiseProb_mono_iff (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (x y z : A) :
    pairwiseProb v y z ≤ pairwiseProb v x z ↔ v y ≤ v x := by
  simp only [pairwiseProb]
  rw [div_le_div_iff₀ (add_pos (hv y) (hv z)) (add_pos (hv x) (hv z))]
  constructor <;> intro h <;> nlinarith [hv z]

-- ============================================================================
-- §2. Just Noticeable Differences (Definition 3, p. 34)
-- ============================================================================

/-- The `L(π)` relation (Definition 3, Luce 1959, p. 34):
    `x L(π) y` iff `P(x, {x,y}) > π`.

    This means `x` is **discriminably preferred** to `y` at threshold `π`:
    the observer can reliably tell that `x` is "better" than `y`. The
    threshold `π` must satisfy `1/2 < π < 1`; it represents the minimum
    probability that constitutes a "noticeable difference." -/
def jndL (v : A → ℝ) (thr : ℝ) (x y : A) : Prop :=
  thr < pairwiseProb v x y

/-- The `I(π)` relation (Definition 3, Luce 1959, p. 34):
    `x I(π) y` iff `1 - π ≤ P(x, {x,y}) ≤ π`.

    This means `x` and `y` are **indistinguishable** at threshold `π`:
    neither is reliably discriminated from the other. By complementarity,
    `x I(π) y` iff `1 - π ≤ P(x,y) ≤ π` iff `1 - π ≤ P(y,x) ≤ π`,
    so `I` is symmetric. -/
def jndI (v : A → ℝ) (thr : ℝ) (x y : A) : Prop :=
  1 - thr ≤ pairwiseProb v x y ∧ pairwiseProb v x y ≤ thr

-- ============================================================================
-- §3. Semiorder Properties (Theorem 5, p. 35)
-- ============================================================================

/-!
## Semiorder axioms

Luce (1959, p. 35) defines a **semiordering** of a set `U` as a pair
`(L, I)` of relations satisfying, for all `x, y, z, w ∈ U`:

(i)   **Trichotomy**: exactly one of `xLy`, `yLx`, or `xIy` holds
(ii)  **I-reflexivity**: `xIx`
(iii) **Interval condition**: `xLy ∧ yIz ∧ zLw → xLw`
(iv)  **No sandwiching**: `xLy ∧ yLz → ¬(xIw ∧ wIz)`

Theorem 5 proves these hold for `(L(π), I(π))` under Axiom 1.
-/

/-- I(π) is symmetric: if `x` and `y` are indistinguishable, so are `y` and `x`.

    Since `P(y,x) = 1 - P(x,y)`, the condition `1-π ≤ P(x,y) ≤ π`
    is equivalent to `1-π ≤ P(y,x) ≤ π`. -/
theorem jndI_symm (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ) (x y : A)
    (h : jndI v thr x y) : jndI v thr y x := by
  simp only [jndI] at *
  have hc := pairwiseProb_complement v hv x y
  constructor <;> linarith [h.1, h.2]

/-- **I-reflexivity**: `x I(π) x`, since `P(x, x) = 1/2` and `1-π < 1/2 < π`
    whenever `1/2 < π < 1`. -/
theorem jndI_refl (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ)
    (hthr_lower : 1 / 2 < thr) (_hthr_upper : thr < 1) (x : A) :
    jndI v thr x x := by
  simp only [jndI, pairwiseProb_self v hv]
  constructor <;> linarith

omit [DecidableEq A] in
/-- **Trichotomy**: for any `x, y`, exactly one of `xLy`, `yLx`, or `xIy` holds.

    Since `P(x,y) + P(y,x) = 1`, the three conditions `P(x,y) > π`,
    `P(y,x) > π` (i.e., `P(x,y) < 1-π`), and `1-π ≤ P(x,y) ≤ π`
    partition the interval `[0, 1]`. -/
theorem jnd_trichotomy (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ)
    (_hthr_lower : 1 / 2 < thr) (_hthr_upper : thr < 1) (x y : A) :
    (jndL v thr x y ∧ ¬jndL v thr y x ∧ ¬jndI v thr x y) ∨
    (jndL v thr y x ∧ ¬jndL v thr x y ∧ ¬jndI v thr x y) ∨
    (jndI v thr x y ∧ ¬jndL v thr x y ∧ ¬jndL v thr y x) := by
  sorry -- TODO: case split on P(x,y) vs thr: P > thr gives xLy; P(y,x) > thr gives yLx;
         -- otherwise 1-thr ≤ P ≤ thr gives xIy. Follows from P(x,y) + P(y,x) = 1.

omit [DecidableEq A] in
/-- **L-transitivity**: `xLy ∧ yLz → xLz`.

    Under Axiom 1, `P(x,y) > π` means `v(x)/(v(x)+v(y)) > π`, i.e.,
    `v(x)/v(y) > π/(1-π)`. If also `v(y)/v(z) > π/(1-π)`, then
    `v(x)/v(z) > (π/(1-π))² > π/(1-π)` (since `π/(1-π) > 1`),
    so `P(x,z) > π`. -/
theorem jndL_trans (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ)
    (hthr_lower : 1 / 2 < thr) (_hthr_upper : thr < 1) (x y z : A)
    (hxy : jndL v thr x y) (hyz : jndL v thr y z) :
    jndL v thr x z := by
  simp only [jndL, pairwiseProb] at *
  have hvx := hv x; have hvy := hv y; have hvz := hv z
  rw [lt_div_iff₀ (add_pos hvx hvy)] at hxy
  rw [lt_div_iff₀ (add_pos hvy hvz)] at hyz
  rw [lt_div_iff₀ (add_pos hvx hvz)]
  have h1 : thr * v y < (1 - thr) * v x := by nlinarith
  have h2 : thr * v z < (1 - thr) * v y := by nlinarith
  nlinarith [mul_pos (by linarith : (0:ℝ) < 1 - thr) hvy]

/-- **Interval condition**: `xLy ∧ yIz ∧ zLw → xLw`.

    Under Axiom 1: `xLy` gives `v(x)/v(y) > π/(1-π)`, `yIz` gives
    `v(y)/v(z) ≥ (1-π)/π` (from `P(y,z) ≥ 1-π`), and `zLw` gives
    `v(z)/v(w) > π/(1-π)`. Multiplying the first and third ratios and
    using the bound on `v(y)/v(z)`:
    `v(x)/v(w) = (v(x)/v(y)) · (v(y)/v(z)) · (v(z)/v(w)) > π/(1-π)`
    since the middle factor is ≥ (1-π)/π and the outer factors are > π/(1-π),
    giving a product > (π/(1-π))·((1-π)/π)·(π/(1-π)) = π/(1-π). -/
theorem jndL_interval (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ)
    (hthr_lower : 1 / 2 < thr) (hthr_upper : thr < 1) (x y z w : A)
    (hxy : jndL v thr x y) (hyz : jndI v thr y z) (hzw : jndL v thr z w) :
    jndL v thr x w := by
  sorry -- TODO: Follows from the ratio bounds described above.
         -- The key step is showing v(x)/v(w) > π/(1-π) by multiplying
         -- the ratios v(x)/v(y), v(y)/v(z), v(z)/v(w) and bounding
         -- each factor. Requires careful nonlinear arithmetic with
         -- the positivity constraints.

/-- **No sandwiching**: `xLy ∧ yLz → ¬(xIw ∧ wIz)`.

    If `v(x) ≫ v(y) ≫ v(z)` (both with ratio > π/(1-π)), then no
    `w` can be indistinguishable from both `x` and `z`: such a `w`
    would need `v(w) ≈ v(x)` and `v(w) ≈ v(z)` simultaneously, but
    `v(x)/v(z) > (π/(1-π))² ≫ 1` prevents this. -/
theorem jndL_no_sandwich (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ)
    (hthr_lower : 1 / 2 < thr) (hthr_upper : thr < 1) (x y z w : A)
    (hxy : jndL v thr x y) (hyz : jndL v thr y z) :
    ¬(jndI v thr x w ∧ jndI v thr w z) := by
  sorry -- TODO: From xLy ∧ yLz, get v(x)/v(z) > (π/(1-π))². If xIw,
         -- then v(x)/v(w) ≤ π/(1-π). If wIz, then v(w)/v(z) ≤ π/(1-π).
         -- But v(x)/v(z) = (v(x)/v(w))·(v(w)/v(z)) ≤ (π/(1-π))²,
         -- contradicting the strict bound from transitivity through y.

-- ============================================================================
-- §4. The Trace (Definition 4 and Theorem 6, p. 37)
-- ============================================================================

/-- The trace relation (Definition 4, Luce 1959, p. 37):
    `x ≥_T y` iff `P(x, z) ≥ P(y, z)` for all `z`.

    The trace extracts the "underlying" preference ordering by requiring
    that `x` is at least as preferred as `y` in **every** pairwise
    comparison against a common reference `z`. This is a stronger condition
    than just `P(x, y) ≥ 1/2`. -/
def traceGe (v : A → ℝ) (x y : A) : Prop :=
  ∀ z : A, pairwiseProb v y z ≤ pairwiseProb v x z

/-- **Theorem 6** (Luce 1959, p. 37): Under Axiom 1, the trace relation
    is equivalent to `v(x) ≥ v(y)`.

    **Proof sketch**: Under Axiom 1, `P(x,z) = v(x)/(v(x)+v(z))`. Since
    `t ↦ t/(t+c)` is monotone increasing for `c > 0`, we have
    `P(x,z) ≥ P(y,z)` for all `z` iff `v(x) ≥ v(y)`.

    (→) Take `z = y`: `P(x,y) ≥ P(y,y) = 1/2`, hence `v(x) ≥ v(y)`.
    (←) If `v(x) ≥ v(y)`, monotonicity of `t/(t+c)` gives `P(x,z) ≥ P(y,z)`. -/
theorem trace_iff_scale_ge (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (x y : A) :
    traceGe v x y ↔ v y ≤ v x := by
  simp only [traceGe]
  constructor
  · intro h
    -- Take z = y: P(y,y) ≤ P(x,y), i.e. 1/2 ≤ P(x,y)
    have := h y
    rwa [pairwiseProb_mono_iff v hv x y y] at this
  · intro hle z
    rwa [pairwiseProb_mono_iff v hv x y z]

/-- Corollary: `x ≥_T y` iff `P(x, y) ≥ 1/2` (Luce 1959, p. 37). -/
theorem trace_iff_pairwiseProb_ge_half (v : A → ℝ) (hv : ∀ a : A, 0 < v a)
    (x y : A) :
    traceGe v x y ↔ 1 / 2 ≤ pairwiseProb v x y := by
  rw [trace_iff_scale_ge v hv, pairwiseProb_ge_half_iff v hv]

omit [DecidableEq A] in
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

    This completes the proof that the trace is a **weak order** (total
    preorder). Under Axiom 1, the trace is determined by the ratio scale
    values, which are totally ordered reals. -/
theorem traceGe_total (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (x y : A) :
    traceGe v x y ∨ traceGe v y x := by
  rw [trace_iff_scale_ge v hv, trace_iff_scale_ge v hv]
  exact le_total (v y) (v x)

/-- The trace agrees with L: if `xLy` for any `π`, then `x ≥_T y`.

    `P(x,y) > π > 1/2` implies `v(x) > v(y)` implies `x ≥_T y`. -/
theorem traceGe_of_jndL (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ)
    (hthr : 1 / 2 < thr) (x y : A) (h : jndL v thr x y) :
    traceGe v x y := by
  rw [trace_iff_scale_ge v hv]
  rw [jndL, pairwiseProb] at h
  have hD := add_pos (hv x) (hv y)
  have := (lt_div_iff₀ hD).mp h
  nlinarith

end Core
