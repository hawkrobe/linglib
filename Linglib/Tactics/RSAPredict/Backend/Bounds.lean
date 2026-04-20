import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

/-!
# Bounds — Rational Interval Arithmetic for the `rsa_predict` Backend

Closed intervals `[lo, hi]` over ℚ, with proofs that arithmetic and transcendental
operations preserve ℝ containment. This is the numeric foundation for the
`rsa_predict` tactic:

1. Reify an ℝ expression into a tree of `QInterval` operations
2. Evaluate the tree to get a concrete `[lo, hi]` (computable ℚ)
3. Check separation `b.hi < a.lo` (decidable on ℚ)
4. Conclude `a > b` on ℝ via `gt_of_separated`

## Layered structure

The file is organized in dependency order:

* **QInterval** — the core type and exact arithmetic (`add`, `sub`, `mul`, `divPos`,
  `invPos`, `powNat`, `rpowNat`), separation predicate, and rational coarsening
  (`truncDown`/`truncUp`/`coarsen`) that bounds bit growth across long products.
* **PadeExp** — `[4/4]` Padé approximant for `Real.exp` on `[-1, 1]` with argument
  reduction by repeated squaring, giving `expPoint`/`expInterval` with relative
  error `< 1/4000000`.
* **LogInterval** — `Real.log` for positive rationals via 50-step bisection against
  `expPoint`, with bracket bits proportional to `log q`. Includes a `log 0` fall-through.
* **SqrtInterval** — `√x = exp(log x / 2)` for positive intervals, used by
  Hellinger-distance RSA models (@cite{herbstritt-franke-2019}).
* **rpow specials** — `rpowNat` thin re-export with `rpowZero`/`rpowOne_containsReal`
  closures for the dominant RSA case (`α : ℕ`).

All transcendental routines deliberately stop at `containsReal` rather than
proving exact bounds: the `rsa_predict` tactic only needs `lo ≤ ⟦e⟧ ≤ hi`.
-/

namespace Interval

/-- A closed rational interval [lo, hi]. -/
structure QInterval where
  lo : ℚ
  hi : ℚ
  valid : lo ≤ hi
  deriving Repr

namespace QInterval

-- ============================================================================
-- Containment
-- ============================================================================

/-- The interval contains a real number x: lo ≤ x ≤ hi (via ℚ → ℝ cast). -/
def containsReal (I : QInterval) (x : ℝ) : Prop :=
  (↑I.lo : ℝ) ≤ x ∧ x ≤ (↑I.hi : ℝ)

-- ============================================================================
-- Point Interval
-- ============================================================================

/-- Zero-width interval [q, q]. -/
def exact (q : ℚ) : QInterval where
  lo := q
  hi := q
  valid := le_refl q

theorem exact_containsReal (q : ℚ) : (exact q).containsReal (↑q : ℝ) :=
  ⟨le_refl _, le_refl _⟩

/-- Containment for `(0 : ℝ)`. Uses the literal `0` so the proof type mentions
    `@OfNat.ofNat ℝ 0 _` (= `@Zero.zero ℝ _`), matching expressions directly. -/
theorem exact_zero_containsReal :
    (exact (0 : ℚ)).containsReal (0 : ℝ) := by
  simp only [containsReal, exact]
  constructor <;> exact_mod_cast le_refl (0 : ℚ)

/-- Containment for `(1 : ℝ)`. Uses the literal `1` so the proof type mentions
    `@OfNat.ofNat ℝ 1 _` (= `@One.one ℝ _`), avoiding the `Nat.cast 1 = 0 + 1`
    mismatch that breaks nested proof terms. -/
theorem exact_one_containsReal :
    (exact (1 : ℚ)).containsReal (1 : ℝ) := by
  simp only [containsReal, exact]
  constructor <;> exact_mod_cast le_refl (1 : ℚ)

/-- Containment for natural number literals ≥ 2 cast via `Nat.cast`.
    For n ≥ 2, `@OfNat.ofNat ℝ n _` is definitionally equal to `@Nat.cast ℝ _ n`
    (via Mathlib's `instOfNat`). For n = 0, 1, use `exact_zero_containsReal` /
    `exact_one_containsReal` instead (since `Nat.cast 1 ≢ OfNat.ofNat 1`). -/
theorem exact_natCast_containsReal (n : ℕ) :
    (exact (↑n : ℚ)).containsReal (↑n : ℝ) := by
  simp only [containsReal, exact]
  constructor <;> exact_mod_cast le_refl (↑n : ℚ)

-- ============================================================================
-- Addition
-- ============================================================================

/-- Interval addition: [a.lo + b.lo, a.hi + b.hi]. -/
def add (a b : QInterval) : QInterval where
  lo := a.lo + b.lo
  hi := a.hi + b.hi
  valid := add_le_add a.valid b.valid

theorem add_containsReal {a b : QInterval} {x y : ℝ}
    (hx : a.containsReal x) (hy : b.containsReal y) :
    (a.add b).containsReal (x + y) := by
  simp only [add, containsReal]
  push_cast
  exact ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

-- ============================================================================
-- Negation
-- ============================================================================

/-- Interval negation: [-hi, -lo]. -/
def neg (a : QInterval) : QInterval where
  lo := -a.hi
  hi := -a.lo
  valid := neg_le_neg a.valid

theorem neg_containsReal {a : QInterval} {x : ℝ}
    (hx : a.containsReal x) : (a.neg).containsReal (-x) := by
  simp only [neg, containsReal]
  push_cast
  exact ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩

-- ============================================================================
-- Subtraction
-- ============================================================================

/-- Interval subtraction: a - b = a + (-b). -/
def sub (a b : QInterval) : QInterval := a.add b.neg

theorem sub_containsReal {a b : QInterval} {x y : ℝ}
    (hx : a.containsReal x) (hy : b.containsReal y) :
    (a.sub b).containsReal (x - y) := by
  show (a.add b.neg).containsReal (x + (-y))
  exact add_containsReal hx (neg_containsReal hy)

-- ============================================================================
-- Multiplication (nonneg case)
-- ============================================================================

/-- Multiplication for nonneg intervals: [a.lo*b.lo, a.hi*b.hi]. -/
def mulNonneg (a b : QInterval) (ha : 0 ≤ a.lo) (hb : 0 ≤ b.lo) : QInterval where
  lo := a.lo * b.lo
  hi := a.hi * b.hi
  valid := mul_le_mul a.valid b.valid hb (le_trans ha a.valid)

theorem mulNonneg_containsReal {a b : QInterval} {x y : ℝ}
    (ha : 0 ≤ a.lo) (hb : 0 ≤ b.lo)
    (hx : a.containsReal x) (hy : b.containsReal y) :
    (a.mulNonneg b ha hb).containsReal (x * y) := by
  have hx_nn : (0 : ℝ) ≤ x := le_trans (by exact_mod_cast ha) hx.1
  have hy_nn : (0 : ℝ) ≤ y := le_trans (by exact_mod_cast hb) hy.1
  have hahi_nn : (0 : ℝ) ≤ ↑a.hi := le_trans hx_nn hx.2
  have hblo_nn : (0 : ℝ) ≤ ↑b.lo := by exact_mod_cast hb
  simp only [mulNonneg, containsReal]
  push_cast
  exact ⟨mul_le_mul hx.1 hy.1 hblo_nn hx_nn,
         mul_le_mul hx.2 hy.2 hy_nn hahi_nn⟩

-- ============================================================================
-- Division by positive interval
-- ============================================================================

/-- Division of nonneg by positive: [a.lo/b.hi, a.hi/b.lo].
    Requires 0 ≤ a.lo for monotonicity. -/
def divPos (a b : QInterval) (ha : 0 ≤ a.lo) (hb_pos : 0 < b.lo) : QInterval where
  lo := a.lo / b.hi
  hi := a.hi / b.lo
  valid := by
    have hbhi_pos : 0 < b.hi := lt_of_lt_of_le hb_pos b.valid
    -- a.lo/b.hi ≤ a.hi/b.hi ≤ a.hi/b.lo
    calc a.lo / b.hi ≤ a.hi / b.hi :=
          div_le_div_of_nonneg_right a.valid (le_of_lt hbhi_pos)
      _ ≤ a.hi / b.lo := by
          apply div_le_div_of_nonneg_left (le_trans ha a.valid) hb_pos b.valid

theorem divPos_containsReal {a b : QInterval} {x y : ℝ}
    (ha : 0 ≤ a.lo) (hb_pos : 0 < b.lo)
    (hx : a.containsReal x) (hy : b.containsReal y) :
    (a.divPos b ha hb_pos).containsReal (x / y) := by
  simp only [divPos, containsReal]
  push_cast
  have hx_nn : (0 : ℝ) ≤ x := le_trans (by exact_mod_cast ha) hx.1
  have hy_pos : (0 : ℝ) < y := lt_of_lt_of_le (by exact_mod_cast hb_pos) hy.1
  have hbhi_pos : (0 : ℝ) < ↑b.hi := by exact_mod_cast lt_of_lt_of_le hb_pos b.valid
  have hblo_pos : (0 : ℝ) < ↑b.lo := by exact_mod_cast hb_pos
  have hahi_nn : (0 : ℝ) ≤ ↑a.hi := le_trans hx_nn hx.2
  exact ⟨calc (↑a.lo : ℝ) / ↑b.hi ≤ x / ↑b.hi :=
              div_le_div_of_nonneg_right hx.1 (le_of_lt hbhi_pos)
            _ ≤ x / y :=
              div_le_div_of_nonneg_left hx_nn hy_pos hy.2,
        calc x / y ≤ (↑a.hi : ℝ) / y :=
              div_le_div_of_nonneg_right hx.2 (le_of_lt hy_pos)
            _ ≤ ↑a.hi / ↑b.lo :=
              div_le_div_of_nonneg_left hahi_nn hblo_pos hy.1⟩

-- ============================================================================
-- General multiplication (4-corner method)
-- ============================================================================

/-- General interval multiplication via 4-corner method.
    For intervals [a, b] and [c, d], the product interval is
    [min(ac, ad, bc, bd), max(ac, ad, bc, bd)].
    Handles arbitrary signs (unlike `mulNonneg` which requires both nonneg). -/
def mul (a b : QInterval) : QInterval where
  lo := min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi))
  hi := max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi))
  valid :=
    calc min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi))
        ≤ a.lo * b.lo := min_le_of_left_le (min_le_left _ _)
      _ ≤ max (a.lo * b.lo) (a.lo * b.hi) := le_max_left _ _
      _ ≤ max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi)) :=
          le_max_left _ _

/-- Containment for general interval multiplication.
    For `a.lo ≤ x ≤ a.hi` and `b.lo ≤ y ≤ b.hi`, `x·y` lies between
    `min(corners)` and `max(corners)` since extrema of a bilinear function
    on a rectangle occur at corners. -/
theorem mul_containsReal {a b : QInterval} {x y : ℝ}
    (hx : a.containsReal x) (hy : b.containsReal y) :
    (a.mul b).containsReal (x * y) := by
  simp only [mul, containsReal] at *
  push_cast
  obtain ⟨hxlo, hxhi⟩ := hx
  obtain ⟨hylo, hyhi⟩ := hy
  constructor
  · -- Lower bound: min₄(corners) ≤ x * y
    by_cases hx0 : (0 : ℝ) ≤ x <;> by_cases hy0 : (0 : ℝ) ≤ y
    · -- x ≥ 0, y ≥ 0
      by_cases halo : (0 : ℝ) ≤ ↑a.lo
      · -- a.lo*b.lo ≤ a.lo*y ≤ x*y
        exact le_trans (min_le_of_left_le (min_le_left _ _))
          (le_trans (mul_le_mul_of_nonneg_left hylo halo)
                    (mul_le_mul_of_nonneg_right hxlo hy0))
      · -- a.lo*b.hi ≤ 0 ≤ x*y
        push_neg at halo
        exact le_trans (min_le_of_left_le (min_le_right _ _))
          (le_trans (mul_nonpos_of_nonpos_of_nonneg (le_of_lt halo) (le_trans hy0 hyhi))
                    (mul_nonneg hx0 hy0))
    · -- x ≥ 0, y < 0: a.hi*b.lo ≤ x*b.lo ≤ x*y
      push_neg at hy0
      have hblo_np : (↑b.lo : ℝ) ≤ 0 := le_trans hylo (le_of_lt hy0)
      exact le_trans (min_le_of_right_le (min_le_left _ _))
        (le_trans (mul_le_mul_of_nonpos_right hxhi hblo_np)
                  (mul_le_mul_of_nonneg_left hylo hx0))
    · -- x < 0, y ≥ 0: a.lo*b.hi ≤ x*b.hi ≤ x*y
      push_neg at hx0
      have hbhi_nn : (0 : ℝ) ≤ ↑b.hi := le_trans hy0 hyhi
      exact le_trans (min_le_of_left_le (min_le_right _ _))
        (le_trans (mul_le_mul_of_nonneg_right hxlo hbhi_nn)
                  (mul_le_mul_of_nonpos_left hyhi (le_of_lt hx0)))
    · -- x < 0, y < 0
      push_neg at hx0 hy0
      by_cases hahi : (↑a.hi : ℝ) ≤ 0
      · -- a.hi*b.hi ≤ a.hi*y ≤ x*y
        exact le_trans (min_le_of_right_le (min_le_right _ _))
          (le_trans (mul_le_mul_of_nonpos_left hyhi hahi)
                    (mul_le_mul_of_nonpos_right hxhi (le_of_lt hy0)))
      · -- a.hi*b.lo ≤ 0 ≤ x*y
        push_neg at hahi
        have hblo_np : (↑b.lo : ℝ) ≤ 0 := le_trans hylo (le_of_lt hy0)
        exact le_trans (min_le_of_right_le (min_le_left _ _))
          (le_trans (mul_nonpos_of_nonneg_of_nonpos (le_of_lt hahi) hblo_np)
                    (le_of_lt (mul_pos_of_neg_of_neg hx0 hy0)))
  · -- Upper bound: x * y ≤ max₄(corners)
    by_cases hx0 : (0 : ℝ) ≤ x <;> by_cases hy0 : (0 : ℝ) ≤ y
    · -- x ≥ 0, y ≥ 0: x*y ≤ a.hi*y ≤ a.hi*b.hi
      exact le_trans
        (le_trans (mul_le_mul_of_nonneg_right hxhi hy0)
                  (mul_le_mul_of_nonneg_left hyhi (le_trans hx0 hxhi)))
        (le_max_of_le_right (le_max_right _ _))
    · -- x ≥ 0, y < 0: x*y ≤ x*b.hi ≤ corner
      push_neg at hy0
      by_cases hbhi : (0 : ℝ) ≤ ↑b.hi
      · exact le_trans
          (le_trans (mul_le_mul_of_nonneg_left hyhi hx0)
                    (mul_le_mul_of_nonneg_right hxhi hbhi))
          (le_max_of_le_right (le_max_right _ _))
      · push_neg at hbhi
        exact le_trans
          (le_trans (mul_le_mul_of_nonneg_left hyhi hx0)
                    (mul_le_mul_of_nonpos_right hxlo (le_of_lt hbhi)))
          (le_max_of_le_left (le_max_right _ _))
    · -- x < 0, y ≥ 0: x*y ≤ a.hi*y ≤ corner
      push_neg at hx0
      by_cases hahi : (0 : ℝ) ≤ ↑a.hi
      · exact le_trans
          (le_trans (mul_le_mul_of_nonneg_right hxhi hy0)
                    (mul_le_mul_of_nonneg_left hyhi hahi))
          (le_max_of_le_right (le_max_right _ _))
      · push_neg at hahi
        exact le_trans
          (le_trans (mul_le_mul_of_nonneg_right hxhi hy0)
                    (mul_le_mul_of_nonpos_left hylo (le_of_lt hahi)))
          (le_max_of_le_right (le_max_left _ _))
    · -- x < 0, y < 0: x*y ≤ a.lo*y ≤ a.lo*b.lo
      push_neg at hx0 hy0
      exact le_trans
        (le_trans (mul_le_mul_of_nonpos_right hxlo (le_of_lt hy0))
                  (mul_le_mul_of_nonpos_left hylo (le_trans hxlo (le_of_lt hx0))))
        (le_max_of_le_left (le_max_left _ _))

-- ============================================================================
-- Scale by nonneg constant
-- ============================================================================

/-- Scale interval by a nonneg rational: [q*a.lo, q*a.hi]. -/
def scaleNonneg (q : ℚ) (a : QInterval) (hq : 0 ≤ q) : QInterval where
  lo := q * a.lo
  hi := q * a.hi
  valid := mul_le_mul_of_nonneg_left a.valid hq

theorem scaleNonneg_containsReal {q : ℚ} {a : QInterval} {x : ℝ}
    (hq : 0 ≤ q) (hx : a.containsReal x) :
    (scaleNonneg q a hq).containsReal (↑q * x) := by
  have hq_r : (0 : ℝ) ≤ ↑q := by exact_mod_cast hq
  simp only [scaleNonneg, containsReal]
  push_cast
  exact ⟨mul_le_mul_of_nonneg_left hx.1 hq_r, mul_le_mul_of_nonneg_left hx.2 hq_r⟩

-- ============================================================================
-- Separation and Ordering
-- ============================================================================

/-- Check that `a.lo > b.hi` (decidable on ℚ). -/
def separated (a b : QInterval) : Bool := b.hi < a.lo

/-- **Key theorem**: interval separation implies ℝ strict ordering. -/
theorem gt_of_separated {a b : QInterval} {x y : ℝ}
    (hx : a.containsReal x) (hy : b.containsReal y)
    (hsep : b.hi < a.lo) : x > y :=
  calc x ≥ ↑a.lo := hx.1
    _ > ↑b.hi := by exact_mod_cast hsep
    _ ≥ y := hy.2

/-- If a.hi ≤ b.lo, then x ≤ y. Dual of `gt_of_separated`. -/
theorem le_of_separated {a b : QInterval} {x y : ℝ}
    (hx : a.containsReal x) (hy : b.containsReal y)
    (hsep : a.hi ≤ b.lo) : x ≤ y :=
  calc x ≤ ↑a.hi := hx.2
    _ ≤ ↑b.lo := by exact_mod_cast hsep
    _ ≤ y := hy.1

/-- Interval separation implies ≥. -/
theorem ge_of_le_lo {a b : QInterval} {x y : ℝ}
    (hx : a.containsReal x) (hy : b.containsReal y)
    (hge : b.hi ≤ a.lo) : x ≥ y :=
  calc x ≥ ↑a.lo := hx.1
    _ ≥ ↑b.hi := by exact_mod_cast hge
    _ ≥ y := hy.2

/-- Two exact intervals at the same point imply equality. -/
theorem eq_of_exact {q : ℚ} {x y : ℝ}
    (hx : (exact q).containsReal x) (hy : (exact q).containsReal y) :
    x = y := by
  have hx_eq : x = ↑q := le_antisymm hx.2 hx.1
  have hy_eq : y = ↑q := le_antisymm hy.2 hy.1
  linarith

-- ============================================================================
-- Conditional (if-then-else support)
-- ============================================================================

/-- If the condition is known false, take the else branch. -/
theorem ite_neg_containsReal {c : Prop} [Decidable c] {I : QInterval} {x y : ℝ}
    (hc : ¬c) (hy : I.containsReal y) :
    I.containsReal (if c then x else y) := by
  simp [hc, hy]

/-- If the condition is known true, take the then branch. -/
theorem ite_pos_containsReal {c : Prop} [Decidable c] {I : QInterval} {x y : ℝ}
    (hc : c) (hx : I.containsReal x) :
    I.containsReal (if c then x else y) := by
  simp [hc, hx]

/-- Decidable.rec with condition known true → take the isTrue branch.
    Handles the case where `ite` has been unfolded to `Decidable.rec` by whnf. -/
theorem decidable_rec_pos_containsReal {p : Prop} {inst : Decidable p}
    {I : QInterval} (f : ¬p → ℝ) (g : p → ℝ) (hc : p)
    (hx : I.containsReal (g hc)) :
    I.containsReal (@Decidable.rec p (fun _ => ℝ) f g inst) := by
  cases inst with
  | isTrue _ => exact hx
  | isFalse h => exact absurd hc h

/-- Decidable.rec with condition known false → take the isFalse branch. -/
theorem decidable_rec_neg_containsReal {p : Prop} {inst : Decidable p}
    {I : QInterval} (f : ¬p → ℝ) (g : p → ℝ) (hnc : ¬p)
    (hy : I.containsReal (f hnc)) :
    I.containsReal (@Decidable.rec p (fun _ => ℝ) f g inst) := by
  cases inst with
  | isTrue h => exact absurd h hnc
  | isFalse _ => exact hy

-- ============================================================================
-- Nonzero detection
-- ============================================================================

/-- If an interval has positive lower bound, the contained value is positive. -/
theorem pos_of_lo_pos {a : QInterval} {x : ℝ}
    (hx : a.containsReal x) (hlo : 0 < a.lo) : 0 < x :=
  lt_of_lt_of_le (by exact_mod_cast hlo) hx.1

/-- If an interval has positive lower bound, the contained value is nonzero. -/
theorem ne_zero_of_lo_pos {a : QInterval} {x : ℝ}
    (hx : a.containsReal x) (hlo : 0 < a.lo) : x ≠ 0 :=
  ne_of_gt (pos_of_lo_pos hx hlo)

/-- If an interval has nonneg lower bound and nonpos upper bound, the value is zero.
    Used by the tactic to prove `x = 0` when the interval is `[0, 0]`. -/
theorem eq_zero_of_contained_nonneg {I : QInterval} {x : ℝ}
    (hx : I.containsReal x) (hlo : 0 ≤ I.lo) (hhi : I.hi ≤ 0) : x = 0 :=
  le_antisymm (le_trans hx.2 (by exact_mod_cast hhi)) (le_trans (by exact_mod_cast hlo) hx.1)

-- ============================================================================
-- Inverse (positive case)
-- ============================================================================

/-- Inverse of a positive interval: [1/hi, 1/lo]. -/
def invPos (a : QInterval) (ha : 0 < a.lo) : QInterval where
  lo := 1 / a.hi
  hi := 1 / a.lo
  valid := div_le_div_of_nonneg_left (by norm_num : (0 : ℚ) ≤ 1) ha a.valid

theorem invPos_containsReal {a : QInterval} {x : ℝ}
    (ha : 0 < a.lo) (hx : a.containsReal x) :
    (invPos a ha).containsReal (x⁻¹) := by
  simp only [invPos, containsReal]
  push_cast
  have hx_pos : (0 : ℝ) < x := lt_of_lt_of_le (by exact_mod_cast ha) hx.1
  rw [one_div, one_div]
  exact ⟨inv_anti₀ hx_pos hx.2, inv_anti₀ (by exact_mod_cast ha) hx.1⟩

/-- If an interval has lo = 0 and hi = 0, the contained value equals zero. -/
theorem eq_zero_of_bounds {a : QInterval} {x : ℝ}
    (hx : a.containsReal x) (hlo : a.lo = 0) (hhi : a.hi = 0) : x = 0 := by
  have h1 := hx.1; have h2 := hx.2
  rw [hlo] at h1; rw [hhi] at h2
  simp at h1 h2
  linarith

-- ============================================================================
-- Zero short-circuit for multiplication
-- ============================================================================

/-- If x is in a zero interval, x * y is in the zero interval. -/
theorem zero_mul_containsReal {a : QInterval} {x y : ℝ}
    (hx : a.containsReal x) (hlo : a.lo = 0) (hhi : a.hi = 0) :
    (exact 0).containsReal (x * y) := by
  have := eq_zero_of_bounds hx hlo hhi
  subst this; simp [exact, containsReal]

/-- If y is in a zero interval, x * y is in the zero interval. -/
theorem mul_zero_containsReal {b : QInterval} {x y : ℝ}
    (hy : b.containsReal y) (hlo : b.lo = 0) (hhi : b.hi = 0) :
    (exact 0).containsReal (x * y) := by
  have := eq_zero_of_bounds hy hlo hhi
  subst this; simp [exact, containsReal]

/-- If x is in a zero interval, x / y is in the zero interval. -/
theorem zero_div_containsReal {a : QInterval} {x y : ℝ}
    (hx : a.containsReal x) (hlo : a.lo = 0) (hhi : a.hi = 0) :
    (exact 0).containsReal (x / y) := by
  have := eq_zero_of_bounds hx hlo hhi
  subst this; simp [exact, containsReal]

-- ============================================================================
-- Transport along equality
-- ============================================================================

/-- Transport containment along a real-valued equality.
    If `y = x` and the interval contains `x`, it contains `y`. -/
theorem containsReal_of_eq {I : QInterval} {x y : ℝ}
    (h : y = x) (hx : I.containsReal x) : I.containsReal y :=
  h ▸ hx

-- ============================================================================
-- Natural-number rpow
-- ============================================================================

/-- Interval for nonneg base raised to a natural power: [lo^n, hi^n]. -/
def rpowNat (a : QInterval) (n : ℕ) (ha : 0 ≤ a.lo) : QInterval where
  lo := a.lo ^ n
  hi := a.hi ^ n
  valid := pow_le_pow_left₀ ha a.valid n

/-- Containment for `x ^ n` (nat power) with nonneg base. -/
theorem powNat_containsReal {a : QInterval} {x : ℝ} (n : ℕ)
    (ha : 0 ≤ a.lo) (hx : a.containsReal x) :
    (a.rpowNat n ha).containsReal (x ^ n) := by
  have hx_nn : (0 : ℝ) ≤ x := le_trans (by exact_mod_cast ha) hx.1
  simp only [rpowNat, containsReal]
  push_cast
  exact ⟨pow_le_pow_left₀ (by exact_mod_cast ha) hx.1 n,
         pow_le_pow_left₀ hx_nn hx.2 n⟩

/-- Raise an interval to a natural power. No proof obligation — checks nonneg
    at runtime and uses `rpowNat` for sound computation, fallback otherwise. -/
def powNat (iv : QInterval) (n : ℕ) : QInterval :=
  if n == 0 then exact 1
  else if h : 0 ≤ iv.lo then iv.rpowNat n h
  else ⟨0, 1, by norm_num⟩

/-- If a real value is contained in an interval with lo = 0 and hi = 0,
    the value equals zero. -/
theorem eq_zero_of_containsReal {I : QInterval} {x : ℝ}
    (h : I.containsReal x) (hlo : I.lo = 0) (hhi : I.hi = 0) : x = 0 := by
  simp only [containsReal, hlo, hhi] at h
  push_cast at h
  linarith [h.1, h.2]

-- ============================================================================
-- Coarsening: bound rational precision to avoid blowup
-- ============================================================================

/-- Maximum bit length for rational numerator/denominator.
    64 bits ≈ 19 decimal digits, enough precision for RSA comparisons. -/
def maxBits : ℕ := 64

/-- Number of bits in the absolute value of an integer. -/
private def Int.bitLen : ℤ → ℕ
  | .ofNat n => n.log2 + 1
  | .negSucc n => (n + 1).log2 + 1

/-- Round a rational downward (toward -∞) to bounded bit precision.
    If num or den exceeds `maxBits`, shift both right. Denominator rounding
    direction depends on numerator sign to ensure the result ≤ q. -/
private def truncDown (q : ℚ) (bits : ℕ := maxBits) : ℚ :=
  let numBits := Int.bitLen q.num
  let denBits := Nat.log2 q.den + 1
  let excess := max numBits denBits - bits
  if excess ≤ 0 then q  -- already small enough
  else
    let shift := (2 : ℤ) ^ excess
    let newNum := q.num / shift  -- floor div (toward -∞) for all signs
    let newDen := if q.num ≥ 0
                  then ((q.den : ℤ) + shift - 1) / shift  -- ceil(den) for nonneg q
                  else (q.den : ℤ) / shift                 -- floor(den) for neg q
    if newDen ≤ 0 then q else  -- safety (shouldn't happen)
    newNum / newDen

/-- Round a rational upward (toward +∞) to bounded bit precision.
    Denominator rounding direction depends on numerator sign to ensure
    the result ≥ q. -/
private def truncUp (q : ℚ) (bits : ℕ := maxBits) : ℚ :=
  let numBits := Int.bitLen q.num
  let denBits := Nat.log2 q.den + 1
  let excess := max numBits denBits - bits
  if excess ≤ 0 then q
  else
    let shift := (2 : ℤ) ^ excess
    let newNum := (q.num + shift - 1) / shift  -- ceil(num/shift) for all signs
    let newDen := if q.num ≥ 0
                  then (q.den : ℤ) / shift                 -- floor(den) for nonneg q
                  else ((q.den : ℤ) + shift - 1) / shift  -- ceil(den) for neg q
    if newDen ≤ 0 then q else
    newNum / newDen

private theorem truncDown_le (q : ℚ) (bits : ℕ) :
    truncDown q bits ≤ q := by
  unfold truncDown; simp only []
  split
  case isTrue => exact le_refl q
  case isFalse h_excess =>
    push_neg at h_excess
    set shift := (2 : ℤ) ^ (max (Int.bitLen q.num) (Nat.log2 q.den + 1) - bits)
    have hS : (0 : ℤ) < shift := by positivity
    have hD : (0 : ℤ) < q.den := Int.ofNat_lt.mpr q.den_pos
    conv_rhs => rw [← Rat.num_div_den q]
    split
    case isTrue hnn =>
      set nd := ((q.den : ℤ) + shift - 1) / shift
      split
      case isTrue => exact le_of_eq (Rat.num_div_den q).symm
      case isFalse hnd =>
        push_neg at hnd
        rw [div_le_div_iff₀ (by exact_mod_cast hnd : (0:ℚ) < (↑nd : ℚ))
                            (by exact_mod_cast hD : (0:ℚ) < (↑↑q.den : ℚ))]
        suffices h : (q.num / shift) * (q.den : ℤ) ≤ q.num * nd by exact_mod_cast h
        have h1 := Int.ediv_mul_le q.num (ne_of_gt hS)
        have h2 : (q.den : ℤ) ≤ nd * shift := by
          nlinarith [Int.lt_ediv_add_one_mul_self ((q.den : ℤ) + shift - 1) hS]
        nlinarith [mul_le_mul_of_nonneg_right h1 (show (0:ℤ) ≤ q.den from hD.le),
                   mul_le_mul_of_nonneg_left h2 hnn]
    case isFalse hneg =>
      push_neg at hneg
      set nd := (q.den : ℤ) / shift
      split
      case isTrue => exact le_of_eq (Rat.num_div_den q).symm
      case isFalse hnd =>
        push_neg at hnd
        rw [div_le_div_iff₀ (by exact_mod_cast hnd : (0:ℚ) < (↑nd : ℚ))
                            (by exact_mod_cast hD : (0:ℚ) < (↑↑q.den : ℚ))]
        suffices h : (q.num / shift) * (q.den : ℤ) ≤ q.num * nd by exact_mod_cast h
        have h1 := Int.ediv_mul_le q.num (ne_of_gt hS)
        have h2 := Int.ediv_mul_le (q.den : ℤ) (ne_of_gt hS)
        nlinarith [mul_le_mul_of_nonneg_right h1 (show (0:ℤ) ≤ q.den from hD.le),
                   mul_le_mul_of_nonpos_left h2 hneg.le]

private theorem le_truncUp (q : ℚ) (bits : ℕ) :
    q ≤ truncUp q bits := by
  unfold truncUp; simp only []
  split
  case isTrue => exact le_refl q
  case isFalse h_excess =>
    push_neg at h_excess
    set shift := (2 : ℤ) ^ (max (Int.bitLen q.num) (Nat.log2 q.den + 1) - bits)
    have hS : (0 : ℤ) < shift := by positivity
    have hD : (0 : ℤ) < q.den := Int.ofNat_lt.mpr q.den_pos
    conv_lhs => rw [← Rat.num_div_den q]
    set cn := (q.num + shift - 1) / shift
    split
    case isTrue hnn =>
      set nd := (q.den : ℤ) / shift
      split
      case isTrue => exact le_of_eq (Rat.num_div_den q)
      case isFalse hnd =>
        push_neg at hnd
        rw [div_le_div_iff₀ (by exact_mod_cast hD : (0:ℚ) < (↑↑q.den : ℚ))
                            (by exact_mod_cast hnd : (0:ℚ) < (↑nd : ℚ))]
        suffices h : q.num * nd ≤ cn * (q.den : ℤ) by exact_mod_cast h
        have h1 : q.num ≤ cn * shift := by
          nlinarith [Int.lt_ediv_add_one_mul_self (q.num + shift - 1) hS]
        have h2 := Int.ediv_mul_le (q.den : ℤ) (ne_of_gt hS)
        have h3 : 0 ≤ cn := Int.ediv_nonneg (by linarith) hS.le
        nlinarith [mul_le_mul_of_nonneg_right h2 h3,
                   mul_le_mul_of_nonneg_left h1 hD.le]
    case isFalse hneg =>
      push_neg at hneg
      set nd := ((q.den : ℤ) + shift - 1) / shift
      split
      case isTrue => exact le_of_eq (Rat.num_div_den q)
      case isFalse hnd =>
        push_neg at hnd
        rw [div_le_div_iff₀ (by exact_mod_cast hD : (0:ℚ) < (↑↑q.den : ℚ))
                            (by exact_mod_cast hnd : (0:ℚ) < (↑nd : ℚ))]
        suffices h : q.num * nd ≤ cn * (q.den : ℤ) by exact_mod_cast h
        have h1 : q.num ≤ cn * shift := by
          nlinarith [Int.lt_ediv_add_one_mul_self (q.num + shift - 1) hS]
        have h2 : (q.den : ℤ) ≤ nd * shift := by
          nlinarith [Int.lt_ediv_add_one_mul_self ((q.den : ℤ) + shift - 1) hS]
        have h3 : cn ≤ 0 := by
          have := Int.ediv_mul_le (q.num + shift - 1) (ne_of_gt hS)
          nlinarith [Int.le_sub_one_of_lt (show cn * shift < 1 * shift by linarith)]
        nlinarith [mul_le_mul_of_nonneg_right h1 hnd.le,
                   mul_le_mul_of_nonpos_left h2 h3]

/-- Widen an interval to bounded-precision rationals.
    Sound: only makes the interval wider, so containment is preserved. -/
def coarsen (I : QInterval) (bits : ℕ := maxBits) : QInterval where
  lo := truncDown I.lo bits
  hi := truncUp I.hi bits
  valid := le_trans (truncDown_le I.lo bits) (le_trans I.valid (le_truncUp I.hi bits))

theorem coarsen_containsReal {I : QInterval} {x : ℝ} (bits : ℕ)
    (hx : I.containsReal x) : (I.coarsen bits).containsReal x := by
  constructor
  · exact le_trans (by exact_mod_cast truncDown_le I.lo bits) hx.1
  · exact le_trans hx.2 (by exact_mod_cast le_truncUp I.hi bits)

end QInterval

end Interval

-- ============================================================================
-- PadeExp: Padé approximant for Real.exp
-- ============================================================================

namespace Interval

open Interval.QInterval

-- ============================================================================
-- Padé Coefficients
-- ============================================================================

/-- Padé [4/4] numerator: 1 + x/2 + 3x²/28 + x³/84 + x⁴/1680 (Horner form). -/
def padeNum (x : ℚ) : ℚ :=
  1 + x * (1/2 + x * (3/28 + x * (1/84 + x * (1/1680))))

/-- Padé [4/4] denominator: padeNum(-x). -/
def padeDen (x : ℚ) : ℚ := padeNum (-x)

/-- Padé [4/4] approximant: padeNum(x) / padeDen(x). -/
def padeExp (x : ℚ) : ℚ := padeNum x / padeDen x

-- ============================================================================
-- Error Bound
-- ============================================================================

/-- Conservative error bound for Padé [4/4] on [-1, 1].
    True error is ~4.3×10⁻⁸; this bound gives 2.3× safety margin. -/
def padeErrorBound : ℚ := 1 / 4000000

/-- Triangle inequality for 6 terms (left-associated addition). -/
private lemma abs_sum6_le {a b c d e f A B C D E F : ℝ}
    (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
    (hd : |d| ≤ D) (he : |e| ≤ E) (hf : |f| ≤ F) :
    |a + b + c + d + e + f| ≤ A + B + C + D + E + F := by
  calc |a + b + c + d + e + f|
      ≤ |a + b + c + d + e| + |f| := abs_add_le _ f
    _ ≤ (|a + b + c + d| + |e|) + |f| := by linarith [abs_add_le (a + b + c + d) e]
    _ ≤ ((|a + b + c| + |d|) + |e|) + |f| := by linarith [abs_add_le (a + b + c) d]
    _ ≤ (((|a + b| + |c|) + |d|) + |e|) + |f| := by linarith [abs_add_le (a + b) c]
    _ ≤ ((((|a| + |b|) + |c|) + |d|) + |e|) + |f| := by linarith [abs_add_le a b]
    _ ≤ A + B + C + D + E + F := by linarith

/-- padeDen(q) ≥ 143/240 for q ≤ 1 (minimum at q = 1). -/
private lemma padeDen_lower_real (q : ℚ) (hhi : q ≤ 1) :
    (143 : ℝ) / 240 ≤ (↑(padeDen q) : ℝ) := by
  suffices h : (143 : ℚ) / 240 ≤ padeDen q by
    have h' : (↑((143 : ℚ) / 240) : ℝ) ≤ ↑(padeDen q) := by exact_mod_cast h
    simp only [Rat.cast_div, Rat.cast_ofNat] at h'; exact h'
  simp only [padeDen, padeNum]
  nlinarith [sq_nonneg q, sq_nonneg (q * q), sq_nonneg (1 - q), sq_nonneg (1 + q),
             mul_self_nonneg (q^2 - q/2), sq_nonneg (q^2 - 7*q)]

set_option maxHeartbeats 800000 in
/-- Σ_{k=0}^{10} x^k/k! in Horner form. -/
private lemma taylor_eq_horner (x : ℝ) :
    ∑ m ∈ Finset.range 11, x ^ m / (m.factorial : ℝ) =
    1 + x * (1 + x * (1/2 + x * (1/6 + x * (1/24 + x * (1/120 +
    x * (1/720 + x * (1/5040 + x * (1/40320 + x * (1/362880 +
    x * (1/3628800)))))))))) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [Nat.factorial]; push_cast; ring

set_option maxHeartbeats 800000 in
/-- T₁₀(q) · padeDen(q) - padeNum(q) = D₁₁(q), a degree-14 polynomial with
    terms only at degrees 9-14 (the Padé matching property). -/
private lemma poly_identity (q : ℚ) :
    let x := (q : ℝ)
    (1 + x * (1 + x * (1/2 + x * (1/6 + x * (1/24 + x * (1/120 +
      x * (1/720 + x * (1/5040 + x * (1/40320 + x * (1/362880 +
      x * (1/3628800))))))))))) *
    (↑(padeDen q) : ℝ) - (↑(padeNum q) : ℝ) =
    x^9 / 25401600 + x^10 / 50803200 - x^11 / 50803200 +
    x^12 / 87091200 - x^13 / 609638400 + x^14 / 6096384000 := by
  simp only [padeDen, padeNum]; push_cast; ring

/-- Coefficient-sum bound on D₁₁: |D₁₁(x)| ≤ 187/2032128000 for |x| ≤ 1. -/
private lemma D11_bound (x : ℝ) (hx : |x| ≤ 1) :
    |x^9 / 25401600 + x^10 / 50803200 - x^11 / 50803200 +
     x^12 / 87091200 - x^13 / 609638400 + x^14 / 6096384000| ≤
    (187 : ℝ) / 2032128000 := by
  have hpow : ∀ n : ℕ, |x ^ n| ≤ 1 := fun n => by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hx
  have hterm : ∀ (n : ℕ) (d : ℝ), 0 < d → |x ^ n / d| ≤ 1 / d := fun n d hd => by
    rw [abs_div, abs_of_pos hd]
    exact div_le_div_of_nonneg_right (hpow n) (le_of_lt hd)
  have hnterm : ∀ (n : ℕ) (d : ℝ), 0 < d → |-(x ^ n) / d| ≤ 1 / d := fun n d hd => by
    rw [neg_div, abs_neg]; exact hterm n d hd
  rw [show x^9 / 25401600 + x^10 / 50803200 - x^11 / 50803200 +
      x^12 / 87091200 - x^13 / 609638400 + x^14 / 6096384000 =
      x^9 / 25401600 + x^10 / 50803200 + (-(x^11) / 50803200) +
      x^12 / 87091200 + (-(x^13) / 609638400) + x^14 / 6096384000 from by ring]
  calc |x ^ 9 / 25401600 + x ^ 10 / 50803200 + -(x ^ 11) / 50803200 +
        x ^ 12 / 87091200 + -(x ^ 13) / 609638400 + x ^ 14 / 6096384000|
      ≤ 1/25401600 + 1/50803200 + 1/50803200 + 1/87091200 + 1/609638400 + 1/6096384000 :=
        abs_sum6_le (hterm 9 _ (by norm_num)) (hterm 10 _ (by norm_num))
          (hnterm 11 _ (by norm_num)) (hterm 12 _ (by norm_num))
          (hnterm 13 _ (by norm_num)) (hterm 14 _ (by norm_num))
    _ ≤ 187 / 2032128000 := by norm_num

set_option maxHeartbeats 1600000 in
/-- The Padé [4/4] approximant is within `padeErrorBound` of exp on [-1, 1].

    Proof via triangle inequality: |exp(q) - P(q)/Q(q)| ≤ |exp(q) - T₁₀(q)| + |T₁₀(q) - P(q)/Q(q)|
    where T₁₀ is the degree-10 Taylor polynomial. The first term is bounded by `Real.exp_bound`
    with n = 11 (≤ 1/36590400 ≈ 2.73×10⁻⁸). The second term equals |T₁₀·Q - P|/Q; the numerator
    is a polynomial with terms only at degrees 9-14 (Padé matching property), bounded by
    187/2032128000 ≈ 9.2×10⁻⁸ via coefficient sum, and Q ≥ 143/240. -/
theorem pade_error_bound (q : ℚ) (hq_lo : -1 ≤ q) (hq_hi : q ≤ 1)
    (hden_pos : 0 < padeDen q) :
    |Real.exp (↑q : ℝ) - (↑(padeExp q) : ℝ)| ≤ (↑padeErrorBound : ℝ) := by
  set x := (q : ℝ) with hx_def
  set T := ∑ m ∈ Finset.range 11, x ^ m / (m.factorial : ℝ)
  set P := (↑(padeNum q) : ℝ)
  set Q := (↑(padeDen q) : ℝ)
  have hQ_pos : (0 : ℝ) < Q := by
    show (0 : ℝ) < ↑(padeDen q); exact_mod_cast hden_pos
  have hQ_ne : Q ≠ 0 := ne_of_gt hQ_pos
  have hx_abs : |x| ≤ 1 := by
    rw [abs_le]; exact ⟨by show (-1 : ℝ) ≤ ↑q; exact_mod_cast hq_lo,
                         by show (↑q : ℝ) ≤ 1; exact_mod_cast hq_hi⟩
  -- padeExp = P / Q
  have h_pade : (↑(padeExp q) : ℝ) = P / Q := by
    simp only [padeExp, P, Q]; push_cast; rfl
  -- |exp(x) - T₁₀| ≤ 1/36590400  (Taylor remainder with n = 11)
  have hA : |Real.exp x - T| ≤ 1 / 36590400 := by
    calc |Real.exp x - T|
        ≤ |x| ^ 11 * ((12 : ℝ) / (↑(Nat.factorial 11) * 11)) :=
          Real.exp_bound hx_abs (by norm_num : (0 : ℕ) < 11)
      _ ≤ 1 * ((12 : ℝ) / (↑(Nat.factorial 11) * 11)) := by
          exact mul_le_mul_of_nonneg_right (pow_le_one₀ (abs_nonneg _) hx_abs) (by positivity)
      _ = 1 / 36590400 := by simp [Nat.factorial]; norm_num
  -- T₁₀·Q - P = D₁₁ (polynomial identity verified by ring)
  have hD_eq : T * Q - P = x^9 / 25401600 + x^10 / 50803200 - x^11 / 50803200 +
      x^12 / 87091200 - x^13 / 609638400 + x^14 / 6096384000 := by
    show T * Q - P = _; rw [show T = _ from taylor_eq_horner x]; exact poly_identity q
  -- |D₁₁| ≤ 187/2032128000
  have hTQ : |T * Q - P| ≤ 187 / 2032128000 := by rw [hD_eq]; exact D11_bound x hx_abs
  -- Combine: exp(x) - P/Q = ((exp(x) - T)·Q + (T·Q - P)) / Q
  rw [h_pade, show Real.exp x - P / Q = ((Real.exp x - T) * Q + (T * Q - P)) / Q from
    by field_simp; ring]
  rw [abs_div, abs_of_pos hQ_pos, div_le_iff₀ hQ_pos]
  calc |(Real.exp x - T) * Q + (T * Q - P)|
      ≤ |(Real.exp x - T) * Q| + |T * Q - P| := abs_add_le _ _
    _ = |Real.exp x - T| * Q + |T * Q - P| := by rw [abs_mul, abs_of_pos hQ_pos]
    _ ≤ (1 / 36590400) * Q + 187 / 2032128000 := by
        linarith [mul_le_mul_of_nonneg_right hA (le_of_lt hQ_pos)]
    _ ≤ ↑padeErrorBound * Q := by
        simp only [padeErrorBound]; push_cast; nlinarith [padeDen_lower_real q hq_hi]

-- ============================================================================
-- Point interval for exp at a rational
-- ============================================================================

/-- Interval containing exp(q) for q ∈ [-1, 1], computed via Padé.
    Returns [padeExp(q) - ε, padeExp(q) + ε] where ε = padeErrorBound. -/
private def expPointSmall (q : ℚ) (_hq_lo : -1 ≤ q) (_hq_hi : q ≤ 1)
    (_hden_pos : 0 < padeDen q) : QInterval where
  lo := padeExp q - padeErrorBound
  hi := padeExp q + padeErrorBound
  valid := by simp only [padeErrorBound]; linarith

private theorem expPointSmall_containsReal (q : ℚ) (hq_lo : -1 ≤ q) (hq_hi : q ≤ 1)
    (hden_pos : 0 < padeDen q) :
    (expPointSmall q hq_lo hq_hi hden_pos).containsReal (Real.exp (↑q : ℝ)) := by
  simp only [expPointSmall, containsReal]
  have h := pade_error_bound q hq_lo hq_hi hden_pos
  rw [abs_le] at h
  push_cast
  constructor <;> linarith

-- ============================================================================
-- Argument Reduction
-- ============================================================================

/-- Number of halvings needed so q / 2^k ∈ [-1, 1]. -/
def reductionSteps (q : ℚ) : ℕ :=
  if q.num.natAbs ≤ q.den then 0
  else Nat.log 2 q.num.natAbs - Nat.log 2 q.den + 1

/-- Repeated squaring of a nonneg interval (carries nonneg proof with value). -/
private def repeatedSqCore (I : QInterval) (n : ℕ) (h : 0 ≤ I.lo) :
    { J : QInterval // 0 ≤ J.lo } :=
  match n with
  | 0 => ⟨I, h⟩
  | n + 1 =>
    let ⟨prev, hprev⟩ := repeatedSqCore I n h
    ⟨prev.mulNonneg prev hprev hprev, mul_nonneg hprev hprev⟩

/-- Repeated squaring of a nonneg interval.
    Squares I a total of n times: repeatedSq I 0 = I, repeatedSq I (n+1) = (repeatedSq I n)². -/
def repeatedSq (I : QInterval) (n : ℕ) (h : 0 ≤ I.lo) : QInterval :=
  (repeatedSqCore I n h).val

theorem repeatedSq_nonneg (I : QInterval) (n : ℕ) (h : 0 ≤ I.lo) :
    0 ≤ (repeatedSq I n h).lo :=
  (repeatedSqCore I n h).property

-- ============================================================================
-- expPoint: Point interval for exp(q) at arbitrary rational q
-- ============================================================================

/-- Point interval containing exp(q) for arbitrary rational q.

    Strategy: reduce q → q' = q/2^k with |q'| ≤ 1 via `reductionSteps`,
    compute exp(q') via Padé [4/4], then square k times since exp(q) = exp(q')^(2^k).

    The nonneg guard on `small.lo` is always true by construction:
    padeExp(q') ≈ exp(q') ≥ exp(-1) ≈ 0.368 >> padeErrorBound = 2.5×10⁻⁷. -/
def expPoint (q : ℚ) : QInterval :=
  let k := reductionSteps q
  let q' := q / (2 ^ k : ℚ)
  let approx := padeExp q'
  let small : QInterval :=
    ⟨approx - padeErrorBound, approx + padeErrorBound,
     by simp only [padeErrorBound]; linarith⟩
  if h : 0 ≤ small.lo then
    repeatedSq small k h
  else
    -- Unreachable: padeExp(q') ≈ exp(q') ≥ exp(-1) ≈ 0.368 >> padeErrorBound.
    -- Sound fallback: exp(q) ∈ (0, 3^|num(q)|] since e < 3.
    ⟨0, (3 : ℚ) ^ q.num.natAbs,
     le_of_lt (pow_pos (by norm_num : (0 : ℚ) < 3) _)⟩

/-- padeDen(q) > 0 for -1 ≤ q ≤ 1. Writing padeDen(q) = (1 - q/2) + q²·(3/28 - q/84 + q²/1680),
    the first term ≥ 1/2 and the second ≥ 0 since 3/28 - q/84 ≥ 3/28 - 1/84 > 0. -/
private theorem padeDen_pos (q : ℚ) (_hlo : -1 ≤ q) (hhi : q ≤ 1) :
    0 < padeDen q := by
  simp only [padeDen, padeNum]
  nlinarith [sq_nonneg q, sq_nonneg (q * q), sq_nonneg (1 - q), sq_nonneg (1 + q),
             mul_self_nonneg (q * q - q / 2)]

/-- |q| ≤ 1 when q.num.natAbs ≤ q.den. -/
private theorem abs_le_one_of_natAbs_le_den (q : ℚ) (h : q.num.natAbs ≤ q.den) :
    -1 ≤ q ∧ q ≤ 1 := by
  have hd_pos : (0 : ℚ) < ↑q.den := Nat.cast_pos.mpr q.pos
  constructor
  · -- -1 ≤ q ↔ -↑q.den ≤ ↑q.num (after multiplying by q.den)
    rw [← Rat.num_div_den q]
    have hneg : (-1 : ℚ) = -(↑q.den) / ↑q.den := by rw [neg_div_self (ne_of_gt hd_pos)]
    rw [hneg]
    apply div_le_div_of_nonneg_right _ (le_of_lt hd_pos)
    exact_mod_cast le_trans (neg_le_neg (Int.ofNat_le.mpr h))
      (show -(↑q.num.natAbs : ℤ) ≤ q.num from by rw [← Int.abs_eq_natAbs]; exact neg_abs_le _)
  · -- q ≤ 1 ↔ ↑q.num ≤ ↑q.den
    rw [← Rat.num_div_den q]
    have hone : (1 : ℚ) = ↑q.den / ↑q.den := by rw [div_self (ne_of_gt hd_pos)]
    rw [hone]
    apply div_le_div_of_nonneg_right _ (le_of_lt hd_pos)
    exact_mod_cast le_trans Int.le_natAbs (Int.ofNat_le.mpr h)

/-- natAbs ≤ den * 2^k where k = log₂(natAbs) - log₂(den) + 1.
    Key step: natAbs < 2^(log₂ natAbs + 1) = 2^(log₂ den + k) = 2^(log₂ den) · 2^k ≤ den · 2^k. -/
private lemma natAbs_le_den_mul_pow (den natAbs : ℕ) (hden : 0 < den) (hgt : den < natAbs) :
    natAbs ≤ den * 2 ^ (Nat.log 2 natAbs - Nat.log 2 den + 1) := by
  have hden_ne : den ≠ 0 := by omega
  have h_log_le : Nat.log 2 den ≤ Nat.log 2 natAbs :=
    Nat.log_mono_right (le_of_lt hgt)
  calc natAbs
      ≤ 2 ^ (Nat.log 2 natAbs + 1) :=
        le_of_lt (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) natAbs)
    _ = 2 ^ (Nat.log 2 den + (Nat.log 2 natAbs - Nat.log 2 den + 1)) := by congr 1; omega
    _ = 2 ^ Nat.log 2 den * 2 ^ (Nat.log 2 natAbs - Nat.log 2 den + 1) := by ring_nf
    _ ≤ den * 2 ^ (Nat.log 2 natAbs - Nat.log 2 den + 1) := by
        apply Nat.mul_le_mul_right; exact Nat.pow_log_le_self 2 hden_ne

/-- q / 2^(reductionSteps q) ∈ [-1, 1]. -/
private theorem reductionSteps_spec (q : ℚ) :
    -1 ≤ q / (2 ^ reductionSteps q : ℚ) ∧ q / (2 ^ reductionSteps q : ℚ) ≤ 1 := by
  simp only [reductionSteps]
  split
  · -- q.num.natAbs ≤ q.den, k = 0
    simp only [pow_zero, div_one]
    exact abs_le_one_of_natAbs_le_den q ‹_›
  · -- q.num.natAbs > q.den, k = log₂(natAbs) - log₂(den) + 1
    rename_i hgt; push_neg at hgt
    set k := Nat.log 2 q.num.natAbs - Nat.log 2 q.den + 1
    have hpow_pos : (0 : ℚ) < 2 ^ k := pow_pos (by norm_num : (0 : ℚ) < 2) k
    have hna_le := natAbs_le_den_mul_pow q.den q.num.natAbs q.pos hgt
    have hd_pos : (0 : ℚ) < ↑q.den := Nat.cast_pos.mpr q.pos
    have hq_le : q ≤ (2 : ℚ) ^ k := by
      rw [← Rat.num_div_den q, div_le_iff₀ hd_pos]
      calc (↑q.num : ℚ)
          ≤ ↑(↑q.num.natAbs : ℤ) := by exact_mod_cast Int.le_natAbs
        _ ≤ ↑(q.den * 2 ^ k : ℕ) := by exact_mod_cast hna_le
        _ = 2 ^ k * ↑q.den := by push_cast; ring
    have hq_ge : -((2 : ℚ) ^ k) ≤ q := by
      rw [← Rat.num_div_den q, le_div_iff₀ hd_pos]
      calc -(2 ^ k : ℚ) * ↑q.den
          = -(↑(q.den * 2 ^ k : ℕ) : ℚ) := by push_cast; ring
        _ ≤ -(↑(↑q.num.natAbs : ℤ) : ℚ) := by
            apply neg_le_neg; exact_mod_cast hna_le
        _ ≤ ↑q.num := by
            show -(↑(↑q.num.natAbs : ℤ) : ℚ) ≤ ↑q.num
            exact_mod_cast show -(↑q.num.natAbs : ℤ) ≤ q.num from
              by rw [← Int.abs_eq_natAbs]; exact neg_abs_le _
    exact ⟨by rwa [le_div_iff₀ hpow_pos, neg_mul, one_mul],
           by rwa [div_le_iff₀ hpow_pos, one_mul]⟩

/-- Repeated squaring preserves containment: if I contains z ≥ 0,
    then repeatedSq I n h contains z^(2^n). -/
private theorem repeatedSq_containsReal {I : QInterval} {z : ℝ}
    (h : 0 ≤ I.lo) (hz : I.containsReal z) (hz_nn : 0 ≤ z) :
    ∀ n, (repeatedSq I n h).containsReal (z ^ (2 ^ n))
  | 0 => by simp [repeatedSq, repeatedSqCore]; exact hz
  | n + 1 => by
    simp only [repeatedSq, repeatedSqCore]
    have ih := repeatedSq_containsReal h hz hz_nn n
    have h_nn := repeatedSq_nonneg I n h
    show (QInterval.mulNonneg _ _ h_nn h_nn).containsReal (z ^ 2 ^ (n + 1))
    rw [show 2 ^ (n + 1) = 2 ^ n * 2 from by ring, pow_mul, sq]
    exact QInterval.mulNonneg_containsReal h_nn h_nn ih ih

/-- exp(q) = exp(q / 2^k)^(2^k), via Real.exp_nat_mul. -/
private theorem exp_pow_reduction (q : ℚ) (k : ℕ) :
    Real.exp (↑q : ℝ) = Real.exp (↑(q / (2 ^ k : ℚ)) : ℝ) ^ (2 ^ k) := by
  conv_lhs =>
    rw [show (↑q : ℝ) = ↑(2 ^ k : ℕ) * ↑(q / (2 ^ k : ℚ)) from by
      push_cast
      rw [mul_div_cancel₀]
      exact_mod_cast ne_of_gt (pow_pos (by norm_num : (0 : ℚ) < 2) k)]
  exact Real.exp_nat_mul _ _

/-- exp(n) ≤ 3^n for all n : ℕ, since e < 3. -/
private theorem exp_le_three_pow (n : ℕ) : Real.exp (↑n : ℝ) ≤ (3 : ℝ) ^ n := by
  induction n with
  | zero => simp [Real.exp_zero]
  | succ n ih =>
    rw [show (↑(n + 1) : ℝ) = ↑n + 1 from by push_cast; ring]
    rw [Real.exp_add, pow_succ]
    exact mul_le_mul ih (le_of_lt Real.exp_one_lt_three) (le_of_lt (Real.exp_pos _)) (by positivity)

/-- q ≤ q.num.natAbs as reals, since q = num/den with den ≥ 1. -/
private theorem rat_le_natAbs_num (q : ℚ) : (↑q : ℝ) ≤ ↑(q.num.natAbs : ℕ) := by
  suffices h : q ≤ (↑q.num.natAbs : ℚ) by exact_mod_cast h
  have hd_pos : (0 : ℚ) < ↑q.den := Nat.cast_pos.mpr q.pos
  calc q = ↑q.num / ↑q.den := (Rat.num_div_den q).symm
    _ ≤ ↑(↑q.num.natAbs : ℤ) / ↑q.den := by
        apply div_le_div_of_nonneg_right _ hd_pos.le
        exact_mod_cast le_trans (le_abs_self q.num) (le_of_eq (Int.abs_eq_natAbs q.num))
    _ ≤ ↑(↑q.num.natAbs : ℤ) / 1 := by
        apply div_le_div_of_nonneg_left _ one_pos (by exact_mod_cast q.pos)
        exact_mod_cast Nat.zero_le q.num.natAbs
    _ = ↑(↑q.num.natAbs : ℤ) := div_one _

set_option maxHeartbeats 400000 in
/-- Containment theorem for expPoint. -/
theorem expPoint_containsReal (q : ℚ) :
    (expPoint q).containsReal (Real.exp (↑q : ℝ)) := by
  unfold expPoint
  simp only []
  split
  · -- Main path: small.lo ≥ 0, so result = repeatedSq small k h
    rename_i h
    have ⟨hlo, hhi⟩ := reductionSteps_spec q
    have hden := padeDen_pos _ hlo hhi
    -- The small interval contains exp(q')
    have h_small := expPointSmall_containsReal _ hlo hhi hden
    -- The raw ⟨..., ...⟩ interval equals expPointSmall definitionally
    change (repeatedSq _ (reductionSteps q) h).containsReal _
    have h_nn : (0 : ℝ) ≤ Real.exp (↑(q / (2 ^ reductionSteps q : ℚ)) : ℝ) :=
      le_of_lt (Real.exp_pos _)
    rw [exp_pow_reduction q (reductionSteps q)]
    exact repeatedSq_containsReal h h_small h_nn _
  · -- Fallback: exp(q) ∈ [0, 3^|num(q)|]
    simp only [QInterval.containsReal]
    constructor
    · exact_mod_cast le_of_lt (Real.exp_pos _)
    · have h := le_trans (Real.exp_le_exp_of_le (rat_le_natAbs_num q)) (exp_le_three_pow _)
      exact_mod_cast h

-- ============================================================================
-- Main entry point
-- ============================================================================

/-- Interval containing exp(x) for x in rational interval I.

    Uses monotonicity of exp: for x ∈ [lo, hi],
      exp(lo) ≤ exp(x) ≤ exp(hi)
    so exp(x) ∈ [expPoint(lo).lo, expPoint(hi).hi]. -/
def expInterval (I : QInterval) : QInterval where
  lo := (expPoint I.lo).lo
  hi := (expPoint I.hi).hi
  valid := by
    have hlo := expPoint_containsReal I.lo
    have hhi := expPoint_containsReal I.hi
    have hmon : Real.exp (↑I.lo : ℝ) ≤ Real.exp (↑I.hi : ℝ) :=
      Real.exp_le_exp_of_le (by exact_mod_cast I.valid)
    have h : (↑(expPoint I.lo).lo : ℝ) ≤ ↑(expPoint I.hi).hi :=
      le_trans (le_trans hlo.1 hmon) hhi.2
    exact_mod_cast h

/-- Containment theorem for expInterval: monotonicity of exp + expPoint containment. -/
theorem expInterval_containsReal {I : QInterval} {x : ℝ}
    (hx : I.containsReal x) :
    (expInterval I).containsReal (Real.exp x) := by
  simp only [expInterval, QInterval.containsReal]
  have hlo := expPoint_containsReal I.lo
  have hhi := expPoint_containsReal I.hi
  constructor
  · exact le_trans hlo.1 (Real.exp_le_exp_of_le hx.1)
  · exact le_trans (Real.exp_le_exp_of_le hx.2) hhi.2

end Interval

-- ============================================================================
-- LogInterval: Real.log via bisection against expPoint
-- ============================================================================

namespace Interval

open Interval.QInterval

-- ============================================================================
-- Bisection
-- ============================================================================

/-- Bisection loop: narrow `[lo, hi]` such that `exp(lo) ≤ q ≤ exp(hi)`.

    Three-way check at the midpoint for soundness:
    - If `expPoint(mid).hi ≤ q`: `exp(mid) ≤ q`, so `mid ≤ log(q)` → narrow to `[mid, hi]`
    - If `q ≤ expPoint(mid).lo`: `q ≤ exp(mid)`, so `log(q) ≤ mid` → narrow to `[lo, mid]`
    - Otherwise: Padé interval straddles `q`, don't narrow (decrement `n` only) -/
private def logBisectCore (q : ℚ) :
    (lo hi : ℚ) → lo ≤ hi → ℕ → { p : ℚ × ℚ // p.1 ≤ p.2 }
  | lo, hi, h, 0 => ⟨(lo, hi), h⟩
  | lo, hi, h, n + 1 =>
    let mid := (lo + hi) / 2
    have hmid : mid = (lo + hi) / 2 := rfl
    if (expPoint mid).hi ≤ q then
      logBisectCore q mid hi (by linarith [hmid]) n
    else if q ≤ (expPoint mid).lo then
      logBisectCore q lo mid (by linarith [hmid]) n
    else
      logBisectCore q lo hi h n

/-- Number of bisection iterations. -/
def logIterations : ℕ := 50

-- ============================================================================
-- logPoint
-- ============================================================================

/-- Point interval containing `log(q)` for rational `q > 0`.

    Initial bracket: `[-(Nat.log 2 q.den + 1), Nat.log 2 q.num.natAbs + 1]`.
    This uses bit lengths instead of raw values, giving a bracket width
    proportional to `log₂(q)` rather than `q` itself — critical for
    large-denominator rationals from interval arithmetic chains.

    Lower: `exp(-(log₂ d + 1)) < 1/d ≤ q` since `d < 2^(log₂ d + 1) ≤ exp(log₂ d + 1)`.
    Upper: `q ≤ p ≤ exp(log₂ p + 1)` by the same argument.

    50 bisection iterations narrow this to precision `bracket_width / 2^50`. -/
def logPoint (q : ℚ) (_hq : 0 < q) : QInterval :=
  -- Special case: log(1) = 0 exactly. This is the only rational q with
  -- log(q) ∈ ℚ (by Lindemann-Weierstrass), so the bisection stalls here
  -- because exp(0) = 1 = q and the Padé interval straddles the target.
  if q = 1 then QInterval.exact 0
  else
  let lo₀ : ℚ := -(↑(Nat.log 2 q.den + 1) : ℚ)
  let hi₀ : ℚ := ↑(Nat.log 2 q.num.natAbs + 1)
  have hle₀ : lo₀ ≤ hi₀ := by
    show -(↑(Nat.log 2 q.den + 1) : ℚ) ≤ ↑(Nat.log 2 q.num.natAbs + 1)
    have : (0 : ℚ) ≤ ↑(Nat.log 2 q.den + 1) := Nat.cast_nonneg _
    have : (0 : ℚ) ≤ ↑(Nat.log 2 q.num.natAbs + 1) := Nat.cast_nonneg _
    linarith
  let ⟨(lo, hi), hle⟩ := logBisectCore q lo₀ hi₀ hle₀ logIterations
  ⟨lo, hi, hle⟩

/-- n ≤ exp(n) for natural numbers, since exp(x) ≥ 1 + x ≥ x. -/
private theorem nat_le_exp (n : ℕ) : (↑n : ℝ) ≤ Real.exp (↑n : ℝ) :=
  le_trans (le_add_of_nonneg_right zero_le_one) (Real.add_one_le_exp _)

/-- 2^k ≤ exp(k) for natural k, since exp(1) ≥ 2 and exp is multiplicative. -/
private theorem pow2_le_exp (k : ℕ) : (2 : ℝ) ^ k ≤ Real.exp (↑k : ℝ) := by
  induction k with
  | zero => simp [Real.exp_zero]
  | succ n ih =>
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc (2 : ℝ) ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
      _ = 2 * 2 ^ n := by ring
      _ ≤ Real.exp 1 * Real.exp (↑n) := mul_le_mul h2 ih (pow_nonneg (by norm_num) n)
            (Real.exp_nonneg _)
      _ = Real.exp (1 + ↑n) := (Real.exp_add 1 ↑n).symm
      _ = Real.exp (↑(n + 1) : ℝ) := by push_cast; ring_nf

/-- n < exp(Nat.log 2 n + 1) for positive n, using n < 2^(log₂ n + 1) ≤ exp(log₂ n + 1). -/
private theorem lt_exp_log2_succ (n : ℕ) (_hn : 0 < n) :
    (↑n : ℝ) < Real.exp (↑(Nat.log 2 n + 1) : ℝ) := by
  have h1 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  calc (↑n : ℝ) < ↑(2 ^ (Nat.log 2 n + 1) : ℕ) := by exact_mod_cast h1
    _ = (2 : ℝ) ^ (Nat.log 2 n + 1) := by push_cast; ring
    _ ≤ Real.exp (↑(Nat.log 2 n + 1) : ℝ) := pow2_le_exp _

/-- logBisectCore preserves the bisection invariant exp(lo) ≤ q ≤ exp(hi). -/
private theorem logBisectCore_sound (q : ℚ) (lo hi : ℚ) (hle : lo ≤ hi) (n : ℕ)
    (h_lo : Real.exp (↑lo : ℝ) ≤ ↑q) (h_hi : (↑q : ℝ) ≤ Real.exp (↑hi : ℝ)) :
    Real.exp (↑(logBisectCore q lo hi hle n).val.1 : ℝ) ≤ ↑q ∧
    (↑q : ℝ) ≤ Real.exp (↑(logBisectCore q lo hi hle n).val.2 : ℝ) := by
  induction n generalizing lo hi with
  | zero => simp [logBisectCore]; exact ⟨h_lo, h_hi⟩
  | succ n ih =>
    simp only [logBisectCore]
    split
    · rename_i h_mid_le
      exact ih _ _ _
        (le_trans (expPoint_containsReal _).2 (by exact_mod_cast h_mid_le)) h_hi
    · split
      · rename_i _ h_le_mid
        exact ih _ _ _ h_lo
          (le_trans (by exact_mod_cast h_le_mid) (expPoint_containsReal _).1)
      · exact ih _ _ _ h_lo h_hi

/-- Initial lower bracket: exp(-(Nat.log 2 den + 1)) ≤ q for q > 0.
    Since den < 2^(log₂ den + 1) ≤ exp(log₂ den + 1), we get
    exp(-(log₂ den + 1)) ≤ 1/den ≤ q. -/
private theorem initial_lower_bound (q : ℚ) (hq : 0 < q) :
    Real.exp (↑(-(↑(Nat.log 2 q.den + 1) : ℚ)) : ℝ) ≤ (↑q : ℝ) := by
  have hd_pos : (0 : ℝ) < ↑q.den := by exact_mod_cast Nat.cast_pos.mpr q.pos
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq
  have hd_lt_exp : (↑q.den : ℝ) < Real.exp (↑(Nat.log 2 q.den + 1) : ℝ) :=
    lt_exp_log2_succ q.den q.pos
  have hgoal : Real.exp (-(↑(Nat.log 2 q.den + 1) : ℝ)) ≤ (↑q : ℝ) := by
    calc Real.exp (-(↑(Nat.log 2 q.den + 1) : ℝ))
        = (Real.exp (↑(Nat.log 2 q.den + 1) : ℝ))⁻¹ := Real.exp_neg _
      _ ≤ (↑q.den : ℝ)⁻¹ := inv_anti₀ hd_pos hd_lt_exp.le
      _ = 1 / (↑q.den : ℝ) := (one_div (↑q.den : ℝ)).symm
      _ ≤ ↑q.num / ↑q.den := by
          apply div_le_div_of_nonneg_right _ hd_pos.le
          exact_mod_cast hnum_pos
      _ = ↑q := by exact_mod_cast Rat.num_div_den q
  simp only [Rat.cast_neg, Rat.cast_natCast] at hgoal ⊢
  exact hgoal

/-- Initial upper bracket: q ≤ exp(Nat.log 2 num + 1) for q > 0. -/
private theorem initial_upper_bound (q : ℚ) (hq : 0 < q) :
    (↑q : ℝ) ≤ Real.exp (↑(↑(Nat.log 2 q.num.natAbs + 1) : ℚ) : ℝ) := by
  have hnum_pos : 0 < q.num := Rat.num_pos.mpr hq
  have hna_pos : 0 < q.num.natAbs := Int.natAbs_pos.mpr (ne_of_gt hnum_pos)
  have h_q_le : q ≤ (↑q.num.natAbs : ℚ) := by
    have h1 : q * ↑q.den = ↑q.num := by exact_mod_cast Rat.mul_den_eq_num q
    have h2 : (1 : ℚ) ≤ ↑q.den := by exact_mod_cast q.pos
    have h3 : q ≤ q * ↑q.den :=
      le_mul_of_one_le_right (le_of_lt (by exact_mod_cast hq)) h2
    have h4 : q ≤ ↑q.num := by linarith
    exact le_trans h4 (by
      show (↑q.num : ℚ) ≤ ↑(↑q.num.natAbs : ℤ)
      exact_mod_cast le_of_eq (Int.natAbs_of_nonneg hnum_pos.le).symm)
  have hgoal : (↑q : ℝ) ≤ Real.exp (↑(Nat.log 2 q.num.natAbs + 1) : ℝ) := by
    calc (↑q : ℝ) ≤ (↑q.num.natAbs : ℝ) := by exact_mod_cast h_q_le
      _ ≤ Real.exp (↑(Nat.log 2 q.num.natAbs + 1) : ℝ) :=
            le_of_lt (lt_exp_log2_succ q.num.natAbs hna_pos)
  simp only [Rat.cast_natCast] at hgoal ⊢
  exact hgoal

/-- Containment theorem for logPoint: the bisection invariant exp(lo) ≤ q ≤ exp(hi)
    implies lo ≤ log(q) ≤ hi by monotonicity of log. -/
theorem logPoint_containsReal (q : ℚ) (hq : 0 < q) :
    (logPoint q hq).containsReal (Real.log (↑q : ℝ)) := by
  unfold logPoint
  simp only []
  split
  · -- q = 1: exact 0 contains log(1) = 0
    subst ‹q = 1›
    simp [QInterval.exact, QInterval.containsReal, Real.log_one]
  · -- q ≠ 1: bisection
    simp only [QInterval.containsReal]
    have hle₀ : -(↑(Nat.log 2 q.den + 1) : ℚ) ≤ (↑(Nat.log 2 q.num.natAbs + 1) : ℚ) := by
      linarith [Nat.cast_nonneg (α := ℚ) (Nat.log 2 q.den + 1),
                Nat.cast_nonneg (α := ℚ) (Nat.log 2 q.num.natAbs + 1)]
    have hsound := logBisectCore_sound q
        (-(↑(Nat.log 2 q.den + 1) : ℚ)) (↑(Nat.log 2 q.num.natAbs + 1)) hle₀
        logIterations (initial_lower_bound q hq) (initial_upper_bound q hq)
    have hq_pos : (0 : ℝ) < ↑q := by exact_mod_cast hq
    constructor
    · -- lo ≤ log(q): from exp(lo) ≤ q, take log
      have h := Real.log_le_log (Real.exp_pos _) hsound.1
      rwa [Real.log_exp] at h
    · -- log(q) ≤ hi: from q ≤ exp(hi), take log
      have h := Real.log_le_log hq_pos hsound.2
      rwa [Real.log_exp] at h

-- ============================================================================
-- logInterval
-- ============================================================================

/-- Interval containing `log(x)` for `x` in a positive rational interval `I`.

    Uses monotonicity of log: for `x ∈ [lo, hi]` with `lo > 0`,
      `log(lo) ≤ log(x) ≤ log(hi)`
    so `log(x) ∈ [logPoint(lo).lo, logPoint(hi).hi]`. -/
def logInterval (I : QInterval) (hI : 0 < I.lo) : QInterval where
  lo := (logPoint I.lo hI).lo
  hi := (logPoint I.hi (lt_of_lt_of_le hI I.valid)).hi
  valid := by
    have hlog_lo := logPoint_containsReal I.lo hI
    have hlog_hi := logPoint_containsReal I.hi (lt_of_lt_of_le hI I.valid)
    have hmon : Real.log (↑I.lo : ℝ) ≤ Real.log (↑I.hi : ℝ) :=
      Real.log_le_log (by exact_mod_cast hI) (by exact_mod_cast I.valid)
    have h : (↑(logPoint I.lo hI).lo : ℝ) ≤
        ↑(logPoint I.hi (lt_of_lt_of_le hI I.valid)).hi :=
      le_trans (le_trans hlog_lo.1 hmon) hlog_hi.2
    exact_mod_cast h

/-- Containment theorem for logInterval: monotonicity of log + logPoint containment. -/
theorem logInterval_containsReal {I : QInterval} {x : ℝ}
    (hI : 0 < I.lo) (hx : I.containsReal x) :
    (logInterval I hI).containsReal (Real.log x) := by
  simp only [logInterval, QInterval.containsReal]
  have hx_pos : (0 : ℝ) < x := lt_of_lt_of_le (by exact_mod_cast hI) hx.1
  have hlog_lo := logPoint_containsReal I.lo hI
  have hlog_hi := logPoint_containsReal I.hi (lt_of_lt_of_le hI I.valid)
  constructor
  · exact le_trans hlog_lo.1 (Real.log_le_log (by exact_mod_cast hI) hx.1)
  · exact le_trans (Real.log_le_log hx_pos hx.2) hlog_hi.2

/-- When the argument is known to be zero (from interval [0,0]),
    `Real.log x = Real.log 0 = 0`, contained in `exact 0`. -/
theorem log_zero_containsReal {I : QInterval} {x : ℝ}
    (hx : I.containsReal x) (hlo : 0 ≤ I.lo) (hhi : I.hi ≤ 0) :
    (QInterval.exact 0).containsReal (Real.log x) := by
  have : x = 0 := QInterval.eq_zero_of_contained_nonneg hx hlo hhi
  rw [this, Real.log_zero]
  exact QInterval.exact_zero_containsReal

end Interval

-- ============================================================================
-- SqrtInterval: Real.sqrt = exp(log/2)
-- ============================================================================

namespace Interval

open Interval.QInterval

/-- Interval square root for positive intervals.
    Uses the identity `√x = exp(log(x) / 2)` for `x > 0`.
    Chains `logInterval`, rational halving, and `expInterval`. -/
def sqrtInterval (a : QInterval) (ha : 0 < a.lo) : QInterval :=
  let logA := logInterval a ha
  let halfLog : QInterval := {
    lo := logA.lo / 2,
    hi := logA.hi / 2,
    valid := by linarith [logA.valid]
  }
  expInterval halfLog

/-- Soundness: if `x ∈ [a.lo, a.hi]` and `a.lo > 0`, then `√x ∈ sqrtInterval a`. -/
theorem sqrtInterval_containsReal {a : QInterval} {x : ℝ}
    (ha : 0 < a.lo) (hx : a.containsReal x) :
    (sqrtInterval a ha).containsReal (Real.sqrt x) := by
  have hx_pos : 0 < x := lt_of_lt_of_le (by exact_mod_cast ha) hx.1
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx_pos]
  unfold sqrtInterval
  apply expInterval_containsReal
  have hlog := logInterval_containsReal ha hx
  simp only [containsReal]
  push_cast
  constructor <;> nlinarith [hlog.1, hlog.2]

end Interval

-- ============================================================================
-- rpow specials: nat exponent + edge cases
-- ============================================================================

namespace Interval

open Interval.QInterval

-- ============================================================================
-- rpow for natural exponents
-- ============================================================================

/-- Exact rational power for nonneg intervals: [lo^n, hi^n].
    Requires 0 ≤ lo (so the interval is nonneg) and n : ℕ.
    Exact — no approximation error.

    Thin wrapper around `QInterval.rpowNat`; kept under `Interval` namespace so
    rpow-shaped consumers (RSA reflection backend) call it directly. -/
def rpowNat (a : QInterval) (n : ℕ) (ha : 0 ≤ a.lo) : QInterval :=
  a.rpowNat n ha

theorem rpowNat_containsReal {a : QInterval} {x : ℝ} {n : ℕ}
    (ha : 0 ≤ a.lo) (hx : a.containsReal x) :
    (rpowNat a n ha).containsReal (x ^ (↑n : ℝ)) := by
  rw [Real.rpow_natCast]
  exact QInterval.powNat_containsReal n ha hx

-- ============================================================================
-- Special cases
-- ============================================================================

/-- Interval for rpow(x, 0) = [1, 1]. -/
def rpowZero : QInterval := QInterval.exact 1

theorem rpowZero_containsReal (x : ℝ) :
    rpowZero.containsReal (x ^ (0 : ℝ)) := by
  simp only [rpowZero, Real.rpow_zero]
  exact_mod_cast QInterval.exact_containsReal 1

/-- For rpow(x, 1) with x ∈ interval a, the result is just a. -/
theorem rpowOne_containsReal {a : QInterval} {x : ℝ}
    (_ha : 0 ≤ a.lo) (hx : a.containsReal x) :
    a.containsReal (x ^ (1 : ℝ)) := by
  rw [Real.rpow_one]
  exact hx

end Interval
