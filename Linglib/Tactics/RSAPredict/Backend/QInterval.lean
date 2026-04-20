import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-!
# QInterval — Rational Interval Arithmetic with ℝ Containment

Closed intervals `[lo, hi]` over ℚ, with proofs that arithmetic operations
preserve ℝ containment. This is the foundation for the `rsa_decide` tactic:

1. Reify an ℝ expression into a tree of `QInterval` operations
2. Evaluate the tree to get a concrete `[lo, hi]` (computable ℚ)
3. Check separation `b.hi < a.lo` (decidable on ℚ)
4. Conclude `a > b` on ℝ via `gt_of_separated`
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
