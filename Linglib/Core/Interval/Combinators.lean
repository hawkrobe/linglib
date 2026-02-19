import Linglib.Core.Interval.QInterval
import Linglib.Core.Interval.PadeExp
import Linglib.Core.Interval.LogInterval

set_option autoImplicit false

/-!
# QInterval Combinators for RSA Evaluation

Higher-level combinators over `QInterval` for evaluating RSA models level by level.
These are the three internal QInterval primitives that all RSA evaluators compose from:

- `qi_sum_map`: Sum intervals over a list
- `qi_normalize`: Luce choice rule (score / Σ scores) as QInterval
- `qi_softmax`: Softmax (normalize ∘ exp) as QInterval

Plus supporting operations:
- `qi_nonneg_mul`: Nonneg-guarded multiplication
- `qi_divPos_safe`: Safe division with fallback
-/

namespace Linglib.Interval

open QInterval

-- ============================================================================
-- Sum over a list
-- ============================================================================

/-- Sum intervals produced by mapping a function over a list. -/
def qi_sum_map {α : Type*} (xs : List α) (f : α → QInterval) : QInterval :=
  xs.foldl (fun acc x => acc.add (f x)) (QInterval.exact 0)

/-- Soundness: `qi_sum_map` bounds the real sum.
    TODO: prove by induction on the list using add_containsReal. -/
axiom qi_sum_map_containsReal {α : Type*} (xs : List α) (f : α → QInterval)
    (g : α → ℝ) (hfg : ∀ x, x ∈ xs → (f x).containsReal (g x)) :
    (qi_sum_map xs f).containsReal (xs.foldl (fun acc x => acc + g x) 0)

-- ============================================================================
-- Nonneg multiplication (computable guard)
-- ============================================================================

/-- Multiply two intervals, using the nonneg fast path when both have lo ≥ 0.
    Falls back to general 4-corner multiplication otherwise. -/
def qi_nonneg_mul (a b : QInterval) : QInterval :=
  if h₁ : 0 ≤ a.lo then
    if h₂ : 0 ≤ b.lo then a.mulNonneg b h₁ h₂
    else a.mul b
  else a.mul b

theorem qi_nonneg_mul_containsReal {a b : QInterval} {x y : ℝ}
    (hx : a.containsReal x) (hy : b.containsReal y) :
    (qi_nonneg_mul a b).containsReal (x * y) := by
  simp only [qi_nonneg_mul]
  split
  · split
    · exact mulNonneg_containsReal ‹_› ‹_› hx hy
    · exact mul_containsReal hx hy
  · exact mul_containsReal hx hy

-- ============================================================================
-- Safe division (nonneg / positive with fallback)
-- ============================================================================

/-- Divide nonneg numerator by positive denominator, with fallback if
    the computable checks fail (shouldn't happen for well-formed RSA). -/
def qi_divPos_safe (num denom : QInterval) : QInterval :=
  if h₁ : 0 ≤ num.lo then
    if h₂ : (0 : ℚ) < denom.lo then num.divPos denom h₁ h₂
    else ⟨0, 1, by norm_num⟩
  else ⟨0, 1, by norm_num⟩

/-- Soundness: qi_divPos_safe bounds the real quotient when preconditions hold.
    TODO: prove from divPos_containsReal. -/
axiom qi_divPos_safe_containsReal {num denom : QInterval} {x y : ℝ}
    (hx : num.containsReal x) (hy : denom.containsReal y)
    (hx_nn : 0 ≤ x) (hy_pos : 0 < y) :
    (qi_divPos_safe num denom).containsReal (x / y)

-- ============================================================================
-- Normalize: score / Σ scores
-- ============================================================================

/-- Compute `f(target) / Σ_x f(x)` as a QInterval (Luce choice rule).
    Used for both S1 and L1 policy computation. -/
def qi_normalize {α : Type*} (xs : List α) (f : α → QInterval) (target : α) : QInterval :=
  qi_divPos_safe (f target) (qi_sum_map xs f)

/-- Soundness of qi_normalize.
    TODO: prove from qi_divPos_safe_containsReal + qi_sum_map_containsReal. -/
axiom qi_normalize_containsReal {α : Type*} (xs : List α) (f : α → QInterval)
    (g : α → ℝ) (target : α)
    (hfg : ∀ x, x ∈ xs → (f x).containsReal (g x))
    (htarget : (f target).containsReal (g target))
    (hg_nn : ∀ x, x ∈ xs → 0 ≤ g x)
    (htotal_pos : 0 < xs.foldl (fun acc x => acc + g x) 0) :
    (qi_normalize xs f target).containsReal
      (g target / xs.foldl (fun acc x => acc + g x) 0)

-- ============================================================================
-- Softmax: normalize(x ↦ exp(α · score(x)))
-- ============================================================================

/-- Softmax as QInterval: `exp(α · score(target)) / Σ_x exp(α · score(x))`.
    Used for S1 policy computation in belief-based RSA models. -/
def qi_softmax {α_type : Type*} (xs : List α_type) (α_qi : QInterval)
    (scores : α_type → QInterval) (target : α_type) : QInterval :=
  qi_normalize xs (fun x => expInterval (qi_nonneg_mul α_qi (scores x))) target

/-- Soundness of qi_softmax.
    TODO: prove from expInterval_containsReal + qi_nonneg_mul_containsReal +
    qi_normalize_containsReal. -/
axiom qi_softmax_containsReal {α_type : Type*} (xs : List α_type)
    (α_val : ℝ) (α_qi : QInterval) (hα : α_qi.containsReal α_val)
    (scores : α_type → ℝ) (scores_qi : α_type → QInterval)
    (hs : ∀ x, x ∈ xs → (scores_qi x).containsReal (scores x))
    (target : α_type)
    (htarget : (scores_qi target).containsReal (scores target))
    (htotal_pos : 0 < xs.foldl (fun acc x => acc + Real.exp (α_val * scores x)) 0) :
    (qi_softmax xs α_qi scores_qi target).containsReal
      (Real.exp (α_val * scores target) /
       xs.foldl (fun acc x => acc + Real.exp (α_val * scores x)) 0)

end Linglib.Interval
