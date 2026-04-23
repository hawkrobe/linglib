import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Tactic.NormNum

/-!
# Probability Distributions
@cite{goodman-stuhlmuller-2013} @cite{herbstritt-franke-2019}

General-purpose discrete probability distributions used across RSA models.

## Hypergeometric Distribution

The hypergeometric distribution describes sampling without replacement from
a finite population. It is the observation model in urn-based RSA scenarios:

    P(k | N, K, n) = C(K, k) · C(N−K, n−k) / C(N, n)

where N = population size, K = success states, n = draws, k = observed successes.

Used by:
- @cite{goodman-stuhlmuller-2013}: speaker observation of 3 objects (N=3)
- @cite{herbstritt-franke-2019}: urn-based probability expressions (N=10)

The general formula replaces paper-specific match tables (e.g., `obsPriorTable`
in `GoodmanStuhlmuller2013.lean`), enabling reuse across RSA models with
different population sizes.
-/

set_option autoImplicit false

namespace Core.Distributions

-- ============================================================================
-- §1. Hypergeometric PMF
-- ============================================================================

/-- Hypergeometric PMF: probability of drawing exactly `k` successes
    in `n` draws without replacement from a population of `N` items
    containing `K` successes.

    P(k | N, K, n) = C(K, k) · C(N−K, n−k) / C(N, n)

    Returns 0 for impossible combinations (k > K, k > n, n−k > N−K, n > N)
    because `Nat.choose a b = 0` when `b > a`. Division by zero (when
    n > N) yields 0 in ℚ, which is the correct probability. -/
def hypergeometric (N K n k : ℕ) : ℚ :=
  (↑(Nat.choose K k * Nat.choose (N - K) (n - k)) : ℚ) / ↑(Nat.choose N n)

-- ============================================================================
-- §2. Properties
-- ============================================================================

/-- Hypergeometric probabilities are non-negative. -/
theorem hypergeometric_nonneg (N K n k : ℕ) :
    0 ≤ hypergeometric N K n k := by
  unfold hypergeometric
  apply div_nonneg <;> exact_mod_cast Nat.zero_le _

-- ============================================================================
-- §3. Concrete examples (verification)
-- ============================================================================

/-- Drawing 1 success from 3 with 2 successes in 1 draw: C(2,1)·C(1,0)/C(3,1) = 2/3.
    Matches `obsPriorTable .a1 .s2 .o1a1` in @cite{goodman-stuhlmuller-2013}. -/
example : hypergeometric 3 2 1 1 = 2/3 := by unfold hypergeometric; simp [Nat.choose]

/-- Drawing 0 successes from 3 with 1 success in 2 draws: C(1,0)·C(2,2)/C(3,2) = 1/3.
    Matches `obsPriorTable .a2 .s1 .o0a2`. -/
example : hypergeometric 3 1 2 0 = 1/3 := by unfold hypergeometric; simp [Nat.choose]

/-- Full access, exact match: C(2,2)·C(1,1)/C(3,3) = 1.
    Matches `obsPriorTable .a3 .s2 .o2a3 = 1`. -/
example : hypergeometric 3 2 3 2 = 1 := by unfold hypergeometric; simp [Nat.choose]

/-- N=10 urn: drawing 3 red from 5 total red in 4 draws.
    C(5,3)·C(5,1)/C(10,4) = 10·5/210 = 50/210 = 5/21. -/
example : hypergeometric 10 5 4 3 = 5/21 := by
  unfold hypergeometric; simp [Nat.choose]; norm_num

/-- N=10 urn: drawing 0 red from 0 total red in 8 draws.
    C(0,0)·C(10,8)/C(10,8) = 1·45/45 = 1. -/
example : hypergeometric 10 0 8 0 = 1 := by unfold hypergeometric; simp [Nat.choose]

/-- Impossible draw: 5 red from 3 total red. -/
example : hypergeometric 10 3 8 5 = 0 := by unfold hypergeometric; simp [Nat.choose]

end Core.Distributions
