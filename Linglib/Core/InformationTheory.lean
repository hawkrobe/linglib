import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Information-Theoretic Primitives
@cite{ackerman-malouf-2013} @cite{cheng-holyoak-1995} @cite{cover-thomas-2006}
@cite{dunn-2025} @cite{ellis-2006}

Domain-agnostic information-theoretic functions, used by both pragmatic models
(RSA) and morphological complexity metrics.

The entropy / mutual-information / conditional-entropy / Jensen-Shannon
families are real-valued and route through mathlib's `Real.negMulLog`
(`x ↦ -x · log x`), the canonical Shannon-entropy summand. Entropy is
expressed in **nats** (natural log) — the mathlib convention. To convert
to bits, multiply by `1 / Real.log 2` (or use `Real.logb 2` directly).

For the abstract `(ι → ℝ)`-indexed counterpart with proven non-negativity,
max-entropy bounds, and Gibbs VP, see `Core.shannonEntropy` in
`Linglib/Core/Agent/RationalAction.lean` (§4). Both definitions agree
pointwise via `Real.negMulLog`.

## Main definitions

- `entropy`: Shannon entropy H(X) over a `List (α × ℝ)` of (outcome, prob) pairs
- `conditionalEntropy`: H(Y|X) = H(X,Y) - H(X)
- `mutualInformation`: I(X;Y) = H(X) + H(Y) - H(X,Y)
- `jsdOf`: Jensen-Shannon divergence over an explicit inventory
- `deltaP`: ΔP directional association measure (ℚ-valued, no log)
- `deltaPCounts`: ΔP from a 2×2 contingency table (ℚ-valued, no log)
-/

namespace Core.InformationTheory

open Real

/-- Shannon entropy of a distribution (in nats).

H(X) = -Σ_x P(x) log P(x) = Σ_x negMulLog(P(x))

The convention `0 · log 0 = 0` is built into `Real.negMulLog` (which
returns `0` at `x = 0` because `Real.log 0 = 0` in mathlib).

This is a list-indexed counterpart of `Core.shannonEntropy` in
`RationalAction.lean`; the latter is the function-indexed version with
proven properties (`shannonEntropy_nonneg`, `shannonEntropy_le_log_card`,
Gibbs VP). Use the function-indexed version for proofs over a `Fintype`
domain; use this list-indexed version when the support is given as an
explicit list. -/
noncomputable def entropy {α : Type} (dist : List (α × ℝ)) : ℝ :=
  (dist.map fun (_, p) => Real.negMulLog p).sum

/-- Mutual information I(X;Y) = H(X) + H(Y) - H(X,Y).

Alternative form: I(X;Y) = H(X) - H(X|Y) = H(Y) - H(Y|X). In nats. -/
noncomputable def mutualInformation {α β : Type}
    (joint : List ((α × β) × ℝ))
    (marginalX : List (α × ℝ))
    (marginalY : List (β × ℝ)) : ℝ :=
  entropy marginalX + entropy marginalY - entropy joint

/-- Conditional entropy H(Y|X) = H(X,Y) - H(X), in nats.

Used by MemorySurprisal for computing average surprisal S_M = H(W_t | M_t),
and by LCEC for paradigm cell conditional entropy H(Cᵢ|Cⱼ). -/
noncomputable def conditionalEntropy {α β : Type}
    (joint : List ((α × β) × ℝ))
    (marginalX : List (α × ℝ)) : ℝ :=
  entropy joint - entropy marginalX

/-- Jensen-Shannon divergence over an explicit inventory.

JSD(p, q) = H(m) - (H(p) + H(q)) / 2 where m(x) = (p(x) + q(x)) / 2.
Symmetric, bounded, and a metric (after sqrt). In nats.

Used for grammar distance, register comparison, and anywhere
KL divergence's asymmetry is undesirable. -/
noncomputable def jsdOf {α : Type} (xs : List α) (p q : α → ℝ) : ℝ :=
  let distP := xs.map fun x => (x, p x)
  let distQ := xs.map fun x => (x, q x)
  let distM := xs.map fun x => (x, (p x + q x) / 2)
  entropy distM - (entropy distP + entropy distQ) / 2

/-- ΔP: directional association measure (@cite{ellis-2006}, Table 1;
via @cite{cheng-holyoak-1995} Probabilistic Contrast Model).

ΔP(x → y) = P(y | x) - P(y | ¬x)

Measures how much knowing x changes the probability of y.
@cite{ellis-2006} uses ΔP to explain L2 morpheme acquisition: grammatical
functors with low ΔP (many cue-outcome competitors) are acquired late.
@cite{dunn-2025} uses ΔP to identify constructions from corpus data.

Properties:
- Bounded: ΔP ∈ [-1, 1] for valid probability inputs
- ΔP = 0 when x and y are independent (see `deltaP_eq_zero_of_independent`)
- Directional: ΔP(x→y) ≠ ΔP(y→x) in general

Takes joint probability P(x,y), marginal P(x), and marginal P(y).
Returns the directional association from x to y. -/
def deltaP (pXY pX pY : ℚ) : ℚ :=
  let pYgivenX := if pX ≤ 0 then 0 else pXY / pX
  let pYgivenNotX := if pX ≥ 1 then 0 else (pY - pXY) / (1 - pX)
  pYgivenX - pYgivenNotX

/-- ΔP from a 2×2 contingency table (@cite{ellis-2006}, Table 1).

Given observed counts:

|     |  y  | ¬y  |
|-----|-----|-----|
|  x  |  a  |  b  |
| ¬x  |  c  |  d  |

ΔP(x → y) = a/(a+b) - c/(c+d)

This is the standard form for contingency learning: `a` is the frequency of
cue-outcome co-occurrence, `b` is cue without outcome, `c` is outcome
without cue, `d` is neither. Also used in corpus-based CxG (@cite{dunn-2025})
for slot-filler association strength. -/
def deltaPCounts (a b c d : ℕ) : ℚ :=
  let ab : ℚ := ↑a + ↑b
  let cd : ℚ := ↑c + ↑d
  (if ab = 0 then 0 else ↑a / ab) - (if cd = 0 then 0 else ↑c / cd)

/-- ΔP vanishes under independence: if P(x,y) = P(x)·P(y), then ΔP = 0.

This is the key property: ΔP measures departure from independence.
When slot and filler are statistically independent (knowing the slot
tells you nothing about the filler), ΔP is zero. -/
theorem deltaP_eq_zero_of_independent (pX pY : ℚ)
    (hpX_pos : 0 < pX) (hpX_lt : pX < 1) :
    deltaP (pX * pY) pX pY = 0 := by
  have hne : pX ≠ 0 := (ne_of_lt hpX_pos).symm
  have hne1 : (1 : ℚ) - pX ≠ 0 := sub_ne_zero.mpr (ne_of_lt hpX_lt).symm
  dsimp only [deltaP]
  rw [if_neg (not_le.mpr hpX_pos), if_neg (not_le.mpr hpX_lt)]
  rw [mul_div_cancel_left₀ pY hne]
  rw [show pY - pX * pY = pY * (1 - pX) from by
    rw [mul_sub, mul_one, mul_comm pY pX]]
  rw [mul_div_cancel_right₀ pY hne1, sub_self]

end Core.InformationTheory
