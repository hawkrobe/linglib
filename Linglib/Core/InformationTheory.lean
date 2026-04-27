import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators

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

## Mathlib-canonical form

Following mathlib's `Finset.sum` discipline, all entropy-family functions
take a `Finset α` (the support) plus a probability function `α → ℝ`. This
matches mathlib's pattern (cf. `Finset.sum`, `MeasureTheory.integral`):
ONE canonical type-indexed form, not parallel implementations.

For the function-indexed version over a `Fintype` use
`entropy Finset.univ p`. For ad-hoc list-of-pairs distributions
common in study files, `Finset.image Prod.fst dist.toFinset` extracts the
support and `fun a => (dist.find? (·.1 = a)).map Prod.snd |>.getD 0`
extracts the function (or just refactor the upstream definition to
return `(Finset α, α → ℝ)` directly).

## Main definitions

- `entropy s p`: Shannon entropy `H(p) = ∑ a ∈ s, negMulLog (p a)`
- `conditionalEntropy s sj joint marginalX`: H(Y|X) = H(X,Y) - H(X)
- `mutualInformation`: I(X;Y) = H(X) + H(Y) - H(X,Y)
- `jsdOf s p q`: Jensen-Shannon divergence
- `deltaP`: ΔP directional association measure (ℚ-valued, no log)
- `deltaPCounts`: ΔP from a 2×2 contingency table (ℚ-valued, no log)
-/

namespace Core.InformationTheory

open Real

/-! ## Shannon entropy — Finset-and-function form

Mathlib-canonical shape: `(Finset α, α → ℝ) → ℝ` via `∑ a ∈ s, negMulLog (p a)`.
The mathlib convention `0 · log 0 = 0` is built into `Real.negMulLog`. -/

/-- Shannon entropy of a probability function over a finite support (in nats):

    `H(p) = -Σ_{a ∈ s} p(a) log p(a) = Σ_{a ∈ s} negMulLog(p(a))`.

    Mathlib-canonical form: take the support as a `Finset` and the probability
    as a function. For `[Fintype α]`, use `Finset.univ` for the support. -/
noncomputable def entropy {α : Type*} (s : Finset α) (p : α → ℝ) : ℝ :=
  ∑ a ∈ s, Real.negMulLog (p a)

/-- Entropy is non-negative for probability distributions on the support. -/
theorem entropy_nonneg {α : Type*} (s : Finset α) (p : α → ℝ)
    (hp_nonneg : ∀ a ∈ s, 0 ≤ p a) (hp_sum : ∑ a ∈ s, p a = 1) :
    0 ≤ entropy s p :=
  Finset.sum_nonneg fun a ha =>
    Real.negMulLog_nonneg (hp_nonneg a ha)
      (le_trans (Finset.single_le_sum (f := p)
        (fun b hb => hp_nonneg b hb) ha) hp_sum.le)

/-- Entropy of the uniform distribution `p ≡ 1/|s|` over a non-empty `s`. -/
theorem entropy_uniform {α : Type*} (s : Finset α) (h : s.Nonempty) :
    entropy s (fun _ => 1 / s.card) = log s.card := by
  simp only [entropy, Real.negMulLog]
  have hcard_pos : (0 : ℝ) < s.card := Nat.cast_pos.mpr (Finset.card_pos.mpr h)
  have hne : (s.card : ℝ) ≠ 0 := ne_of_gt hcard_pos
  rw [Finset.sum_const, nsmul_eq_mul,
      log_div one_ne_zero hne, log_one, zero_sub]
  field_simp

/-! ## Mutual information, conditional entropy, JSD

All take the supports as `Finset` and the joint/marginal distributions as
functions, mirroring `entropy`'s shape. -/

/-- Mutual information `I(X;Y) = H(X) + H(Y) - H(X,Y)` (in nats).

    Take the support of joint as `sJoint : Finset (α × β)`, supports of
    marginals as `sX : Finset α` and `sY : Finset β`, and the corresponding
    probability functions. Alternative form: `I(X;Y) = H(X) - H(X|Y)`. -/
noncomputable def mutualInformation {α β : Type*}
    (sJoint : Finset (α × β)) (joint : α × β → ℝ)
    (sX : Finset α) (marginalX : α → ℝ)
    (sY : Finset β) (marginalY : β → ℝ) : ℝ :=
  entropy sX marginalX + entropy sY marginalY -
    entropy sJoint joint

/-- Conditional entropy `H(Y|X) = H(X,Y) - H(X)` (in nats).

    Used by MemorySurprisal for `S_M = H(W_t | M_t)` and by LCEC for
    `H(Cᵢ|Cⱼ)`. -/
noncomputable def conditionalEntropy {α β : Type*}
    (sJoint : Finset (α × β)) (joint : α × β → ℝ)
    (sX : Finset α) (marginalX : α → ℝ) : ℝ :=
  entropy sJoint joint - entropy sX marginalX

/-- Jensen-Shannon divergence over a finite support:

    `JSD(p, q) = H(m) - (H(p) + H(q)) / 2` where `m(a) = (p(a) + q(a)) / 2`.

    Symmetric, bounded, and a metric (after sqrt). In nats. Used for
    grammar distance, register comparison, and anywhere KL divergence's
    asymmetry is undesirable. -/
noncomputable def jsdOf {α : Type*} (s : Finset α) (p q : α → ℝ) : ℝ :=
  entropy s (fun a => (p a + q a) / 2) -
    (entropy s p + entropy s q) / 2

/-! ## ΔP (directional association, no log) -/

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
