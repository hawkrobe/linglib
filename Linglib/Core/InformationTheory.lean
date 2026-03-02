import Mathlib.Algebra.Order.Ring.Rat

/-!
# Information-Theoretic Primitives (ℚ-valued)
@cite{ackerman-malouf-2013} @cite{cover-thomas-2006} @cite{dunn-2025} @cite{ellis-2006}

Domain-agnostic information-theoretic functions over rational numbers, suitable
for decidable computation. These are used by both pragmatic models (RSA) and
morphological complexity metrics.

For the ℝ-valued counterpart, see `Core.shannonEntropy` in
`Linglib/Core/Agent/RationalAction.lean` (§4), which uses `Real.log` and
supports proofs of non-negativity, max-entropy bounds, and Gibbs VP.

## Main definitions

- `log2Approx`: rational approximation of log₂
- `entropy`: Shannon entropy H(X)
- `conditionalEntropy`: H(Y|X) = H(X,Y) - H(X)
- `mutualInformation`: I(X;Y) = H(X) + H(Y) - H(X,Y)
- `deltaP`: ΔP directional association measure
- `deltaPCounts`: ΔP from a 2×2 contingency table

-/

namespace Core.InformationTheory

/-- Natural logarithm approximated as a rational (for decidable proofs).

We use a simple linear approximation log₂(x) ≈ 3 * (x - 1) / (x + 1).
This is only used for concrete computations; proofs use abstract properties.
For exact proofs about limiting behavior, we would need Mathlib.Analysis. -/
def log2Approx (x : ℚ) : ℚ :=
  if x ≤ 0 then 0
  else
    -- Linear approximation around x=1: log2(x) ≈ 2.885 * (x-1)/(x+1)
    -- Reasonably accurate for 0.5 < x < 2
    let ratio := (x - 1) / (x + 1)
    -- 2.885 ≈ 2/ln(2) but we use 3 for simplicity
    3 * ratio

/-- Shannon entropy of a distribution (in bits).

H(X) = -Σ_x P(x) log P(x)

Note: 0 log 0 is defined as 0 (standard convention).

This is the ℚ counterpart of `Core.shannonEntropy` in `RationalAction.lean`,
using `log2Approx` (rational linear approximation) instead of `Real.log`.
Suitable for decidable computation; for mathematical proofs, use
`shannonEntropy` and its theorems (`shannonEntropy_nonneg`,
`shannonEntropy_le_log_card`, etc.). -/
def entropy {α : Type} [BEq α] (dist : List (α × ℚ)) : ℚ :=
  let terms := dist.map λ (_, p) =>
    if p ≤ 0 then 0
    else -p * log2Approx p
  terms.sum

/-- Mutual information I(X;Y) = H(X) + H(Y) - H(X,Y).

Alternative: I(X;Y) = H(X) - H(X|Y) = H(Y) - H(Y|X) -/
def mutualInformation {α β : Type} [BEq α] [BEq β]
    (joint : List ((α × β) × ℚ))
    (marginalX : List (α × ℚ))
    (marginalY : List (β × ℚ)) : ℚ :=
  entropy marginalX + entropy marginalY - entropy joint

/-- Conditional entropy H(Y|X) = H(X,Y) - H(X).

Used by MemorySurprisal for computing average surprisal S_M = H(W_t | M_t),
and by LCEC for paradigm cell conditional entropy H(Cᵢ|Cⱼ). -/
def conditionalEntropy {α β : Type} [BEq α] [BEq β]
    (joint : List ((α × β) × ℚ))
    (marginalX : List (α × ℚ)) : ℚ :=
  entropy joint - entropy marginalX

/-- Jensen-Shannon divergence over an explicit inventory.

JSD(p, q) = H(m) - (H(p) + H(q)) / 2 where m(x) = (p(x) + q(x)) / 2.
Symmetric, bounded (0 ≤ JSD ≤ 1 bit), and a metric (after sqrt).

Used for grammar distance, register comparison, and anywhere
KL divergence's asymmetry is undesirable. -/
def jsdOf {α : Type} [BEq α] (xs : List α) (p q : α → ℚ) : ℚ :=
  let distP := xs.map fun x => (x, p x)
  let distQ := xs.map fun x => (x, q x)
  let distM := xs.map fun x => (x, (p x + q x) / 2)
  entropy distM - (entropy distP + entropy distQ) / 2

/-- ΔP: directional association measure.

ΔP(x → y) = P(y | x) - P(y | ¬x)

Measures how much knowing x changes the probability of y. Used by
@cite{dunn-2025} to identify constructions from corpus data: a slot-filler
pair (x, y) is constructional when ΔP is high in both directions.

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

/-- ΔP from a 2×2 contingency table.

Given observed counts:

|     |  y  | ¬y  |
|-----|-----|-----|
|  x  |  a  |  b  |
| ¬x  |  c  |  d  |

ΔP(x → y) = a/(a+b) - c/(c+d)

This is the form used in corpus-based CxG: count how often
a filler appears in a slot (a) vs not (b), and how often it appears
elsewhere (c) vs not (d). -/
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
