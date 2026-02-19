import Mathlib.Algebra.Order.Ring.Rat

/-!
# Information-Theoretic Primitives (ℚ-valued)

Domain-agnostic information-theoretic functions over rational numbers, suitable
for decidable computation. These are used by both pragmatic models (RSA) and
morphological complexity metrics (Ackerman & Malouf 2013).

For ℝ-valued proofs (non-negativity, max-entropy bounds, Gibbs VP), see
`Core/RationalAction.lean`.

## Main definitions

- `log2Approx`: rational approximation of log₂
- `entropy`: Shannon entropy H(X)
- `conditionalEntropy`: H(Y|X) = H(X,Y) - H(X)
- `mutualInformation`: I(X;Y) = H(X) + H(Y) - H(X,Y)

## References

- Cover, T. M. & Thomas, J. A. (2006). Elements of Information Theory.
- Ackerman, F. & Malouf, R. (2013). Morphological Organization: The Low
  Conditional Entropy Conjecture. Language 89(3), 429–464.
-/

namespace Core.InformationTheory

/-- Natural logarithm approximated as a rational (for decidable proofs).

We use a simple linear approximation log₂(x) ≈ (x - 1) / (x + 1) * 2.885.
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

Note: 0 log 0 is defined as 0 (standard convention). -/
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

end Core.InformationTheory
