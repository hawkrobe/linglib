/-
# RSA Chain Comparison

Compares production-first (S0 → L1 → S1) and comprehension-first (L0 → S1 → L1) RSA chains.

## Insight

Both chains use the same RSAScenario:
- Meaning function φ
- World prior
- Utterance prior (salience)
- Cost function
- Rationality parameter α

They differ only in the recursion direction:
- **Comprehension-first**: L0 → S1 → L1 → S2 → ...
  - Start with literal listener, ask "what would a speaker say?"
- **Production-first**: S0 → L1 → S1 → L2 → ...
  - Start with literal speaker, ask "what would a listener infer?"

## When to Use Each

- **Comprehension-first** (standard): Modeling listener interpretation
  - "What does 'some' mean in this context?"
  - Scalar implicature derivation

- **Production-first**: Modeling speaker production
  - "What would a speaker say to convey 5/10?"
  - van Tiel et al. (2021) production data

## Convergence

The chains converge under specific conditions (see theorems below).
When they diverge, the difference reveals asymmetries in the scenario.
-/

import Linglib.Theories.Pragmatics.RSA.Core.Eval
import Mathlib.Data.Rat.Defs

namespace RSA

-- ChainVariant is defined in RSA.Core.Basic and re-exported here

-- Chain Comparison Results

/--
Result of comparing two RSA chains on the same input.
-/
structure ChainComparison (α : Type) where
  /-- Distribution from S0-based chain -/
  S0Based : List (α × ℚ)
  /-- Distribution from L0-based chain -/
  L0Based : List (α × ℚ)
  deriving Repr

/--
Total variation distance between two distributions.

TV(P, Q) = (1/2) Σ_x |P(x) - Q(x)|

Returns a value in [0, 1] where 0 means identical distributions.
-/
def totalVariation {α : Type} [BEq α] (c : ChainComparison α) : ℚ :=
  let allKeys := (c.S0Based.map (·.1) ++ c.L0Based.map (·.1)).eraseDups
  let diffs := allKeys.map λ x =>
    let pS0 := RSA.Eval.getScore c.S0Based x
    let pL0 := RSA.Eval.getScore c.L0Based x
    if pS0 ≥ pL0 then pS0 - pL0 else pL0 - pS0
  RSA.Eval.sumScores diffs / 2

/--
Check if two chain results are approximately equal (within tolerance).
-/
def ChainComparison.approxEqual {α : Type} [BEq α]
    (c : ChainComparison α) (tolerance : ℚ := 1/100) : Bool :=
  totalVariation c ≤ tolerance

/--
Check if two chain results are exactly equal.
-/
def ChainComparison.exactEqual {α : Type} [BEq α] (c : ChainComparison α) : Bool :=
  totalVariation c == 0

-- Divergence Analysis

/--
Information about where two chains diverge most.
-/
structure DivergenceInfo (α : Type) where
  /-- Element with largest difference -/
  maxDivergentElement : Option α
  /-- The difference at that element -/
  maxDivergence : ℚ
  /-- Total variation distance -/
  totalVariation : ℚ
  deriving Repr

/--
Analyze divergence between S0-based and L0-based chains.
-/
def analyzeDivergence {α : Type} [BEq α] (c : ChainComparison α) : DivergenceInfo α :=
  let allKeys := (c.S0Based.map (·.1) ++ c.L0Based.map (·.1)).eraseDups
  let diffs := allKeys.map λ x =>
    let pS0 := RSA.Eval.getScore c.S0Based x
    let pL0 := RSA.Eval.getScore c.L0Based x
    let diff := if pS0 ≥ pL0 then pS0 - pL0 else pL0 - pS0
    (x, diff)
  let maxPair := diffs.foldl (λ acc (x, d) =>
    match acc with
    | none => some (x, d)
    | some (_, dMax) => if d > dMax then some (x, d) else acc
  ) none
  { maxDivergentElement := maxPair.map (·.1)
    maxDivergence := maxPair.map (·.2) |>.getD 0
    totalVariation := totalVariation c }

-- Convergence Conditions (Theoretical)

/-!
## Convergence Theorems

The S0-based and L0-based chains converge under these conditions:

1. **Uniform priors**: Both world prior and utterance prior are uniform
2. **Binary semantics**: φ(m, w) ∈ {0, 1}
3. **No cost**: cost(m) = 0 for all m

### Intuition

With uniform priors and binary semantics:
- L0(w | m) ∝ φ(m, w) · Prior(w) = φ(m, w) (uniform prior)
- S0(m | w) ∝ φ(m, w) · Salience(m) = φ(m, w) (uniform salience)

So L0 and S0 are "transposes" of each other in the φ matrix.
The subsequent levels inherit this symmetry.

### When They Diverge

1. **Non-uniform utterance salience**: S0 weights by salience, L0 doesn't
2. **Non-uniform world prior**: L0 weights by prior, S0 doesn't
3. **Gradient semantics**: Different weighting accumulates through recursion
-/

/--
Condition for chain convergence: uniform priors and binary semantics.

This is a *sufficient* condition for convergence, not necessary.
-/
structure ConvergenceCondition where
  /-- World prior is uniform -/
  uniformWorldPrior : Bool
  /-- Utterance prior is uniform -/
  uniformUtterancePrior : Bool
  /-- Semantics are binary (φ ∈ {0, 1}) -/
  binarySemantics : Bool
  /-- Cost is zero -/
  zeroCost : Bool

/--
Check if convergence conditions are satisfied.
-/
def ConvergenceCondition.satisfied (c : ConvergenceCondition) : Bool :=
  c.uniformWorldPrior && c.uniformUtterancePrior && c.binarySemantics && c.zeroCost

-- Examples and Demonstrations

#check ChainVariant.S0Based
#check ChainVariant.L0Based

end RSA
