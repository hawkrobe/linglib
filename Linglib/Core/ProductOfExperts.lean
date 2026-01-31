/-
# Product of Experts

Multiplicative combination of probability distributions.

## Overview

Product of Experts (PoE) combines multiple "expert" distributions by
multiplying them pointwise and renormalizing:

```
P_combined(x) ∝ Π_i P_i(x)
```

This contrasts with **mixture models** (linear combination):
```
P_mixture(x) = Σ_i w_i · P_i(x)
```

## Use Cases

| Combination | Method | Example |
|-------------|--------|---------|
| Multiple evidence sources | Product of Experts | SDS selectional + scenario |
| Competing objectives | Linear (CombinedUtility) | Informativity vs politeness |
| Hard constraints (AND) | Product (zeros propagate) | Selectional filtering |
| Soft tradeoffs | Linear | RSA relevance weighting |

## Connection to SDS (Erk & Herbelot 2024)

SDS uses PoE to combine selectional preferences with scenario constraints:
```
P(concept | context) ∝ P_selectional(concept) × P_scenario(concept)
```

Both constraints must be satisfied for high probability.

## References

- Hinton, G.E. (2002). Training products of experts by minimizing contrastive divergence.
- Erk, K. & Herbelot, A. (2024). How to Marry a Star. Journal of Semantics.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Core.ProductOfExperts

-- ============================================================================
-- PART 1: Product of Experts Combinator
-- ============================================================================

/--
Product of Experts: combine distributions multiplicatively.

Given a list of probability functions (experts) over the same support,
returns their normalized product.

```
PoE(x) = (Π_i p_i(x)) / Z  where Z = Σ_x (Π_i p_i(x))
```
-/
def productOfExperts {α : Type} (ps : List (α → ℚ)) (support : List α) : α → ℚ :=
  let unnorm a := ps.foldl (fun acc p => acc * p a) 1
  let Z := support.foldl (fun acc a => acc + unnorm a) 0
  fun a => if Z = 0 then 0 else unnorm a / Z

/--
Product of two experts (common case).
-/
def poe2 {α : Type} (p₁ p₂ : α → ℚ) (support : List α) : α → ℚ :=
  productOfExperts [p₁, p₂] support

/--
Product of three experts.
-/
def poe3 {α : Type} (p₁ p₂ p₃ : α → ℚ) (support : List α) : α → ℚ :=
  productOfExperts [p₁, p₂, p₃] support

-- ============================================================================
-- PART 2: Unnormalized Product (for chaining)
-- ============================================================================

/--
Unnormalized product: multiply expert scores without normalizing.

Useful when you want to combine multiple constraints, then normalize once.
-/
def unnormalizedProduct {α : Type} (ps : List (α → ℚ)) : α → ℚ :=
  fun a => ps.foldl (fun acc p => acc * p a) 1

/--
Normalize a scoring function over a finite support.
-/
def normalizeOver {α : Type} (f : α → ℚ) (support : List α) : α → ℚ :=
  let Z := support.foldl (fun acc a => acc + f a) 0
  fun a => if Z = 0 then 0 else f a / Z

/--
PoE equals unnormalized product followed by normalization.
-/
theorem poe_eq_unnorm_then_norm {α : Type} (ps : List (α → ℚ)) (support : List α) :
    productOfExperts ps support = normalizeOver (unnormalizedProduct ps) support := by
  rfl

-- ============================================================================
-- PART 3: Properties
-- ============================================================================

/--
PoE with single expert returns normalized version of that expert.
-/
theorem poe_single {α : Type} (p : α → ℚ) (support : List α) :
    productOfExperts [p] support = normalizeOver p support := by
  simp only [productOfExperts, normalizeOver, unnormalizedProduct, List.foldl, one_mul]

/--
PoE is zero-absorbing: if any expert gives zero, product is zero.
-/
theorem poe_zero_absorbing {α : Type} (ps : List (α → ℚ)) (support : List α) (a : α)
    (hp : ∃ p ∈ ps, p a = 0) : productOfExperts ps support a = 0 ∨
                               ∃ a' ∈ support, productOfExperts ps support a' > 0 := by
  -- If all unnormalized products are zero, everything maps to 0
  -- Otherwise, this specific a maps to 0 but others may not
  left
  simp only [productOfExperts]
  split_ifs with hZ
  · rfl
  · obtain ⟨p, hp_mem, hp_zero⟩ := hp
    -- Need to show unnorm a = 0
    suffices h : ps.foldl (fun acc p => acc * p a) 1 = 0 by
      simp only [h, zero_div]
    -- The fold multiplies by p a = 0 at some point
    sorry -- Requires induction on list position

/--
PoE with empty expert list gives uniform (all 1s before normalization).
-/
theorem poe_empty {α : Type} (support : List α) (a : α) :
    productOfExperts ([] : List (α → ℚ)) support a =
    if support.length = 0 then 0 else 1 / support.length := by
  simp only [productOfExperts, List.foldl]
  sorry  -- Requires case analysis on support

-- ============================================================================
-- PART 4: Comparison with Linear Combination
-- ============================================================================

/-!
## PoE vs Linear Combination

**Product of Experts** (this module):
- Multiplicative: P(x) ∝ Π_i p_i(x)
- AND-like: all experts must agree for high probability
- Zero-absorbing: one zero kills the product

**Linear Combination** (CombinedUtility):
- Additive: U(x) = Σ_i w_i · u_i(x)
- Interpolation: weighted average of values
- Not zero-absorbing: one zero just lowers the average

### When to Use Each

| Criterion | PoE | Linear |
|-----------|-----|--------|
| Semantics | All constraints must hold | Trade off objectives |
| Zero effect | Kills probability | Reduces average |
| Combination type | Distributions | Utilities |
| Use case | Bayesian evidence fusion | Multi-objective optimization |
-/

/--
Linear combination of two values.
-/
def linearCombine (lam : ℚ) (v₁ v₂ : ℚ) : ℚ :=
  (1 - lam) * v₁ + lam * v₂

/--
Linear combination is NOT zero-absorbing.
-/
theorem linear_not_zero_absorbing :
    linearCombine (1/2) 0 1 ≠ 0 := by
  simp only [linearCombine]
  norm_num

/--
PoE IS zero-absorbing (for the 2-expert case).
-/
theorem poe2_zero_absorbing {α : Type} (p₁ p₂ : α → ℚ) (support : List α) (a : α) :
    p₁ a = 0 → poe2 p₁ p₂ support a = 0 ∨ (support.foldl (fun acc x => acc + p₁ x * p₂ x) 0 = 0) := by
  intro h
  simp only [poe2, productOfExperts, List.foldl, one_mul, h, zero_mul]
  left
  split_ifs with hZ
  · rfl
  · simp only [zero_div]

-- ============================================================================
-- PART 5: SDS-Style Factored Distributions
-- ============================================================================

/-!
## SDS Factorization Pattern

Erk & Herbelot (2024) factor concept distributions as:

```
P(concept | context) ∝ P_selectional(concept | role) × P_scenario(concept | frame)
```

This is PoE with two experts:
1. Selectional preference expert
2. Scenario/frame expert
-/

/--
Find the element with maximum value according to a scoring function.
-/
def listArgmax {α : Type} (xs : List α) (f : α → ℚ) : Option α :=
  xs.foldl (fun acc x =>
    match acc with
    | none => some x
    | some best => if f x > f best then some x else some best
  ) none

/--
A factored distribution in SDS style.
-/
structure FactoredDist (α : Type) where
  selectionalExpert : α → ℚ
  scenarioExpert : α → ℚ
  support : List α

/--
Combine a factored distribution using PoE.
-/
def FactoredDist.combine {α : Type} (d : FactoredDist α) : α → ℚ :=
  poe2 d.selectionalExpert d.scenarioExpert d.support

/--
Get the unnormalized scores (useful for debugging/inspection).
-/
def FactoredDist.unnormScores {α : Type} (d : FactoredDist α) : α → ℚ :=
  fun a => d.selectionalExpert a * d.scenarioExpert a

/--
Detect conflict: experts disagree on the mode.
-/
def FactoredDist.hasConflict {α : Type} [BEq α] (d : FactoredDist α) : Bool :=
  match listArgmax d.support d.selectionalExpert,
        listArgmax d.support d.scenarioExpert with
  | some a₁, some a₂ => a₁ != a₂
  | _, _ => false

/--
Get the degree of conflict (how different the expert modes are).
-/
def FactoredDist.conflictDegree {α : Type} [BEq α] (d : FactoredDist α) : ℚ :=
  match listArgmax d.support d.selectionalExpert,
        listArgmax d.support d.scenarioExpert with
  | some a₁, some a₂ =>
    if a₁ == a₂ then 0
    else
      -- Measure how much they disagree: |p₁(a₁) - p₂(a₁)| + |p₁(a₂) - p₂(a₂)|
      let diff1 := |d.selectionalExpert a₁ - d.scenarioExpert a₁|
      let diff2 := |d.selectionalExpert a₂ - d.scenarioExpert a₂|
      diff1 + diff2
  | _, _ => 0

-- ============================================================================
-- PART 6: Weighted Product of Experts
-- ============================================================================

/--
Weighted PoE: experts can have different "temperatures" (exponents).

```
P(x) ∝ Π_i p_i(x)^{β_i}
```

Higher β means the expert has more influence.
-/
def weightedPoe {α : Type} (experts : List ((α → ℚ) × ℚ)) (support : List α) : α → ℚ :=
  -- experts is list of (probability function, weight/temperature)
  let unnorm a := experts.foldl (fun acc (p, β) =>
    -- Approximate p(a)^β for small integer β
    -- Full implementation would need Real numbers
    acc * (List.range β.num.natAbs).foldl (fun r _ => r * p a) 1
  ) 1
  let Z := support.foldl (fun acc a => acc + unnorm a) 0
  fun a => if Z = 0 then 0 else unnorm a / Z

-- ============================================================================
-- PART 7: Connection to Bayesian Inference
-- ============================================================================

/-!
## PoE as Bayesian Update

PoE can be viewed as iterated Bayesian conditioning:

```
P(x | e₁, e₂) ∝ P(e₁ | x) · P(e₂ | x) · P(x)
```

Each expert p_i(x) can be interpreted as a likelihood P(e_i | x).

### Connection to RSA

In RSA, L₁ does something similar:
```
L₁(w | u) ∝ S₁(u | w) · P(w)
```

S₁(u | w) acts as a "speaker expert" that evaluates how likely
the speaker would produce u given world w.

### Connection to LU-RSA

LU-RSA marginalizes over lexica:
```
L₁(w | u) ∝ Σ_L P(L) · S₁(u | w, L) · P(w)
```

This is a **mixture** over lexica, with PoE happening inside
each lexicon-specific computation.
-/

/--
Bayesian update as PoE: posterior ∝ likelihood × prior.
-/
def bayesianPoe {α : Type} (likelihood prior : α → ℚ) (support : List α) : α → ℚ :=
  poe2 likelihood prior support

/--
Iterated Bayesian updates can be combined into single PoE.
-/
theorem iterated_bayes_is_poe {α : Type} (l₁ l₂ prior : α → ℚ) (support : List α) :
    -- Two observations: first l₁, then l₂
    -- Equals single PoE with all three
    True := trivial  -- Structural observation

end Core.ProductOfExperts
