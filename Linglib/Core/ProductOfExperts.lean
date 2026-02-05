import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Product of Experts

Multiplicative combination of probability distributions.
-/

namespace Core.ProductOfExperts

/-- Product of Experts: combine distributions multiplicatively. -/
def productOfExperts {α : Type} (ps : List (α → ℚ)) (support : List α) : α → ℚ :=
  let unnorm a := ps.foldl (λ acc p => acc * p a) 1
  let Z := support.foldl (λ acc a => acc + unnorm a) 0
  λ a => if Z = 0 then 0 else unnorm a / Z

/-- Product of two experts. -/
def poe2 {α : Type} (p₁ p₂ : α → ℚ) (support : List α) : α → ℚ :=
  productOfExperts [p₁, p₂] support

/-- Product of three experts. -/
def poe3 {α : Type} (p₁ p₂ p₃ : α → ℚ) (support : List α) : α → ℚ :=
  productOfExperts [p₁, p₂, p₃] support

/-- Unnormalized product: multiply expert scores without normalizing. -/
def unnormalizedProduct {α : Type} (ps : List (α → ℚ)) : α → ℚ :=
  λ a => ps.foldl (λ acc p => acc * p a) 1

/-- Normalize a scoring function over a finite support. -/
def normalizeOver {α : Type} (f : α → ℚ) (support : List α) : α → ℚ :=
  let Z := support.foldl (λ acc a => acc + f a) 0
  λ a => if Z = 0 then 0 else f a / Z

/-- PoE equals unnormalized product followed by normalization. -/
theorem poe_eq_unnorm_then_norm {α : Type} (ps : List (α → ℚ)) (support : List α) :
    productOfExperts ps support = normalizeOver (unnormalizedProduct ps) support := by
  rfl

/-- Folding multiplication with zero accumulator stays zero. -/
theorem foldl_mul_zero_init {α : Type} (ps : List (α → ℚ)) (a : α) :
    ps.foldl (λ acc p => acc * p a) 0 = 0 := by
  induction ps with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons, zero_mul, ih]

/-- Folding multiplication absorbs zero. -/
theorem foldl_mul_zero {α : Type} (ps : List (α → ℚ)) (a : α) (init : ℚ)
    (hp : ∃ p ∈ ps, p a = 0) :
    ps.foldl (λ acc p => acc * p a) init = 0 := by
  obtain ⟨p, hp_mem, hp_zero⟩ := hp
  induction ps generalizing init with
  | nil => simp at hp_mem
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [List.mem_cons] at hp_mem
    rcases hp_mem with rfl | htl
    · simp only [hp_zero, mul_zero, foldl_mul_zero_init]
    · exact ih (init * hd a) htl

/-- PoE with single expert returns normalized version of that expert. -/
theorem poe_single {α : Type} (p : α → ℚ) (support : List α) :
    productOfExperts [p] support = normalizeOver p support := by
  simp only [productOfExperts, normalizeOver, List.foldl, one_mul]

/-- PoE is zero-absorbing: if any expert gives zero, product is zero. -/
theorem poe_zero_absorbing {α : Type} (ps : List (α → ℚ)) (support : List α) (a : α)
    (hp : ∃ p ∈ ps, p a = 0) : productOfExperts ps support a = 0 ∨
                               ∃ a' ∈ support, productOfExperts ps support a' > 0 := by
  left
  simp only [productOfExperts]
  split_ifs with hZ
  · rfl
  · simp only [foldl_mul_zero ps a 1 hp, zero_div]

/-- Foldl adding 1 with any init. -/
theorem foldl_add_one {α : Type} (xs : List α) (init : ℚ) :
    xs.foldl (λ acc _ => acc + (1 : ℚ)) init = init + xs.length := by
  induction xs generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [ih]
    ring

/-- Foldl adding 1 equals length. -/
theorem foldl_add_one_eq_length {α : Type} (xs : List α) :
    xs.foldl (λ acc _ => acc + (1 : ℚ)) 0 = xs.length := by
  simp [foldl_add_one]

/-- PoE with empty expert list gives uniform. -/
theorem poe_empty {α : Type} (support : List α) (a : α) :
    productOfExperts ([] : List (α → ℚ)) support a =
    if support.length = 0 then 0 else 1 / (support.length : ℚ) := by
  simp only [productOfExperts, List.foldl]
  rw [foldl_add_one_eq_length]
  by_cases h : support.length = 0
  · simp [h]
  · simp only [h, ↓reduceIte, Nat.cast_ne_zero.mpr h]

/-- Linear combination of two values. -/
def linearCombine (lam : ℚ) (v₁ v₂ : ℚ) : ℚ :=
  (1 - lam) * v₁ + lam * v₂

/-- Linear combination is NOT zero-absorbing. -/
theorem linear_not_zero_absorbing :
    linearCombine (1/2) 0 1 ≠ 0 := by
  simp only [linearCombine]
  norm_num

/-- PoE IS zero-absorbing (for the 2-expert case). -/
theorem poe2_zero_absorbing {α : Type} (p₁ p₂ : α → ℚ) (support : List α) (a : α) :
    p₁ a = 0 → poe2 p₁ p₂ support a = 0 ∨ (support.foldl (λ acc x => acc + p₁ x * p₂ x) 0 = 0) := by
  intro h
  simp only [poe2, productOfExperts, List.foldl, one_mul, h, zero_mul]
  left
  split_ifs with hZ
  · rfl
  · simp only [zero_div]

/-- Find the element with maximum value according to a scoring function. -/
def listArgmax {α : Type} (xs : List α) (f : α → ℚ) : Option α :=
  xs.foldl (λ acc x =>
    match acc with
    | none => some x
    | some best => if f x > f best then some x else some best
  ) none

/-- A factored distribution in SDS style. -/
structure FactoredDist (α : Type) where
  selectionalExpert : α → ℚ
  scenarioExpert : α → ℚ
  support : List α

/-- Combine a factored distribution using PoE. -/
def FactoredDist.combine {α : Type} (d : FactoredDist α) : α → ℚ :=
  poe2 d.selectionalExpert d.scenarioExpert d.support

/-- Get the unnormalized scores. -/
def FactoredDist.unnormScores {α : Type} (d : FactoredDist α) : α → ℚ :=
  λ a => d.selectionalExpert a * d.scenarioExpert a

/-- Detect conflict: experts disagree on the mode. -/
def FactoredDist.hasConflict {α : Type} [BEq α] (d : FactoredDist α) : Bool :=
  match listArgmax d.support d.selectionalExpert,
        listArgmax d.support d.scenarioExpert with
  | some a₁, some a₂ => a₁ != a₂
  | _, _ => false

/-- Get the degree of conflict between expert modes. -/
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

/-- Weighted PoE: P(x) ∝ Π_i p_i(x)^{β_i}. -/
def weightedPoe {α : Type} (experts : List ((α → ℚ) × ℚ)) (support : List α) : α → ℚ :=
  -- experts is list of (probability function, weight/temperature)
  let unnorm a := experts.foldl (λ acc (p, β) =>
    -- Approximate p(a)^β for small integer β
    -- Full implementation would need Real numbers
    acc * (List.range β.num.natAbs).foldl (λ r _ => r * p a) 1
  ) 1
  let Z := support.foldl (λ acc a => acc + unnorm a) 0
  λ a => if Z = 0 then 0 else unnorm a / Z

/-- Bayesian update as PoE: posterior ∝ likelihood × prior. -/
def bayesianPoe {α : Type} (likelihood prior : α → ℚ) (support : List α) : α → ℚ :=
  poe2 likelihood prior support

/-- Unnormalized PoE is order-independent. -/
theorem unnormalizedProduct_comm {α : Type} (p q : α → ℚ) (a : α) :
    unnormalizedProduct [p, q] a = unnormalizedProduct [q, p] a := by
  simp only [unnormalizedProduct, List.foldl, one_mul]
  ring

/-- PoE with reordered experts gives same result. -/
theorem poe_comm {α : Type} (p q : α → ℚ) (support : List α) :
    productOfExperts [p, q] support = productOfExperts [q, p] support := by
  simp only [productOfExperts]
  have h : ∀ a, [p, q].foldl (λ acc f => acc * f a) 1 =
               [q, p].foldl (λ acc f => acc * f a) 1 := by
    intro a; simp only [List.foldl, one_mul]; ring
  simp_rw [h]

end Core.ProductOfExperts
