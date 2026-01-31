/-
# Graded Propositions for Probabilistic Semantics

Infrastructure for graded/continuous-valued propositions used in probabilistic
approaches to semantics (Degen et al. 2020, Yoon et al. 2020).

## Motivation

Standard formal semantics uses Boolean propositions: `W → Bool`. But several
phenomena are better modeled with graded truth values in [0,1]:

- **Semantic noise** (Degen et al. 2020): Color adjectives are more reliable
  than size adjectives, so φ("blue", obj) ≈ 0.99 but φ("small", obj) ≈ 0.8

- **Soft adjective meanings** (Yoon et al. 2020): "terrible" is 0.95 compatible
  with 0-hearts but 0.05 compatible with 1-heart

- **Vagueness**: Borderline cases have intermediate truth values

These graded values feed into RSA's Bayesian inference (normalization via
Bayes' rule), not into fuzzy logic operations.

## Operations

The operations here are **probabilistically motivated**:

| Operation | Definition | Interpretation |
|-----------|------------|----------------|
| neg | 1 - p | P(¬A) = 1 - P(A) |
| conj | p * q | P(A ∧ B) under independence |
| disj | p + q - p*q | P(A ∨ B) under independence |
| entails | ∀w, p w ≤ q w | Pointwise ordering |

## Connection to RSA

RSA's φ function already supports graded values:

```
φ : Interp → Lexicon → Utterance → World → ℚ
```

This module provides the compositional building blocks for constructing
graded meanings that can be plugged into φ.

## References

- Degen et al. (2020). When redundancy is useful.
- Yoon et al. (2020). Polite speech emerges from competing social goals.
- Erk (2022). The probabilistic turn in semantics and pragmatics.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Order.Basic

namespace Core.GradedProposition

-- ============================================================================
-- Graded Proposition Type
-- ============================================================================

/--
A graded proposition assigns a truth degree in ℚ to each world.

Unlike `BProp W = W → Bool`, graded propositions allow intermediate
truth values. Values should typically be in [0,1], though this is
not enforced at the type level for computational convenience.

This is the semantic type for:
- Soft adjective meanings (Yoon et al.)
- Noisy feature predicates (Degen et al.)
- Vague predicates generally
-/
abbrev GProp (W : Type*) := W → ℚ

-- ============================================================================
-- Basic Operations
-- ============================================================================

variable {W : Type*}

/--
Graded negation: P(¬A) = 1 - P(A)

This is the probabilistic complement, not fuzzy negation.
It mirrors Boolean negation when restricted to {0, 1}.
-/
def neg (p : GProp W) : GProp W := fun w => 1 - p w

/--
Graded conjunction: P(A ∧ B) = P(A) × P(B) under independence.

This is the product combination, appropriate when features are
independent (as in Degen et al.'s color × size × type).
-/
def conj (p q : GProp W) : GProp W := fun w => p w * q w

/--
Graded disjunction: P(A ∨ B) = P(A) + P(B) - P(A)P(B) under independence.

This is the probabilistic "or" assuming independence.
-/
def disj (p q : GProp W) : GProp W := fun w => p w + q w - p w * q w

/--
Minimum-based conjunction (alternative to product).

Some applications use min instead of product:
- More conservative (doesn't compound small probabilities)
- Idempotent: min p p = p
-/
def conjMin (p q : GProp W) : GProp W := fun w => min (p w) (q w)

/--
Maximum-based disjunction (alternative to probabilistic or).

Dual to conjMin.
-/
def disjMax (p q : GProp W) : GProp W := fun w => max (p w) (q w)

/--
The always-true graded proposition (degree 1 everywhere).
-/
def top : GProp W := fun _ => 1

/--
The always-false graded proposition (degree 0 everywhere).
-/
def bot : GProp W := fun _ => 0

-- ============================================================================
-- Entailment (Pointwise Ordering)
-- ============================================================================

/--
Graded entailment: p entails q iff p(w) ≤ q(w) for all worlds.

This is the natural ordering on graded propositions. It means:
"Whenever p has some truth degree, q has at least that much."

This coincides with classical entailment when restricted to {0, 1}.
-/
def entails (p q : GProp W) : Prop := ∀ w, p w ≤ q w

/--
Graded equivalence: p and q have the same truth degree everywhere.
-/
def equiv (p q : GProp W) : Prop := ∀ w, p w = q w

instance : LE (GProp W) where
  le := entails

instance : Preorder (GProp W) where
  le := entails
  le_refl := fun _ _ => le_refl _
  le_trans := fun _ _ _ hab hbc w => le_trans (hab w) (hbc w)

instance : Top (GProp W) where
  top := top

instance : Bot (GProp W) where
  bot := bot

/--
Partial order on graded propositions: p = q iff equal everywhere.
-/
instance : PartialOrder (GProp W) where
  le := entails
  le_refl := fun _ _ => le_refl _
  le_trans := fun _ _ _ hab hbc w => le_trans (hab w) (hbc w)
  le_antisymm := fun p q hpq hqp => by
    funext w
    exact le_antisymm (hpq w) (hqp w)

-- ============================================================================
-- Coercion from Boolean
-- ============================================================================

/--
Convert a Boolean proposition to a graded proposition.

Maps `true` to 1 and `false` to 0. This is how most RSA implementations
currently work: they define Boolean meanings and convert via this coercion.
-/
def ofBool (p : W → Bool) : GProp W := fun w => if p w then 1 else 0

/--
Alias matching the existing RSA function name.
-/
def boolToGProp (p : W → Bool) : GProp W := ofBool p

-- ============================================================================
-- Key Theorems: Negation
-- ============================================================================

/--
Graded negation is involutive: neg (neg p) = p

This mirrors the Boolean property: ¬¬p = p
-/
theorem neg_involutive (p : GProp W) : neg (neg p) = p := by
  funext w
  simp only [neg]
  ring

/--
Graded negation is antitone: if p ≤ q then neg q ≤ neg p

This is the key property for downward-entailing contexts.
It mirrors the Boolean property that negation reverses entailment.
-/
theorem neg_antitone (p q : GProp W) (h : entails p q) : entails (neg q) (neg p) := by
  intro w
  simp only [neg]
  linarith [h w]

/--
Negation swaps top and bot.
-/
theorem neg_top : neg (top : GProp W) = bot := by
  funext w
  simp [neg, top, bot]

theorem neg_bot : neg (bot : GProp W) = top := by
  funext w
  simp [neg, top, bot]

-- ============================================================================
-- Key Theorems: Conjunction (Product)
-- ============================================================================

/--
Product conjunction is commutative.
-/
theorem conj_comm (p q : GProp W) : conj p q = conj q p := by
  funext w
  simp only [conj]
  ring

/--
Product conjunction is associative.
-/
theorem conj_assoc (p q r : GProp W) : conj (conj p q) r = conj p (conj q r) := by
  funext w
  simp only [conj]
  ring

/--
Top is the identity for product conjunction.
-/
theorem conj_top (p : GProp W) : conj p top = p := by
  funext w
  simp only [conj, top]
  ring

theorem top_conj (p : GProp W) : conj top p = p := by
  funext w
  simp only [conj, top]
  ring

/--
Bot is absorbing for product conjunction.
-/
theorem conj_bot (p : GProp W) : conj p bot = bot := by
  funext w
  simp only [conj, bot]
  ring

-- ============================================================================
-- Key Theorems: Disjunction
-- ============================================================================

/--
Probabilistic disjunction is commutative.
-/
theorem disj_comm (p q : GProp W) : disj p q = disj q p := by
  funext w
  simp only [disj]
  ring

/--
Bot is the identity for disjunction.
-/
theorem disj_bot (p : GProp W) : disj p bot = p := by
  funext w
  simp only [disj, bot]
  ring

/--
Top is absorbing for disjunction.
-/
theorem disj_top (p : GProp W) : disj p top = top := by
  funext w
  simp only [disj, top]
  ring

-- ============================================================================
-- De Morgan Laws
-- ============================================================================

/--
De Morgan's law for graded conjunction: ∼(p ⊗ q) = ∼p ⊕ ∼q

This is the probabilistic version: P(¬(A∧B)) = P(¬A∨¬B) under independence.
-/
theorem deMorgan_conj (p q : GProp W) : neg (conj p q) = disj (neg p) (neg q) := by
  funext w
  simp only [neg, conj, disj]
  ring

/--
De Morgan's law for graded disjunction: ∼(p ⊕ q) = ∼p ⊗ ∼q

This is the probabilistic version: P(¬(A∨B)) = P(¬A∧¬B) under independence.
-/
theorem deMorgan_disj (p q : GProp W) : neg (disj p q) = conj (neg p) (neg q) := by
  funext w
  simp only [neg, conj, disj]
  ring

-- ============================================================================
-- Bounds Preservation (for [0,1] values)
-- ============================================================================

/--
Negation preserves [0,1] bounds: if 0 ≤ p w ≤ 1, then 0 ≤ neg p w ≤ 1.
-/
theorem neg_preserves_bounds (p : GProp W) (w : W)
    (h0 : 0 ≤ p w) (h1 : p w ≤ 1) : 0 ≤ neg p w ∧ neg p w ≤ 1 := by
  simp only [neg]
  constructor
  · linarith
  · linarith

/--
Conjunction preserves [0,1] bounds: if p, q ∈ [0,1], then p * q ∈ [0,1].
-/
theorem conj_preserves_bounds (p q : GProp W) (w : W)
    (hp0 : 0 ≤ p w) (hp1 : p w ≤ 1) (hq0 : 0 ≤ q w) (hq1 : q w ≤ 1) :
    0 ≤ conj p q w ∧ conj p q w ≤ 1 := by
  simp only [conj]
  constructor
  · exact mul_nonneg hp0 hq0
  · calc p w * q w ≤ p w * 1 := by exact mul_le_mul_of_nonneg_left hq1 hp0
    _ = p w := by ring
    _ ≤ 1 := hp1

/--
Disjunction preserves [0,1] bounds: if p, q ∈ [0,1], then p + q - pq ∈ [0,1].
-/
theorem disj_preserves_bounds (p q : GProp W) (w : W)
    (hp0 : 0 ≤ p w) (hp1 : p w ≤ 1) (hq0 : 0 ≤ q w) (hq1 : q w ≤ 1) :
    0 ≤ disj p q w ∧ disj p q w ≤ 1 := by
  simp only [disj]
  constructor
  · -- p + q - pq ≥ 0 when p,q ∈ [0,1]
    have h : p w + q w - p w * q w = p w + q w * (1 - p w) := by ring
    rw [h]
    have hp1' : 0 ≤ 1 - p w := by linarith
    exact add_nonneg hp0 (mul_nonneg hq0 hp1')
  · -- p + q - pq ≤ 1 when p,q ∈ [0,1]
    have h : p w + q w - p w * q w = 1 - (1 - p w) * (1 - q w) := by ring
    rw [h]
    have hp1' : 0 ≤ 1 - p w := by linarith
    have hq1' : 0 ≤ 1 - q w := by linarith
    linarith [mul_nonneg hp1' hq1']

-- ============================================================================
-- Monotonicity Properties
-- ============================================================================

/--
Conjunction is monotone in both arguments.
-/
theorem conj_monotone_left (p q r : GProp W)
    (hpq : entails p q) (hr : ∀ w, 0 ≤ r w) : entails (conj p r) (conj q r) := by
  intro w
  simp only [conj]
  exact mul_le_mul_of_nonneg_right (hpq w) (hr w)

/--
Disjunction is monotone in both arguments.
-/
theorem disj_monotone_left (p q r : GProp W)
    (hpq : entails p q) (_hr : ∀ w, 0 ≤ r w) (hr1 : ∀ w, r w ≤ 1) :
    entails (disj p r) (disj q r) := by
  intro w
  simp only [disj]
  have h1 : p w + r w - p w * r w ≤ q w + r w - q w * r w := by
    have hdiff : q w - p w ≥ 0 := by linarith [hpq w]
    have hr1w := hr1 w
    calc p w + r w - p w * r w
        = p w * (1 - r w) + r w := by ring
      _ ≤ q w * (1 - r w) + r w := by linarith [mul_nonneg hdiff (by linarith : 0 ≤ 1 - r w)]
      _ = q w + r w - q w * r w := by ring
  exact h1

-- ============================================================================
-- Boolean Correspondence
-- ============================================================================

/--
When restricted to Boolean values, graded negation equals Boolean negation.
-/
theorem neg_ofBool (p : W → Bool) :
    neg (ofBool p) = ofBool (fun w => !p w) := by
  funext w
  simp only [neg, ofBool]
  split <;> simp_all

/--
When restricted to Boolean values, graded conjunction equals Boolean conjunction.
-/
theorem conj_ofBool (p q : W → Bool) :
    conj (ofBool p) (ofBool q) = ofBool (fun w => p w && q w) := by
  funext w
  simp only [conj, ofBool]
  split <;> split <;> simp_all

/--
When restricted to Boolean values, graded disjunction equals Boolean disjunction.
-/
theorem disj_ofBool (p q : W → Bool) :
    disj (ofBool p) (ofBool q) = ofBool (fun w => p w || q w) := by
  funext w
  simp only [disj, ofBool]
  split <;> split <;> simp_all

-- ============================================================================
-- Notation (Scoped)
-- ============================================================================

scoped prefix:75 "∼" => neg
scoped infixl:65 " ⊗ " => conj      -- Product conjunction
scoped infixl:60 " ⊕ " => disj      -- Probabilistic disjunction
scoped infixl:65 " ⊓ᵍ " => conjMin  -- Min conjunction
scoped infixl:60 " ⊔ᵍ " => disjMax  -- Max disjunction

-- ============================================================================
-- Graded Predicate Application
-- ============================================================================

/--
A graded predicate is a function from entities to truth degrees.

This is the graded analog of `Entity → Bool` predicates.
-/
abbrev GPred (E : Type*) := E → ℚ

/--
Lift a Boolean predicate to a graded predicate.
-/
def GPred.ofBool {E : Type*} (p : E → Bool) : GPred E :=
  fun e => if p e then 1 else 0

-- ============================================================================
-- Semantic Noise Parameters (à la Degen et al.)
-- ============================================================================

/--
Semantic reliability parameters for a feature dimension.

Following Degen et al. (2020), different feature types have different
noise levels:
- Color: high reliability (match ≈ 0.99, mismatch ≈ 0.01)
- Size: lower reliability (match ≈ 0.8, mismatch ≈ 0.2)
-/
structure FeatureReliability where
  /-- Truth degree when feature matches -/
  onMatch : ℚ := 1
  /-- Truth degree when feature doesn't match -/
  onMismatch : ℚ := 0
  /-- Match value should be higher than mismatch -/
  match_gt_mismatch : onMismatch ≤ onMatch := by native_decide
  deriving Repr

/--
Boolean (crisp) feature reliability: 1 on match, 0 on mismatch.
-/
def FeatureReliability.crisp : FeatureReliability :=
  { onMatch := 1, onMismatch := 0 }

/--
High reliability feature (like color in Degen et al.).
-/
def FeatureReliability.high : FeatureReliability :=
  { onMatch := 99/100, onMismatch := 1/100, match_gt_mismatch := by native_decide }

/--
Medium reliability feature (like size in Degen et al.).
-/
def FeatureReliability.medium : FeatureReliability :=
  { onMatch := 8/10, onMismatch := 2/10, match_gt_mismatch := by native_decide }

/--
Apply a feature reliability to a Boolean match result.

This converts a crisp feature check into a graded truth value
based on the reliability parameters.
-/
def FeatureReliability.apply (rel : FeatureReliability) (isMatch : Bool) : ℚ :=
  if isMatch then rel.onMatch else rel.onMismatch

-- ============================================================================
-- Algebraic Structure
-- ============================================================================

/-!
## Algebraic Structure: Probabilistic Algebra

The graded proposition operations form a well-behaved algebraic structure:

### Structure: Bounded Commutative Monoids with De Morgan Duality

**(GProp W, ⊗, ⊤)** is a commutative monoid:
- `conj_comm`: p ⊗ q = q ⊗ p
- `conj_assoc`: (p ⊗ q) ⊗ r = p ⊗ (q ⊗ r)
- `conj_top`, `top_conj`: p ⊗ ⊤ = ⊤ ⊗ p = p

**(GProp W, ⊕, ⊥)** is a commutative monoid:
- `disj_comm`: p ⊕ q = q ⊕ p
- `disj_bot`: p ⊕ ⊥ = p

**De Morgan negation (∼)** connects them:
- `neg_involutive`: ∼∼p = p
- `deMorgan_conj`: ∼(p ⊗ q) = ∼p ⊕ ∼q
- `deMorgan_disj`: ∼(p ⊕ q) = ∼p ⊗ ∼q
- `neg_top`, `neg_bot`: ∼⊤ = ⊥, ∼⊥ = ⊤

### Relationship to Known Algebras

| Property | Boolean Algebra | Our Prob Algebra | MV-Algebra |
|----------|-----------------|------------------|------------|
| Negation | ¬p | 1 - p | 1 - p |
| Conjunction | p ∧ q | p × q | max(0, p+q-1) |
| Disjunction | p ∨ q | p + q - pq | min(1, p+q) |
| Idempotent? | Yes | No (p×p ≠ p) | No |

Our operations are the **probabilistic** versions assuming independence:
- P(A ∧ B) = P(A) × P(B)
- P(A ∨ B) = P(A) + P(B) - P(A)P(B)
- P(¬A) = 1 - P(A)

### Why This Matters

These algebraic properties guarantee:
1. **Compositionality**: Complex meanings built from simple operations
2. **Bounds preservation**: If inputs ∈ [0,1], outputs ∈ [0,1]
3. **Boolean compatibility**: Reduces to Boolean algebra on {0,1}
4. **Monotonicity**: Entailment is preserved by operations

See `RSA.LassiterGoodman2017.threshold_graded_equivalence` for the deeper
result: threshold semantics + uncertainty = graded semantics.
-/

-- ============================================================================
-- Equivalence: When Boolean and Graded Semantics Agree
-- ============================================================================

/-!
## Boolean-Graded Correspondence

The theorems below establish when Boolean and graded semantics produce
equivalent results. This is important for:

1. **Backward compatibility**: Existing Boolean RSA models are special cases
2. **Generalization**: Graded models strictly extend Boolean models
3. **Validation**: Graded ops reduce to Boolean ops at {0,1}

### Key Result

For propositions with values in {0,1} only:
- Graded negation = Boolean negation (`neg_ofBool`)
- Graded conjunction = Boolean conjunction (`conj_ofBool`)
- Graded disjunction = Boolean disjunction (`disj_ofBool`)

This means: **Any theorem about graded propositions also holds for Boolean
propositions via the `ofBool` embedding.**

### Connection to Lassiter & Goodman (2017)

That paper proves an even stronger result: threshold semantics (Boolean for
each θ) becomes graded semantics after marginalizing over θ. See
`RSA.LassiterGoodman2017.threshold_graded_equivalence`.

This shows that graded semantics can ARISE from Boolean semantics + uncertainty,
not just be stipulated separately.
-/

/--
Entailment is preserved by `ofBool`: if p implies q pointwise on Bool,
then ofBool p implies ofBool q on ℚ.

This ensures Boolean entailment judgments lift to graded entailment.
-/
theorem entails_ofBool_of_implies {W : Type*} (p q : W → Bool) (h : ∀ w, p w → q w) :
    entails (ofBool p) (ofBool q) := by
  intro w
  simp only [ofBool]
  cases hp : p w <;> cases hq : q w <;> simp_all

/--
Graded entailment reduces to Boolean entailment for {0,1} propositions.

If p and q only take values 0 and 1, then graded entailment (pointwise ≤)
is equivalent to Boolean entailment (p w → q w for all w).
-/
theorem entails_iff_bool {W : Type*} (p q : W → Bool) :
    entails (ofBool p) (ofBool q) ↔ ∀ w, p w → q w := by
  constructor
  · intro h w hp
    have hle := h w
    simp only [ofBool] at hle
    cases hpw : p w <;> cases hqw : q w <;> simp_all
    -- The contradiction case: 1 ≤ 0
    exact absurd hle (by decide : ¬(1 : ℚ) ≤ 0)
  · exact entails_ofBool_of_implies p q

/--
Bot is the smallest graded proposition (for non-negative propositions).
-/
theorem bot_entails (p : GProp W) (hp : ∀ w, 0 ≤ p w) : entails bot p := by
  intro w
  simp only [bot]
  exact hp w

-- ============================================================================
-- Summary
-- ============================================================================

/-!
## What This Module Provides

### Types
- `GProp W`: Graded propositions (W → ℚ)
- `GPred E`: Graded predicates (E → ℚ)
- `FeatureReliability`: Noise parameters for feature dimensions

### Operations
- `neg`: Probabilistic negation (1 - p)
- `conj`: Product conjunction (p * q)
- `disj`: Probabilistic disjunction (p + q - pq)
- `conjMin`, `disjMax`: Alternative min/max operations
- `entails`: Pointwise ordering

### Key Theorems
- `neg_involutive`: ∼∼p = p
- `neg_antitone`: p ≤ q → ∼q ≤ ∼p
- `conj_comm`, `conj_assoc`: Product conjunction is commutative/associative
- `*_ofBool`: Operations agree with Boolean when restricted to {0,1}

### Usage Pattern

```lean
import Linglib.Core.GradedProposition

-- Define graded meanings
def colorMeaning (rel : FeatureReliability) (c : Color) (obj : Object) : ℚ :=
  rel.apply (obj.color == c)

-- Compose into utterance meaning
def utteranceMeaning (u : Utterance) (obj : Object) : ℚ :=
  colorMeaning .high u.color obj *
  sizeMeaning .medium u.size obj

-- Use in RSA φ
def φ : Utterance → Object → ℚ := utteranceMeaning
```
-/

end Core.GradedProposition
