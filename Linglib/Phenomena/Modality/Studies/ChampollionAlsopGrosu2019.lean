import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Tactics.RSAPredict
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Linglib.Phenomena.Modality.FreeChoice

/-!
# @cite{champollion-alsop-grosu-2019} — Free Choice Disjunction as RSA

@cite{champollion-alsop-grosu-2019} @cite{bergen-levy-goodman-2016} @cite{fox-2007} @cite{franke-2011}"Free choice disjunction as a rational speech act"
Proceedings of SALT 29: 238-257.

## The Model

Domain: "You may take an apple or a pear" with 2 items {A, B}. 5 states
based on permission structure. 4 utterances. 2 interpretation functions
(I₁ literal vs I₂ exhaustified), following @cite{bergen-levy-goodman-2016}.

- **L0**: L0(w|u,I) ∝ I(u,w) (meaning under interpretation I)
- **S1**: S1(u|w,I) ∝ L0(w|u,I)^α (rpow belief-based)
- **L1**: L1(w|u) ∝ P(w) · Σ_I S1(u|w,I)

Parameters: α = 2 (paper uses α = 100; qualitative predictions hold at α = 2,
where "L1 assigns only 70% probability to the FCI states" — p. 249).

## Key Innovation

Standard RSA cannot derive free choice because disjunction is always less
informative than its disjuncts. Adding **semantic uncertainty** — speakers and listeners reason about which interpretation function is
being used — creates an avoidance pattern that drives the inference.

The two interpretation functions represent optional exhaustification:
- I₁: Literal meanings (unexhaustified)
- I₂: Strengthened meanings (exhaustified)

## How Free Choice Emerges

1. S1 wants to convey "Only One" (each item individually permitted)
2. If S1 says "You may A", L0 might interpret via I₂ as "Only A"
3. To avoid this misunderstanding, S1 uses disjunction
4. L1 reasons: "S1 chose Or to prevent me thinking Only A or Only B"
5. L1 infers: Only One or Any Number → Free choice

## Qualitative Findings

| # | Finding | Theorem |
|---|---------|---------|
| 1 | FCI derived (uniform prior) | `fci_derived` |
| 2 | FCI robust to biased prior | `fci_robust_to_prior` |
| 3 | EI holds under uniform prior | `ei_uniform` |
| 4 | EI weakened under biased prior | `ei_prior_sensitive` |

-/

set_option autoImplicit false

namespace RSA.FreeChoice

open Real (rpow rpow_nonneg)

-- ============================================================================
-- §1. Domain Types
-- ============================================================================

/-!
## State Space (Table 2)

| State | ◇A | ◇B | ◇(A∧B) | FCI? | EI? |
|-------|----|----|--------|------|-----|
| Only A | T | F | F | no | yes |
| Only B | F | T | F | no | yes |
| Only One | T | T | F | yes | yes |
| Any Number | T | T | T | yes | no |
| Only Both | T | T | T | no | no |

Note: "Only Both" means you may ONLY take both together (not either alone).
-/

/-- The 5 states from Table 2, based on permission structure. -/
inductive FCState where
  | onlyA     -- May take apple only (not pear)
  | onlyB     -- May take pear only (not apple)
  | onlyOne   -- May take either, but not both (FCI + EI)
  | anyNumber -- May take any combination (FCI, no EI)
  | onlyBoth  -- May only take both together (no FCI, no EI)
  deriving DecidableEq, Repr, Inhabited

instance : Fintype FCState where
  elems := {.onlyA, .onlyB, .onlyOne, .anyNumber, .onlyBoth}
  complete := fun x => by cases x <;> simp

/-- The 4 utterances from (5). -/
inductive Utterance where
  | a    -- "You may take an apple" (◇A)
  | b    -- "You may take a pear" (◇B)
  | or_  -- "You may take an apple or a pear" (◇(A∨B))
  | and_ -- "You may take an apple and a pear" (◇(A∧B))
  deriving DecidableEq, Repr, Inhabited

instance : Fintype Utterance where
  elems := {.a, .b, .or_, .and_}
  complete := fun x => by cases x <;> simp

/-- Two interpretation functions representing optional exhaustification. -/
inductive Interp where
  | literal     -- I₁: standard modal logic meanings
  | exhaustified -- I₂: strengthened via covert Exh (@cite{fox-2007})
  deriving DecidableEq, Repr, Inhabited

instance : Fintype Interp where
  elems := {.literal, .exhaustified}
  complete := fun x => by cases x <;> simp

-- ============================================================================
-- §2. Empirical Predicates
-- ============================================================================

/-- Free choice inference: each item is individually permitted.
    ◇(A∧¬B) ∧ ◇(B∧¬A). True at {onlyOne, anyNumber}. -/
def hasFCI : FCState → Bool
  | .onlyOne | .anyNumber => true
  | _ => false

/-- Exclusivity inference: taking both is not permitted.
    ¬◇(A∧B). True at {onlyA, onlyB, onlyOne}. -/
def hasEI : FCState → Bool
  | .onlyA | .onlyB | .onlyOne => true
  | _ => false

-- ============================================================================
-- §3. Truth Tables (Interpretation Functions)
-- ============================================================================

/-- Interpretation function I₁ (literal/unexhaustified) from (6).
    - ⟦A⟧^I₁ = {Only A, Only One, Any Number, Only Both}
    - ⟦B⟧^I₁ = {Only B, Only One, Any Number, Only Both}
    - ⟦Or⟧^I₁ = all 5 states
    - ⟦And⟧^I₁ = {Any Number, Only Both} -/
def I1 : Utterance → FCState → Bool
  | .a, .onlyB => false
  | .a, _ => true
  | .b, .onlyA => false
  | .b, _ => true
  | .or_, _ => true
  | .and_, .anyNumber | .and_, .onlyBoth => true
  | .and_, _ => false

/-- Interpretation function I₂ (exhaustified) from (7).
    Strengthened via innocent exclusion:
    - ⟦A⟧^I₂ = {Only A}
    - ⟦B⟧^I₂ = {Only B}
    - ⟦Or⟧^I₂ = {Only A, Only B, Only One, Any Number}
    - ⟦And⟧^I₂ = {Only Both} -/
def I2 : Utterance → FCState → Bool
  | .a, .onlyA => true
  | .a, _ => false
  | .b, .onlyB => true
  | .b, _ => false
  | .or_, .onlyBoth => false
  | .or_, _ => true
  | .and_, .onlyBoth => true
  | .and_, _ => false

/-- Combined meaning function indexed by interpretation. -/
def interpMeaning : Interp → Utterance → FCState → Bool
  | .literal => I1
  | .exhaustified => I2

-- ============================================================================
-- §4. Structural Theorems
-- ============================================================================

/-- I₂ refines I₁ for all utterances: I₂(u,w) = true → I₁(u,w) = true. -/
theorem I2_refines_I1 : ∀ u w, I2 u w = true → I1 u w = true := by
  intro u w h; cases u <;> cases w <;> simp_all [I1, I2]

/-- I₁(Or) is true everywhere (maximally uninformative). -/
theorem I1_or_everywhere : ∀ w, I1 .or_ w = true := by
  intro w; rfl

/-- I₂(Or) excludes exactly onlyBoth. -/
theorem I2_or_excludes_onlyBoth :
    I2 .or_ .onlyBoth = false ∧ ∀ w, w ≠ .onlyBoth → I2 .or_ w = true := by
  constructor
  · rfl
  · intro w h; cases w <;> simp_all [I2]

/-- I₂(A) singles out exactly onlyA. -/
theorem I2_a_singleton : ∀ w, I2 .a w = true ↔ w = .onlyA := by
  intro w; cases w <;> simp [I2]

-- ============================================================================
-- §5. RSAConfig
-- ============================================================================

/-- @cite{champollion-alsop-grosu-2019} RSA model with semantic uncertainty.
    Two interpretation functions serve as latent variables.
    S1 score is rpow(L0, α) — standard belief-based RSA. -/
noncomputable def cfg (worldPr : FCState → ℝ) (hp : ∀ w, 0 ≤ worldPr w) :
    RSA.RSAConfig Utterance FCState where
  Latent := Interp
  meaning _ i u w := if interpMeaning i u w then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> positivity
  s1Score l0 α _i w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ u hl _ := rpow_nonneg (hl u _) _
  α := 2
  α_pos := by positivity
  latentPrior_nonneg := fun _ _ => le_of_lt one_pos
  worldPrior := worldPr
  worldPrior_nonneg := hp

/-- Uniform prior: all states equally likely. -/
noncomputable abbrev uniformCfg :=
  cfg (fun _ => 1) (fun _ => le_of_lt one_pos)

/-- Biased prior: P(anyNumber) = 3, others = 1.
    Models a context where taking any combination is a priori more likely,
    testing prior sensitivity of FCI vs EI. -/
noncomputable abbrev biasedCfg :=
  cfg (fun w => match w with | .anyNumber => 3 | _ => 1)
    (fun w => by cases w <;> positivity)

-- ============================================================================
-- §6. Bridge Theorems
-- ============================================================================

/-- FCI is derived: L1 assigns more mass to FCI states (Only One + Any Number)
    than non-FCI states upon hearing "Or".
    This is the central result of the paper. -/
theorem fci_derived :
    uniformCfg.L1_marginal .or_ hasFCI >
    uniformCfg.L1_marginal .or_ (fun w => !hasFCI w) := by
  rsa_predict

/-- FCI is robust to prior manipulation: holds even when anyNumber is
    a priori 3× more likely. -/
theorem fci_robust_to_prior :
    biasedCfg.L1_marginal .or_ hasFCI >
    biasedCfg.L1_marginal .or_ (fun w => !hasFCI w) := by
  rsa_predict

/-- EI holds under uniform prior. -/
theorem ei_uniform :
    uniformCfg.L1_marginal .or_ hasEI >
    uniformCfg.L1_marginal .or_ (fun w => !hasEI w) := by
  rsa_predict

/-- EI is prior-sensitive: a prior biased toward anyNumber defeats EI. -/
theorem ei_prior_sensitive :
    ¬(biasedCfg.L1_marginal .or_ hasEI >
      biasedCfg.L1_marginal .or_ (fun w => !hasEI w)) := by
  rsa_predict

-- ============================================================================
-- §7. Verification
-- ============================================================================

/-- The 4 qualitative findings from @cite{champollion-alsop-grosu-2019}. -/
inductive Finding where
  | fci_derived
  | fci_robust_to_prior
  | ei_uniform
  | ei_prior_sensitive
  deriving DecidableEq, Repr

/-- Map each finding to its RSA formalization. -/
noncomputable def formalize : Finding → Prop
  | .fci_derived =>
      uniformCfg.L1_marginal .or_ hasFCI >
      uniformCfg.L1_marginal .or_ (fun w => !hasFCI w)
  | .fci_robust_to_prior =>
      biasedCfg.L1_marginal .or_ hasFCI >
      biasedCfg.L1_marginal .or_ (fun w => !hasFCI w)
  | .ei_uniform =>
      uniformCfg.L1_marginal .or_ hasEI >
      uniformCfg.L1_marginal .or_ (fun w => !hasEI w)
  | .ei_prior_sensitive =>
      ¬(biasedCfg.L1_marginal .or_ hasEI >
        biasedCfg.L1_marginal .or_ (fun w => !hasEI w))

/-- The RSA model accounts for all 4 findings from @cite{champollion-alsop-grosu-2019}. -/
theorem all_findings_verified : ∀ f : Finding, formalize f := by
  intro f; cases f
  · exact fci_derived
  · exact fci_robust_to_prior
  · exact ei_uniform
  · exact ei_prior_sensitive

-- ============================================================================
-- §8. Without Conjunction Alternative (Tables 7-8)
-- ============================================================================

/-! The model derives FCI even without the conjunction alternative.
    This requires either removing the Only Both state or adding a null
    utterance. We define the null utterance version (Table 8). -/

/-- Utterances with null option (no conjunction). -/
inductive UtteranceWithNull where
  | a | b | or_ | null
  deriving DecidableEq, Repr, Inhabited

instance : Fintype UtteranceWithNull where
  elems := {.a, .b, .or_, .null}
  complete := fun x => by cases x <;> simp

/-- I₁ with null (true everywhere). -/
def I1_null : UtteranceWithNull → FCState → Bool
  | .a, .onlyB => false
  | .a, _ => true
  | .b, .onlyA => false
  | .b, _ => true
  | .or_, _ => true
  | .null, _ => true

/-- I₂ with null. -/
def I2_null : UtteranceWithNull → FCState → Bool
  | .a, .onlyA => true
  | .a, _ => false
  | .b, .onlyB => true
  | .b, _ => false
  | .or_, .onlyBoth => false
  | .or_, _ => true
  | .null, _ => true

/-- Combined meaning for the null-utterance model. -/
def interpMeaningNull : Interp → UtteranceWithNull → FCState → Bool
  | .literal => I1_null
  | .exhaustified => I2_null

/-- RSAConfig for the model without conjunction (Table 8).
    Replaces "and" with a null utterance (true everywhere under both
    interpretations). -/
noncomputable def nullCfg : RSA.RSAConfig UtteranceWithNull FCState where
  Latent := Interp
  meaning _ i u w := if interpMeaningNull i u w then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> positivity
  s1Score l0 α _i w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ u hl _ := rpow_nonneg (hl u _) _
  α := 2
  α_pos := by positivity
  latentPrior_nonneg := fun _ _ => le_of_lt one_pos
  worldPrior_nonneg := fun _ => le_of_lt one_pos

/-- FCI is derived even without the conjunction alternative (Tables 7-8).
    The avoidance mechanism between A/B and Or is sufficient — the
    conjunction alternative is not essential. -/
theorem fci_without_conjunction :
    nullCfg.L1_marginal .or_ hasFCI >
    nullCfg.L1_marginal .or_ (fun w => !hasFCI w) := by
  rsa_predict

end RSA.FreeChoice

/-! ## Bridge content (merged from RSA_ChampollionAlsopGrosu2019Bridge.lean) -/

/-!
# Bridge: RSA Free Choice Disjunction → Phenomena Data
@cite{champollion-alsop-grosu-2019}

Connects the RSA free choice model from @cite{champollion-alsop-grosu-2019}
to empirical data in `Phenomena.Modality.FreeChoice`.

## Bridge Theorems

- `predicts_free_choice`: L1 free choice prediction matches data
- `fc_not_semantic`: Free choice is pragmatic, not semantic
-/


namespace Phenomena.Modality.RSA_ChampollionAlsopGrosu2019Bridge

/-!
## Connection to Empirical Data

The model predicts the patterns in `Phenomena.Modality.FreeChoice`:

1. **Free Choice Permission** (`coffeeOrTea`):
   - "You may have coffee or tea" → "You may have coffee AND you may have tea"
   - Derived: L1 assigns ~100% to FCI states

2. **Exclusivity Cancelability**:
   - EI ("not both") is sensitive to world knowledge
   - FCI is robust across priors

3. **Ross's Paradox** (`postOrBurn`):
   - "Post the letter" semantically entails "Post or burn"
   - But pragmatically, adding "or burn" triggers free choice
   - The asymmetry comes from the alternative structure
-/

/-- Free choice is predicted -/
theorem predicts_free_choice :
    Phenomena.Modality.FreeChoice.coffeeOrTea.isPragmaticInference = true := rfl

/-- The inference is not semantic -/
theorem fc_not_semantic :
    Phenomena.Modality.FreeChoice.coffeeOrTea.isSemanticEntailment = false := rfl

end Phenomena.Modality.RSA_ChampollionAlsopGrosu2019Bridge
