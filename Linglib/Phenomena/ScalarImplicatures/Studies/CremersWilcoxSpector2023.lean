/-
# Cremers, Wilcox & Spector (2023): Exhaustivity and Anti-Exhaustivity in RSA

Empirical data and domain types for RSA exhaustivity models.

## Key Phenomenon: Anti-Exhaustivity

In baseline RSA, hearing "A" can INCREASE belief in w_ab (where A and B are both true)
when priors are biased. This "anti-exhaustive" behavior contradicts human interpretation.

## Domain

**Two worlds:**
- `w_a`: A true, B false (A ∧ ¬B)
- `w_ab`: A and B both true (A ∧ B)

**Three utterances:**
- `A` with cost 0 (base utterance)
- `A∧B` with cost c_AB
- `A∧¬B` with cost c_A¬B

## Anti-Exhaustivity Condition (Equation 6)

L1(w_ab | A) > P(w_ab) iff prior(w_ab) / prior(w_a) > c_A¬B / c_AB

## Model Comparison

| # | Model | Description |
|---|-------|-------------|
| 1 | Baseline RSA | Standard RSA with costs |
| 2 | wRSA | Wonky speaker (non-cooperative) |
| 3 | BwRSA | Bayesian wonky inference |
| 4 | svRSA | Supervaluationist QUD semantics |
| 5 | FREE-LU | Lexical uncertainty (4 lexica) |
| 6 | EXH-LU | Exhaustification + LU (key test) |
| 7-8 | RSA-LI | Lexical Intentions variants |

## Reference

Cremers, A., Wilcox, E., & Spector, B. (2023). "Exhaustivity and Anti-Exhaustivity
in the RSA Framework". Semantics & Pragmatics.
-/

import Mathlib.Data.Rat.Defs

namespace Phenomena.ScalarImplicatures.Studies.CremersWilcoxSpector2023

-- World Model

/-- Two-world model for exhaustivity.

    - `w_a`: A true, B false (A ∧ ¬B)
    - `w_ab`: A and B both true (A ∧ B)

    Note: No w_b (B without A) or w_none (neither) because we condition on A being true.
    The listener knows A is true; the question is whether B is also true. -/
inductive CWSWorld where
  | w_a : CWSWorld   -- Only A is true
  | w_ab : CWSWorld  -- Both A and B are true
  deriving DecidableEq, BEq, Repr, Inhabited

/-- All worlds -/
def allWorlds : List CWSWorld := [.w_a, .w_ab]

theorem allWorlds_length : allWorlds.length = 2 := rfl

-- Utterance Types

/-- Three utterances in the minimal exhaustivity domain.

    - `A`: Simple assertion (cost 0)
    - `AandB`: Explicit conjunction (cost c_AB)
    - `AandNotB`: Explicit negative (cost c_A¬B) -/
inductive CWSUtterance where
  | A : CWSUtterance        -- "A"
  | AandB : CWSUtterance    -- "A and B"
  | AandNotB : CWSUtterance -- "A and not B"
  deriving DecidableEq, BEq, Repr, Inhabited

/-- All utterances -/
def allUtterances : List CWSUtterance := [.A, .AandB, .AandNotB]

theorem allUtterances_length : allUtterances.length = 3 := rfl

/-- String representation -/
def CWSUtterance.toString : CWSUtterance → String
  | .A => "A"
  | .AandB => "A∧B"
  | .AandNotB => "A∧¬B"

instance : ToString CWSUtterance := ⟨CWSUtterance.toString⟩

-- Literal Semantics

/-- Literal truth: which utterance is true in which world -/
def literalTruth : CWSWorld → CWSUtterance → Bool
  | .w_a, .A => true
  | .w_a, .AandB => false
  | .w_a, .AandNotB => true
  | .w_ab, .A => true
  | .w_ab, .AandB => true
  | .w_ab, .AandNotB => false

/-- A is true in both worlds -/
theorem A_true_everywhere : ∀ w, literalTruth w .A = true := by
  intro w; cases w <;> rfl

/-- A∧B only true in w_ab -/
theorem AandB_only_in_wab : literalTruth .w_a .AandB = false ∧ literalTruth .w_ab .AandB = true := by
  constructor <;> rfl

/-- A∧¬B only true in w_a -/
theorem AandNotB_only_in_wa : literalTruth .w_a .AandNotB = true ∧ literalTruth .w_ab .AandNotB = false := by
  constructor <;> rfl

-- Cost Structure

/-- Cost parameters for utterances.

    Following the paper:
    - c(A) = 0 (base utterance)
    - c(A∧B) = c_AB
    - c(A∧¬B) = c_A¬B

    Key insight: Anti-exhaustivity depends on the RATIO c_A¬B / c_AB -/
structure CWSCosts where
  /-- Cost of "A∧B" -/
  c_AB : ℚ
  /-- Cost of "A∧¬B" -/
  c_AnotB : ℚ
  /-- Costs must be positive -/
  hAB_pos : 0 < c_AB
  hAnotB_pos : 0 < c_AnotB

/-- Get cost of an utterance -/
def CWSCosts.cost (c : CWSCosts) : CWSUtterance → ℚ
  | .A => 0
  | .AandB => c.c_AB
  | .AandNotB => c.c_AnotB

/-- Default costs: equal cost for both conjunctions -/
def defaultCosts : CWSCosts where
  c_AB := 1
  c_AnotB := 1
  hAB_pos := by decide
  hAnotB_pos := by decide

-- Prior Structure

/-- Prior probability over worlds.

    Must be a valid probability distribution:
    - Non-negative
    - Sum to 1 -/
structure CWSPrior where
  /-- P(w_a) -/
  p_wa : ℚ
  /-- P(w_ab) -/
  p_wab : ℚ
  /-- Non-negative -/
  hwa_nonneg : 0 ≤ p_wa
  hwab_nonneg : 0 ≤ p_wab
  /-- Sum to 1 -/
  hsum : p_wa + p_wab = 1

/-- Get prior probability of a world -/
def CWSPrior.prob (prior : CWSPrior) : CWSWorld → ℚ
  | .w_a => prior.p_wa
  | .w_ab => prior.p_wab

/-- Uniform prior -/
def uniformPrior : CWSPrior where
  p_wa := 1/2
  p_wab := 1/2
  hwa_nonneg := by native_decide
  hwab_nonneg := by native_decide
  hsum := by native_decide

-- Anti-Exhaustivity Condition (Equation 6)

/-- The anti-exhaustivity condition from Cremers et al. (2023), Equation 6.

    In baseline RSA:
    L1(w_ab | A) > P(w_ab) iff P(w_ab) / P(w_a) > c(A∧¬B) / c(A∧B)

    When the prior ratio exceeds the cost ratio, the listener's posterior
    on w_ab given "A" INCREASES relative to the prior. This is "anti-exhaustive"
    because normally we expect "A" (without "and B") to suggest NOT B. -/
def antiExhaustivityCondition (prior : CWSPrior) (costs : CWSCosts) : Prop :=
  prior.p_wab / prior.p_wa > costs.c_AnotB / costs.c_AB

/-- Check if anti-exhaustivity condition holds (decidable version) -/
def antiExhaustivityHolds (prior : CWSPrior) (costs : CWSCosts) : Bool :=
  prior.p_wab / prior.p_wa > costs.c_AnotB / costs.c_AB

/-- With uniform prior and equal costs, no anti-exhaustivity -/
theorem uniform_equal_no_antiexh :
    antiExhaustivityHolds uniformPrior defaultCosts = false := by
  native_decide

/-- Strong bias towards w_ab with equal costs triggers anti-exhaustivity.
    Example: P(w_ab) = 3/4, P(w_a) = 1/4, so ratio = 3 > 1 = cost ratio -/
def stronglyBiasedPrior : CWSPrior where
  p_wa := 1/4
  p_wab := 3/4
  hwa_nonneg := by native_decide
  hwab_nonneg := by native_decide
  hsum := by native_decide

theorem strongly_biased_triggers_antiexh :
    antiExhaustivityHolds stronglyBiasedPrior defaultCosts = true := by
  native_decide

-- Exhaustified Semantics (for EXH-LU model)

/-- EXH positions for the CWS domain.

    Since utterances are simple (not nested quantifiers), we only have
    matrix-level EXH. But we model it for consistency with the interface. -/
inductive CWSExhPosition where
  | matrix : CWSExhPosition  -- EXH at matrix level
  deriving DecidableEq, BEq, Repr

/-- Parse = whether EXH is applied -/
inductive CWSParse where
  | literal : CWSParse  -- No EXH
  | exh : CWSParse      -- EXH applied
  deriving DecidableEq, BEq, Repr, Inhabited

/-- All parses -/
def allParses : List CWSParse := [.literal, .exh]

/-- Exhaustified meaning of "A".

    EXH(A) = A ∧ ¬B (strengthened meaning)

    Under exhaustification, "A" means "only A" = A ∧ ¬B.
    This eliminates anti-exhaustivity because EXH(A) is only true in w_a. -/
def exhMeaning : CWSWorld → CWSUtterance → Bool
  | w, .A => literalTruth w .AandNotB  -- EXH(A) = A ∧ ¬B
  | w, u => literalTruth w u           -- Others unchanged

/-- EXH(A) is only true in w_a -/
theorem exhA_only_in_wa : exhMeaning .w_a .A = true ∧ exhMeaning .w_ab .A = false := by
  constructor <;> rfl

-- Lexica for FREE-LU (Model 5)

/-- Four lexica for FREE-LU model.

    The listener doesn't know which lexicon the speaker is using:
    - `strong_both`: A means A∧¬B, A∧B means exactly A∧B
    - `strong_A`: A means A∧¬B (exhaustive), others literal
    - `strong_AB`: A∧B means exactly A∧B (exclusive), others literal
    - `weak`: All meanings are literal (inclusive) -/
inductive CWSLexicon where
  | strong_both : CWSLexicon
  | strong_A : CWSLexicon
  | strong_AB : CWSLexicon
  | weak : CWSLexicon
  deriving DecidableEq, BEq, Repr, Inhabited

/-- All lexica -/
def allLexica : List CWSLexicon := [.strong_both, .strong_A, .strong_AB, .weak]

theorem allLexica_length : allLexica.length = 4 := rfl

/-- Meaning under each lexicon -/
def lexiconMeaning : CWSLexicon → CWSWorld → CWSUtterance → Bool
  | .strong_both, w, .A => literalTruth w .AandNotB
  | .strong_both, w, u => literalTruth w u
  | .strong_A, w, .A => literalTruth w .AandNotB
  | .strong_A, w, u => literalTruth w u
  | .strong_AB, w, u => literalTruth w u
  | .weak, w, u => literalTruth w u

-- QUDs for svRSA (Model 4)

/-- QUDs for supervaluationist RSA: full vs coarse resolution -/
inductive CWSQUD
  | full
  | coarse
  deriving DecidableEq, BEq, Repr, Inhabited

/-- QUD equivalence: when are two worlds equivalent under a QUD? -/
def qudEquiv : CWSQUD → CWSWorld → CWSWorld → Bool
  | .full, w1, w2 => w1 == w2
  | .coarse, _, _ => true

-- Wonky Goals for wRSA/BwRSA (Models 2-3)

/-- Speaker goal types for Bayesian wonky RSA (BwRSA, Model 3).

    - `informative`: Standard cooperative speaker who aims to inform
    - `wonky`: Non-cooperative speaker who doesn't distinguish worlds

    In wRSA (Model 2), wonkiness is a mixture parameter, not Bayesian inference.
    In BwRSA (Model 3), the listener reasons about which goal the speaker has. -/
inductive WonkyGoal where
  | informative : WonkyGoal
  | wonky : WonkyGoal
  deriving DecidableEq, BEq, Repr, Inhabited

/-- All wonky goals -/
def allWonkyGoals : List WonkyGoal := [.informative, .wonky]

theorem allWonkyGoals_length : allWonkyGoals.length = 2 := rfl

-- Model Parameters

/-- Configuration for a specific RSA model instance -/
structure CWSConfig where
  /-- Prior over worlds -/
  prior : CWSPrior
  /-- Utterance costs -/
  costs : CWSCosts
  /-- Rationality parameter -/
  alpha : ℕ := 1

/-- Default configuration: uniform prior, equal costs -/
def defaultConfig : CWSConfig where
  prior := uniformPrior
  costs := defaultCosts

/-- Anti-exhaustivity-inducing configuration -/
def antiExhConfig : CWSConfig where
  prior := stronglyBiasedPrior
  costs := defaultCosts

-- Key Theoretical Claims

/-- Central claim: Baseline RSA can be anti-exhaustive under biased priors.

    This is the core problem that Cremers et al. identify. Human listeners
    do NOT become anti-exhaustive even with strong prior bias. -/
def baselineAntiExhaustivityClaim : String :=
  "In baseline RSA with biased priors, L1(w_ab | A) > P(w_ab). " ++
  "This 'anti-exhaustive' interpretation is not observed in humans."

/-- Key insight: EXH blocks anti-exhaustivity by strengthening the meaning.

    When EXH is inserted, "A" means "A ∧ ¬B", which is false in w_ab.
    This forces L1(w_ab | A) = 0, eliminating anti-exhaustivity. -/
def exhBlocksAntiExhaustivityClaim : String :=
  "Grammatical EXH strengthens 'A' to 'A ∧ ¬B', which is false in w_ab. " ++
  "This blocks anti-exhaustive interpretations regardless of prior bias."

-- Summary

/-
## What This Module Provides

### Domain Types
- `CWSWorld`: Two worlds (w_a, w_ab)
- `CWSUtterance`: Three utterances (A, A∧B, A∧¬B)
- `CWSPrior`: Prior probability structure
- `CWSCosts`: Cost parameters

### Semantics
- `literalTruth`: Literal meaning
- `exhMeaning`: Exhaustified meaning (with EXH)
- `lexiconMeaning`: Meaning under each of 4 lexica

### Anti-Exhaustivity
- `antiExhaustivityCondition`: Equation 6 from the paper
- `antiExhaustivityHolds`: Decidable check
- Example showing biased priors trigger anti-exhaustivity

### Model Infrastructure
- `CWSParse`: literal vs exhaustified
- `CWSLexicon`: 4 lexica for FREE-LU
- `CWSQUD`: QUDs for svRSA
- `CWSConfig`: Model configuration

## Key Theorems
- `uniform_equal_no_antiexh`: Uniform prior + equal costs = no anti-exhaustivity
- `strongly_biased_triggers_antiexh`: Biased prior triggers anti-exhaustivity
- `exhA_only_in_wa`: EXH(A) is only true in w_a (blocks anti-exhaustivity)
-/

end CremersWilcoxSpector2023
