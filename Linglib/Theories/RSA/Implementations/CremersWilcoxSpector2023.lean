/-
# Cremers, Wilcox & Spector (2023): RSA Exhaustivity Models

Implementation of RSA models for exhaustivity and anti-exhaustivity.

## Models Implemented

| # | Model | Smart Constructor | Description |
|---|-------|-------------------|-------------|
| 1 | Baseline RSA | `RSAScenario.basic` | Standard RSA with costs |
| 4 | svRSA | `RSAScenario.qud` | QUD with supervaluationist semantics |
| 5 | FREE-LU | `RSAScenario.lexicalUncertainty` | Lexical uncertainty (4 lexica) |
| 6 | EXH-LU | Full `RSAScenario` | Key stress test: Interp=Parse, Lexicon=LU |

## Key Result

Baseline RSA predicts anti-exhaustivity under biased priors (L1(w_ab|A) > P(w_ab)),
which contradicts human behavior. EXH-LU blocks this by strengthening "A" to "A ∧ ¬B".

## Reference

Cremers, A., Wilcox, E., & Spector, B. (2023). "Exhaustivity and Anti-Exhaustivity
in the RSA Framework". Semantics & Pragmatics.
-/

import Linglib.Theories.RSA.Core.Basic
import Linglib.Phenomena.CremersWilcoxSpector2023.Data

namespace RSA.Implementations.CremersWilcoxSpector2023

open _root_.CremersWilcoxSpector2023
open RSA

-- ============================================================================
-- PART 1: Baseline RSA (Model 1)
-- ============================================================================

/-- Convert Bool meaning to ℚ (for RSA φ function) -/
def boolToQ (b : Bool) : ℚ := if b then 1 else 0

/-- Baseline RSA scenario for the CWS domain.

    This is standard RSA with literal semantics and costs.
    Under biased priors, this can produce anti-exhaustive interpretations
    where L1(w_ab | A) > P(w_ab). -/
def baselineScenario (cfg : CWSConfig) : RSAScenario :=
  RSAScenario.basic
    allUtterances
    allWorlds
    (fun u w => boolToQ (literalTruth w u))
    cfg.prior.prob
    cfg.alpha

/-- Baseline with uniform prior -/
def baselineUniform : RSAScenario := baselineScenario defaultConfig

/-- Baseline with biased prior (triggers anti-exhaustivity) -/
def baselineBiased : RSAScenario := baselineScenario antiExhConfig

-- ============================================================================
-- PART 2: Exhaustified RSA (Simple EXH model)
-- ============================================================================

/-- Meaning with parse-dependent exhaustification.

    - literal parse: use literal semantics
    - exh parse: use exhaustified semantics (EXH(A) = A ∧ ¬B) -/
def parseMeaning : CWSParse → CWSWorld → CWSUtterance → Bool
  | .literal, w, u => literalTruth w u
  | .exh, w, u => exhMeaning w u

/-- RSA scenario with EXH ambiguity (parse as Interp).

    Listener reasons about whether speaker used literal or EXH parse.
    This is a simplified version of EXH-LU with fixed lexicon. -/
def exhScenario (cfg : CWSConfig) : RSAScenario :=
  RSAScenario.ambiguousBool
    allUtterances
    allWorlds
    allParses
    (fun p w u => parseMeaning p w u)
    cfg.prior.prob
    (fun _ => 1)  -- Uniform prior over parses
    cfg.alpha

/-- EXH scenario with uniform prior -/
def exhUniform : RSAScenario := exhScenario defaultConfig

/-- EXH scenario with biased prior -/
def exhBiased : RSAScenario := exhScenario antiExhConfig

-- ============================================================================
-- PART 3: FREE-LU (Model 5) - Lexical Uncertainty
-- ============================================================================

/-- Convert lexicon meaning to ℚ -/
def lexiconMeaningQ (l : CWSLexicon) (u : CWSUtterance) (w : CWSWorld) : ℚ :=
  boolToQ (lexiconMeaning l w u)

/-- FREE-LU scenario: lexical uncertainty without EXH parses.

    Listener doesn't know which lexicon the speaker is using.
    This models uncertainty about whether "A" means A or A∧¬B. -/
def freeLUScenario (cfg : CWSConfig) : RSAScenario :=
  RSAScenario.lexicalUncertainty
    allUtterances
    allWorlds
    allLexica
    lexiconMeaningQ
    cfg.prior.prob
    (fun _ => 1)  -- Uniform prior over lexica
    cfg.alpha

/-- FREE-LU with uniform prior -/
def freeLUUniform : RSAScenario := freeLUScenario defaultConfig

/-- FREE-LU with biased prior -/
def freeLUBiased : RSAScenario := freeLUScenario antiExhConfig

-- ============================================================================
-- PART 4: svRSA (Model 4) - Supervaluationist QUD
-- ============================================================================

/-- svRSA scenario: QUD-sensitive with supervaluationist semantics.

    When QUD is coarse (only asking about A), the speaker doesn't need
    to distinguish w_a from w_ab, reducing anti-exhaustivity pressure. -/
def svRSAScenario (cfg : CWSConfig) : RSAScenario :=
  RSAScenario.qud
    allUtterances
    allWorlds
    [CWSQUD.full, CWSQUD.coarse]
    (fun u w => boolToQ (literalTruth w u))
    qudEquiv
    cfg.prior.prob
    (fun _ => 1)  -- Uniform prior over QUDs
    cfg.alpha

/-- svRSA with uniform prior -/
def svRSAUniform : RSAScenario := svRSAScenario defaultConfig

/-- svRSA with biased prior -/
def svRSABiased : RSAScenario := svRSAScenario antiExhConfig

-- ============================================================================
-- PART 5: EXH-LU (Model 6) - Full Integration
-- ============================================================================

/-- Combined meaning: parse-dependent exhaustification + lexicon uncertainty.

    This is the KEY stress test for the architecture:
    - Interp = CWSParse (literal vs exh)
    - Lexicon = CWSLexicon (4 lexica)
    - φ combines both -/
def exhLUMeaning (p : CWSParse) (l : CWSLexicon) (u : CWSUtterance) (w : CWSWorld) : ℚ :=
  match p with
  | .literal => boolToQ (lexiconMeaning l w u)
  | .exh =>
    -- Under EXH parse, strengthen A to A∧¬B regardless of lexicon
    match u with
    | .A => boolToQ (literalTruth w .AandNotB)
    | _ => boolToQ (lexiconMeaning l w u)

/-- EXH-LU scenario: Full model with both parse and lexicon uncertainty.

    This is the key test from Cremers et al. (2023):
    - Listener reasons about BOTH parse and lexicon
    - When EXH parse is inferred, anti-exhaustivity is blocked -/
def exhLUScenario (cfg : CWSConfig) : RSAScenario where
  Utterance := CWSUtterance
  World := CWSWorld
  Interp := CWSParse
  Lexicon := CWSLexicon
  BeliefState := Unit
  Goal := Unit
  φ := exhLUMeaning
  goalProject := fun _ w w' => w == w'
  speakerCredence := fun _ _ => 1
  utterances := allUtterances
  worlds := allWorlds
  interps := allParses
  lexica := allLexica
  beliefStates := [()]
  goals := [()]
  worldPrior := cfg.prior.prob
  interpPrior := fun _ => 1  -- Uniform over parses
  lexiconPrior := fun _ => 1  -- Uniform over lexica
  beliefStatePrior := fun _ => 1
  goalPrior := fun _ => 1
  α := cfg.alpha

/-- EXH-LU with uniform prior -/
def exhLUUniform : RSAScenario := exhLUScenario defaultConfig

/-- EXH-LU with biased prior -/
def exhLUBiased : RSAScenario := exhLUScenario antiExhConfig

-- ============================================================================
-- PART 6: wRSA (Model 2) - Non-Bayesian Wonky Mixture
-- ============================================================================

/-- wRSA: Non-Bayesian wonky world model (Model 2).

    This is NOT a standard Bayesian RSA model. L1 is computed as a mixture:
    L1(w | u) ∝ w_wonk × P(w) + (1 - w_wonk) × S1(u | w) × P(w)

    When w_wonk = 0: Standard RSA
    When w_wonk = 1: Listener just uses prior (speaker is totally uninformative)
    When 0 < w_wonk < 1: Mixture

    This reduces anti-exhaustivity because the wonky component pulls toward prior. -/
def wRSA_L1 (cfg : CWSConfig) (w_wonk : ℚ) (u : CWSUtterance) : List (CWSWorld × ℚ) :=
  let baseline := baselineScenario cfg
  -- For each world, compute mixture of prior and S1-derived posterior
  let scores := allWorlds.map fun w =>
    let priorW := cfg.prior.prob w
    -- Get baseline L1 (standard RSA posterior)
    let baselineL1 := RSA.getScore (RSA.L1_world baseline u) w
    -- Mixture: wonky component uses prior, non-wonky uses baseline L1
    let score := w_wonk * priorW + (1 - w_wonk) * baselineL1
    (w, score)
  RSA.normalize scores

/-- wRSA L1(w_ab | A) with given wonkiness parameter -/
def wRSA_L1_wab_given_A (cfg : CWSConfig) (w_wonk : ℚ) : ℚ :=
  RSA.getScore (wRSA_L1 cfg w_wonk .A) .w_ab

-- ============================================================================
-- PART 7: BwRSA (Model 3) - Bayesian Wonky Inference
-- ============================================================================

/-- BwRSA goal projection: how goals partition worlds.

    - informative: Full partition (distinguish all worlds)
    - wonky: Trivial partition (all worlds equivalent, speaker doesn't care) -/
def wonkyGoalProject : WonkyGoal → CWSWorld → CWSWorld → Bool
  | .informative, w1, w2 => w1 == w2  -- Standard: distinguish worlds
  | .wonky, _, _ => true              -- Wonky: all worlds equivalent

/-- BwRSA scenario: Bayesian reasoning about wonky vs informative goals.

    Unlike wRSA, this is proper Bayesian RSA where the listener infers
    which goal the speaker has. When goal = wonky, the speaker doesn't
    try to distinguish worlds, so "A" is equally likely in both worlds.

    This is mathematically equivalent to a QUD-sensitive model where one
    QUD is trivial (coarse). -/
def bwRSAScenario (cfg : CWSConfig) (p_wonk : ℚ) : RSAScenario :=
  RSAScenario.qud
    allUtterances
    allWorlds
    allWonkyGoals
    (fun u w => boolToQ (literalTruth w u))
    wonkyGoalProject
    cfg.prior.prob
    (fun g => match g with | .wonky => p_wonk | .informative => 1 - p_wonk)
    cfg.alpha

/-- BwRSA with uniform prior, 50% wonky -/
def bwRSAUniform : RSAScenario := bwRSAScenario defaultConfig (1/2)

/-- BwRSA with biased prior, 50% wonky -/
def bwRSABiased : RSAScenario := bwRSAScenario antiExhConfig (1/2)

/-- BwRSA L1(w_ab | A) -/
def bwRSA_L1_wab_given_A (cfg : CWSConfig) (p_wonk : ℚ) : ℚ :=
  RSA.getScore (RSA.L1_world (bwRSAScenario cfg p_wonk) .A) .w_ab

-- ============================================================================
-- PART 8: RSA-LI (Models 7-8) - Lexical Intentions
-- ============================================================================

/-
RSA-LI: Lexical Intentions model.

In RSA-LI, the speaker INTENTIONALLY chooses a lexicon (not just uncertainty).
The key insight: RSA-LI is computationally equivalent to FREE-LU when
extracting world predictions via L1_world (marginalize over lexica).

The difference is in interpretation:
- FREE-LU: Listener is uncertain about lexicon
- RSA-LI: Listener infers speaker's intentional lexicon choice

For world predictions, they're equivalent because both marginalize.

Models 7 (uniform lexicon prior) and 8 (biased lexicon prior) differ only
in the lexiconPrior parameter.
-/

/-- RSA-LI scenario with uniform lexicon prior (Model 7).

    Uniform prior over all 4 lexica. -/
def rsaLI_uniform_Scenario (cfg : CWSConfig) : RSAScenario :=
  freeLUScenario cfg  -- Computationally equivalent to FREE-LU

/-- RSA-LI scenario with biased lexicon prior (Model 8).

    Biases toward the "weak" (literal) lexicon. This models the assumption
    that speakers default to literal meanings unless there's reason not to. -/
def rsaLI_biased_Scenario (cfg : CWSConfig) (p_weak : ℚ) : RSAScenario :=
  RSAScenario.lexicalUncertainty
    allUtterances
    allWorlds
    allLexica
    lexiconMeaningQ
    cfg.prior.prob
    (fun l => match l with
      | .weak => p_weak
      | _ => (1 - p_weak) / 3)  -- Split remaining probability equally
    cfg.alpha

/-- RSA-LI (uniform) with biased world prior -/
def rsaLI_uniform_Biased : RSAScenario := rsaLI_uniform_Scenario antiExhConfig

/-- RSA-LI (biased toward weak) with biased world prior, 50% weak -/
def rsaLI_biased_Biased : RSAScenario := rsaLI_biased_Scenario antiExhConfig (1/2)

/-- RSA-LI L1(w_ab | A) with uniform lexicon prior -/
def rsaLI_uniform_L1_wab_given_A (cfg : CWSConfig) : ℚ :=
  RSA.getScore (RSA.L1_world (rsaLI_uniform_Scenario cfg) .A) .w_ab

/-- RSA-LI L1(w_ab | A) with biased lexicon prior -/
def rsaLI_biased_L1_wab_given_A (cfg : CWSConfig) (p_weak : ℚ) : ℚ :=
  RSA.getScore (RSA.L1_world (rsaLI_biased_Scenario cfg p_weak) .A) .w_ab

/-- Get L1 distribution over lexica (for RSA-LI interpretation).

    This shows which lexicon the listener infers the speaker intended. -/
def rsaLI_L1_lexicon (cfg : CWSConfig) (u : CWSUtterance) : List (CWSLexicon × ℚ) :=
  RSA.L1_lexicon (rsaLI_uniform_Scenario cfg) u

-- ============================================================================
-- PART 9: Verification - Dimensions
-- ============================================================================

/-- Baseline scenario has correct dimensions: 3 utterances × 2 worlds -/
theorem baseline_dimensions :
    baselineUniform.utterances.length = 3 ∧
    baselineUniform.worlds.length = 2 := by
  constructor <;> native_decide

/-- EXH scenario has correct dimensions: 3 utterances × 2 worlds × 2 parses -/
theorem exh_dimensions :
    exhUniform.utterances.length = 3 ∧
    exhUniform.worlds.length = 2 ∧
    exhUniform.interps.length = 2 := by
  constructor
  · native_decide
  · constructor <;> native_decide

/-- FREE-LU has 4 lexica -/
theorem freeLU_dimensions :
    freeLUUniform.lexica.length = 4 := by
  native_decide

/-- EXH-LU has correct full dimensions: 3 × 2 × 2 × 4 -/
theorem exhLU_dimensions :
    exhLUUniform.utterances.length = 3 ∧
    exhLUUniform.worlds.length = 2 ∧
    exhLUUniform.interps.length = 2 ∧
    exhLUUniform.lexica.length = 4 := by
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  · native_decide

/-- BwRSA has 2 goals (informative, wonky) -/
theorem bwRSA_dimensions :
    bwRSAUniform.goals.length = 2 := by
  native_decide

-- ============================================================================
-- PART 10: Anti-Exhaustivity Analysis
-- ============================================================================

/-- Compute L1 distribution over worlds for baseline RSA -/
def baselineL1_world (cfg : CWSConfig) (u : CWSUtterance) : List (CWSWorld × ℚ) :=
  L1_world (baselineScenario cfg) u

/-- Compute L1 distribution over worlds for EXH-LU -/
def exhLU_L1_world (cfg : CWSConfig) (u : CWSUtterance) : List (CWSWorld × ℚ) :=
  L1_world (exhLUScenario cfg) u

/-- Get L1 probability of a specific world -/
def getL1Prob (dist : List (CWSWorld × ℚ)) (w : CWSWorld) : ℚ :=
  RSA.getScore dist w

/-- Helper: baseline L1(w_ab | A) -/
def baselineL1_wab_given_A (cfg : CWSConfig) : ℚ :=
  getL1Prob (baselineL1_world cfg .A) .w_ab

/-- Helper: EXH-LU L1(w_ab | A) -/
def exhLU_L1_wab_given_A (cfg : CWSConfig) : ℚ :=
  getL1Prob (exhLU_L1_world cfg .A) .w_ab

-- ============================================================================
-- PART 11: Key Theorems - Baseline Behavior
-- ============================================================================

/-- Under uniform prior, baseline RSA does NOT produce anti-exhaustivity.

    L1(w_ab | A) ≤ P(w_ab) when prior is uniform. -/
theorem baseline_uniform_no_antiexh :
    baselineL1_wab_given_A defaultConfig ≤ uniformPrior.p_wab := by
  native_decide

/-- Under biased prior, baseline RSA CAN produce anti-exhaustivity.

    This is the problematic prediction that Cremers et al. identify:
    When P(w_ab) / P(w_a) > 1, we get L1(w_ab | A) > P(w_ab). -/
theorem baseline_biased_antiexh :
    baselineL1_wab_given_A antiExhConfig > stronglyBiasedPrior.p_wab := by
  native_decide

/-- EXH meaning is only true in w_a (key property).

    This is why EXH blocks anti-exhaustivity: EXH(A) = A ∧ ¬B is false in w_ab. -/
theorem exh_meaning_blocks_wab :
    exhMeaning .w_ab .A = false := by rfl

-- ============================================================================
-- PART 12: Key Theorems - Model Comparison
-- ============================================================================

/-- With EXH-LU under biased prior, anti-exhaustivity is reduced.

    When EXH parse is possible, the strengthened meaning blocks
    excessive posterior on w_ab. -/
theorem exhLU_reduces_antiexh :
    exhLU_L1_wab_given_A antiExhConfig ≤ baselineL1_wab_given_A antiExhConfig := by
  native_decide

/-- wRSA with non-zero wonkiness reduces anti-exhaustivity.

    The wonky component pulls the posterior toward the prior, reducing
    the anti-exhaustive boost that baseline RSA provides to w_ab. -/
theorem wRSA_reduces_antiexh :
    wRSA_L1_wab_given_A antiExhConfig (1/2) < baselineL1_wab_given_A antiExhConfig := by
  native_decide

/-- BwRSA reduces anti-exhaustivity compared to baseline.

    When the listener considers that the speaker might be wonky,
    they discount the informativity of "A" about B. -/
theorem bwRSA_reduces_antiexh :
    bwRSA_L1_wab_given_A antiExhConfig (1/2) < baselineL1_wab_given_A antiExhConfig := by
  native_decide

/-- RSA-LI (uniform) world predictions match FREE-LU.

    This validates that RSA-LI and FREE-LU are computationally equivalent
    when extracting world predictions (marginalized over lexica). -/
theorem rsaLI_matches_freeLU_L1_world :
    rsaLI_uniform_L1_wab_given_A antiExhConfig =
    RSA.getScore (L1_world (freeLUScenario antiExhConfig) .A) .w_ab := by
  native_decide

/-- FREE-LU reduces anti-exhaustivity compared to baseline.

    Lexical uncertainty allows the listener to infer strengthened meanings,
    reducing anti-exhaustive interpretations. -/
theorem freeLU_reduces_antiexh :
    RSA.getScore (L1_world (freeLUScenario antiExhConfig) .A) .w_ab ≤
    baselineL1_wab_given_A antiExhConfig := by
  native_decide

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This Module Provides

### RSA Scenarios (All 9 Models from CWS 2023)

| # | Model | Constructor | Status |
|---|-------|-------------|--------|
| 1 | Baseline RSA | `baselineScenario` | ✓ |
| 2 | wRSA | `wRSA_L1` (custom L1) | ✓ |
| 3 | BwRSA | `bwRSAScenario` | ✓ |
| 4 | svRSA | `svRSAScenario` | ✓ |
| 5 | FREE-LU | `freeLUScenario` | ✓ |
| 6 | EXH-LU | `exhLUScenario` | ✓ |
| 7 | RSA-LI (uniform) | `rsaLI_uniform_Scenario` | ✓ |
| 8 | RSA-LI (biased) | `rsaLI_biased_Scenario` | ✓ |

### Analysis Functions
- `baselineL1_world`: Compute L1 for baseline
- `exhLU_L1_world`: Compute L1 for EXH-LU
- `wRSA_L1`: Non-Bayesian wonky mixture L1
- `bwRSA_L1_wab_given_A`: BwRSA posterior on w_ab
- `rsaLI_L1_lexicon`: Inferred lexicon distribution (for RSA-LI)
- `getL1Prob`: Extract probability for a world

### Key Theorems

**Baseline behavior:**
- `baseline_uniform_no_antiexh`: Uniform prior → no anti-exhaustivity
- `baseline_biased_antiexh`: Biased prior → anti-exhaustivity (the problem)
- `exh_meaning_blocks_wab`: EXH(A) is false in w_ab (why EXH works)

**Model comparison (all reduce anti-exhaustivity):**
- `exhLU_reduces_antiexh`: EXH-LU ≤ baseline
- `wRSA_reduces_antiexh`: wRSA < baseline
- `bwRSA_reduces_antiexh`: BwRSA < baseline
- `freeLU_reduces_antiexh`: FREE-LU ≤ baseline

**Equivalences:**
- `rsaLI_matches_freeLU_L1_world`: RSA-LI = FREE-LU for world predictions

## Architecture Validation

This module validates that the RSAScenario architecture can:
1. Support BOTH Interp AND Lexicon latent variables simultaneously
2. Compute correct L1 distributions with the full 5-latent-variable model
3. Handle non-standard models (wRSA mixture) via custom L1 functions
4. Model goal/QUD reasoning (BwRSA, svRSA) with the Goal type
5. Demonstrate all theoretically predicted effects (anti-exhaustivity reduction)

## Model Insights

The 9 models collapse into 5 computational patterns:
1. **Standard RSA**: `RSAScenario.basic` (Model 1)
2. **QUD/Goal RSA**: `RSAScenario.qud` or Goal dimension (Models 3, 4)
3. **Lexical Uncertainty RSA**: `RSAScenario.lexicalUncertainty` (Models 5, 7, 8)
4. **Full multi-latent RSA**: Full RSAScenario (Model 6)
5. **Non-Bayesian mixture**: Custom function (Model 2)
-/

end RSA.Implementations.CremersWilcoxSpector2023
