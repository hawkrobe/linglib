/-
# Cremers, Wilcox & Spector (2023): RSA Exhaustivity Models

RSA models for exhaustivity and anti-exhaustivity. Baseline RSA predicts anti-exhaustivity
under biased priors, which contradicts human behavior. EXH-LU blocks this via exhaustification.

## Main definitions

`baselineL1`, `exhL1`, `freeLU_L1`, `svRSA_L1`, `exhLU_L1`, `wRSA_L1`, `bwRSA_L1`,
`rsaLI_uniform_L1`, `rsaLI_biased_L1`

## References

Cremers, A., Wilcox, E., & Spector, B. (2023). Exhaustivity and Anti-Exhaustivity
in the RSA Framework. Semantics & Pragmatics.
-/

import Linglib.Theories.RSA.Core.Basic
import Linglib.Theories.RSA.Core.Eval
import Linglib.Phenomena.ScalarImplicatures.Studies.CremersWilcoxSpector2023

namespace RSA.Implementations.CremersWilcoxSpector2023

open Phenomena.ScalarImplicatures.Studies.CremersWilcoxSpector2023


/-- Convert Bool meaning to ℚ (for RSA φ function) -/
def boolToQ (b : Bool) : ℚ := if b then 1 else 0

/-- Compute L1 for baseline RSA using RSA.Eval -/
def baselineL1 (cfg : CWSConfig) (u : CWSUtterance) : List (CWSWorld × ℚ) :=
  RSA.Eval.basicL1 allUtterances allWorlds
    (λ u w => boolToQ (literalTruth w u))
    cfg.prior.prob cfg.alpha (λ _ => 0) u


/-- Meaning with parse-dependent exhaustification.

    - literal parse: use literal semantics
    - exh parse: use exhaustified semantics (EXH(A) = A ∧ ¬B) -/
def parseMeaning : CWSParse → CWSWorld → CWSUtterance → Bool
  | .literal, w, u => literalTruth w u
  | .exh, w, u => exhMeaning w u

/-- Compute L1 for EXH model (with parse ambiguity) using RSA.Eval -/
def exhL1 (cfg : CWSConfig) (u : CWSUtterance) : List (CWSWorld × ℚ) :=
  RSA.Eval.L1_world allUtterances allWorlds allParses [()] [()] [()]
    (λ p _ u w => boolToQ (parseMeaning p w u))
    cfg.prior.prob (λ _ => 1) (λ _ => 1) (λ _ => 1) (λ _ => 1)
    (λ _ _ => 1) (λ _ w w' => w == w') (λ _ => 0) cfg.alpha u


/-- Convert lexicon meaning to ℚ -/
def lexiconMeaningQ (l : CWSLexicon) (u : CWSUtterance) (w : CWSWorld) : ℚ :=
  boolToQ (lexiconMeaning l w u)

/-- Compute L1 for FREE-LU using RSA.Eval -/
def freeLU_L1 (cfg : CWSConfig) (u : CWSUtterance) : List (CWSWorld × ℚ) :=
  RSA.Eval.L1_world allUtterances allWorlds [()] allLexica [()] [()]
    (λ _ l u w => lexiconMeaningQ l u w)
    cfg.prior.prob (λ _ => 1) (λ _ => 1) (λ _ => 1) (λ _ => 1)
    (λ _ _ => 1) (λ _ w w' => w == w') (λ _ => 0) cfg.alpha u


/-- Compute L1 for svRSA using RSA.Eval -/
def svRSA_L1 (cfg : CWSConfig) (u : CWSUtterance) : List (CWSWorld × ℚ) :=
  RSA.Eval.L1_world allUtterances allWorlds [()] [()] [()] [CWSQUD.full, CWSQUD.coarse]
    (λ _ _ u w => boolToQ (literalTruth w u))
    cfg.prior.prob (λ _ => 1) (λ _ => 1) (λ _ => 1) (λ _ => 1)
    (λ _ _ => 1) (λ q w w' => qudEquiv q w w') (λ _ => 0) cfg.alpha u


/-- Combined meaning: parse-dependent exhaustification + lexicon uncertainty.

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

/-- Compute L1 for EXH-LU using RSA.Eval -/
def exhLU_L1 (cfg : CWSConfig) (u : CWSUtterance) : List (CWSWorld × ℚ) :=
  RSA.Eval.L1_world allUtterances allWorlds allParses allLexica [()] [()]
    (λ p l u w => exhLUMeaning p l u w)
    cfg.prior.prob (λ _ => 1) (λ _ => 1) (λ _ => 1) (λ _ => 1)
    (λ _ _ => 1) (λ _ w w' => w == w') (λ _ => 0) cfg.alpha u


/-- wRSA: Non-Bayesian wonky world model (Model 2).

    This is not a standard Bayesian RSA model. L1 is computed as a mixture:
    L1(w | u) ∝ w_wonk × P(w) + (1 - w_wonk) × S1(u | w) × P(w)

    When w_wonk = 0: Standard RSA
    When w_wonk = 1: Listener just uses prior (speaker is totally uninformative)
    When 0 < w_wonk < 1: Mixture

    This reduces anti-exhaustivity because the wonky component pulls toward prior. -/
def wRSA_L1 (cfg : CWSConfig) (w_wonk : ℚ) (u : CWSUtterance) : List (CWSWorld × ℚ) :=
  let baseL1 := baselineL1 cfg u
  -- For each world, compute mixture of prior and S1-derived posterior
  let scores := allWorlds.map λ w =>
    let priorW := cfg.prior.prob w
    -- Get baseline L1 (standard RSA posterior)
    let baselineL1w := RSA.Eval.getScore baseL1 w
    -- Mixture: wonky component uses prior, non-wonky uses baseline L1
    let score := w_wonk * priorW + (1 - w_wonk) * baselineL1w
    (w, score)
  RSA.Eval.normalize scores

/-- wRSA L1(w_ab | A) with given wonkiness parameter -/
def wRSA_L1_wab_given_A (cfg : CWSConfig) (w_wonk : ℚ) : ℚ :=
  RSA.Eval.getScore (wRSA_L1 cfg w_wonk .A) .w_ab


/-- BwRSA goal projection: how goals partition worlds.

    - informative: Full partition (distinguish all worlds)
    - wonky: Trivial partition (all worlds equivalent, speaker doesn't care) -/
def wonkyGoalProject : WonkyGoal → CWSWorld → CWSWorld → Bool
  | .informative, w1, w2 => w1 == w2  -- Standard: distinguish worlds
  | .wonky, _, _ => true              -- Wonky: all worlds equivalent

/-- Compute L1 for BwRSA using RSA.Eval -/
def bwRSA_L1 (cfg : CWSConfig) (p_wonk : ℚ) (u : CWSUtterance) : List (CWSWorld × ℚ) :=
  RSA.Eval.L1_world allUtterances allWorlds [()] [()] [()] allWonkyGoals
    (λ _ _ u w => boolToQ (literalTruth w u))
    cfg.prior.prob (λ _ => 1) (λ _ => 1) (λ _ => 1)
    (λ g => match g with | .wonky => p_wonk | .informative => 1 - p_wonk)
    (λ _ _ => 1) wonkyGoalProject (λ _ => 0) cfg.alpha u

/-- BwRSA L1(w_ab | A) -/
def bwRSA_L1_wab_given_A (cfg : CWSConfig) (p_wonk : ℚ) : ℚ :=
  RSA.Eval.getScore (bwRSA_L1 cfg p_wonk .A) .w_ab


/-
RSA-LI: Lexical Intentions model.

In RSA-LI, the speaker intentionally chooses a lexicon (not just uncertainty).
RSA-LI is computationally equivalent to FREE-LU when extracting world
predictions via L1_world (marginalize over lexica).

The difference is in interpretation:
- FREE-LU: Listener is uncertain about lexicon
- RSA-LI: Listener infers speaker's intentional lexicon choice

For world predictions, they're equivalent because both marginalize.

Models 7 (uniform lexicon prior) and 8 (biased lexicon prior) differ only
in the lexiconPrior parameter.
-/

/-- Compute L1 for RSA-LI with uniform lexicon prior (Model 7) -/
def rsaLI_uniform_L1 (cfg : CWSConfig) (u : CWSUtterance) : List (CWSWorld × ℚ) :=
  freeLU_L1 cfg u  -- Computationally equivalent to FREE-LU

/-- Compute L1 for RSA-LI with biased lexicon prior (Model 8) -/
def rsaLI_biased_L1 (cfg : CWSConfig) (p_weak : ℚ) (u : CWSUtterance) : List (CWSWorld × ℚ) :=
  RSA.Eval.L1_world allUtterances allWorlds [()] allLexica [()] [()]
    (λ _ l u w => lexiconMeaningQ l u w)
    cfg.prior.prob (λ _ => 1)
    (λ l => match l with
      | .weak => p_weak
      | _ => (1 - p_weak) / 3)  -- Split remaining probability equally
    (λ _ => 1) (λ _ => 1)
    (λ _ _ => 1) (λ _ w w' => w == w') (λ _ => 0) cfg.alpha u

/-- RSA-LI L1(w_ab | A) with uniform lexicon prior -/
def rsaLI_uniform_L1_wab_given_A (cfg : CWSConfig) : ℚ :=
  RSA.Eval.getScore (rsaLI_uniform_L1 cfg .A) .w_ab

/-- RSA-LI L1(w_ab | A) with biased lexicon prior -/
def rsaLI_biased_L1_wab_given_A (cfg : CWSConfig) (p_weak : ℚ) : ℚ :=
  RSA.Eval.getScore (rsaLI_biased_L1 cfg p_weak .A) .w_ab


/-- Verify utterance count -/
theorem utterance_count : allUtterances.length = 3 := by native_decide

/-- Verify world count -/
theorem world_count : allWorlds.length = 2 := by native_decide

/-- Verify parse count -/
theorem parse_count : allParses.length = 2 := by native_decide

/-- Verify lexica count -/
theorem lexica_count : allLexica.length = 4 := by native_decide

/-- Verify wonky goals count -/
theorem wonky_goals_count : allWonkyGoals.length = 2 := by native_decide


/-- Compute L1 distribution over worlds for baseline RSA -/
def baselineL1_world (cfg : CWSConfig) (u : CWSUtterance) : List (CWSWorld × ℚ) :=
  baselineL1 cfg u

/-- Compute L1 distribution over worlds for EXH-LU -/
def exhLU_L1_world (cfg : CWSConfig) (u : CWSUtterance) : List (CWSWorld × ℚ) :=
  exhLU_L1 cfg u

/-- Get L1 probability of a specific world -/
def getL1Prob (dist : List (CWSWorld × ℚ)) (w : CWSWorld) : ℚ :=
  RSA.Eval.getScore dist w

/-- Helper: baseline L1(w_ab | A) -/
def baselineL1_wab_given_A (cfg : CWSConfig) : ℚ :=
  getL1Prob (baselineL1_world cfg .A) .w_ab

/-- Helper: EXH-LU L1(w_ab | A) -/
def exhLU_L1_wab_given_A (cfg : CWSConfig) : ℚ :=
  getL1Prob (exhLU_L1_world cfg .A) .w_ab


/-- Under uniform prior, baseline RSA does not produce anti-exhaustivity.

    L1(w_ab | A) ≤ P(w_ab) when prior is uniform. -/
theorem baseline_uniform_no_antiexh :
    baselineL1_wab_given_A defaultConfig ≤ uniformPrior.p_wab := by
  native_decide

/-- Under biased prior, baseline RSA can produce anti-exhaustivity.

    This is the problematic prediction that Cremers et al. identify:
    When P(w_ab) / P(w_a) > 1, we get L1(w_ab | A) > P(w_ab). -/
theorem baseline_biased_antiexh :
    baselineL1_wab_given_A antiExhConfig > stronglyBiasedPrior.p_wab := by
  native_decide

/-- EXH meaning is only true in w_a.

    EXH blocks anti-exhaustivity because EXH(A) = A ∧ ¬B is false in w_ab. -/
theorem exh_meaning_blocks_wab :
    exhMeaning .w_ab .A = false := by rfl


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
    RSA.Eval.getScore (freeLU_L1 antiExhConfig .A) .w_ab := by
  native_decide

/-- FREE-LU reduces anti-exhaustivity compared to baseline.

    Lexical uncertainty allows the listener to infer strengthened meanings,
    reducing anti-exhaustive interpretations. -/
theorem freeLU_reduces_antiexh :
    RSA.Eval.getScore (freeLU_L1 antiExhConfig .A) .w_ab ≤
    baselineL1_wab_given_A antiExhConfig := by
  native_decide

end RSA.Implementations.CremersWilcoxSpector2023
