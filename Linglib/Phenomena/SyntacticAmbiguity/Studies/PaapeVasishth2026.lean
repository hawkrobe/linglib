import Linglib.Phenomena.SyntacticAmbiguity.Basic

/-!
# Paape & Vasishth (2026) @cite{paape-vasishth-2026}

Context ameliorates but does not eliminate garden-pathing: Novel insights
from latent-process modeling. *Journal of Memory and Language* 148, 104748.

## Overview

The paper replicates @cite{altmann-garnham-dennis-1992}'s CC/RC × referential
context design (3×2: {amb-CC, amb-RC, unamb-RC} × {unique, non-unique referents})
with N = 319 using masked bidirectional self-paced reading (BSPR). The central
contribution is a **multinomial processing tree (MPT)** model that decomposes
reading time distributions into latent cognitive processes: attention, first-pass
attachment (garden-pathing), optional triage, covert/overt reanalysis, and
success/failure.

## Key Findings

The MPT decomposition yields three conclusions (p. 11) unavailable from
standard factorial comparison of means:

I.  Regardless of context, RC disambiguation results in a higher probability
    of garden-pathing (choosing an incorrect first-pass parse).
II. Contextual match decreases but does not eliminate the first-pass anti-RC bias.
III. The cost of in-situ reanalysis is higher for RC than for CC disambiguation,
     and is lower but still non-zero in cases of context match versus mismatch.

## MPT vs. Surprisal

The no-triage MPT outperforms LLM surprisal-based models (GPT-2, LLaMA-2,
Mistral, Falcon) and standard factorial models in cross-validated predictive
fit (PSIS-LOO elpd). The key architectural difference: the MPT assumes reading
times at disambiguation are *mixture distributions* — bimodal with garden-pathed
(slow) and non-garden-pathed (fast) components. Surprisal-based models assume
unimodal distributions shifted by surprisal value, which cannot capture this
bimodality (@cite{van-schijndel-linzen-2021}, @cite{huang-etal-2024}).

## Connections

- `Basic.lean`: Reuses `Disambiguation`, `ReferentialContext`, `Condition`,
  `disambiguationProfile`, `rc_pareto_harder`
- `Core.ProcessingModel`: Ordinal profile bridge (§ 7)
-/

namespace Phenomena.SyntacticAmbiguity.Studies.PaapeVasishth2026

open Phenomena.SyntacticAmbiguity

-- ════════════════════════════════════════════════════
-- § 1. Multinomial Processing Tree
-- ════════════════════════════════════════════════════

/-! ### MPT Structure (Fig. 1)

The MPT models each trial as a cascade of probabilistic binary decisions.
Each path through the tree yields a distinct combination of processing
stages and a corresponding reading time distribution.

The full MPT includes a **triage** path (garden-pathed readers sometimes
reject immediately without reanalysis). The best-fitting model variant
(no-triage MPT) drops this path, but we include it in the type for
completeness. -/

/-- Outcome of a single trial through the processing cascade.

Each constructor corresponds to a leaf node in the MPT (Fig. 1),
determining which processing costs accumulate and whether the
sentence is ultimately accepted or rejected. -/
inductive TrialOutcome where
  /-- Inattentive trial: biased guess (accept with p_bias ≈ 0.79).
      Fast reading time, no garden-path processing. -/
  | inattentive
  /-- Attentive, correct first-pass parse: no garden-pathing. -/
  | correctFirstPass
  /-- Garden-pathed, triaged: reader rejects immediately without
      attempting reanalysis. Present in the full MPT but dropped
      in the best-fitting no-triage variant. -/
  | triage
  /-- Garden-pathed, overt reanalysis (regression to earlier material),
      reanalysis succeeds. -/
  | overtSuccess
  /-- Garden-pathed, overt reanalysis (regression), fails → reject. -/
  | overtFail
  /-- Garden-pathed, covert (in-situ) reanalysis, immediate, succeeds. -/
  | covertImmediateSuccess
  /-- Garden-pathed, covert reanalysis, immediate, fails → reject. -/
  | covertImmediateFail
  /-- Garden-pathed, covert reanalysis, postponed to spillover, succeeds. -/
  | covertPostponedSuccess
  /-- Garden-pathed, covert reanalysis, postponed to spillover, fails → reject. -/
  | covertPostponedFail
  deriving DecidableEq, Repr, BEq

/-- Whether a trial outcome involves garden-pathing. -/
def TrialOutcome.isGardenPathed : TrialOutcome → Bool
  | .inattentive       => false
  | .correctFirstPass  => false
  | _                  => true

/-- Whether a trial outcome results in sentence acceptance. -/
def TrialOutcome.accepted : TrialOutcome → Bool
  | .inattentive              => true   -- biased guess (≈79% accept)
  | .correctFirstPass         => true
  | .covertImmediateSuccess   => true
  | .covertPostponedSuccess   => true
  | .overtSuccess             => true
  | _                         => false

/-- Whether a trial outcome involves a first-pass regression
    (rereading earlier material). In the MPT, regressions occur only
    on the overt reanalysis path. Covert reanalysis is signaled by
    in-situ reading slowdown, not regression. -/
def TrialOutcome.hasRegression : TrialOutcome → Bool
  | .overtSuccess => true
  | .overtFail    => true
  | _             => false

-- ════════════════════════════════════════════════════
-- § 2. MPT Parameters
-- ════════════════════════════════════════════════════

/-! ### Process Probabilities

Each branching node in the MPT has a probability parameter. Some parameters
are affected by the experimental manipulation; the predictor structure is:

- `p_gp ~ context + disambiguation + context : disambiguation`
- `p_covert_success ~ disambiguation + match`
- `p_overt_success ~ disambiguation + match`
- `covert_reanalysis_cost ~ disambiguation + match`

Parameters `p_attentive`, `p_covert`, `p_postpone` can vary between
participants but are not assumed to vary by condition.

Estimated via Bayesian inference in Stan (4 MCMC chains × 2000 iterations,
1000 burn-in each). -/

/-- The probability parameters of the MPT model.
    Values are stored as percentages (0–100). -/
structure MPTParams where
  pAttentive : Nat        -- Prob. of reading attentively
  pGardenPath : Nat       -- Prob. of incorrect first-pass parse
  pCovert : Nat           -- Prob. covert (vs overt) reanalysis
  pPostpone : Nat         -- Prob. of postponing covert reanalysis
  pCovertSuccess : Nat    -- Prob. covert reanalysis succeeds
  pOvertSuccess : Nat     -- Prob. overt reanalysis succeeds
  deriving Repr

-- ════════════════════════════════════════════════════
-- § 3. Experimental Design and Conditions
-- ════════════════════════════════════════════════════

/-! ### Study Design

Replication of @cite{altmann-garnham-dennis-1992} with N = 319 English
speakers (Prolific) via masked BSPR with end-of-sentence acceptability
judgments. 36 stimulus sentences adapted from the original (replacing
*told* with varied verbs per @cite{staub-etal-2018}), crossed with
2-level context (unique vs. non-unique referents). -/

/-- Experimental conditions in the 3 × 2 design. -/
inductive ExpCondition where
  | ambCC_unique         -- ambiguous CC, unique referent (man and woman)
  | ambCC_nonUnique      -- ambiguous CC, non-unique referents (two women)
  | ambRC_unique         -- ambiguous RC, unique referent
  | ambRC_nonUnique      -- ambiguous RC, non-unique referents
  | unambRC_unique       -- unambiguous RC, unique referent
  | unambRC_nonUnique    -- unambiguous RC, non-unique referents
  deriving DecidableEq, Repr, BEq

/-- Map experimental conditions to the abstract Condition type. -/
def ExpCondition.toCondition : ExpCondition → Condition
  | .ambCC_unique       => ⟨.complementClause, .uniqueReferent⟩
  | .ambCC_nonUnique    => ⟨.complementClause, .nonUniqueReferents⟩
  | .ambRC_unique       => ⟨.relativeClause, .uniqueReferent⟩
  | .ambRC_nonUnique    => ⟨.relativeClause, .nonUniqueReferents⟩
  | .unambRC_unique     => ⟨.relativeClause, .uniqueReferent⟩
  | .unambRC_nonUnique  => ⟨.relativeClause, .nonUniqueReferents⟩

/-- Matching conditions verified. -/
theorem ambRC_nonUnique_matches :
    (ExpCondition.ambRC_nonUnique.toCondition).isMatch = true := by native_decide

theorem ambCC_unique_matches :
    (ExpCondition.ambCC_unique.toCondition).isMatch = true := by native_decide

theorem ambRC_unique_mismatches :
    (ExpCondition.ambRC_unique.toCondition).isMatch = false := by native_decide

theorem ambCC_nonUnique_mismatches :
    (ExpCondition.ambCC_nonUnique.toCondition).isMatch = false := by native_decide

-- ════════════════════════════════════════════════════
-- § 4. Bayesian Factorial Analysis (Tables 2–3)
-- ════════════════════════════════════════════════════

/-! ### Bayesian Analysis Results

Standard Bayesian linear mixed-effects analysis using brms, with sum
contrasts for CONTEXT (unique = −1, non-unique = +1) and treatment
contrasts for DISAMBIGUATION (amb-RC = baseline). Lognormal likelihood
for first-pass reading times (FPRT), Bernoulli for first-pass regressions.

BF10 values > 3 indicate evidence for the alternative hypothesis. We record
the critical region effects, which are the earliest measures potentially
affected by garden-pathing. -/

/-- Bayes factor (BF10) for key effects at the critical disambiguating region.
    BF10 > 3 indicates evidence; values >1000 are decisive. -/
structure CriticalRegionBF where
  label : String
  bf10 : Nat              -- BF10 (truncated to Nat; >1000 stored as 1000)
  deriving Repr

/-- Key Bayesian analysis results from Table 2 (critical region). -/
def bayesianResults : List CriticalRegionBF :=
  [ ⟨"context (FPRT)",                1000⟩   -- BF10 > 1000
  , ⟨"CC vs RC (FPRT)",               467⟩    -- BF10 = 467.40
  , ⟨"unambRC vs RC (FPRT)",          611⟩    -- BF10 = 611.36
  , ⟨"context × CC (FPRT)",           1000⟩   -- BF10 > 1000
  , ⟨"context × unambRC (FPRT)",      4⟩      -- BF10 = 4.73
  , ⟨"context (regressions)",         46⟩     -- BF10 = 46.68
  , ⟨"context × CC (regressions)",    10⟩     -- BF10 = 10.57
  ]

/-- All recorded Bayes factors exceed the evidence threshold of 3. -/
theorem all_effects_evidenced :
    bayesianResults.all (·.bf10 > 3) = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 5. MPT Parameter Estimates (No-Triage Model)
-- ════════════════════════════════════════════════════

/-! ### Parameter Estimates

The no-triage MPT model achieves the best cross-validated predictive fit
(Fig. 6). The following estimates are approximate posterior medians
from Fig. 8–10. The intercept corresponds to the mean probability in
the ambiguous RC condition across matching and mismatching contexts. -/

/-- Baseline MPT parameters (ambiguous RC, averaged over contexts).
    Approximate posterior medians from the no-triage model. -/
def baselineParams : MPTParams :=
  { pAttentive    := 75   -- ~75% of trials are attentive
    pGardenPath   := 75   -- ~75% of amb-RC trials are garden-pathed
    pCovert       := 60   -- ~60% covert (vs. 40% overt)
    pPostpone     := 25   -- ~25% of covert reanalysis postponed
    pCovertSuccess := 85  -- ~85% covert reanalysis succeeds
    pOvertSuccess  := 60  -- ~60% overt reanalysis succeeds
  }

/-! ### Garden-Path Probability by Condition

Approximate cell estimates derived from the intercept + slope posteriors
(Figs. 8–9). The slopes are on the logit scale; back-transformed
estimates are approximate.

Key constraints from the paper (p. 8):
- Amb-RC average across contexts ≈ 75%
- Non-unique referents decrease RC GP by ~15 pp
- Non-unique referents increase CC GP by ~40 pp
- Unamb-RC is reduced by ~35 pp relative to amb-RC -/

/-- Garden-path probability estimates (percent) by condition.

These are approximate back-transformed posterior medians for p_gp
from the no-triage MPT model, constructed to satisfy the paper's
stated constraints. -/
def gardenPathRate : ExpCondition → Nat
  | .ambRC_unique       => 82   -- mismatching context → higher GP
  | .ambRC_nonUnique    => 67   -- matching context → reduced by ~15 pp
  | .ambCC_unique       => 10   -- matching context → low GP (CC preferred)
  | .ambCC_nonUnique    => 50   -- mismatching context → increased by ~40 pp
  | .unambRC_unique     => 45   -- unamb-RC: ~35 pp below amb-RC
  | .unambRC_nonUnique  => 35   -- unamb-RC with support

/-- Amb-RC cell estimates average to approximately 75%. -/
theorem ambRC_averages_near_75 :
    (gardenPathRate .ambRC_unique + gardenPathRate .ambRC_nonUnique) / 2 = 74 := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 6. Key Findings as Theorems
-- ════════════════════════════════════════════════════

/-! ### Finding I: RC always harder (p. 11)

"Regardless of context, RC disambiguation results in a higher
probability of garden-pathing, that is, choosing an incorrect
first-pass attachment." -/

theorem finding_I_rc_harder_than_cc :
    gardenPathRate .ambRC_unique > gardenPathRate .ambCC_unique ∧
    gardenPathRate .ambRC_nonUnique > gardenPathRate .ambCC_nonUnique := by
  constructor <;> native_decide

/-! ### Finding II: Context reduces but does not eliminate (p. 11)

"Contextual match decreases but does not eliminate the first-pass
anti-RC bias." -/

/-- Context reduces RC garden-pathing. -/
theorem finding_II_context_reduces_rc :
    gardenPathRate .ambRC_nonUnique < gardenPathRate .ambRC_unique := by
  native_decide

/-- Context does not eliminate RC garden-pathing — the rate with
    supporting context still far exceeds the CC baseline. -/
theorem finding_II_not_eliminated :
    gardenPathRate .ambRC_nonUnique > gardenPathRate .ambCC_unique := by
  native_decide

/-- Context × disambiguation crossover: non-unique referents help RC
    but hurt CC. This is the interaction predicted by the context-sensitive
    attachment hypothesis. -/
theorem context_crossover :
    gardenPathRate .ambRC_nonUnique < gardenPathRate .ambRC_unique ∧
    gardenPathRate .ambCC_nonUnique > gardenPathRate .ambCC_unique := by
  constructor <;> native_decide

/-- The results support a graded version of context-sensitive attachment:
    context affects first-pass parsing (there IS an interaction), but
    the bias is not fully overridden (there IS a main effect of
    disambiguation). Neither hypothesis alone suffices. -/
theorem graded_context_sensitivity :
    -- There is an interaction (context-sensitive prediction)
    (gardenPathRate .ambRC_nonUnique < gardenPathRate .ambRC_unique) ∧
    -- There is a main effect (context-insensitive prediction)
    (gardenPathRate .ambRC_nonUnique > gardenPathRate .ambCC_nonUnique) := by
  constructor <;> native_decide

/-! ### Finding III: Reanalysis cost is separable (p. 11)

"The cost of in-situ reanalysis is higher for RC than for CC
disambiguation, and is lower but still non-zero in cases of
context–disambiguation match versus mismatch." -/

/-- Processing cost structure from posterior estimates (Fig. 10).
    All values in milliseconds. -/
structure ProcessingCosts where
  gardenPathCost : Nat       -- pure GP cost (small: ~10–20ms)
  attentionCost : Nat        -- cost of paying attention (~5ms)
  regressionCost : Nat       -- cost of launching a regression
  covertReanalysisCost : Nat -- in-situ reanalysis cost
  deriving Repr

/-- Baseline costs for RC disambiguation (intercept posteriors, Fig. 10). -/
def rcCosts : ProcessingCosts :=
  { gardenPathCost       := 15    -- ~10–20ms
    attentionCost        := 5     -- ~2.5–10ms
    regressionCost       := 275   -- ~225–300ms
    covertReanalysisCost := 400   -- ~350–450ms
  }

/-- CC disambiguation costs: covert reanalysis is ~150–200ms cheaper
    than RC (Fig. 10 CC vs RC slope centered around -150 to -200ms). -/
def ccCosts : ProcessingCosts :=
  { gardenPathCost       := 15
    attentionCost        := 5
    regressionCost       := 275
    covertReanalysisCost := 225   -- ~400 - 175 = ~225ms
  }

/-- Finding III: RC covert reanalysis is costlier than CC. -/
theorem finding_III_rc_costlier :
    rcCosts.covertReanalysisCost > ccCosts.covertReanalysisCost := by
  native_decide

/-- Finding III (second part): covert reanalysis cost is non-trivial
    even for CC disambiguation (i.e., still non-zero). -/
theorem finding_III_cc_still_costly :
    ccCosts.covertReanalysisCost > 0 := by native_decide

/-- Pure garden-pathing cost is small relative to reanalysis cost.
    This is a key MPT insight: the cost of *being* garden-pathed is
    tiny; the cost comes from reanalysis. -/
theorem gp_cost_small_relative_to_reanalysis :
    rcCosts.gardenPathCost * 10 < rcCosts.covertReanalysisCost := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 7. Bridge: MPT vs. Surprisal
-- ════════════════════════════════════════════════════

/-! ### Why the MPT outperforms surprisal

Surprisal theory (@cite{hale-2001}, @cite{levy-2008}) predicts that
processing difficulty is proportional to the negative log probability
of a word in context. For garden-path sentences, surprisal at the
disambiguating region should be higher for less expected continuations.

The MPT outperforms all four LLM surprisal models and the standard
factorial model in cross-validated predictive fit. The key architectural
difference is the **mixture assumption**: reading times at disambiguation
are generated by a mixture of latent populations (garden-pathed vs. not),
each with distinct cost distributions. Single-stage surprisal models
predict a unimodal distribution shifted by the surprisal value.

This is structurally analogous to the limitation identified by
@cite{van-schijndel-linzen-2021} and @cite{huang-etal-2024}: single-stage
surprisal models underestimate the magnitude of garden-path effects
because they lack a distinct, costly reanalysis mechanism. -/

/-- Model rankings from cross-validated predictive fit (PSIS-LOO elpd,
    Fig. 6). Higher rank = better fit. Rank 1 = best.

    The ranking shows that even the simplest MPT model (mpt-simple)
    outperforms the best surprisal model, and adding an inattention
    component to a factorial model (factorial-inattention) only barely
    exceeds mpt-simple. -/
inductive ModelVariant where
  | factorial            -- standard factorial model
  | factorialInattention -- factorial + inattention mixture
  | gpt2Surprisal        -- GPT-2 surprisal
  | llamaSurprisal       -- LLaMA-2 surprisal
  | mistralSurprisal     -- Mistral surprisal
  | falconSurprisal      -- Falcon surprisal
  | gpt2Inattention      -- GPT-2 + inattention
  | mptSimple            -- MPT: garden-pathing + reanalysis only
  | mptNoTriage          -- MPT without triage (best model)
  | mptFull              -- full MPT with triage
  deriving DecidableEq, Repr, BEq

/-- Cross-validated predictive fit ranking (1 = best). -/
def modelRank : ModelVariant → Nat
  | .mptNoTriage          => 1
  | .mptFull              => 2
  | .mptSimple            => 3
  | .gpt2Inattention      => 4
  | .factorialInattention => 5
  | .falconSurprisal      => 6
  | .mistralSurprisal     => 7
  | .llamaSurprisal       => 8
  | .gpt2Surprisal        => 9
  | .factorial            => 10

/-- All MPT variants outperform all surprisal models. -/
theorem mpt_beats_surprisal :
    modelRank .mptSimple < modelRank .gpt2Surprisal ∧
    modelRank .mptSimple < modelRank .llamaSurprisal ∧
    modelRank .mptSimple < modelRank .mistralSurprisal ∧
    modelRank .mptSimple < modelRank .falconSurprisal := by
  constructor <;> first | constructor <;> native_decide | native_decide

/-- The no-triage variant beats the full MPT — triage is not needed. -/
theorem noTriage_beats_full :
    modelRank .mptNoTriage < modelRank .mptFull := by native_decide

-- ════════════════════════════════════════════════════
-- § 8. Bridge: Processing Profile Consistency
-- ════════════════════════════════════════════════════

/-! ### From ordinal to quantitative

The `ProcessingProfile` from `Core.ProcessingModel` captures the ordinal
claim that RC is harder than CC (see `rc_pareto_harder` in `Basic.lean`).
The MPT *explains* this ordering by decomposing it into quantitative
components: RC has higher garden-path probability, higher reanalysis cost,
and lower reanalysis success rate. The ordinal profile is the observable
consequence; the MPT is the latent mechanism. -/

/-- The MPT decomposition is consistent with the Pareto ordering:
    every quantitative measure points in the same direction. -/
theorem mpt_consistent_with_pareto :
    gardenPathRate .ambRC_unique > gardenPathRate .ambCC_unique ∧
    rcCosts.covertReanalysisCost > ccCosts.covertReanalysisCost := by
  constructor <;> native_decide

end Phenomena.SyntacticAmbiguity.Studies.PaapeVasishth2026
