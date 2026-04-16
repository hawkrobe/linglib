import Linglib.Phenomena.SyntacticAmbiguity.Basic
import Linglib.Theories.Semantics.Definiteness.Basic

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
- `Theories/Semantics/Lexical/Determiner/Definite.lean`: Uniqueness
  presupposition of `the_uniq` grounds the context manipulation — bare
  definites fail uniqueness in non-unique contexts, motivating RC modifiers (§ 9)
- `Phenomena/Reference/Studies/SedivyEtAl1999.lean`: Shared mechanism —
  modifier informativity given a contrast set drives both contrastive
  inference (Sedivy) and context-sensitive attachment (§ 9)
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
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

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

-- ════════════════════════════════════════════════════
-- § 9. Bridge: Uniqueness Presupposition Grounds Context Effect
-- ════════════════════════════════════════════════════

/-! ### Uniqueness presupposition grounds referential context

The experimental manipulation of referential context (unique vs. non-unique
referents) is grounded in the **uniqueness presupposition** of definite
descriptions (`the_uniq` in `Theories/Semantics/Lexical/Determiner/Definite.lean`).

In the non-unique condition (*He was introduced to two women. He told the
woman that...*), a bare definite "the woman" fails uniqueness because two
entities satisfy the restrictor. An RC modifier ("the woman that he'd risked
his life for") intersects the restrictor with the RC predicate, narrowing
to a single entity and rescuing uniqueness.

This makes the RC pragmatically *necessary* in non-unique contexts — the same
mechanism underlying @cite{sedivy-etal-1999}'s contrastive inference: a
modifier is informative when a contrast set is available. In Sedivy et al.'s
visual-world paradigm, the contrast set is perceptual (tall glass vs. short
glass); here, it is discourse-referential (woman₁ vs. woman₂). Both are
instances of modifier informativity increasing with the availability of
alternatives.

The argument chain:
1. `the_uniq` presupposes exactly one restrictor-satisfier
2. Non-unique context → presupposition fails for bare NP
3. RC modifier narrows restrictor → presupposition can succeed
4. Therefore RC is pragmatically licensed in non-unique contexts
5. This matches `contextSupports .nonUniqueReferents .relativeClause = true`
6. Parser is biased toward RC → less garden-pathing (Finding II)
-/

section UniquenessBridge

open Semantics.Definiteness (the_uniq modifierNecessary evalDefinite)
open Core.Definiteness (DefiniteDesc)

/-- Toy discourse entity for the uniqueness worked example. -/
inductive DiscEntity where
  | woman1   -- the woman he risked his life for
  | woman2   -- a second woman
  | man
  deriving DecidableEq, Repr

/-- Non-unique context domain: a man and two women. -/
def nonUniqueDomain : List DiscEntity := [.woman1, .woman2, .man]

/-- Unique context domain: a man and one woman. -/
def uniqueDomain : List DiscEntity := [.woman1, .man]

/-- Restrictor predicate: "woman". -/
def isWoman : DiscEntity → Bool
  | .woman1 => true | .woman2 => true | .man => false

/-- RC modifier predicate: "that he'd risked his life for". -/
def rcModifier : DiscEntity → Bool
  | .woman1 => true | _ => false

/-- Trivial scope for the worked example. -/
def toldScope : DiscEntity → Bool := fun _ => true

/-- In non-unique context, bare "the woman" FAILS uniqueness:
    two entities satisfy the restrictor, so the presupposition
    of `the_uniq` is not met. -/
theorem bare_fails_nonunique :
    ¬(the_uniq nonUniqueDomain isWoman toldScope).presup () := by
  simp only [the_uniq, evalDefinite, DefiniteDesc.unique, Bool.and_true,
    nonUniqueDomain, List.filter, isWoman]; decide

/-- In non-unique context, modified "the woman that he'd risked his
    life for" SUCCEEDS: the RC modifier narrows to one entity. -/
theorem modified_succeeds_nonunique :
    (the_uniq nonUniqueDomain
      (fun e => isWoman e && rcModifier e) toldScope).presup () := by
  simp only [the_uniq, evalDefinite, DefiniteDesc.unique, Bool.and_true,
    nonUniqueDomain, List.filter, isWoman, rcModifier,
    Bool.and_false, Bool.true_and]

/-- In unique context, bare "the woman" already SUCCEEDS:
    only one entity satisfies the restrictor, so no modifier needed. -/
theorem bare_succeeds_unique :
    (the_uniq uniqueDomain isWoman toldScope).presup () := by
  simp only [the_uniq, evalDefinite, DefiniteDesc.unique, Bool.and_true,
    uniqueDomain, List.filter, isWoman]

/-- The full argument chain: uniqueness presupposition grounds
    `contextSupports` from `Basic.lean`.

    1. Non-unique context → bare definite fails → RC modifier needed
    2. This is exactly `contextSupports .nonUniqueReferents .relativeClause`
    3. Unique context → bare definite succeeds → no modifier needed
    4. This is exactly `contextSupports .uniqueReferent .complementClause` -/
theorem uniqueness_grounds_context_supports :
    -- Non-unique: bare fails, modified succeeds, RC is supported
    ¬(the_uniq nonUniqueDomain isWoman toldScope).presup () ∧
    (the_uniq nonUniqueDomain (fun e => isWoman e && rcModifier e)
      toldScope).presup () ∧
    contextSupports .nonUniqueReferents .relativeClause = true ∧
    -- Unique: bare succeeds, CC is supported
    (the_uniq uniqueDomain isWoman toldScope).presup () ∧
    contextSupports .uniqueReferent .complementClause = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [the_uniq, evalDefinite, DefiniteDesc.unique, Bool.and_true,
      nonUniqueDomain, List.filter, isWoman]; decide
  · simp only [the_uniq, evalDefinite, DefiniteDesc.unique, Bool.and_true,
      nonUniqueDomain, List.filter, isWoman, rcModifier,
      Bool.and_false, Bool.true_and]
  · native_decide
  · simp only [the_uniq, evalDefinite, DefiniteDesc.unique, Bool.and_true,
      uniqueDomain, List.filter, isWoman]
  · native_decide

-- ────────────────────────────────────────────────────
-- § 9b. Formal Shared Mechanism: modifierNecessary
-- ────────────────────────────────────────────────────

/-! ### Shared mechanism with contrastive inference

`modifierNecessary` (defined in `Definite.lean`) captures the abstract
predicate: a modifier rescues a failed uniqueness presupposition. Both
Paape & Vasishth's context-sensitive attachment and @cite{sedivy-etal-1999}'s
contrastive inference are instances of the same predicate — the modifier
type differs (RC vs. scalar adjective) but the referential mechanism is
identical. -/

/-- In non-unique context, the RC modifier is referentially necessary:
    bare "the woman" is ambiguous, modified "the woman that P" is unique. -/
theorem pv_modifier_necessary :
    modifierNecessary nonUniqueDomain isWoman rcModifier = true := by
  native_decide

/-- In unique context, the RC modifier is unnecessary:
    bare "the woman" already uniquely identifies. -/
theorem pv_modifier_unnecessary :
    modifierNecessary uniqueDomain isWoman rcModifier = false := by
  native_decide

-- Sedivy et al. (1999) visual-world scenario

/-- Toy visual-world entity for the @cite{sedivy-etal-1999} scenario. -/
inductive SedivyEntity where
  | tallGlass    -- target
  | shortGlass   -- same-category competitor
  | ball         -- distractor
  | key          -- distractor
  deriving DecidableEq, Repr

/-- Contrast display: two glasses (tall and short) plus distractors. -/
def contrastDisplay : List SedivyEntity :=
  [.tallGlass, .shortGlass, .ball, .key]

/-- No-contrast display: one glass plus distractors. -/
def noContrastDisplay : List SedivyEntity :=
  [.tallGlass, .ball, .key]

/-- Restrictor predicate: "glass". -/
def isGlass : SedivyEntity → Bool
  | .tallGlass => true | .shortGlass => true | _ => false

/-- Modifier predicate: "tall". -/
def isTall : SedivyEntity → Bool
  | .tallGlass => true | _ => false

/-- With a contrast set (two glasses), "tall" is referentially necessary:
    bare "the glass" is ambiguous, "the tall glass" is unique. -/
theorem sedivy_modifier_necessary :
    modifierNecessary contrastDisplay isGlass isTall = true := by
  native_decide

/-- Without a contrast set (one glass), "tall" is unnecessary:
    bare "the glass" already uniquely identifies. -/
theorem sedivy_modifier_unnecessary :
    modifierNecessary noContrastDisplay isGlass isTall = false := by
  native_decide

/-- **Structural identity**: the same `modifierNecessary` predicate governs
    both phenomena. When alternatives are available, the modifier is
    necessary; when the referent is already unique, the modifier is
    redundant. The modifier type is irrelevant — RC (Paape & Vasishth)
    and scalar adjective (Sedivy et al.) behave identically at this
    level of abstraction. -/
theorem shared_mechanism :
    -- Both: modifier necessary when alternatives present
    modifierNecessary nonUniqueDomain isWoman rcModifier = true ∧
    modifierNecessary contrastDisplay isGlass isTall = true ∧
    -- Both: modifier unnecessary when referent unique
    modifierNecessary uniqueDomain isWoman rcModifier = false ∧
    modifierNecessary noContrastDisplay isGlass isTall = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

end UniquenessBridge

end Phenomena.SyntacticAmbiguity.Studies.PaapeVasishth2026
