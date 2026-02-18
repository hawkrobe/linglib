import Linglib.Core.Empirical

/-!
# Sikos et al. (2021) @cite{sikos-etal-2021}

Sikos, L., Venhuizen, N. J., Drenhaus, H. & Crocker, M. W. (2021).
Reevaluating pragmatic reasoning in language games.
*PLOS ONE* 16(3): e0248388.

## Core Contribution

Replicates Frank & Goodman (2012) reference games and tests whether RSA's
recursive reasoning (S1→L1) adds predictive value beyond a simpler baseline
model that uses only the prior and literal semantics (= L0).

Three experiments with increasing pragmatic demands:

- **Experiment 1** (FG2012 replication): 3-object contexts with color, shape,
  texture features. Baseline r = 0.988 vs RSA r = 0.992.
- **Experiment 2** (extended): 4-object contexts. Baseline r = 0.990 vs
  RSA r = 0.992.
- **Experiment 3** (critical test): Contexts specifically designed to be
  "pragmatically informative" — where L0 and L1 make different predictions.
  Baseline r = 0.77 vs RSA r = 0.82 (non-significant difference).

## Key Arguments

1. **Prior-driven variance dominates.** In Experiments 1–2, most of the
   correlation between model and data is driven by object priors and literal
   semantics, not pragmatic reasoning. Trivially true items (where L0 = L1)
   inflate the correlation.

2. **Methodology critique.** Correlation-based evaluation across all items
   conflates two sources of variance: (a) prior-driven (which any model with
   the right priors gets right) and (b) pragmatic (where L0 and L1 differ).
   Removing trivially-predicted items collapses RSA's advantage.

3. **Pragmatically informative contexts (Experiment 3).** Even in contexts
   designed to maximize the L0/L1 difference, RSA does not significantly
   outperform the baseline.

4. **Typicality priors matter.** The paper uses empirically-measured typicality
   priors (not uniform), which do substantial predictive work independent of
   pragmatic reasoning.

## Relationship to RSA

The baseline model is, mathematically, RSA's own L0 (literal listener with
priors). Both sides agree on this. The critique is that the *additional* layers
of recursive reasoning (S1, L1) don't add empirical value — the first step of
RSA may be all that's needed.
-/

namespace Phenomena.Reference.Studies.SikosEtAl2021

open Phenomena


/-! ## Measure Specifications -/

/-- Listener comprehension measure: forced choice among context objects. -/
def listenerMeasure : MeasureSpec :=
  { scale := .proportion
  , task := .forcedChoice
  , unit := "probability 0-1" }


/-! ## Context Types

Sikos et al. classify reference game contexts by how much pragmatic reasoning
they require. This taxonomy is central to their argument: FG2012's stimuli
are dominated by trivial contexts. -/

/-- Classification of reference game contexts by pragmatic demands. -/
inductive ContextType where
  /-- Only one object matches the utterance. L0 = L1 trivially. -/
  | trivial
  /-- Multiple objects match, but pragmatic reasoning can break the tie.
      L0 ≠ L1: this is where RSA should add value. -/
  | pragSolvable
  /-- Multiple objects match; pragmatic reasoning helps but cannot fully
      disambiguate (e.g., symmetry among speakers). -/
  | pragReducible
  /-- Multiple objects match and pragmatic reasoning cannot help.
      L0 ≈ L1 even with full RSA. -/
  | ambiguous
  deriving DecidableEq, BEq, Repr


/-! ## Model Fit Data

Correlation coefficients for the two competing models across experiments.
The key comparison: baseline (= L0 with priors) vs full RSA (L1). -/

/-- Model fit for one experiment, comparing baseline and RSA correlations.
    Correlations stored as thousandths (e.g., 988 = r = 0.988). -/
structure ModelFit where
  /-- Experiment number (1, 2, or 3) -/
  experiment : Nat
  /-- Brief description of the experiment -/
  description : String
  /-- Number of unique context–utterance items -/
  nItems : Nat
  /-- Pearson r × 1000: baseline model (prior × literal semantics = L0) -/
  baselineR_thou : Nat
  /-- Pearson r × 1000: full RSA model (L1) -/
  rsaR_thou : Nat
  deriving Repr

/-- Experiment 1: Replication of FG2012. 3-object contexts.
    Both models fit almost identically (r = 0.988 vs 0.992). -/
def exp1 : ModelFit :=
  { experiment := 1
  , description := "FG2012 replication, 3-object contexts"
  , nItems := 54
  , baselineR_thou := 988
  , rsaR_thou := 992 }

/-- Experiment 2: Extended to 4-object contexts.
    Still baseline ≈ RSA (r = 0.990 vs 0.992). -/
def exp2 : ModelFit :=
  { experiment := 2
  , description := "Extended contexts, 4-object contexts"
  , nItems := 72
  , baselineR_thou := 990
  , rsaR_thou := 992 }

/-- Experiment 3: Pragmatically informative contexts designed to maximize
    L0/L1 divergence. RSA's advantage is non-significant (r = 0.77 vs 0.82).
    This is the critical test of the critique. -/
def exp3 : ModelFit :=
  { experiment := 3
  , description := "Pragmatically informative contexts (critical test)"
  , nItems := 48
  , baselineR_thou := 770
  , rsaR_thou := 820 }

/-- All three experiments. -/
def allExperiments : List ModelFit := [exp1, exp2, exp3]


/-! ## Key Empirical Findings -/

/-- In Experiment 1, the baseline fits nearly as well as RSA
    (difference is only 4 thousandths of a correlation point). -/
theorem exp1_baseline_near_rsa :
    exp1.rsaR_thou - exp1.baselineR_thou ≤ 10 := by native_decide

/-- In Experiment 3 (the critical test), the difference between models
    is 50 thousandths — small and non-significant. -/
theorem exp3_small_difference :
    exp3.rsaR_thou - exp3.baselineR_thou ≤ 100 := by native_decide

/-- RSA never dramatically outperforms the baseline in any experiment
    (gap < 100 thousandths = 0.100 correlation points in all cases). -/
theorem rsa_never_dominant :
    allExperiments.all (λ mf => mf.rsaR_thou - mf.baselineR_thou < 100)
    = true := by native_decide


/-! ## Context Composition

Sikos et al. show that FG2012's stimuli are dominated by trivially-predicted
items, which inflate correlations for any model with the right priors. -/

/-- Proportion of items in FG2012 that are trivially predicted.
    Stored as tenths of percent (780 = 78.0%). The exact value depends on
    the counting method; the paper reports that the majority of items in
    Experiments 1–2 are trivially predicted. -/
def trivialItemProportion_exp1 : Nat := 780


/-! ## Competing Interpretations -/

/-- Two interpretations of the finding that baseline ≈ RSA. -/
inductive Interpretation where
  /-- RSA's recursive reasoning is empirically unnecessary — the literal
      listener with priors suffices. The additional S1→L1 computation adds
      no predictive value. (Sikos et al.'s interpretation) -/
  | rsaUnnecessary
  /-- RSA's L0 IS the baseline model, so high baseline fit is consistent
      with RSA. The question is whether L1 adds value in contexts where
      L0 ≠ L1. Sikos et al.'s Experiment 3 suggests it may not, though
      the test has limited statistical power. (Structural observation) -/
  | baselineIsL0
  deriving DecidableEq, BEq, Repr


end Phenomena.Reference.Studies.SikosEtAl2021
