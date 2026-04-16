import Linglib.Core.GeneralisedSurprisal

/-!
# Giulianelli, Wallbridge, Cotterell & Fernández (2026)
@cite{giulianelli-etal-2026}

Incremental alternative sampling as a lens into the temporal and
representational resolution of linguistic prediction.
*Journal of Memory and Language*, 148, 104715.

## Key contributions

1. Defines **incremental information value** — the expected representational
   distance between alternatives sampled before vs. after observing a word
2. Shows that different psycholinguistic measures are best predicted by
   different (forecast horizon, representational level) configurations
3. The full IAS model (all h × all l) outperforms standard surprisal
   for most measures
4. Surprisal implicitly integrates across multiple temporal and
   representational resolutions — its predictability is closest to a
   best-case (d^{min}) notion rather than average discrepancy (d^{mean})

## Datasets

- **Aligned**: 1,726 target–context pairs from 205 English sentences
  (predictability ratings, cloze, eye-tracking, ERPs, self-paced RT)
- **Natural Stories**: 10 English narratives, ~1,000 words each
  (self-paced RT via dashed moving-window display)

## Language models

GPT-2 in four sizes (Small 12L / Medium 24L / Large 36L / XL 48L),
forecast horizons h ∈ 1..10, k = 50 sampled alternatives per timestep.

## Connection to ProcessingModel

*Editorial note*: The following bridge is our interpretation connecting
IAS's findings to linglib's `ProcessingModel.ProcessingProfile`. The paper
itself does not reference `ProcessingProfile`.

IAS's layer-wise decomposition reveals that different representational
levels predict different psycholinguistic measures. This parallels
ProcessingProfile's separation of `locality`, `boundaries`,
`referentialLoad`, and `ease` into orthogonal cognitive dimensions —
both architectures recognize that processing cost is irreducibly
multi-dimensional.
-/

set_option autoImplicit false

namespace GiulianelliEtAl2026

open Core.GeneralisedSurprisal

-- ============================================================================
-- §1: Datasets
-- ============================================================================

/-- The two psycholinguistic datasets used in this study. -/
inductive Dataset where
  /-- 205 English sentences, sentence-level stimuli, multiple response types -/
  | aligned
  /-- 10 English narratives (~1000 words each), multi-sentence, self-paced RT -/
  | naturalStories
  deriving DecidableEq, Repr

-- ============================================================================
-- §2: Optimal Resolution per Measure
-- ============================================================================

/-- For each psycholinguistic measure, the forecast horizon at which
incremental information value is most predictive (highest Δ_{Adj.R²})
in the sentence-level Aligned dataset. N400 and P600 peak at h = 2
(two-word lookahead); all other measures peak at h = 1 (next word). -/
def peakHorizon : PsychMeasure → Nat
  | .n400 | .p600 => 2
  | _              => 1

/-- For each psycholinguistic measure, the representational level at which
incremental information value is most predictive (primary peak).

- Explicit predictability (cloze, ratings): embedding layer (lexical identity)
- N400: embedding layer — shallow lexical-semantic prediction error
- Eye-tracked RT: early-to-intermediate layers — structural processing
- Self-paced RT and P600: intermediate layers — syntactic integration

Note: most measures show bimodal layer patterns; see `layerPattern`
for the full picture. -/
def peakLevel : PsychMeasure → RepLevel
  | .predictabilityRating | .clozeProbability | .clozeSurprisal => .lexical
  | .n400                                                      => .lexical
  | .firstFixationRT | .firstPassRT | .rightBoundedRT | .goPastRT
                                                               => .shallowSyntactic
  | .selfPacedRT | .p600                                       => .syntactic

/-- Layer-activation pattern across representational depth.

The paper's central finding is that predictive power as a function of
layer depth has distinct shapes for different measure classes. -/
inductive LayerPattern where
  /-- Single peak at one depth region (N400: embedding; P600: intermediate) -/
  | unimodal
  /-- Peaks at both boundary layers (embedding + final); characteristic
      of explicit predictability measures (cloze, ratings) -/
  | uShaped
  /-- Peaks at early-to-intermediate layers with secondary rise at final
      layer; characteristic of reading time measures -/
  | sShaped
  deriving DecidableEq, Repr

/-- Layer-activation pattern for each psycholinguistic measure.

- Explicit measures (cloze, ratings): U-shaped — peak at embedding and
  final layer, the two layers closest to lexical identity
- Reading times: S-shaped — peak at early-to-intermediate layers with
  secondary rise at the final layer
- N400: unimodal at embedding layer
- P600: unimodal at intermediate (syntactic) layers -/
def layerPattern : PsychMeasure → LayerPattern
  | .predictabilityRating | .clozeProbability | .clozeSurprisal => .uShaped
  | .n400 | .p600 => .unimodal
  | _ => .sShaped

/-- In Natural Stories (multi-sentence stimuli), self-paced reading time
predictive power increases with forecast horizon up to h = 7, unlike
sentence-level stimuli where h = 1 is optimal. The extended context and
dashed moving-window display promote longer-range predictions. -/
def naturalStoriesSPRT_peakHorizon : Nat := 7

-- ============================================================================
-- §3: Model Comparison
-- ============================================================================

/-- The full IAS model (all h × all l simultaneously) outperforms standard
surprisal in predictive power for most psycholinguistic measures.

Exceptions:
- Predictability ratings: surprisal slightly better (not significant)
- Self-paced RT in Aligned: difference not significant -/
def iasOutperformsSurprisal : PsychMeasure → Dataset → Bool
  | .predictabilityRating, _        => false
  | .selfPacedRT,          .aligned => false
  | _,                     _        => true

/-- Observed sign of the relationship between IAS information value and
each psycholinguistic measure, as actually found in the data.

Differs from `PsychMeasure.expectedSign` for P600: the paper predicted a
positive relationship but found a negative one ("for P600, however, our
directional hypothesis is refuted"). -/
def observedSign : PsychMeasure → Int
  | .predictabilityRating => -1
  | .clozeProbability     => -1
  | .clozeSurprisal       =>  1
  | .firstFixationRT      =>  1
  | .firstPassRT          =>  1
  | .rightBoundedRT       =>  1
  | .goPastRT             =>  1
  | .selfPacedRT          =>  1
  | .n400                 => -1
  | .p600                 => -1  -- predicted +1, observed −1

/-- Whether IAS and surprisal show high complementarity (joint model
substantially exceeds either alone) for a given measure and dataset.

Complementarity is highest for predictability measures and self-paced RT
in multi-sentence stimuli. For other measures, the joint model ≈ IAS alone,
meaning IAS subsumes surprisal's predictive contribution. -/
def highComplementarity : PsychMeasure → Dataset → Bool
  | .predictabilityRating, _               => true
  | .clozeProbability,     _               => true
  | .clozeSurprisal,       _               => true
  | .selfPacedRT,          .naturalStories => true
  | _,                     _               => false

-- ============================================================================
-- §4: Correlation Analysis (Surprisal ↔ IAS)
-- ============================================================================

/-- Under which distance summary statistic surprisal's implicit predictions
are best captured.

Under d^{mean}, surprisal correlates most with the final layer at h = 1
(lexical expectations for the next word). Under d^{min}, surprisal
correlates most with intermediate layers at h = 3–5 (closest-hypothesis
tracking), with correlation coefficients up to 0.81.

The d^{min} finding reveals that surprisal's predictability is closest to
a best-case (closest-hypothesis) notion rather than average discrepancy,
which may explain its strong predictive power despite lacking explicit
temporal-representational resolution. -/
def surprisalBestMatchesSummary : DistanceSummary := .min

-- ============================================================================
-- §5: Key Theorems
-- ============================================================================

/-- Explicit predictability measures all peak at horizon 1 (next word). -/
theorem explicit_measures_peak_at_h1 (m : PsychMeasure) (h : m.isExplicit) :
    peakHorizon m = 1 := by
  cases m <;> simp_all [PsychMeasure.isExplicit, peakHorizon]

/-- N400 and P600 both peak at horizon 2, not horizon 1 — prediction of
ERP components benefits from two-word lookahead. -/
theorem erp_peaks_at_h2 :
    peakHorizon .n400 = 2 ∧ peakHorizon .p600 = 2 :=
  ⟨rfl, rfl⟩

/-- N400 and P600 are predicted by different representational levels:
N400 by embedding (lexical-semantic), P600 by intermediate (syntactic).
This dissociation mirrors the established functional distinction between
these components. -/
theorem n400_p600_level_dissociation :
    peakLevel .n400 = .lexical ∧ peakLevel .p600 = .syntactic :=
  ⟨rfl, rfl⟩

/-- Self-paced RT in multi-sentence stimuli benefits from substantially
longer forecast horizons than sentence-level stimuli. -/
theorem discourse_extends_horizon :
    naturalStoriesSPRT_peakHorizon > peakHorizon .selfPacedRT := by
  native_decide

/-- IAS outperforms surprisal for both ERP components (Aligned dataset). -/
theorem ias_outperforms_for_erps :
    iasOutperformsSurprisal .n400 .aligned ∧
    iasOutperformsSurprisal .p600 .aligned :=
  ⟨rfl, rfl⟩

/-- IAS outperforms surprisal for all eye-tracking measures (Aligned). -/
theorem ias_outperforms_for_eyetracking :
    iasOutperformsSurprisal .firstFixationRT .aligned ∧
    iasOutperformsSurprisal .firstPassRT .aligned ∧
    iasOutperformsSurprisal .rightBoundedRT .aligned ∧
    iasOutperformsSurprisal .goPastRT .aligned :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- IAS outperforms surprisal for self-paced RT in Natural Stories
but not in the sentence-level Aligned dataset. -/
theorem sprt_ias_advantage_dataset_dependent :
    iasOutperformsSurprisal .selfPacedRT .naturalStories ∧
    ¬(iasOutperformsSurprisal .selfPacedRT .aligned) :=
  ⟨rfl, by decide⟩

/-- Explicit measures and implicit measures are predicted by different
representational levels: explicit at lexical, implicit at syntactic
or shallow-syntactic. -/
theorem explicit_implicit_level_dissociation :
    peakLevel .clozeProbability ≠ peakLevel .firstPassRT :=
  by decide

/-- Explicit measures show U-shaped layer patterns while reading times
show S-shaped patterns — different measure classes engage different
representational geometries. -/
theorem explicit_rt_pattern_dissociation :
    layerPattern .clozeProbability = .uShaped ∧
    layerPattern .firstPassRT = .sShaped :=
  ⟨rfl, rfl⟩

/-- P600's observed sign is negative, contradicting the predicted positive
relationship. This is the only measure where the directional hypothesis
is refuted. -/
theorem p600_sign_reversal :
    PsychMeasure.expectedSign .p600 = 1 ∧
    observedSign .p600 = -1 :=
  ⟨rfl, rfl⟩

/-- All other measures confirm their predicted signs. -/
theorem other_signs_confirmed :
    observedSign .n400 = PsychMeasure.expectedSign .n400 ∧
    observedSign .selfPacedRT = PsychMeasure.expectedSign .selfPacedRT ∧
    observedSign .firstPassRT = PsychMeasure.expectedSign .firstPassRT :=
  ⟨rfl, rfl, rfl⟩

/-- For most measures, IAS subsumes surprisal (low complementarity),
but for explicit predictability measures, they complement each other. -/
theorem complementarity_dissociation :
    highComplementarity .clozeProbability .aligned ∧
    ¬(highComplementarity .firstPassRT .aligned) :=
  ⟨rfl, by decide⟩

/-- Surprisal's implicit predictions are best characterized by the
minimum distance statistic, not mean distance. -/
theorem surprisal_is_best_case :
    surprisalBestMatchesSummary = .min :=
  rfl

end GiulianelliEtAl2026
