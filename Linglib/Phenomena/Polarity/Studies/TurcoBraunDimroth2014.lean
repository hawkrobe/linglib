import Linglib.Core.InformationStructure
import Linglib.Fragments.Dutch.Particles
import Linglib.Fragments.German.PolarityMarking
import Linglib.Fragments.French.PolarityMarking
import Linglib.Fragments.Swedish.AnswerParticles
import Linglib.Fragments.English.PolarityMarking
import Linglib.Fragments.Spanish.PolarityMarking
import Linglib.Fragments.Italian.PolarityMarking
import Linglib.Theories.Semantics.Focus.PolarityLevel

/-!
# @cite{turco-braun-dimroth-2014} — Polarity Marking in Dutch and German
@cite{turco-braun-dimroth-2014}

Cross-linguistic production study comparing how Dutch and German speakers
mark polarity switches (negation → affirmation) in two discourse contexts:
polarity contrast (different topic situations) and polarity correction
(same topic situation, mutually exclusive claims).

## Key Findings

1. **Dutch** uses the affirmative particle *wel* as its dominant strategy
   (~88% in contrast, ~63% in correction).
2. **German** uses Verum focus (pitch accent on finite verb) as its dominant
   strategy (~82% in contrast, ~78% in correction).
3. German has **zero** sentence-internal polarity particles.
4. Correction contexts elicit more prosodic prominence than contrast contexts
   in both languages.
5. Dutch *wel* accent type varies by context: downstepped fall (!H*L L%) in
   contrast, plain fall (H*L L%) in correction.

## Theoretical contribution

@cite{turco-braun-dimroth-2014} (p. 104, following Blühdorn 2012)
argue that VF and *wel* operate at different semantic levels: VF targets
the *assertion operator* (the element carrying the assertive relation
between topic and comment), while *wel* targets the *polarity operator*
([±Pol]). Both achieve polarity contrast/correction pragmatically, but
they are structurally distinct. See `PolarityLevel.lean` for the
formal theory.

## Data Sources

- Fig. 2: Dutch production strategy distribution
- Fig. 3: Dutch *wel* accent rate by context
- Fig. 5: Dutch *wel* accent type by context
- Fig. 6: German production strategy distribution
- p. 102: German VF pitch range statistics

Note: Production percentages are approximate (read from bar charts).
-/

namespace TurcoBraunDimroth2014

open Core.InformationStructure (PolaritySwitchContext PolarityMarkingStrategy PolarityMarkingEntry)
open Fragments.Dutch.Particles (wel)
open Fragments.German.PolarityMarking (verumFocus dochPreUtterance)
open Fragments.French.PolarityMarking (si)
open Fragments.Swedish.AnswerParticles (joMarking)
open Fragments.English.PolarityMarking (emphaticDo)
open Fragments.Spanish.PolarityMarking (siQue)
open Fragments.Italian.PolarityMarking (siChe)
open Semantics.Focus.PolarityLevel (PolarityMarkingLevel strategyLevel)

/-! ## Types -/

/-- Languages compared in the study. -/
inductive Language where
  | dutch
  | german
  deriving DecidableEq, Repr

/-- A production-strategy distribution datum (percentages as rationals).
    The distribution is keyed by `PolarityMarkingStrategy`, so adding a
    strategy constructor forces updating every datum. -/
structure ProductionDatum where
  language : Language
  context : PolaritySwitchContext
  /-- Percentage of trials per strategy (approximate, from bar charts) -/
  pctByStrategy : PolarityMarkingStrategy → Rat

/-- A prosodic prominence datum (pitch range in semitones). -/
structure ProminenceDatum where
  context : PolaritySwitchContext
  /-- Pitch range in semitones -/
  pitchRangeST : Rat
  /-- Regression coefficient (contrast relative to correction baseline) -/
  beta : Rat
  /-- Standard error -/
  se : Rat
  /-- p-value (encoded as rational for decidable comparison) -/
  pValue : Rat
  deriving Repr, BEq

/-- An accent-rate datum for Dutch *wel* (Fig. 3). -/
structure AccentRateDatum where
  context : PolaritySwitchContext
  /-- Percentage of *wel* tokens that were accented -/
  pctAccented : Rat
  deriving Repr, BEq

/-- Accent type distribution on Dutch *wel* (Fig. 5).
    ToDI annotation: !H*L L% (downstepped fall) vs H*L L% (fall). -/
structure AccentTypeDatum where
  context : PolaritySwitchContext
  /-- Percentage realized as downstepped fall (!H*L L%) -/
  pctDownsteppedFall : Rat
  /-- Percentage realized as plain fall (H*L L%) -/
  pctFall : Rat
  /-- Percentage other realizations -/
  pctOther : Rat
  deriving Repr, BEq

/-! ## Production Strategy Data (Fig. 2: Dutch, Fig. 6: German) -/

/-- Dutch contrast: ~88% particle, 0% VF, ~5% other, ~7% unmarked -/
def dutchContrast : ProductionDatum where
  language := .dutch
  context := .contrast
  pctByStrategy
    | .particle => 88
    | .verumFocus => 0
    | .polarityReversal => 0
    | .other => 5
    | .unmarked => 7

/-- Dutch correction: ~63% particle, ~5% VF, ~7% other, ~25% unmarked -/
def dutchCorrection : ProductionDatum where
  language := .dutch
  context := .correction
  pctByStrategy
    | .particle => 63
    | .verumFocus => 5
    | .polarityReversal => 0
    | .other => 7
    | .unmarked => 25

/-- German contrast: 0% particle, ~82% VF, 0% other, ~18% unmarked.
    "Others" in the paper's coding = doch pre-utterance + VF combinations;
    these occur only in correction (p. 102). -/
def germanContrast : ProductionDatum where
  language := .german
  context := .contrast
  pctByStrategy
    | .particle => 0
    | .verumFocus => 82
    | .polarityReversal => 0
    | .other => 0
    | .unmarked => 18

/-- German correction: 0% particle, ~78% VF, ~8% other, ~14% unmarked.
    The ~8% "other" = doch pre-utterance followed by VF (p. 102):
    "always followed by a Verum focus utterance." -/
def germanCorrection : ProductionDatum where
  language := .german
  context := .correction
  pctByStrategy
    | .particle => 0
    | .verumFocus => 78
    | .polarityReversal => 0
    | .other => 8
    | .unmarked => 14

def allProductionData : List ProductionDatum :=
  [dutchContrast, dutchCorrection, germanContrast, germanCorrection]

/-! ## Dutch *wel* Accent Data (Fig. 3) -/

/-- *Wel* is accented ~93% of the time in contrast contexts. -/
def welAccentContrast : AccentRateDatum where
  context := .contrast
  pctAccented := 93

/-- *Wel* is accented ~97% of the time in correction contexts. -/
def welAccentCorrection : AccentRateDatum where
  context := .correction
  pctAccented := 97

/-! ## Dutch *wel* Accent Type Data (Fig. 5)

ToDI annotation (Gussenhoven 2005): in contrast, *wel* is mostly
realized as a downstepped fall (!H*L L%); in correction, as a plain
fall (H*L L%). The plain fall is more prominent. -/

/-- Contrast: ~60% downstepped fall, ~30% fall, ~10% other -/
def welTypeContrast : AccentTypeDatum where
  context := .contrast
  pctDownsteppedFall := 60
  pctFall := 30
  pctOther := 10

/-- Correction: ~30% downstepped fall, ~60% fall, ~10% other -/
def welTypeCorrection : AccentTypeDatum where
  context := .correction
  pctDownsteppedFall := 30
  pctFall := 60
  pctOther := 10

/-! ## Prosodic Prominence Data (p. 102) -/

/-- German VF pitch range in contrast: 3.1 semitones.
    β = −1.85 (contrast is 1.85 ST *below* correction baseline),
    SE = 0.39, p < .0001.
    The regression coefficient is for the contrast condition relative
    to the correction baseline (correction is the reference level). -/
def germanVFContrast : ProminenceDatum where
  context := .contrast
  pitchRangeST := 31 / 10
  beta := -185 / 100
  se := 39 / 100
  pValue := 1 / 10000

/-- German VF pitch range in correction: 5.3 semitones.
    This is the reference level (baseline) in the regression model. -/
def germanVFCorrection : ProminenceDatum where
  context := .correction
  pitchRangeST := 53 / 10
  beta := 0
  se := 0
  pValue := 1

/-! ## Verification Theorems — Dominant Strategies -/

/-- Dutch dominant strategy is particles in contrast. -/
theorem dutch_contrast_particle_dominant :
    ∀ s, s ≠ PolarityMarkingStrategy.particle →
      dutchContrast.pctByStrategy .particle > dutchContrast.pctByStrategy s := by
  intro s hs; cases s <;> simp_all <;> decide

/-- Dutch dominant strategy is particles in correction. -/
theorem dutch_correction_particle_dominant :
    ∀ s, s ≠ PolarityMarkingStrategy.particle →
      dutchCorrection.pctByStrategy .particle > dutchCorrection.pctByStrategy s := by
  intro s hs; cases s <;> simp_all <;> decide

/-- German dominant strategy is Verum focus in contrast. -/
theorem german_contrast_vf_dominant :
    ∀ s, s ≠ PolarityMarkingStrategy.verumFocus →
      germanContrast.pctByStrategy .verumFocus > germanContrast.pctByStrategy s := by
  intro s hs; cases s <;> simp_all <;> decide

/-- German dominant strategy is Verum focus in correction. -/
theorem german_correction_vf_dominant :
    ∀ s, s ≠ PolarityMarkingStrategy.verumFocus →
      germanCorrection.pctByStrategy .verumFocus > germanCorrection.pctByStrategy s := by
  intro s hs; cases s <;> simp_all <;> decide

/-! ## Verification Theorems — German Zero Particles -/

/-- German has zero sentence-internal particles in contrast. -/
theorem german_contrast_no_particles :
    germanContrast.pctByStrategy .particle = 0 := rfl

/-- German has zero sentence-internal particles in correction. -/
theorem german_correction_no_particles :
    germanCorrection.pctByStrategy .particle = 0 := rfl

/-! ## Verification Theorems — Dutch VF Asymmetry -/

/-- Dutch speakers never use VF in polarity contrast (0%). -/
theorem dutch_contrast_no_vf :
    dutchContrast.pctByStrategy .verumFocus = 0 := rfl

/-- Dutch speakers occasionally use VF in polarity correction (~5%),
    but never in contrast — an asymmetry the paper notes (p. 102) but
    does not explain. -/
theorem dutch_vf_correction_only :
    dutchContrast.pctByStrategy .verumFocus = 0 ∧
    dutchCorrection.pctByStrategy .verumFocus > 0 :=
  ⟨rfl, by decide⟩

/-! ## Verification Theorems — German doch Correction-Only

The "others" category in German is exclusively doch+VF combinations
(p. 102). These appear only in correction, consistent with
`dochPreUtterance.contrastOk = false` in the Fragment. -/

/-- German "others" (doch+VF) appears only in correction, never contrast. -/
theorem german_doch_vf_correction_only :
    germanContrast.pctByStrategy .other = 0 ∧
    germanCorrection.pctByStrategy .other > 0 :=
  ⟨rfl, by decide⟩

/-- The production data matches the Fragment: doch is correction-only. -/
theorem german_doch_production_matches_fragment :
    dochPreUtterance.contrastOk = false ∧
    germanContrast.pctByStrategy .other = 0 :=
  ⟨rfl, rfl⟩

/-! ## Verification Theorems — Dutch *wel* Accent -/

/-- *Wel* is accented in >90% of tokens in both contexts. -/
theorem wel_mostly_accented :
    welAccentContrast.pctAccented > 90 ∧ welAccentCorrection.pctAccented > 90 := by
  exact ⟨by decide, by decide⟩

/-- Accent type shifts between contexts: correction favors plain fall
    (H*L) over downstepped fall (!H*L). The plain fall is more prominent,
    consistent with the cross-linguistic pattern that correction elicits
    more prosodic prominence. -/
theorem correction_favors_fall :
    welTypeCorrection.pctFall > welTypeCorrection.pctDownsteppedFall ∧
    welTypeContrast.pctDownsteppedFall > welTypeContrast.pctFall := by
  exact ⟨by decide, by decide⟩

/-! ## Verification Theorems — Prosodic Prominence -/

/-- Correction elicits more prosodic prominence than contrast on German VF. -/
theorem correction_more_prominent :
    germanVFCorrection.pitchRangeST > germanVFContrast.pitchRangeST := by norm_num [germanVFCorrection, germanVFContrast]

/-- The correction–contrast difference is significant (p < .05). -/
theorem correction_prominence_significant :
    germanVFContrast.pValue < (5 : Rat) / 100 := by norm_num [germanVFContrast]

/-! ## Bridge Theorems — Fragment Connections -/

/-- Neither Dutch *wel* nor German VF maps to `.unmarked`:
    both languages have overt polarity-marking strategies. -/
theorem dominant_strategies_both_marked :
    wel.strategy ≠ PolarityMarkingStrategy.unmarked ∧
    verumFocus.strategy ≠ PolarityMarkingStrategy.unmarked :=
  ⟨by decide, by decide⟩

/-- Dutch *wel* and German VF instantiate different strategy types. -/
theorem strategies_differ :
    wel.strategy ≠ verumFocus.strategy := by decide

/-- Dutch *wel* is sentence-internal; German *doch* is not.
    This captures the key typological contrast: Dutch has a sentence-internal
    particle for polarity switches, German does not. -/
theorem dutch_particle_internal_german_doch_not :
    wel.sentenceInternal = true ∧ dochPreUtterance.sentenceInternal = false :=
  ⟨rfl, rfl⟩

/-- Both Dutch *wel* and German VF are available in both contexts. -/
theorem both_strategies_context_general :
    (wel.contrastOk = true ∧ wel.correctionOk = true) ∧
    (verumFocus.contrastOk = true ∧ verumFocus.correctionOk = true) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-! ## Bridge Theorems — Polarity-Marking Levels

Blühdorn (2012): Dutch *wel* targets [±Pol] (polarity level);
German VF targets the assertion operator (assertion level). This
explains why VF can co-occur with negation (emphatic denial) while
*wel* cannot. -/

/-- Dutch *wel* targets the polarity level. -/
theorem wel_targets_polarity :
    strategyLevel wel.strategy = some .polarity := rfl

/-- German VF targets the assertion level. -/
theorem vf_targets_assertion :
    strategyLevel verumFocus.strategy = some .assertion := rfl

/-- The two dominant strategies operate at different semantic levels.
    This is the paper's key theoretical claim (p. 104). -/
theorem strategies_target_different_levels :
    strategyLevel wel.strategy ≠ strategyLevel verumFocus.strategy := by decide

/-! ## Cross-Linguistic Extension

@cite{turco-braun-dimroth-2014} compare Dutch and German; the analysis
naturally extends to other Western European languages with comparable
polarity-marking inventories: English (emphatic *do*),
French (*si*), Swedish (*jo*), Spanish (*sí (que)*),
Italian (*sì che*). See also @cite{holmberg-2016},
@cite{batllori-hernanz-2013}, @cite{wilder-2013},
@cite{garassino-jacob-2018}.

We aggregate the seven-language sample and verify the strategy–level,
correction-only, context-general, and sentence-internality
generalizations as quantified statements over the inventory rather
than as individual per-entry `rfl`s. -/

/-- All polarity-marking entries across the seven-language sample. -/
def allEntries : List PolarityMarkingEntry :=
  [wel, verumFocus, emphaticDo, si, dochPreUtterance, joMarking, siQue, siChe]

/-- **Generalization 1 — Strategy/level mapping.** Every particle and
    polarity-reversal entry targets the polarity level; every Verum-focus
    entry targets the assertion level. -/
theorem strategy_level_partition :
    ∀ e ∈ allEntries,
      (e.strategy = .particle ∨ e.strategy = .polarityReversal →
        strategyLevel e.strategy = some .polarity) ∧
      (e.strategy = .verumFocus →
        strategyLevel e.strategy = some .assertion) := by
  intro e he
  simp [allEntries] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨?_, ?_⟩ <;> intro h <;>
    simp_all [wel, verumFocus, emphaticDo, si, dochPreUtterance, joMarking,
              siQue, siChe, strategyLevel]

/-- **Generalization 2 — Reversal particles are correction-only.**
    Every polarity-reversal entry has `contrastOk = false` and
    `correctionOk = true`. -/
theorem all_reversal_correction_only :
    ∀ e ∈ allEntries, e.strategy = .polarityReversal →
      e.contrastOk = false ∧ e.correctionOk = true := by
  intro e he hs
  simp [allEntries] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [wel, verumFocus, emphaticDo, si, dochPreUtterance, joMarking,
              siQue, siChe]

/-- **Generalization 3 — Non-reversal strategies are context-general.**
    Every particle or Verum-focus entry has both `contrastOk = true`
    and `correctionOk = true`. -/
theorem all_nonreversal_context_general :
    ∀ e ∈ allEntries,
      e.strategy = .particle ∨ e.strategy = .verumFocus →
      e.contrastOk = true ∧ e.correctionOk = true := by
  intro e he hs
  simp [allEntries] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [wel, verumFocus, emphaticDo, si, dochPreUtterance, joMarking,
              siQue, siChe]

/-- **Generalization 4 — Sentence-internality splits by strategy type.**
    Polarity-reversal entries are not sentence-internal; particles and
    Verum-focus entries are. -/
theorem sentence_internality_by_strategy :
    ∀ e ∈ allEntries,
      (e.strategy = .polarityReversal → e.sentenceInternal = false) ∧
      (e.strategy = .particle ∨ e.strategy = .verumFocus →
        e.sentenceInternal = true) := by
  intro e he
  simp [allEntries] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨?_, ?_⟩ <;> intro h <;>
    simp_all [wel, verumFocus, emphaticDo, si, dochPreUtterance, joMarking,
              siQue, siChe]

/-- Italian *sì che* and Spanish *sí que* are cognates with identical
    formal properties (strategy, sentence-internality, contrast/correction). -/
theorem italian_spanish_cognates :
    siChe.strategy = siQue.strategy ∧
    siChe.sentenceInternal = siQue.sentenceInternal ∧
    siChe.contrastOk = siQue.contrastOk ∧
    siChe.correctionOk = siQue.correctionOk := ⟨rfl, rfl, rfl, rfl⟩

end TurcoBraunDimroth2014
