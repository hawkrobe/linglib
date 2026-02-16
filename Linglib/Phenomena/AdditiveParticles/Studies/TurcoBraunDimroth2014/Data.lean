import Linglib.Core.InformationStructure
import Linglib.Fragments.Dutch.Particles
import Linglib.Fragments.German.PolarityMarking

/-!
# Turco, Braun & Dimroth (2014) — Production Data

Empirical data from Turco, Braun & Dimroth (2014), who compare how Dutch and
German speakers produce polarity-switch utterances (negation → affirmation)
in contrast vs. correction contexts.

## Key Findings

1. **Dutch** uses the affirmative particle *wel* as its dominant strategy
   (88% in contrast, 63% in correction).
2. **German** uses Verum focus (pitch accent on finite verb) as its dominant
   strategy (82% in contrast, 78% in correction).
3. German has **zero** sentence-internal polarity particles.
4. Correction contexts elicit more prosodic prominence than contrast contexts
   (German VF pitch range: 5.3 vs. 3.1 semitones, β = 1.85, p < .0001).

## Data Sources

- Figures 2 & 6 (production strategy distributions)
- Table/statistics for German VF pitch range by context

## References

- Turco, G., Braun, B. & Dimroth, C. (2014). How Dutch and German speakers
  produce and realize focus, contrast and correction. *JASA* 136(3), 1400–1414.
-/

namespace Phenomena.AdditiveParticles.Studies.TurcoBraunDimroth2014

open Core.InformationStructure (PolaritySwitchContext PolarityMarkingStrategy PolarityMarkingEntry)
open Fragments.Dutch.Particles (wel)
open Fragments.German.PolarityMarking (verumFocus dochPreUtterance)

/-! ## Types -/

/-- Languages compared in the study. -/
inductive Language where
  | dutch
  | german
  deriving DecidableEq, Repr, BEq

/-- A production-strategy distribution datum (percentages as rationals).
    The distribution is keyed by `PolarityMarkingStrategy`, so adding a
    strategy constructor forces updating every datum. -/
structure ProductionDatum where
  language : Language
  context : PolaritySwitchContext
  /-- Percentage of trials per strategy -/
  pctByStrategy : PolarityMarkingStrategy → Rat

/-- A prosodic prominence datum (pitch range in semitones). -/
structure ProminenceDatum where
  context : PolaritySwitchContext
  /-- Pitch range in semitones -/
  pitchRangeST : Rat
  /-- Regression coefficient -/
  beta : Rat
  /-- Standard error -/
  se : Rat
  /-- p-value (encoded as rational for decidable comparison) -/
  pValue : Rat
  deriving Repr, BEq

/-! ## Production Strategy Data (Fig. 2) -/

/-- Dutch contrast: 88% particle, 0% VF, 5% other, 7% unmarked -/
def dutchContrast : ProductionDatum where
  language := .dutch
  context := .contrast
  pctByStrategy
    | .particle => 88
    | .verumFocus => 0
    | .other => 5
    | .unmarked => 7

/-- Dutch correction: 63% particle, 5% VF, 7% other, 25% unmarked -/
def dutchCorrection : ProductionDatum where
  language := .dutch
  context := .correction
  pctByStrategy
    | .particle => 63
    | .verumFocus => 5
    | .other => 7
    | .unmarked => 25

/-- German contrast: 0% particle, 82% VF, 0% other, 18% unmarked -/
def germanContrast : ProductionDatum where
  language := .german
  context := .contrast
  pctByStrategy
    | .particle => 0
    | .verumFocus => 82
    | .other => 0
    | .unmarked => 18

/-- German correction: 0% particle, 78% VF, 8% other, 14% unmarked -/
def germanCorrection : ProductionDatum where
  language := .german
  context := .correction
  pctByStrategy
    | .particle => 0
    | .verumFocus => 78
    | .other => 8
    | .unmarked => 14

def allProductionData : List ProductionDatum :=
  [dutchContrast, dutchCorrection, germanContrast, germanCorrection]

/-! ## Prosodic Prominence Data (Fig. 6) -/

/-- German VF pitch range in contrast: 3.1 semitones -/
def germanVFContrast : ProminenceDatum where
  context := .contrast
  pitchRangeST := 31 / 10
  beta := 0
  se := 0
  pValue := 1

/-- German VF pitch range in correction: 5.3 semitones (β=1.85, SE=0.39, p<.0001) -/
def germanVFCorrection : ProminenceDatum where
  context := .correction
  pitchRangeST := 53 / 10
  beta := 185 / 100
  se := 39 / 100
  pValue := 1 / 10000

/-! ## Verification Theorems — Dominant Strategies -/

/-- Dutch dominant strategy is particles in contrast. -/
theorem dutch_contrast_particle_dominant :
    ∀ s, s ≠ PolarityMarkingStrategy.particle →
      dutchContrast.pctByStrategy .particle > dutchContrast.pctByStrategy s := by
  intro s hs; cases s <;> simp_all <;> native_decide

/-- Dutch dominant strategy is particles in correction. -/
theorem dutch_correction_particle_dominant :
    ∀ s, s ≠ PolarityMarkingStrategy.particle →
      dutchCorrection.pctByStrategy .particle > dutchCorrection.pctByStrategy s := by
  intro s hs; cases s <;> simp_all <;> native_decide

/-- German dominant strategy is Verum focus in contrast. -/
theorem german_contrast_vf_dominant :
    ∀ s, s ≠ PolarityMarkingStrategy.verumFocus →
      germanContrast.pctByStrategy .verumFocus > germanContrast.pctByStrategy s := by
  intro s hs; cases s <;> simp_all <;> native_decide

/-- German dominant strategy is Verum focus in correction. -/
theorem german_correction_vf_dominant :
    ∀ s, s ≠ PolarityMarkingStrategy.verumFocus →
      germanCorrection.pctByStrategy .verumFocus > germanCorrection.pctByStrategy s := by
  intro s hs; cases s <;> simp_all <;> native_decide

/-! ## Verification Theorems — German Zero Particles -/

/-- German has zero sentence-internal particles in contrast. -/
theorem german_contrast_no_particles :
    germanContrast.pctByStrategy .particle = 0 := rfl

/-- German has zero sentence-internal particles in correction. -/
theorem german_correction_no_particles :
    germanCorrection.pctByStrategy .particle = 0 := rfl

/-! ## Verification Theorems — Prosodic Prominence -/

/-- Correction elicits more prosodic prominence than contrast on German VF. -/
theorem correction_more_prominent :
    germanVFCorrection.pitchRangeST > germanVFContrast.pitchRangeST := by native_decide

/-- The correction–contrast difference is significant (p < .05). -/
theorem correction_prominence_significant :
    germanVFCorrection.pValue < (5 : Rat) / 100 := by native_decide

/-! ## Bridge Theorems — Fragment Connections -/

/-- Neither Dutch *wel* nor German VF maps to `.unmarked`:
    both languages have overt polarity-marking strategies. -/
theorem dominant_strategies_both_marked :
    wel.strategy ≠ PolarityMarkingStrategy.unmarked ∧
    verumFocus.strategy ≠ PolarityMarkingStrategy.unmarked := by
  exact ⟨by decide, by decide⟩

/-- Dutch *wel* and German VF instantiate different strategy types. -/
theorem strategies_differ :
    wel.strategy ≠ verumFocus.strategy := by decide

/-- Dutch *wel* is sentence-internal; German *doch* is not.
    This captures the key typological contrast: Dutch has a sentence-internal
    particle for polarity switches, German does not. -/
theorem dutch_particle_internal_german_doch_not :
    wel.sentenceInternal = true ∧ dochPreUtterance.sentenceInternal = false := by
  exact ⟨rfl, rfl⟩

/-- Both Dutch *wel* and German VF are available in both contexts. -/
theorem both_strategies_context_general :
    (wel.contrastOk = true ∧ wel.correctionOk = true) ∧
    (verumFocus.contrastOk = true ∧ verumFocus.correctionOk = true) := by
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

end Phenomena.AdditiveParticles.Studies.TurcoBraunDimroth2014
