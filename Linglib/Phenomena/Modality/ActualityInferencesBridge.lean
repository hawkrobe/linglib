import Mathlib.Data.List.Defs
import Linglib.Theories.Semantics.Lexical.Verb.ViewpointAspect

/-!
# Actuality Inference Data (Cross-Linguistic)

Cross-linguistic empirical data on actuality inferences with ability modals,
following the pattern of `Phenomena/Causatives/Data.lean`.

## Key Generalization (Nadathur 2023, Chapter 1)

Across languages, ability modals with **perfective** aspect entail the
complement, while those with **imperfective** aspect do not.

| Language | Modal | PFV entails? | IMPF entails? |
|----------|-------|-------------|---------------|
| Greek | *boro* | Yes | No |
| Hindi | *saknaa* | Yes | No |
| French | *pouvoir* | Yes | No |
| English | *be able* | Yes (episodic) | No (habitual) |

## References

- Nadathur, P. (2023). Actuality Inferences: Causality, Aspect, and Modality.
- Hacquard, V. (2006). Aspects of Modality. MIT dissertation.
- Bhatt, R. (1999). Covert Modality in Non-finite Contexts. UPenn dissertation.
- Mari, A. & Martin, F. (2007). Tense, abilities and actuality entailments.
-/

namespace Phenomena.Modality.ActualityInferencesBridge

open Semantics.Lexical.Verb.ViewpointAspect (ViewpointAspectB)

/-- A single cross-linguistic data point for actuality inferences. -/
structure ActualityDatum where
  /-- Language name -/
  language : String
  /-- The modal form in that language -/
  modalForm : String
  /-- Viewpoint aspect of the sentence -/
  aspect : ViewpointAspectB
  /-- Does the complement entailment hold? -/
  complementEntailed : Bool
  /-- Example sentence gloss -/
  gloss : String
  deriving Repr, DecidableEq, BEq

-- ════════════════════════════════════════════════════
-- Greek: boro 'can/be able'
-- ════════════════════════════════════════════════════

/-- Greek *boro* + perfective (aorist): "She was-able.PFV to swim across"
    → She swam across. (Hacquard 2006) -/
def greek_pfv : ActualityDatum where
  language := "Greek"
  modalForm := "boro"
  aspect := .perfective
  complementEntailed := true
  gloss := "Borese na kolimbisi apenant (She was-able.AOR to swim across)"

/-- Greek *boro* + imperfective: "She was-able.IMPF to swim across"
    ↛ She swam across. (Hacquard 2006) -/
def greek_impf : ActualityDatum where
  language := "Greek"
  modalForm := "boro"
  aspect := .imperfective
  complementEntailed := false
  gloss := "Boruse na kolimbisi apenant (She was-able.IMPF to swim across)"

-- ════════════════════════════════════════════════════
-- Hindi: saknaa 'can/be able'
-- ════════════════════════════════════════════════════

/-- Hindi *saknaa* + perfective: "She was-able.PFV to swim across"
    → She swam across. (Bhatt 1999) -/
def hindi_pfv : ActualityDatum where
  language := "Hindi"
  modalForm := "saknaa"
  aspect := .perfective
  complementEntailed := true
  gloss := "Voh pair ke tair sakii (She was-able.PFV to swim across)"

/-- Hindi *saknaa* + imperfective: "She was-able.IMPF to swim across"
    ↛ She swam across. (Bhatt 1999) -/
def hindi_impf : ActualityDatum where
  language := "Hindi"
  modalForm := "saknaa"
  aspect := .imperfective
  complementEntailed := false
  gloss := "Voh pair ke tair saktii thii (She was-able.IMPF to swim across)"

-- ════════════════════════════════════════════════════
-- French: pouvoir 'can/be able'
-- ════════════════════════════════════════════════════

/-- French *pouvoir* + passé composé (perfective): "She was-able.PFV to swim across"
    → She swam across. (Mari & Martin 2007) -/
def french_pfv : ActualityDatum where
  language := "French"
  modalForm := "pouvoir"
  aspect := .perfective
  complementEntailed := true
  gloss := "Elle a pu traverser a la nage (She was-able.PC to swim across)"

/-- French *pouvoir* + imparfait (imperfective): "She was-able.IMPF to swim across"
    ↛ She swam across. (Mari & Martin 2007) -/
def french_impf : ActualityDatum where
  language := "French"
  modalForm := "pouvoir"
  aspect := .imperfective
  complementEntailed := false
  gloss := "Elle pouvait traverser a la nage (She was-able.IMP to swim across)"

-- ════════════════════════════════════════════════════
-- English: be able (episodic vs habitual)
-- ════════════════════════════════════════════════════

/-- English *be able* + episodic (perfective-like): "She was able to swim across"
    → She swam across. (Bhatt 1999) -/
def english_pfv : ActualityDatum where
  language := "English"
  modalForm := "be able"
  aspect := .perfective
  complementEntailed := true
  gloss := "She was able to swim across (episodic reading)"

/-- English *be able* + habitual (imperfective-like): "She was able to swim across"
    ↛ She swam across on that occasion. (Bhatt 1999) -/
def english_impf : ActualityDatum where
  language := "English"
  modalForm := "be able"
  aspect := .imperfective
  complementEntailed := false
  gloss := "She was able to swim across (habitual/generic reading)"

-- ════════════════════════════════════════════════════
-- Dataset
-- ════════════════════════════════════════════════════

/-- All actuality inference data points. -/
def allData : List ActualityDatum :=
  [greek_pfv, greek_impf, hindi_pfv, hindi_impf,
   french_pfv, french_impf, english_pfv, english_impf]

/-- The perfective subset. -/
def perfData : List ActualityDatum :=
  allData.filter (·.aspect == .perfective)

/-- The imperfective subset. -/
def impfData : List ActualityDatum :=
  allData.filter (·.aspect == .imperfective)

-- ════════════════════════════════════════════════════
-- Verification Theorems
-- ════════════════════════════════════════════════════

/-- All 4 perfective data points have `complementEntailed = true`. -/
theorem perfective_entails :
    perfData.all (·.complementEntailed) = true := by native_decide

/-- All 4 imperfective data points have `complementEntailed = false`. -/
theorem imperfective_no_entailment :
    impfData.all (·.complementEntailed == false) = true := by native_decide

/-- **Central empirical generalization**: across all 8 data points,
    `complementEntailed` tracks `aspect == .perfective` exactly.

    This is the empirical observation that Nadathur (2023) explains
    via the causal sufficiency + aspect interaction. -/
theorem empirical_matches_theory :
    allData.all (λ d => (d.aspect == .perfective) == d.complementEntailed) = true := by
  native_decide

/-- We have data from 4 distinct languages. -/
theorem four_languages :
    (allData.map (·.language)).dedup.length = 4 := by native_decide

/-- Each language contributes exactly one perfective and one imperfective datum. -/
theorem balanced_design :
    perfData.length = 4 ∧ impfData.length = 4 := by
  constructor <;> native_decide

end Phenomena.Modality.ActualityInferencesBridge
