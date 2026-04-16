import Linglib.Core.Discourse.InformationStructure
import Linglib.Fragments.Dutch.Particles
import Linglib.Fragments.German.PolarityMarking
import Linglib.Fragments.French.PolarityMarking
import Linglib.Fragments.Swedish.AnswerParticles
import Linglib.Fragments.English.PolarityMarking
import Linglib.Fragments.Spanish.PolarityMarking
import Linglib.Fragments.Italian.PolarityMarking
import Linglib.Theories.Semantics.Focus.PolarityLevel

/-!
# Cross-Linguistic Polarity-Marking Typology
@cite{turco-braun-dimroth-2014} @cite{holmberg-2016} @cite{batllori-hernanz-2013}
@cite{wilder-2013} @cite{garassino-jacob-2018}

Cross-linguistic comparison of polarity-marking strategies, connecting
Fragment entries from seven languages to the `PolarityMarkingLevel` theory.

## Languages and strategies

| Language | Dominant strategy        | Strategy type       | Level     | Sent-internal |
|----------|-------------------------|---------------------|-----------|---------------|
| Dutch    | *wel*                   | particle            | polarity  | yes           |
| German   | Verum focus             | verumFocus          | assertion | yes           |
| English  | emphatic *do*           | verumFocus          | assertion | yes           |
| French   | *si*                    | polarityReversal    | polarity  | no            |
| German   | *doch* (pre-utterance)  | polarityReversal    | polarity  | no            |
| Swedish  | *jo*                    | polarityReversal    | polarity  | no            |
| Spanish  | *sí (que)*              | polarityReversal    | polarity  | no            |
| Italian  | *sì che*                | polarityReversal    | polarity  | no            |

## Typological generalizations

1. **Strategy–level mapping**: All `.particle` and `.polarityReversal`
   strategies target the polarity level; all `.verumFocus` strategies
   target the assertion level. No exceptions in the sample.

2. **Reversal particles are correction-only**: *doch*, *jo*, *si*, *sí (que)*,
   *sì che* all have `contrastOk = false`. They require a negative context
   to reverse, ruling out simple polarity contrast.

3. **VF strategies are context-general**: Dutch *wel*, German VF, and
   English emphatic *do* all have both `contrastOk = true` and
   `correctionOk = true`.

4. **Sentence-internality splits by strategy type**: Affirmative particles
   (*wel*) and VF strategies are sentence-internal; polarity-reversal
   particles are not (they are clause-initial or standalone responses).
-/

namespace Phenomena.Polarity.MarkingTypology

open Core.InformationStructure (PolarityMarkingEntry PolarityMarkingStrategy)
open Theories.Semantics.Focus.PolarityLevel (PolarityMarkingLevel strategyLevel)

-- Fragment imports
open Fragments.Dutch.Particles (wel)
open Fragments.German.PolarityMarking (verumFocus dochPreUtterance)
open Fragments.French.PolarityMarking (si)
open Fragments.Swedish.AnswerParticles (joMarking)
open Fragments.English.PolarityMarking (emphaticDo)
open Fragments.Spanish.PolarityMarking (siQue)
open Fragments.Italian.PolarityMarking (siChe)

/-! ## All polarity-marking entries -/

/-- All polarity-marking entries across the seven-language sample. -/
def allEntries : List PolarityMarkingEntry :=
  [wel, verumFocus, emphaticDo, si, dochPreUtterance, joMarking, siQue, siChe]

/-! ## Generalization 1: Strategy–Level Mapping

All particle and polarity-reversal strategies target the polarity level;
all VF strategies target the assertion level. -/

theorem wel_targets_polarity :
    strategyLevel wel.strategy = some .polarity := rfl

theorem germanVF_targets_assertion :
    strategyLevel verumFocus.strategy = some .assertion := rfl

theorem englishDo_targets_assertion :
    strategyLevel emphaticDo.strategy = some .assertion := rfl

theorem si_targets_polarity :
    strategyLevel si.strategy = some .polarity := rfl

theorem doch_targets_polarity :
    strategyLevel dochPreUtterance.strategy = some .polarity := rfl

theorem jo_targets_polarity :
    strategyLevel joMarking.strategy = some .polarity := rfl

theorem siQue_targets_polarity :
    strategyLevel siQue.strategy = some .polarity := rfl

theorem siChe_targets_polarity :
    strategyLevel siChe.strategy = some .polarity := rfl

/-- VF strategies (German, English) both target the assertion level. -/
theorem vf_strategies_same_level :
    strategyLevel verumFocus.strategy = strategyLevel emphaticDo.strategy := rfl

/-- Reversal particles (doch, jo, si, sí que, sì che) all target the polarity level. -/
theorem reversal_particles_same_level :
    strategyLevel dochPreUtterance.strategy = strategyLevel joMarking.strategy ∧
    strategyLevel joMarking.strategy = strategyLevel si.strategy ∧
    strategyLevel si.strategy = strategyLevel siQue.strategy ∧
    strategyLevel siQue.strategy = strategyLevel siChe.strategy :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- VF and reversal particles target different levels. -/
theorem vf_vs_reversal_different_levels :
    strategyLevel verumFocus.strategy ≠ strategyLevel dochPreUtterance.strategy := by decide

/-! ## Generalization 2: Reversal particles are correction-only -/

theorem doch_correction_only :
    dochPreUtterance.contrastOk = false ∧ dochPreUtterance.correctionOk = true := ⟨rfl, rfl⟩

theorem jo_correction_only :
    joMarking.contrastOk = false ∧ joMarking.correctionOk = true := ⟨rfl, rfl⟩

theorem si_correction_only :
    si.contrastOk = false ∧ si.correctionOk = true := ⟨rfl, rfl⟩

theorem siQue_correction_only :
    siQue.contrastOk = false ∧ siQue.correctionOk = true := ⟨rfl, rfl⟩

theorem siChe_correction_only :
    siChe.contrastOk = false ∧ siChe.correctionOk = true := ⟨rfl, rfl⟩

/-- All polarity-reversal entries in the sample are correction-only. -/
theorem all_reversal_correction_only :
    ∀ e ∈ allEntries, e.strategy = .polarityReversal →
      e.contrastOk = false ∧ e.correctionOk = true := by
  intro e he hs
  simp [allEntries] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [wel, verumFocus, emphaticDo, si, dochPreUtterance, joMarking, siQue, siChe]

/-! ## Generalization 3: Non-reversal strategies are context-general -/

theorem wel_context_general :
    wel.contrastOk = true ∧ wel.correctionOk = true := ⟨rfl, rfl⟩

theorem germanVF_context_general :
    verumFocus.contrastOk = true ∧ verumFocus.correctionOk = true := ⟨rfl, rfl⟩

theorem englishDo_context_general :
    emphaticDo.contrastOk = true ∧ emphaticDo.correctionOk = true := ⟨rfl, rfl⟩

/-! ## Generalization 4: Sentence-internality -/

/-- Affirmative particle (*wel*) is sentence-internal. -/
theorem wel_internal : wel.sentenceInternal = true := rfl

/-- VF strategies (German VF, English emphatic *do*) are sentence-internal. -/
theorem vf_internal :
    verumFocus.sentenceInternal = true ∧ emphaticDo.sentenceInternal = true := ⟨rfl, rfl⟩

/-- Polarity-reversal particles are not sentence-internal. -/
theorem reversal_not_internal :
    dochPreUtterance.sentenceInternal = false ∧
    joMarking.sentenceInternal = false ∧
    si.sentenceInternal = false ∧
    siQue.sentenceInternal = false ∧
    siChe.sentenceInternal = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- All polarity-reversal entries in the sample are not sentence-internal. -/
theorem all_reversal_not_internal :
    ∀ e ∈ allEntries, e.strategy = .polarityReversal →
      e.sentenceInternal = false := by
  intro e he hs
  simp [allEntries] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [wel, verumFocus, emphaticDo, si, dochPreUtterance, joMarking, siQue, siChe]

/-! ## Cross-linguistic strategy type comparison -/

/-- Dutch and German use different strategy types for polarity marking. -/
theorem dutch_german_differ :
    wel.strategy ≠ verumFocus.strategy := by decide

/-- English and German use the same strategy type (both VF). -/
theorem english_german_same :
    emphaticDo.strategy = verumFocus.strategy := rfl

/-- German *doch* and French *si* use the same strategy type (both reversal). -/
theorem german_doch_french_si_same :
    dochPreUtterance.strategy = si.strategy := rfl

/-- Spanish *sí (que)* and French *si* use the same strategy type. -/
theorem spanish_french_same :
    siQue.strategy = si.strategy := rfl

/-- Italian *sì che* and Spanish *sí que* are cognates with identical properties. -/
theorem italian_spanish_cognates :
    siChe.strategy = siQue.strategy ∧
    siChe.sentenceInternal = siQue.sentenceInternal ∧
    siChe.contrastOk = siQue.contrastOk ∧
    siChe.correctionOk = siQue.correctionOk := ⟨rfl, rfl, rfl, rfl⟩

end Phenomena.Polarity.MarkingTypology
