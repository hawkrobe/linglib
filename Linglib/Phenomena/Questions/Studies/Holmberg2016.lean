import Linglib.Theories.Semantics.Questions.AnsweringSystems
import Linglib.Theories.Semantics.Questions.Denotation.Hamblin
import Linglib.Theories.Syntax.Minimalism.Polarity
import Linglib.Core.Polarity
import Linglib.Phenomena.Questions.PolarAnswerStructure

/-!
# Holmberg (2016): The Syntax of Yes and No
@cite{holmberg-2016}

## Core Contribution

A cross-linguistic typology of polar question answering. The central
parameter is the **answering system**: truth-based vs polarity-based.

## Key Claims Formalized

1. **Hamblin ↔ [±Pol]**: Hamblin's `polar p` yields exactly two answer
   cells, corresponding to [+Pol] and [-Pol] valuations.

2. **Answering system divergence**: Truth-based and polarity-based systems
   give opposite answers to negative questions.

3. **Polarity reversal**: Languages like Swedish (*jo*), German (*doch*),
   and French (*si*) have a dedicated particle that assigns [+Pol] while
   contradicting a negative context.

## Connection to Existing Infrastructure

- `Hamblin.polar` (semantic question denotation)
- `Minimalism.Polarity.PolFeature` (syntactic [±Pol] feature)
- `AnsweringSystem` (typological parameter)
- `NegationHeight` → `predictedSystem` (negation height derives answering system)
- `PolarAnswerProfile` (per-language classification)
- `VerumFocus.lean` (@cite{romero-han-2004}): complementary analysis — VERUM
  explains structural source of bias, Holmberg explains cross-linguistic
  answer variation. Both derive unbalanced partitions for negative questions.
-/

namespace Phenomena.Questions.Studies.Holmberg2016

open Semantics.Questions.Hamblin
open Semantics.Questions (AnsweringSystem PolarAnswerProfile)
open Minimalism.Polarity

-- ════════════════════════════════════════════════════════════════
-- § 1. Bridge: Hamblin polar ↔ [±Pol] variable
-- ════════════════════════════════════════════════════════════════

/-! A Hamblin polar question `{p, ¬p}` corresponds to an unvalued [±Pol]
    feature. Each answer cell values the feature:
    - p → [+Pol] (affirmative)
    - ¬p → [-Pol] (negative)

    The two answer propositions are the "positive cell" and "negative cell"
    of the partition induced by the question. -/

/-- The positive answer to a polar question: the proposition p itself. -/
def positiveAnswer {W : Type*} (p : W → Bool) : W → Bool := p

/-- The negative answer: ¬p. -/
def negativeAnswer {W : Type*} (p : W → Bool) : W → Bool := fun w => !p w

/-- Both answers are in the Hamblin denotation of `polar p`. -/
theorem both_answers_in_polar {W : Type*} [BEq W]
    (p : W → Bool) (worlds : List W) (_hw : worlds ≠ []) :
    polar p worlds (positiveAnswer p) = true ∧
    polar p worlds (negativeAnswer p) = true := by
  constructor
  · simp only [polar, positiveAnswer, Bool.or_eq_true]
    left; exact List.all_eq_true.mpr (fun w _ => by simp [BEq.beq])
  · simp only [polar, negativeAnswer, Bool.or_eq_true]
    right; exact List.all_eq_true.mpr (fun w _ => by simp [BEq.beq])

/-- The positive answer maps to [+Pol] (valued positive). -/
def positiveToPolFeature : PolFeature := .valued .positive

/-- The negative answer maps to [-Pol] (valued negative). -/
def negativeToPolFeature : PolFeature := .valued .negative

/-- Valuing [uPol] as positive gives [+Pol]. -/
theorem positive_valuation :
    PolFeature.unvalued.value .positive = some positiveToPolFeature := rfl

/-- Valuing [uPol] as negative gives [-Pol]. -/
theorem negative_valuation :
    PolFeature.unvalued.value .negative = some negativeToPolFeature := rfl

-- ════════════════════════════════════════════════════════════════
-- § 2. Answering system predictions
-- ════════════════════════════════════════════════════════════════

/-- The central diagnostic: "Doesn't he drink?" → "Yes" means...
    - Truth-based: "He doesn't drink" (negative polarity)
    - Polarity-based: "He does drink" (positive polarity) -/
theorem diagnostic_prediction :
    AnsweringSystem.truthBased.yesToNegativeQuestion = .negative ∧
    AnsweringSystem.polarityBased.yesToNegativeQuestion = .positive := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 3. Cross-linguistic profiles
-- ════════════════════════════════════════════════════════════════

open Phenomena.Questions.PolarAnswerStructure

/-- English and Swedish are both polarity-based. -/
theorem english_swedish_same_system :
    englishProfile.system = swedishProfile.system := rfl

/-- Japanese and Mandarin are both truth-based. -/
theorem japanese_mandarin_same_system :
    japaneseProfile.system = mandarinProfile.system := rfl

/-- English and Japanese differ in answering system. -/
theorem english_japanese_differ :
    englishProfile.system ≠ japaneseProfile.system := by decide

/-- Swedish has polarity reversal; English does not. -/
theorem swedish_reversal_english_not :
    swedishProfile.hasPolarityReversal = true ∧
    englishProfile.hasPolarityReversal = false := ⟨rfl, rfl⟩

/-- The answering system and answer strategy are orthogonal:
    both truth-based and polarity-based systems can use particles. -/
theorem system_strategy_orthogonal :
    englishProfile.strategy = japaneseProfile.strategy ∧
    englishProfile.system ≠ japaneseProfile.system := ⟨rfl, by decide⟩

-- ════════════════════════════════════════════════════════════════
-- § 4. Negation height → answering system derivation
-- ════════════════════════════════════════════════════════════════

open Semantics.Questions (NegationHeight)

/-- Japanese has low negation → truth-based predicted, matches actual profile. -/
theorem japanese_negation_height_predicts :
    NegationHeight.low.predictedSystem = japaneseProfile.system := rfl

/-- Mandarin has low negation → truth-based predicted, matches actual profile. -/
theorem mandarin_negation_height_predicts :
    NegationHeight.low.predictedSystem = mandarinProfile.system := rfl

/-- English has middle negation → polarity-based predicted, matches actual profile. -/
theorem english_negation_height_predicts :
    NegationHeight.middle.predictedSystem = englishProfile.system := rfl

/-- Swedish has middle negation (exclusively, no low negation; §4.5) →
    polarity-based predicted, matches actual profile. -/
theorem swedish_negation_height_predicts :
    NegationHeight.middle.predictedSystem = swedishProfile.system := rfl

/-- Finnish has middle negation (higher variety of middle; §4.6, p178:
    "still technically a middle negation position") →
    polarity-based predicted, matches actual profile. -/
theorem finnish_negation_height_predicts :
    NegationHeight.middle.predictedSystem = finnishProfile.system := rfl

-- ════════════════════════════════════════════════════════════════
-- § 5. End-to-end chains: negation height → specific answer data
-- ════════════════════════════════════════════════════════════════

/-- End-to-end: Japanese low negation → truth-based → "yes" to negative question
    has negative polarity → matches the Japanese *hai* datum. -/
theorem japanese_endtoend :
    NegationHeight.low.predictedSystem.yesToNegativeQuestion =
    japanese_hai_to_neg.answerPolarity := rfl

/-- End-to-end: English middle negation → polarity-based → "yes" to negative
    question has positive polarity → matches the English "yes" datum. -/
theorem english_endtoend :
    NegationHeight.middle.predictedSystem.yesToNegativeQuestion =
    english_yes_to_neg.answerPolarity := rfl

/-- The end-to-end chains for Japanese and English yield opposite polarities,
    as predicted by their different negation heights. -/
theorem endtoend_diverge :
    NegationHeight.low.predictedSystem.yesToNegativeQuestion ≠
    NegationHeight.middle.predictedSystem.yesToNegativeQuestion := by decide

-- ════════════════════════════════════════════════════════════════
-- § 6. Polarity reversal ↔ polarity-based correlation
-- ════════════════════════════════════════════════════════════════

/-! @cite{holmberg-2016} §4.13: languages with a polarity-reversing particle
    (Swedish *jo*, German *doch*, French *si*) are correlated with the
    polarity-based system. Truth-based languages do not need a reversing
    particle because they can always use "no" to disconfirm the negative
    alternative of a negative question. -/

/-- Truth-based languages do not have polarity reversal in our profiles.
    (Japanese and Mandarin both lack a reversing particle.) -/
theorem truthBased_no_reversal :
    japaneseProfile.hasPolarityReversal = false ∧
    mandarinProfile.hasPolarityReversal = false := ⟨rfl, rfl⟩

/-- Among polarity-based languages, reversal is attested but not universal:
    Swedish has it, English does not. -/
theorem polarityBased_reversal_variation :
    swedishProfile.hasPolarityReversal = true ∧
    englishProfile.hasPolarityReversal = false := ⟨rfl, rfl⟩

end Phenomena.Questions.Studies.Holmberg2016
