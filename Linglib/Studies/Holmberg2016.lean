import Linglib.Features.AnsweringSystem
import Linglib.Semantics.Questions.Hamblin
import Linglib.Syntax.Minimalist.Agree.Basic
import Linglib.Syntax.Minimalist.ExtendedProjection.ClauseSpine
import Linglib.Semantics.Mood.ClauseType
import Linglib.Features.Polarity
import Linglib.Fragments.Swedish.AnswerParticles
import Linglib.Data.Examples.Holmberg2016

/-!
# Holmberg (2016): The Syntax of Yes and No
[holmberg-2016]

## Core Contribution

A cross-linguistic typology of polar question answering. The central
parameter is the **answering system**: truth-based vs polarity-based.

## Answers as Elliptical Clauses

Yes/no answers are elliptical full clauses, not general fragments:

    [FocP yes/no Foc⁰ [PolP ... [±Pol] ... ]]

The PolP is elided under identity with the question's PolP; the particle
sits in Spec-FocP and values the [±Pol] feature. This is distinct from
wh-fragment answers, which fill an argument slot of a wh-question
(cf. `Studies/BergenGoodman2015.lean`).

## Key Claims Formalized

1. **Hamblin ↔ [±Pol]**: Hamblin's `polar p` yields exactly two answer
   cells, corresponding to [+Pol] and [-Pol] valuations.

2. **Answering system divergence**: Truth-based and polarity-based systems
   give opposite answers to negative questions.

3. **Polarity reversal**: Languages like Swedish (*jo*), German (*doch*),
   and French (*si*) have a dedicated particle that assigns [+Pol] while
   contradicting a negative context.

## Connection to Existing Infrastructure

- `Question.polar` (substrate-level inquisitive polar question)
- `PolFeature` (syntactic [±Pol] feature; relocated from `Minimalist/Polarity.lean`)
- `AnsweringSystem` (typological parameter)
- `NegationHeight` → `predictedSystem` (negation height derives answering system)
- `PolarAnswerProfile` (per-language classification)
- `VerumFocus.lean` ([romero-han-2004]): complementary analysis — VERUM
  explains structural source of bias, Holmberg explains cross-linguistic
  answer variation. Both derive unbalanced partitions for negative questions.
-/

namespace Holmberg2016

open Question
open Features (AnsweringSystem PolarAnswerProfile)
open Minimalist
open Semantics.Mood (ClauseType GramMood IllocutionaryMood)

/-! ### Syntactic polarity: PolP and [±Pol] (relocated from Minimalist/Polarity.lean)

Syntactic polarity as a formal feature on the PolP functional head,
connecting [laka-1990]'s ΣP and [holmberg-2016]'s analysis
of yes/no answers.

## Key Claims

1. Every finite clause has a polarity head (Pol⁰) projecting PolP in the IP domain
2. In declaratives, [±Pol] is valued: [+Pol] for affirmative, [-Pol] for negative
3. In polar questions, [±Pol] is unvalued — the answer values it
4. "Yes"/"No" are focus-movement remnants of PolP ellipsis under identity

## Connection to Features.Polarity

`Features.Polarity` provides the semantic type (`.positive` / `.negative`).
This file provides the syntactic feature `[±Pol]` that participates in
Agree and maps to `Features.Polarity` at LF.

## Connection to Cat.Pol

`Minimalist.Cat.Pol` is the categorial label for the polarity head.
This file adds the feature infrastructure for what that head carries.
-/

/-- The polarity feature on Pol⁰, which may be valued or unvalued.

    In declaratives: valued [+Pol] or [-Pol]
    In polar questions: unvalued [uPol] — waiting for an answer to value it -/
inductive PolFeature where
  /-- Valued polarity: [+Pol] (affirmative) or [-Pol] (negative) -/
  | valued : Features.Polarity → PolFeature
  /-- Unvalued polarity: the feature in polar questions that the answer resolves -/
  | unvalued : PolFeature
  deriving DecidableEq, Repr

/-- Convert a `PolFeature` to a `FeatureVal` for use in the Agree system.
    [+Pol] maps to `.pol true`, [-Pol] maps to `.pol false`. -/
def PolFeature.toFeatureVal : PolFeature → GramFeature
  | .valued .positive => .valued (.pol true)
  | .valued .negative => .valued (.pol false)
  | .unvalued         => .unvalued (.pol true)  -- placeholder value for type matching

/-- Recover `Features.Polarity` from a valued syntactic [±Pol] feature. -/
def PolFeature.toPolarity : PolFeature → Option Features.Polarity
  | .valued p => some p
  | .unvalued => none

/-- A Pol⁰ head: the functional head projecting PolP.

    In [holmberg-2016]'s analysis, every finite clause has a Pol⁰
    bearing a [±Pol] feature. The head's category is `Cat.Pol`. -/
structure PolHead where
  /-- The polarity feature on this head -/
  feature : PolFeature
  /-- Is this in a question context (unvalued [±Pol])? -/
  inQuestion : Bool := feature matches .unvalued
  deriving Repr

/-- An affirmative declarative Pol⁰: [+Pol] -/
def PolHead.affirmative : PolHead :=
  { feature := .valued .positive }

/-- A negative declarative Pol⁰: [-Pol] -/
def PolHead.negative : PolHead :=
  { feature := .valued .negative }

/-- A polar question Pol⁰: [uPol] -/
def PolHead.question : PolHead :=
  { feature := .unvalued }

/-- Value an unvalued [±Pol] feature — the core operation in answering
    a polar question. The answer provides a `Features.Polarity` that values
    the feature.

    Returns `none` if the feature is already valued (nothing to do). -/
def PolFeature.value (f : PolFeature) (p : Features.Polarity) : Option PolFeature :=
  match f with
  | .unvalued => some (.valued p)
  | .valued _ => none  -- already valued

/-- Valuing an unvalued feature always succeeds. -/
theorem value_unvalued (p : Features.Polarity) :
    PolFeature.unvalued.value p = some (.valued p) := rfl

/-- Valuing a valued feature always fails. -/
theorem value_valued (p q : Features.Polarity) :
    (PolFeature.valued p).value q = none := rfl

/-- Round-trip: valuing then extracting polarity recovers the answer. -/
theorem value_then_toPolarity (p : Features.Polarity) :
    (PolFeature.unvalued.value p).bind PolFeature.toPolarity = some p := rfl

/-- The [±Pol] feature matches itself in the Agree system. -/
theorem pol_feature_matches :
    FeatureVal.sameType (.pol true) (.pol false) = true := rfl

/-- [±Pol] is distinct from [±neg]: polarity and negation are
    separate features on separate heads (PolP vs NegP). -/
theorem pol_ne_neg :
    FeatureVal.sameType (.pol true) (.neg true) = false := rfl

/-! ### Question syntax: ForceP/FinP/PolP (relocated from Minimalist/Questions.lean)

Syntactic projections involved in question formation.

## Clause Structure for Polar Questions

[rizzi-1997]'s split-CP and [holmberg-2016]'s PolP analysis
give the following structure for a polar question:

    [ForceP Force⁰[+Q] [FinP Fin⁰[+finite] [PolP Pol⁰[uPol] [TP ...]]]]

- **ForceP**: Clause-typing head. Force⁰ bears [+Q] for interrogatives,
  [-Q] for declaratives. Corresponds to `Cat.Force` and `FeatureVal.q`.
- **FinP**: Finiteness head. Fin⁰ bears [±finite]. Corresponds to `Cat.Fin`
  and `FeatureVal.finite`.
- **PolP**: Polarity head. Pol⁰ bears valued [±Pol] in declaratives,
  unvalued [uPol] in polar questions. Corresponds to `Cat.Pol` and
  `FeatureVal.pol`. See `Minimalist.Polarity` for the Agree infrastructure.

## Connection to Semantic Questions

`Minimalist.LeftPeriphery` defines `WHFeature` (±WH on C) —
the semantic clause-typing feature. The syntactic `FeatureVal.q` corresponds
to the semantic `WHFeature`:
- `FeatureVal.q true` ↔ `WHFeature.plusWH`
- `FeatureVal.q false` ↔ `WHFeature.minusWH`

## Cross-framework: clause-typing locus is contested

This file places clause-typing at `Force⁰[+Q]` per [rizzi-1997]. Two
sibling analyses in linglib place it elsewhere:

- **[dayal-2025]** (`Studies/Dayal2025.lean`):
  clause-typing locus is `C` for CP-typed languages (English, Italian) and
  `PerspP` for PerspP-typed languages (Hindi-Urdu).
- **[holmberg-2016]** (`Studies/Holmberg2016.lean`):
  the answering-system parameter places polar-Q-typing at `Pol⁰` via
  `Features/AnsweringSystem.lean`.

The bridge theorems (Force⁰[+Q] ↔ C[+WH], Force⁰[+Q] ↔ Pol⁰[uPol]) are
unformalized — silent divergences, not committed disagreements.

## Connection to ClauseType

A clause's `Semantics.Mood.ClauseType` (force × mood) is determined by
the syntactic projections:
- Force⁰[+Q] → `IllocutionaryMood.interrogative`
- Force⁰[-Q] → `IllocutionaryMood.declarative`
- Mood is determined lower (by T/Fin morphology), not by ForceP.
-/

/-- The Q-feature on Force⁰: [+Q] for interrogatives, [-Q] for declaratives. -/
inductive QFeature where
  | plusQ   -- interrogative
  | minusQ  -- declarative
  deriving DecidableEq, Repr

/-- Map the Q-feature to a `FeatureVal` for the Agree system. -/
def QFeature.toFeatureVal : QFeature → FeatureVal
  | .plusQ  => .q true
  | .minusQ => .q false

/-- Map the Q-feature to illocutionary force. -/
def QFeature.toForce : QFeature → IllocutionaryMood
  | .plusQ  => .interrogative
  | .minusQ => .declarative

/-- The clause spine for a polar question: V ... T ... Pol ... Fin ... Force.

    This is the full IP-to-CP spine with the projections relevant to
    [holmberg-2016]'s analysis. The Pol head is between T and Fin. -/
def polarQuestionSpine : ClauseSpine :=
  ⟨[.V, .v, .Voice, .T, .Pol, .Neg, .Fin, .Force], by decide⟩

/-- A declarative spine has the same projections. -/
def declarativeSpine : ClauseSpine :=
  ⟨[.V, .v, .Voice, .T, .Pol, .Neg, .Fin, .Force], by decide⟩

/-- PolP is projected in both declaratives and polar questions. -/
theorem polP_always_projected :
    polarQuestionSpine.projects .Pol = true ∧
    declarativeSpine.projects .Pol = true := ⟨rfl, rfl⟩

/-- Derive `ClauseType` from the syntactic features on Force⁰ and T⁰/Fin⁰.

    The Q-feature on Force determines illocutionary force; mood is
    determined by the morphological properties of the verb (indicative
    vs subjunctive), independent of Force. -/
def clauseType (q : QFeature) (m : GramMood) : ClauseType :=
  { force := q.toForce, mood := m }

/-- A polar question with indicative mood. -/
theorem polar_question_is_interrogative_indicative :
    clauseType .plusQ .indicative = ClauseType.polarQuestion := rfl

/-- A declarative with indicative mood. -/
theorem declarative_is_decl_ind :
    clauseType .minusQ .indicative = ClauseType.declInd := rfl

/-- Force and mood are independently set by different heads. -/
theorem force_from_forceP_mood_from_fin :
    (clauseType .plusQ .indicative).force = .interrogative ∧
    (clauseType .plusQ .subjunctive).force = .interrogative ∧
    (clauseType .plusQ .indicative).mood = .indicative ∧
    (clauseType .plusQ .subjunctive).mood = .subjunctive := ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 1. Bridge: Hamblin polar ↔ [±Pol] variable
-- ════════════════════════════════════════════════════════════════

/-! A polar question `?p = {p, pᶜ}` (substrate `Question.polar`)
    corresponds to an unvalued [±Pol] feature. Each alternative cell
    values the feature:
    - `p` → [+Pol] (affirmative)
    - `pᶜ` → [-Pol] (negative)

    The two alternatives are the "positive cell" and "negative cell"
    of the partition induced by the question. -/

/-- Both alternatives `p` and `pᶜ` lie in `alt (polar p)` (under
    nontriviality). Substrate identification of the two-cell answer
    partition. -/
theorem both_alternatives_in_polar {W : Type*}
    {p : Set W} (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    p ∈ alt (polar p) ∧ pᶜ ∈ alt (polar p) :=
  ⟨(mem_alt_polar_of_nontrivial hne hnu p).mpr (Or.inl rfl),
   (mem_alt_polar_of_nontrivial hne hnu pᶜ).mpr (Or.inr rfl)⟩

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

/-- English polar answer profile (polarity-based, particle). -/
def englishProfile : PolarAnswerProfile :=
  { system := .polarityBased, strategy := .particle, hasPolarityReversal := false }

/-- Japanese polar answer profile (truth-based, particle). -/
def japaneseProfile : PolarAnswerProfile :=
  { system := .truthBased, strategy := .particle, hasPolarityReversal := false }

/-- Swedish polar answer profile (three-way: *ja*/*nej*/*jo*).
    Derived from `Swedish.AnswerParticles.profile`. -/
def swedishProfile : PolarAnswerProfile :=
  Swedish.AnswerParticles.profile

/-- Finnish polar answer profile (mixed: verb echo + *kyllä*, polarity-based). -/
def finnishProfile : PolarAnswerProfile :=
  { system := .polarityBased, strategy := .mixed, hasPolarityReversal := false }

/-- Mandarin polar answer profile (mixed: V-not-V + *shì/bú shì*, truth-based). -/
def mandarinProfile : PolarAnswerProfile :=
  { system := .truthBased, strategy := .mixed, hasPolarityReversal := false }

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

open Features (NegationHeight)

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

/-- The `paperFeatures` encoding of a `Features.Polarity` value, matching
    the `answer_polarity` key in `Holmberg2016.Examples`. -/
def polarityFeature : Features.Polarity → String
  | .positive => "positive"
  | .negative => "negative"

/-- End-to-end: Japanese low negation → truth-based → "yes" to negative question
    has negative polarity → matches the Japanese *hai* datum's
    `answer_polarity` annotation. -/
theorem japanese_endtoend :
    Examples.japanese_hai_to_neg.paperFeatures.lookup "answer_polarity" =
      some (polarityFeature NegationHeight.low.predictedSystem.yesToNegativeQuestion) := rfl

/-- End-to-end: English middle negation → polarity-based → "yes" to negative
    question has positive polarity → matches the English "yes" datum's
    `answer_polarity` annotation. -/
theorem english_endtoend :
    Examples.english_yes_to_neg.paperFeatures.lookup "answer_polarity" =
      some (polarityFeature NegationHeight.middle.predictedSystem.yesToNegativeQuestion) := rfl

/-- The end-to-end chains for Japanese and English yield opposite polarities,
    as predicted by their different negation heights. -/
theorem endtoend_diverge :
    NegationHeight.low.predictedSystem.yesToNegativeQuestion ≠
    NegationHeight.middle.predictedSystem.yesToNegativeQuestion := by decide

-- ════════════════════════════════════════════════════════════════
-- § 6. Polarity reversal ↔ polarity-based correlation
-- ════════════════════════════════════════════════════════════════

/-! [holmberg-2016] §4.13: languages with a polarity-reversing particle
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

end Holmberg2016
