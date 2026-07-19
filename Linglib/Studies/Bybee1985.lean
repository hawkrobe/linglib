import Linglib.Morphology.Morphotactics.RelevanceHierarchy
import Linglib.Morphology.UsageBased.Network
import Linglib.Fragments.English.Predicates.Verbal
import Mathlib.Tactic.DeriveFintype

/-!
# Bybee (1985): the relevance hypothesis

[bybee-1985] (*Morphology: A Study of the Relation Between Meaning and Form*,
Typological Studies in Language 9) tests the **relevance hypothesis** on a
50-language stratified probability sample (Perkins 1980): a morpheme category
whose meaning is more relevant to the verb stem (a) occurs more often as
inflection cross-linguistically, (b) sits closer to the stem in suffixal
morphology, and (c) fuses more tightly with it.

This file formalizes the data behind claims (a) and (b) — the Ch 2 §5 frequency
surveys and the Ch 2 §6 morpheme-order counts — and grounds the substrate's
relevance order (`MorphCategory.peripherality`, via `RelevanceLT` / `RelevanceLE`)
in that evidence. Claim (c), fusion, is qualitative in the source and is not
formalized.

## Main definitions

* `BybeeCategory` — the verbal-inflectional categories of Ch 2, in relevance order.
* `inflectionalCount50`, `derivOrInflCount50` — the Ch 2 §5 frequency surveys (Figs 1+2).
* `orderPairs` — the Ch 2 §6 morpheme-order counts, one `OrderPair` per tested category pair.
* `toMorphCategory` — the embedding of `BybeeCategory` into the substrate `MorphCategory`.
* `SurveyedCloser` — the stem-proximity order *derived from* `orderPairs`.
* `verbToBybeeNetwork` — a verb's Ch 5 paradigm network, derived from a Fragment `VerbEntry`.

## Main results

* `mood_highest_when_inflectional`, `gender_lowest_when_derivOrInfl` — the frequency predictions.
* `predicted_outnumbers_counter`, `aspect_categorical_against_tense_and_mood` — the order predictions.
* `survey_order_iso_relevance` — on the surveyed categories `SurveyedCloser` and the substrate
  `RelevanceLT` coincide via `toMorphCategory`: the hierarchy is the order the §6 survey forces,
  not a stipulated table.
* `bybeeSurveyedSlots_respects_hierarchy` — closes the loop to `RespectsRelevanceHierarchy`.

## Implementation notes

Out of scope: Ch 1 fusion/allomorphy, Ch 3 paradigm organization, Ch 4's
lexical-derivational-inflectional continuum (which no discrete status
enum expresses — flagged for future work), and Part II tense/aspect/mood
detail (Ch 6-9). `MorphCategory.RelevanceLT` is exercised independently by
`Studies/HahnDegenFutrell2021Morphology.lean`; the `BybeeCategory` enum and
`toMorphCategory` bridge feed `Studies/RathiHahnFutrell2026.lean`. The Ch 5
network substrate lives in `Morphology/UsageBased/Network.lean`; §5 below uses
it on the English *eat/ate/eaten* paradigm.
-/

namespace Bybee1985

open Morphology

/-! ### Verbal categories (Ch 2 §3)

Bybee's six core categories in relevance order: valence, voice, aspect, tense,
mood, agreement (number/person/gender are agreement sub-types). -/

/-- Bybee's Ch 2 verbal-inflectional categories, in her relevance order (stem
first). Object agreement, number, and gender are tracked separately. -/
inductive BybeeCategory where
  | valence
  | voice
  | aspect
  | tense
  | mood
  | numberAgr
  | personAgr
  | personAgrObj
  | genderAgr
  deriving DecidableEq, Repr, Fintype

/-! ### Cross-linguistic frequency (Ch 2 §5, Figs 1+2)

Fig 1 counts the 50-sample languages with *inflectional* expression of a
category; Fig 2 counts those with inflectional *or* derivational expression.
Counts are integers because the sample is exactly 50 (count = percentage / 2). -/

/-- Languages (of 50) with *inflectional* expression of `c` (Fig 1). -/
def inflectionalCount50 : BybeeCategory → Nat
  | .valence       => 3   -- 6%
  | .voice         => 13  -- 26%
  | .aspect        => 26  -- 52%
  | .tense         => 24  -- 48%
  | .mood          => 34  -- 68%
  | .numberAgr     => 27  -- 54%
  | .personAgr     => 28  -- 56%
  | .personAgrObj  => 14  -- 28%
  | .genderAgr     => 8   -- 16%

/-- Languages (of 50) with *inflectional or derivational* expression of `c`
(Fig 2). Valence reaches 90% once valence-changing derivation is counted; only
Haitian, Karankawa, Navaho, Serbo-Croatian, and Vietnamese lack it. -/
def derivOrInflCount50 : BybeeCategory → Nat
  | .valence       => 45  -- 90%
  | .voice         => 28  -- 56%
  | .aspect        => 37  -- 74%
  | .tense         => 25  -- 50%
  | .mood          => 34  -- 68%
  | .numberAgr     => 33  -- 66%
  | .personAgr     => 28  -- 56%
  | .personAgrObj  => 14  -- 28%
  | .genderAgr     => 8   -- 16%

/-- Prediction (a), deriv+infl: valence is the most frequent category,
reflecting near-universal valence-changing morphology. -/
theorem valence_highest_when_derivOrInfl :
    ∀ c : BybeeCategory, derivOrInflCount50 c ≤ derivOrInflCount50 .valence := by
  decide

/-- Among purely *inflectional* categories, mood is the most frequent (Fig 1,
68%). Valence's drop from 90% to 6% is Bybee's point that valence-changing
morphology is almost always derivational. -/
theorem mood_highest_when_inflectional :
    ∀ c : BybeeCategory, inflectionalCount50 c ≤ inflectionalCount50 .mood := by
  decide

/-- In the deriv+infl survey (Fig 2), gender agreement is the least frequent
category — Bybee's least-relevant verbal category. (Inflection-only, valence
drops *below* gender, so Fig 2 is the relevance-faithful ranking.) -/
theorem gender_lowest_when_derivOrInfl :
    ∀ c : BybeeCategory, derivOrInflCount50 .genderAgr ≤ derivOrInflCount50 c := by
  decide

/-! ### Morpheme order (Ch 2 §6)

Prediction (b): the most relevant categories sit closest to the stem, the least
relevant furthest. Bybee tests the four most frequent — aspect, tense, mood,
person — counting, per pair, how many languages place one closer than the other.
A pair is excluded when the morphemes are portmanteau, on opposite sides of the
stem, mutually exclusive in one slot, or realized by stem modification. -/

/-- A Ch 2 §6 morpheme-order pair: `closer` / `further` are the predicted
nearer / farther categories, `closerCount` / `furtherCount` the languages
confirming / contradicting it, and `total` the languages where it is testable. -/
structure OrderPair where
  closer : BybeeCategory
  further : BybeeCategory
  closerCount : Nat
  furtherCount : Nat
  total : Nat
  deriving Repr

/-- The six pairs Bybee tests in Ch 2 §6; counts verified against the book, each
inline comment quoting its source passage. -/
def orderPairs : List OrderPair := [
  -- p. 34: "Aspect markers were found to be closer to the stem than tense
  -- markers in 8 languages, while the opposite order did not occur in the
  -- sample. There were a total of 18 languages that have both aspect and
  -- tense, but in 10 cases their ordering was not relevant to the hypothesis."
  ⟨.aspect, .tense, 8, 0, 18⟩,
  -- p. 35: "Aspect markers were found to be closer to the stem than mood
  -- markers in 10 languages, out of a total of 23 that have both aspect
  -- and mood. There were no languages in the sample in which the mood
  -- marker occurred closer to the stem than the aspect marker."
  ⟨.aspect, .mood, 10, 0, 23⟩,
  -- p. 35: "Aspect markers were found to be closer to the stem than person
  -- markers in 12 out of 21 languages. In one language, Navaho, the person
  -- markers occur closer to the stem than the aspect marker."
  ⟨.aspect, .personAgr, 12, 1, 21⟩,
  -- p. 35: "Tense markers occur closer to the stem than mood markers in 8
  -- languages out of 20 that have both tense and mood. In one language,
  -- Ojibwa, the mood marker occurs closer to the stem than the tense marker."
  ⟨.tense, .mood, 8, 1, 20⟩,
  -- p. 35: "Tense markers occur closer to the stem than person markers in
  -- 8 languages out of the 17 that have both [tense and person]. In one
  -- language, Navaho, the person markers occur closer to the stem than
  -- the tense markers."
  ⟨.tense, .personAgr, 8, 1, 17⟩,
  -- p. 35: "Mood markers occur closer to the stem than person markers in
  -- 13 languages out of 26. In 5 languages the opposite order occurs."
  ⟨.mood, .personAgr, 13, 5, 26⟩
]

/-- Aspect vs. tense and aspect vs. mood are categorical: zero counterexamples
in the whole sample, the strongest confirmations Bybee reports. -/
theorem aspect_categorical_against_tense_and_mood :
    ∀ p ∈ orderPairs,
      p.closer = .aspect → (p.further = .tense ∨ p.further = .mood) →
      p.furtherCount = 0 := by
  decide

/-- Mood vs. person is the freest pair: the only one whose
counterexample-to-total ratio exceeds 1/10. -/
theorem mood_person_ordering_is_freer :
    ∀ p ∈ orderPairs,
      p.total < 10 * p.furtherCount ↔ (p.closer = .mood ∧ p.further = .personAgr) := by
  decide

/-- In every one of the six pairs the predicted direction outnumbers the
counter-direction (Ch 2 §6 summary). -/
theorem predicted_outnumbers_counter :
    ∀ p ∈ orderPairs, p.furtherCount < p.closerCount := by
  decide

/-- Aggregate Ch 2 §6 counts: 125 testable observations, 59 in the predicted
direction and 8 against (the other 58 are non-relevant under the exclusion
criteria above). -/
theorem ch2_section6_aggregate_counts :
    (orderPairs.map (·.total)).sum = 125 ∧
    (orderPairs.map (·.closerCount)).sum = 59 ∧
    (orderPairs.map (·.furtherCount)).sum = 8 := by
  decide

/-! ### Connection to substrate `MorphCategory.peripherality`

`MorphCategory.peripherality` (in `Morphology/RelevanceHierarchy.lean`) numerically
encodes the hierarchy — lower = closer to stem = more relevant — faithfully to
Ch 2 §3 for the six core categories. Its extensions (`derivation`, `degree`,
`negation`, `nonfinite`) are linglib additions, not Bybee's. -/

/-- Embed `BybeeCategory` into the substrate `MorphCategory`. All four agreement
subtypes collapse to `.agreement`: Bybee's verbal-number agreement sits at the
low-relevance (rank-8) end with person and gender, *not* with nominal `.number`
(rank 3). Subject vs object is preserved via the controller role. -/
def toMorphCategory : BybeeCategory → MorphCategory
  | .valence       => .valence
  | .voice         => .voice
  | .aspect        => .aspect
  | .tense         => .tense
  | .mood          => .mood
  | .numberAgr     => .agreement .subj
  | .personAgr     => .agreement .subj
  | .personAgrObj  => .agreement .obj
  | .genderAgr     => .agreement .subj

/-- The substrate relevance order is strictly increasing along the six Ch 2 §3
categories: it reproduces valence < voice < aspect < tense < mood < agreement. -/
theorem substrate_matches_bybee_hierarchy :
    List.Pairwise MorphCategory.RelevanceLT
      ([BybeeCategory.valence, .voice, .aspect, .tense, .mood, .personAgr].map
        toMorphCategory) := by
  decide

/-- The Ch 2 §6 morpheme-order data is exactly what `RespectsRelevanceHierarchy`
predicts: in the substrate relevance order, Bybee's predicted-closer category is
never less stem-relevant than the predicted-further one, so the order agrees
with the empirical-majority direction on every tested pair. -/
theorem orderPairs_consistent_with_substrate :
    ∀ p ∈ orderPairs,
      (toMorphCategory p.closer).RelevanceLE (toMorphCategory p.further) := by
  decide

/-! ### Grounding the hierarchy in the survey

On the four categories Bybee surveyed (aspect, tense, mood, person), the
substrate order is not a free choice: `SurveyedCloser`, derived from
`orderPairs`, coincides with `RelevanceLT` via `toMorphCategory`
(`survey_order_iso_relevance`). So a `RespectsRelevanceHierarchy` check over
these categories rests on an order isomorphism, not a stipulated table. -/

/-- `a` is *surveyed closer to the stem than* `b` when some tested Ch 2 §6 pair
predicts `a` closer than `b` and the language counts confirm that direction
(predicted majority). Derived from `orderPairs`, not stipulated. -/
def SurveyedCloser (a b : BybeeCategory) : Prop :=
  ∃ p ∈ orderPairs, p.closer = a ∧ p.further = b ∧ p.furtherCount < p.closerCount

instance : DecidableRel SurveyedCloser := fun _ _ => by
  unfold SurveyedCloser; exact inferInstance

/-- A category is *surveyed* if it appears in any tested Ch 2 §6 pair. -/
def Surveyed (c : BybeeCategory) : Prop :=
  ∃ p ∈ orderPairs, p.closer = c ∨ p.further = c

instance : DecidablePred Surveyed := fun _ => by
  unfold Surveyed; exact inferInstance

/-- `SurveyedCloser` is irreflexive: no tested pair ranks a category against
itself. -/
theorem surveyedCloser_irrefl : ∀ a : BybeeCategory, ¬ SurveyedCloser a a := by
  decide

/-- `SurveyedCloser` is transitive — the §6 survey tested every pair among its
categories, so the confirmed dominances compose. -/
theorem surveyedCloser_trans : ∀ a b c : BybeeCategory,
    SurveyedCloser a b → SurveyedCloser b c → SurveyedCloser a c := by
  decide

/-- `SurveyedCloser` is total on the surveyed categories: any two distinct
surveyed categories are ordered by the §6 data in exactly one direction. With
irreflexivity and transitivity, the survey *alone* determines a strict total
order on its four categories. -/
theorem surveyedCloser_total : ∀ a b : BybeeCategory,
    Surveyed a → Surveyed b → a ≠ b → SurveyedCloser a b ∨ SurveyedCloser b a := by
  decide

/-- Grounding theorem: whenever the survey places `a` closer than `b`, the
substrate ranks `a` strictly more stem-relevant — so `toMorphCategory` is
strictly monotone from the surveyed order into the relevance order. -/
theorem relevance_honors_survey : ∀ a b : BybeeCategory,
    SurveyedCloser a b →
      (toMorphCategory a).RelevanceLT (toMorphCategory b) := by
  decide

/-- Order isomorphism: on the surveyed categories, `SurveyedCloser` and the
substrate `RelevanceLT` coincide via `toMorphCategory`. The hierarchy there is
not merely consistent with Bybee's evidence — it *is* the order the §6 survey
determines. -/
theorem survey_order_iso_relevance : ∀ a b : BybeeCategory,
    Surveyed a → Surveyed b →
      (SurveyedCloser a b ↔ (toMorphCategory a).RelevanceLT (toMorphCategory b)) := by
  decide

/-- The stem-outward ordering of the surveyed categories — a literal, but
validated below as fully `SurveyedCloser`-sorted (`bybeeSurveyedOrder_sorted`)
and exactly the surveyed categories without repeats (`_complete`, `_nodup`). -/
def bybeeSurveyedOrder : List BybeeCategory :=
  [.aspect, .tense, .mood, .personAgr]

theorem bybeeSurveyedOrder_sorted : bybeeSurveyedOrder.Pairwise SurveyedCloser := by
  decide

theorem bybeeSurveyedOrder_complete : ∀ c : BybeeCategory,
    Surveyed c → c ∈ bybeeSurveyedOrder := by decide

theorem bybeeSurveyedOrder_nodup : bybeeSurveyedOrder.Nodup := by decide

/-- The surveyed order mapped to substrate categories — exposed so consumers
(`HahnDegenFutrell2021Morphology`, `Karlsson2017`, `RathiHahnFutrell2026`) check
their slot orders against the survey rather than re-asserting the hierarchy. -/
def bybeeSurveyedSlots : List MorphCategory :=
  bybeeSurveyedOrder.map toMorphCategory

/-- The data-derived surveyed order satisfies the substrate predicate, closing
the loop between Bybee's §6 evidence and `RespectsRelevanceHierarchy`. -/
theorem bybeeSurveyedSlots_respects_hierarchy :
    RespectsRelevanceHierarchy bybeeSurveyedSlots := by decide

/-! ### Ch 5 dynamic network, derived from the English Fragment

Bybee Ch 5 §8 illustrates the network architecture with the Spanish *dormir*
paradigm. We use English *eat/ate/eaten* and, rather than stipulating
`LexicalEntry` strings, **derive** the network from `eat : VerbEntry` in
`Fragments/English/Predicates/Verbal.lean`: changing `eat.formPast` there
updates the network (CLAUDE.md "derive, don't duplicate"). Token frequencies
default to 0; Bybee's verified counts (Francis & Kučera 1982) live in
`Morphology/UsageBased/Network.lean`. -/

open Morphology.UsageBased
open English.Predicates.Verbal

/-- A verb's five inflected forms as Bybee `LexicalEntry` instances (token
frequencies default to 0; the Fragment carries none). -/
def verbToLexicalEntries (v : VerbEntry) : List (LexicalEntry Unit) :=
  [⟨v.form, (), 0⟩, ⟨v.form3sg, (), 0⟩, ⟨v.formPast, (), 0⟩,
   ⟨v.formPastPart, (), 0⟩, ⟨v.formPresPart, (), 0⟩]

/-- The Bybee network of a verb's paradigm, built from its Fragment `VerbEntry`.
Every form pair gets a semantic edge (shared meaning) and a phonological edge —
the latter approximating Bybee's "shared phonological skeleton"; a real
similarity metric would gate it more selectively. -/
def verbToBybeeNetwork (v : VerbEntry) : Network Unit :=
  let entries := verbToLexicalEntries v
  let forms := entries.map (·.form)
  let pairs := forms.flatMap (λ a => forms.map (λ b => (a, b)))
  let connections := pairs.flatMap (λ (a, b) =>
    if a = b then [] else
    [⟨a, b, .semantic⟩, ⟨a, b, .phonological⟩])
  { entries := entries, connections := connections }

/-- The network of the English irregular *eat*, derived from the Fragment. -/
def eatNetwork : Network Unit := verbToBybeeNetwork eat

/-- Sanity check: *eat*'s past form appears as a network entry, read off
`eat.formPast` (no string literal), so `decide` tracks that field. -/
theorem eat_past_in_network :
    ∃ e ∈ eatNetwork.entries, e.form = eat.formPast := by decide

/-- *eat* and its past form are morphologically related (Ch 5 §5), derived from
`eat.formPast` rather than a literal.

Caveat: `verbToBybeeNetwork` connects *every* paradigm-form pair, so this holds
for any two distinct forms by construction — there is no shared-skeleton gate
yet. What the theorems here test is that the network is built from the Fragment
and that a non-paradigm form is correctly unrelated. -/
theorem eat_form_related_to_past_form :
    eatNetwork.HasMorphologicalRelation eat.form eat.formPast := by decide

/-- *eat* and its past-participle form are likewise related, derived from
`eat.formPastPart`. -/
theorem eat_form_related_to_pastPart_form :
    eatNetwork.HasMorphologicalRelation eat.form eat.formPastPart := by decide

/-- Negative test: a form outside *eat*'s paradigm bears no relation to it — the
relation is not vacuously true of arbitrary string pairs. -/
theorem eat_unrelated_to_nonparadigm_form :
    ¬ eatNetwork.HasMorphologicalRelation eat.form "swim" := by decide

end Bybee1985
