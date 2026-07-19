import Linglib.Morphology.Morphotactics.RelevanceHierarchy
import Mathlib.Tactic.DeriveFintype

/-!
# Bybee (1985): relevance and the dynamic lexicon

[bybee-1985] (*Morphology: A Study of the Relation Between Meaning and Form*,
Typological Studies in Language 9) tests the **relevance hypothesis** on a
50-language stratified probability sample ([perkins-1980]): a morpheme category
whose meaning is more relevant to the verb stem (a) occurs more often as
inflection cross-linguistically, (b) sits closer to the stem in suffixal
morphology, and (c) fuses more tightly with it.

This file formalizes the data behind claims (a) and (b) — the Ch 2 §5 frequency
surveys and the Ch 2 §6 morpheme-order counts — and grounds the substrate's
relevance order (`MorphCategory.peripherality`, via `RelevanceLT` / `RelevanceLE`)
in that evidence. Claim (c), fusion, is qualitative in the source and is not
formalized. The second half formalizes Ch 5's dynamic network model of the
lexicon: lexical strength, lexical connection, and the strong-verb frequency
table.

## Main definitions

* `BybeeCategory` — the verbal-inflectional categories of Ch 2, in relevance order.
* `inflectionalCount50`, `derivOrInflCount50` — the Ch 2 §5 frequency surveys (Figs 1+2).
* `orderPairs` — the Ch 2 §6 morpheme-order counts, one `OrderPair` per tested category pair.
* `toMorphCategory` — the embedding of `BybeeCategory` into the substrate `MorphCategory`.
* `SurveyedCloser` — the stem-proximity order *derived from* `orderPairs`.
* `LexicalEntry`, `Network` — the Ch 5 dynamic network: entries with token
  frequency (lexical strength) and typed connections (lexical connection).
* `Network.HasMorphologicalRelation` — the Ch 5 §5 derived relation: parallel
  semantic and phonological connections.
* `strongStillStrong`, `strongRegularized` — the Ch 5 §6 strong-verb frequency
  table.

## Main results

* `valence_highest_when_derivOrInfl`, `valence_lowest_when_inflectional` — the
  relevance and generality frequency predictions.
* `predicted_outnumbers_counter`, `aspect_categorical_against_tense_and_mood` — the order predictions.
* `survey_order_iso_relevance` — on the surveyed categories `SurveyedCloser` and the substrate
  `RelevanceLT` coincide via `toMorphCategory`: the hierarchy is the order the §6 survey forces,
  not a stipulated table.
* `bybeeSurveyedOrder_respects_hierarchy` — closes the loop to `RespectsRelevanceHierarchy`.
* `strong_verbs_higher_frequency_than_regularized` — the Ch 5 §6 diachronic
  claim: still-Strong verbs have a strictly higher mean token frequency than
  the regularized ones.

## Implementation notes

Out of scope: Ch 1 fusion/allomorphy, Ch 3 paradigm organization, Ch 4's
lexical-derivational-inflectional continuum (which no discrete status
enum expresses — flagged for future work), and Part II tense/aspect/mood
detail (Ch 6-9). `MorphCategory.RelevanceLT` is exercised independently by
`Studies/HahnDegenFutrell2021Morphology.lean`; the `BybeeCategory` enum and
`toMorphCategory` bridge feed `Studies/RathiHahnFutrell2026.lean`. Not yet
covered from Ch 5: the frequency-connection interaction (high-frequency items
form more *distant* connections — the autonomy half of the model), and §10-§11
schema emergence and productivity from class size.
-/

namespace Bybee1985

open Morphology

/-! ### Verbal categories (Ch 2 §3)

Bybee's six core categories in relevance order: valence, voice, aspect, tense,
mood, agreement (number/person/gender are agreement sub-types). -/

/-- Bybee's Ch 2 verbal-inflectional categories, in her relevance order (stem
first). Constructor docstrings quote the coding definitions of Ch 2 §4. -/
inductive BybeeCategory where
  /-- Differences in the number or role of the arguments the verb stem takes. -/
  | valence
  /-- The perspective from which the situation described by the verb stem is
  viewed. -/
  | voice
  /-- The way the internal temporal constituency of the situation is viewed. -/
  | aspect
  /-- The situation's placement in time, relative to the moment of speech or
  some other established point. -/
  | tense
  /-- The way the speaker presents the truth of the proposition: probability,
  possibility, certainty; evidentials are included under mood. -/
  | mood
  /-- Concord by number with one or more arguments of the verb. -/
  | numberAgr
  /-- Concord by person with the subject. -/
  | personAgr
  /-- Concord by person with the object. -/
  | personAgrObj
  /-- Concord with arguments by lexical class, assigned arbitrarily or by
  inherent qualities of the referent. -/
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

/-- The generality prediction: restricted to *inflection*, valence is the least
frequent category (6%, down from 90%) — generality "predicts fewer inflections
among the most highly relevant categories", because highly relevant morphology
is rarely obligatory across all stems. -/
theorem valence_lowest_when_inflectional :
    ∀ c : BybeeCategory, inflectionalCount50 .valence ≤ inflectionalCount50 c := by
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
A language with both categories is untestable when the morphemes are
portmanteau, on opposite sides of the stem (unless only one is stem-adjacent),
or mutually exclusive in one slot; a morpheme expressed by stem modification
counts as closer than one expressed by affixation. -/

/-- A Ch 2 §6 morpheme-order pair. -/
structure OrderPair where
  /-- The category predicted closer to the stem. -/
  closer : BybeeCategory
  /-- The category predicted further from the stem. -/
  further : BybeeCategory
  /-- The languages confirming the predicted order. -/
  closerCount : Nat
  /-- The languages showing the opposite order. -/
  furtherCount : Nat
  /-- The languages having both categories, testable or not. -/
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

/-- Mood vs. person is the freest pair — "the ordering of mood and person is
somewhat freer" — cross-multiplied: every other tested pair has a strictly
smaller counterexample rate. -/
theorem mood_person_ordering_is_freest :
    ∀ p ∈ orderPairs, ∀ q ∈ orderPairs,
      q.closer = .mood → p.closer ≠ .mood →
      p.furtherCount * q.total < q.furtherCount * p.total := by
  decide

/-- In every one of the six pairs the predicted direction outnumbers the
counter-direction (Ch 2 §6 summary). -/
theorem predicted_outnumbers_counter :
    ∀ p ∈ orderPairs, p.furtherCount < p.closerCount := by
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

instance : DecidableRel SurveyedCloser := fun _ _ =>
  inferInstanceAs (Decidable (∃ _ ∈ orderPairs, _))

/-- A category is *surveyed* if it appears in any tested Ch 2 §6 pair. -/
def Surveyed (c : BybeeCategory) : Prop :=
  ∃ p ∈ orderPairs, p.closer = c ∨ p.further = c

instance : DecidablePred Surveyed := fun _ =>
  inferInstanceAs (Decidable (∃ _ ∈ orderPairs, _))

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

/-- Order isomorphism: on the surveyed categories, `SurveyedCloser` and the
substrate `RelevanceLT` coincide via `toMorphCategory`. The hierarchy there is
not merely consistent with Bybee's evidence — it *is* the order the §6 survey
determines. -/
theorem survey_order_iso_relevance : ∀ a b : BybeeCategory,
    Surveyed a → Surveyed b →
      (SurveyedCloser a b ↔ (toMorphCategory a).RelevanceLT (toMorphCategory b)) := by
  decide

/-- The stem-outward ordering of the surveyed categories — a literal, but
validated as fully `SurveyedCloser`-sorted (`bybeeSurveyedOrder_sorted`) and
exhaustive (`bybeeSurveyedOrder_complete`). -/
def bybeeSurveyedOrder : List BybeeCategory :=
  [.aspect, .tense, .mood, .personAgr]

theorem bybeeSurveyedOrder_sorted : bybeeSurveyedOrder.Pairwise SurveyedCloser := by
  decide

theorem bybeeSurveyedOrder_complete : ∀ c : BybeeCategory,
    Surveyed c → c ∈ bybeeSurveyedOrder := by decide

/-- The data-derived surveyed order satisfies the substrate predicate, closing
the loop between Bybee's §6 evidence and `RespectsRelevanceHierarchy`. -/
theorem bybeeSurveyedOrder_respects_hierarchy :
    RespectsRelevanceHierarchy (bybeeSurveyedOrder.map toMorphCategory) := by decide

/-! ### Ch 5: the dynamic network model

Ch 5 ("Two Principles in a Dynamic Model of Lexical Representation") abandons
the generative "is it in the lexicon or not?" binary for two gradient, dynamic
notions. **Lexical strength** (§4): each token of use strengthens an item's
representation ("etching it with deeper and darker lines each time"), and
strength declines with disuse. **Lexical connection** (§5): items bear typed
connections to other items, and parallel semantic and phonological connections
constitute a *morphological relation*. Bybee's network model is the usage-based
competitor to the realisational and generative engines in `Morphology/`; not to
be confused with Network Morphology, the DATR-based default-inheritance
framework. -/

/-- A stored item in Bybee's Ch 5 lexicon: a form with its token frequency.
Frequency models lexical strength — each token of use strengthens the
representation, and strength declines with disuse (§4). Bybee's entries pair
the form with a meaning; the semantic side of matching is not modeled here. -/
structure LexicalEntry where
  /-- The phonological form. -/
  form : String
  /-- The token frequency, modeling lexical strength. -/
  tokenFreq : Nat
  deriving Repr

/-- The kind of a connection between lexical entries (Ch 5 §5): shared semantic
features (*table*~*chair*, *deep*~*shallow*), a shared phonological skeleton
without shared meaning (the two senses of *crane*), the morphological relation
(parallel semantic and phonological connections), or identity (§7), the mapping
of one word onto an existing representation. Bybee orders their strengths:
purely phonological relations "usually go unnoticed", semantic connections are
"the strongest and the most important" (*go*~*went* supports *goed*), the
morphological relation is the strongest relation between distinct forms, and
"the strongest relations are relations of identity". -/
inductive ConnectionKind where
  | semantic
  | phonological
  | morphological
  | identity
  deriving DecidableEq, Repr

/-- A directed typed edge between two forms in the lexical network. -/
structure Connection where
  /-- The source form. -/
  src : String
  /-- The target form. -/
  dst : String
  /-- The kind of connection. -/
  kind : ConnectionKind
  deriving Repr

/-- A lexical network: entries plus typed connections among them, as in the
Ch 5 §8 representation of the Spanish *dormir* paradigm, whose three stem
allomorphs (*dwerm*, *dorm*, *durm-y*) are linked by morphological relations
across persons, numbers, and tenses. -/
structure Network where
  /-- The stored lexical entries. -/
  entries : List LexicalEntry
  /-- The typed connections among entries. -/
  connections : List Connection
  deriving Repr

/-- `N.IsRelatedBy a b k` asserts that network `N` has a connection of kind `k`
from form `a` to form `b`. -/
def Network.IsRelatedBy (N : Network) (a b : String) (k : ConnectionKind) : Prop :=
  ∃ c ∈ N.connections, c.src = a ∧ c.dst = b ∧ c.kind = k

/-- `N.HasMorphologicalRelation a b` asserts that `a` and `b` stand in both a
semantic and a phonological connection — Ch 5 §5: "if two words are related by
both semantic and phonological connections, then a morphological relation
exists between them". The relation is derived, not primitive;
`ConnectionKind.morphological` labels edges already so classified. -/
def Network.HasMorphologicalRelation (N : Network) (a b : String) : Prop :=
  N.IsRelatedBy a b .semantic ∧ N.IsRelatedBy a b .phonological

/-! ### Ch 5 §6: strong-verb frequencies

Bybee's central diachronic claim: high-frequency strong verbs maintain their
irregularity, low-frequency strong verbs regularize. The table on p. 120 lists
the modern descendants of the Strong Verbs of classes I, II, and VII in
[sweet-1882]'s *Anglo-Saxon Primer* with their all-forms token frequencies from
[francis-kucera-1982]. *Slit* and *beat* now take the zero allomorph of Past
Tense (Bybee's footnote). -/

/-- The Strong Verbs that have stayed Strong (p. 120), with all-forms token
frequencies. -/
def strongStillStrong : List LexicalEntry := [
  -- Class I (mean 223)
  ⟨"drive", 203⟩, ⟨"rise", 199⟩, ⟨"ride", 126⟩, ⟨"write", 561⟩, ⟨"bite", 26⟩,
  -- Class II (mean 140)
  ⟨"choose", 177⟩, ⟨"fly", 92⟩, ⟨"shoot", 117⟩, ⟨"lose", 274⟩, ⟨"flee", 40⟩,
  -- Class VII (mean 515)
  ⟨"fall", 239⟩, ⟨"hold", 509⟩, ⟨"know", 1473⟩, ⟨"grow", 300⟩, ⟨"blow", 52⟩
]

/-- The Strong Verbs that have regularized or become Weak (p. 120), with
all-forms token frequencies. -/
def strongRegularized : List LexicalEntry := [
  -- Class I (mean 5)
  ⟨"bide", 1⟩, ⟨"reap", 5⟩, ⟨"slit", 3⟩, ⟨"sneak", 11⟩,
  -- Class II (mean 22)
  ⟨"rue", 0⟩, ⟨"seethe", 0⟩, ⟨"smoke", 26⟩, ⟨"float", 23⟩, ⟨"shove", 16⟩,
  -- Class VII (mean 21)
  ⟨"wax", 6⟩, ⟨"weep", 28⟩, ⟨"beat", 66⟩, ⟨"hew", 1⟩, ⟨"leap", 33⟩,
  ⟨"mow", 1⟩, ⟨"sow", 6⟩, ⟨"flow", 40⟩, ⟨"row", 5⟩
]

/-- The mean token frequency of the still-Strong verbs strictly exceeds that of
the regularized ones — irregularity survives where lexical strength is high.
Stated as the cross-multiplied sum comparison to stay in `Nat`. -/
theorem strong_verbs_higher_frequency_than_regularized :
    (strongRegularized.map (·.tokenFreq)).sum * strongStillStrong.length
    < (strongStillStrong.map (·.tokenFreq)).sum * strongRegularized.length := by
  decide

end Bybee1985
