import Linglib.Morphology.MorphRule
import Linglib.Morphology.UsageBased.Network
import Linglib.Fragments.English.Predicates.Verbal
import Mathlib.Tactic.DeriveFintype

/-!
# Bybee (1985): Morphology — A Study of the Relation Between Meaning and Form
[bybee-1985]

[bybee-1985] (Typological Studies in Language 9, John Benjamins) reports
a 50-language sample (Perkins 1980 stratified probability sample) and tests
three predictions of the **relevance hypothesis**: morpheme categories whose
meaning is more directly relevant to the verb stem (a) occur more frequently
as inflectional categories cross-linguistically, (b) occur closer to the stem
in suffixal morphology, and (c) exhibit greater fusion with the stem.

This study file formalizes the cross-linguistic data underlying claims (a)
and (b) — Ch 2 §5 (frequency, Figs 1+2) and Ch 2 §6 (morpheme order, pp.
34-35) — and connects them to the substrate's `MorphCategory.peripherality`
ranking. Claim (c) (fusion) is qualitative in Ch 2 §7 and not formalized
here.

**What this file does NOT cover.** Ch 1 fusion/allomorphy/grammatical
meaning, Ch 3 paradigm organization (basic-derived, local markedness),
Ch 4 lexical-derivational-inflectional CONTINUUM (which contradicts the
substrate's discrete `MorphStatus` enum — flagged for future work), Part
II aspect/tense/mood detail (Ch 6-9). Bybee's Ch 2 §6 relevance ordering
is independently exercised in `Studies/HahnDegenFutrell2021Morphology.lean`
via the substrate's `RespectsRelevanceHierarchy` predicate (that file
does not consume `orderPairs` directly); the `BybeeCategory` enum and
`toMorphCategory` bridge below are consumed by
`Studies/RathiHahnFutrell2026.lean`. Ch 5's **dynamic network model**
substrate now lives in `Morphology/UsageBased/Network.lean`; the network
section below uses it on the English irregular verb *eat/ate/eaten*.

-/

namespace Bybee1985

open Morphology

/-! ### Bybee's verbal categories (Ch 2 §3, p. 20-23) -/

/-! Bybee discusses six core verbal-inflectional categories ordered by
relevance to the verb stem (most relevant first): valence, voice, aspect,
tense, mood, agreement. Number, person, and gender are sub-types of
agreement; object-person is reported separately in the survey data. -/

/-- The verbal-inflectional categories Bybee surveys in Ch 2.

The constructors are listed in Bybee's relevance order (most relevant to
verb stem first; cf. Ch 2 §3 p. 20 which orders "valence, voice, aspect,
tense, mood and agreement"). Object-person, number-as-agreement, and
gender are reported separately in Figs 1+2 (p. 30-31). -/
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

/-! ### Cross-linguistic frequency data (Ch 2 §5, Figures 1 + 2, pp. 30-31) -/

/-! Figure 1 (p. 30) reports the percentage of the 50-language sample with
**inflectional** expression of each category. Figure 2 (p. 31) reports the
same categories counting **both inflectional and derivational** affixes.
The raw counts (percentage × 50 / 100) are integers because the sample is
exactly 50 languages. -/

/-- Number of languages (out of 50) that have *inflectional* expression of
the given category. Verified directly against [bybee-1985] Fig 1
(p. 30). The raw counts equal `0.01 × percentage × 50`. -/
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

/-- Number of languages (out of 50) with *inflectional or derivational*
expression of the category. Fig 2 (p. 31). Valence's 90% reflects the
near-universality of valence-changing morphology (Ch 2 §5 p. 29) when
derivational expression is included; only Haitian, Karankawa, Navaho,
Serbo-Croatian, and Vietnamese show no such morphology in Bybee's
sources. -/
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

/-- Bybee's first prediction (Ch 2 §5 p. 29-30): when both inflectional and
derivational expression are counted, valence shows the highest cross-
linguistic frequency, reflecting its near-universality as a derivational
process even in languages with sparse verbal morphology. -/
theorem valence_highest_when_derivOrInfl :
    ∀ c : BybeeCategory, derivOrInflCount50 c ≤ derivOrInflCount50 .valence := by
  decide

/-- Among purely **inflectional** categories, mood shows the highest
frequency (Fig 1, p. 30: 68%). The valence drop from 90% (deriv+infl) to
6% (infl only) is Bybee's central observation that valence-changing
morphology is "almost always derivational" (Ch 2 §5 p. 30). -/
theorem mood_highest_when_inflectional :
    ∀ c : BybeeCategory, inflectionalCount50 c ≤ inflectionalCount50 .mood := by
  decide

/-- In the deriv+infl survey (Fig 2), gender agreement is the lowest-
frequency category — consistent with Bybee's claim (Ch 2 §3 p. 23) that
gender agreement has least relevance to the verb. (In Fig 1 inflection-
only, valence drops to 6% — *below* gender's 16% — because valence is
near-totally suppressed as inflection while remaining 90% as derivation.
The Fig 2 ranking is the relevance-faithful one.) -/
theorem gender_lowest_when_derivOrInfl :
    ∀ c : BybeeCategory, derivOrInflCount50 .genderAgr ≤ derivOrInflCount50 c := by
  decide

/-! ### Morpheme-order data (Ch 2 §6, pp. 34-35) -/

/-! Bybee's second prediction (Ch 2 §6 p. 33): the morpheme-order corollary.
"The most relevant to occur closest to the verb stem, and the least
relevant to occur at the greatest distance from the verb stem." Tested
on the four most frequent categories — aspect, tense, mood, person — by
counting, for each pair, in how many languages one is closer to the
stem than the other.

Cases were excluded when (a) the morphemes were portmanteau, (b) they
appeared on different sides of the stem (unless one was adjacent and
the other was not), (c) they were mutually exclusive in the same slot,
or (d) one was expressed via stem modification (counted as closer). -/

/-- A morpheme-order pair from Ch 2 §6. The fields record:
- `closer` — the category Bybee predicts to be closer to the stem
- `further` — the category Bybee predicts to be further from the stem
- `closerCount` — # languages where `closer` is closer to stem (predicted)
- `furtherCount` — # languages where `further` is closer to stem (counter-ex)
- `total` — total # languages where the pair is testable (Ch 2 §6 p. 34-35)
-/
structure OrderPair where
  closer : BybeeCategory
  further : BybeeCategory
  closerCount : Nat
  furtherCount : Nat
  total : Nat
  deriving Repr

/-- The six pairs Bybee tests in Ch 2 §6 (pp. 34-35). All counts verified
directly against the book. -/
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

/-- Aspect vs. tense and aspect vs. mood are categorical: zero counter-
examples in the entire 50-language sample. Bybee's summary (p. 35):
"the strongest differences are found between aspect and the other
categories, and between tense and the other categories, where there are
almost no counter-examples to the predicted ordering." -/
theorem aspect_categorical_against_tense_and_mood :
    ∀ p ∈ orderPairs,
      p.closer = .aspect → (p.further = .tense ∨ p.further = .mood) →
      p.furtherCount = 0 := by
  decide

/-- Mood-person ordering is genuinely freer: a pair's predicted-counter /
total ratio exceeds 1/10 *iff* it is the mood-person pair — i.e. mood-
person is the only pair in the survey above that threshold. -/
theorem mood_person_ordering_is_freer :
    ∀ p ∈ orderPairs,
      p.total < 10 * p.furtherCount ↔ (p.closer = .mood ∧ p.further = .personAgr) := by
  decide

/-- Across all six tested pairs, the predicted direction outnumbers the
counter-direction in every case (Ch 2 §6 summary, p. 35: "striking
confirmation of the hierarchical ordering of aspect, tense, mood and
person"). -/
theorem predicted_outnumbers_counter :
    ∀ p ∈ orderPairs, p.furtherCount < p.closerCount := by
  decide

/-- Total testable observations across all six pairs: 125 language-pair
observations contributed to the hierarchy test. The predicted
direction holds in 59 of them; the counter-direction in 8; the
remaining 58 are non-relevant (portmanteau, opposite-side, mutually-
exclusive, or stem-modification cases per Bybee's exclusion criteria
on p. 34). -/
theorem ch2_section6_aggregate_counts :
    (orderPairs.map (·.total)).sum = 125 ∧
    (orderPairs.map (·.closerCount)).sum = 59 ∧
    (orderPairs.map (·.furtherCount)).sum = 8 := by
  decide

/-! ### Connection to substrate `MorphCategory.peripherality` -/

/-! `Morphology/MorphRule.lean::MorphCategory.peripherality` numerically
encodes Bybee's relevance hierarchy: lower number = closer to stem = more
relevant. The substrate is faithful to Bybee Ch 2 §3 (p. 20-23) for the
six core categories Bybee discusses (valence < voice < aspect < tense <
mood < agreement). The substrate adds extensions (`derivation`, `degree`,
`negation`, `nonfinite`) that are not part of Bybee's verbal hierarchy —
those are flagged in `MorphRule.lean`'s docstring as linglib extensions. -/

/-- Map Bybee's category enum to the substrate's `MorphCategory`. All four
agreement subtypes (`personAgr`, `numberAgr`, `genderAgr`, `personAgrObj`)
collapse to `.agreement` — Bybee's verbal-number agreement belongs at the
low-relevance (rank-8) end with person and gender, *not* with nominal
`.number` (rank 3, "number marking on nouns"). Subject vs object agreement
is preserved via the controller role. -/
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

/-- The substrate's relevance order is **strictly increasing** along the six
categories Bybee discusses in Ch 2 §3 (one agreement sub-type stands for the
collapsed agreement rank). In other words, the substrate faithfully reproduces
Bybee's high-relevance-end ordering:
valence < voice < aspect < tense < mood < agreement. -/
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

The substrate's relevance order (`MorphCategory.RelevanceLT`, realized by the
`peripherality` rank) is, on the four categories Bybee surveyed in Ch 2 §6
(aspect, tense, mood, person), not a free choice. `SurveyedCloser` — the
dominance order *derived from* `orderPairs` — coincides with it via
`toMorphCategory` (`survey_order_iso_relevance`). So a consumer's
`RespectsRelevanceHierarchy` check over these categories is grounded in Bybee's
evidence by an order isomorphism, not by trust in a stipulated table. -/

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

/-- **Grounding theorem.** The substrate's relevance order *strictly* honors
every confirmed §6 dominance: whenever the survey places `a` closer than `b`,
the substrate ranks `a` strictly more stem-relevant. So `toMorphCategory` is a
strictly monotone map from the surveyed order into the relevance order. -/
theorem relevance_honors_survey : ∀ a b : BybeeCategory,
    SurveyedCloser a b →
      (toMorphCategory a).RelevanceLT (toMorphCategory b) := by
  decide

/-- **Order isomorphism.** On the categories Bybee surveyed in Ch 2 §6, the
data-derived `SurveyedCloser` order and the substrate's `RelevanceLT` order
*coincide* via `toMorphCategory`: each holds exactly when the other does. The
substrate hierarchy, restricted to the surveyed categories, is not merely
consistent with Bybee's evidence — it *is* the order the §6 survey determines.
This is the structural grounding the stipulated table only gestured at. -/
theorem survey_order_iso_relevance : ∀ a b : BybeeCategory,
    Surveyed a → Surveyed b →
      (SurveyedCloser a b ↔ (toMorphCategory a).RelevanceLT (toMorphCategory b)) := by
  decide

/-- The canonical stem-outward ordering of the surveyed categories. Written as
a literal but *validated against the data* below: it is fully sorted by
`SurveyedCloser` (`bybeeSurveyedOrder_sorted`) and lists exactly the surveyed
categories without repeats (`bybeeSurveyedOrder_complete`, `_nodup`), hence the
unique enumeration the §6 survey forces. -/
def bybeeSurveyedOrder : List BybeeCategory :=
  [.aspect, .tense, .mood, .personAgr]

theorem bybeeSurveyedOrder_sorted : bybeeSurveyedOrder.Pairwise SurveyedCloser := by
  decide

theorem bybeeSurveyedOrder_complete : ∀ c : BybeeCategory,
    Surveyed c → c ∈ bybeeSurveyedOrder := by decide

theorem bybeeSurveyedOrder_nodup : bybeeSurveyedOrder.Nodup := by decide

/-- The surveyed order, mapped to substrate categories — exposed for consumers
(`HahnDegenFutrell2021Morphology`, `Karlsson2017`, `RathiHahnFutrell2026`) to
check their slot orders against Bybee's surveyed evidence rather than
re-asserting the hierarchy. -/
def bybeeSurveyedSlots : List MorphCategory :=
  bybeeSurveyedOrder.map toMorphCategory

/-- The data-derived surveyed order satisfies the substrate predicate, closing
the loop between Bybee's §6 evidence and `RespectsRelevanceHierarchy`. -/
theorem bybeeSurveyedSlots_respects_hierarchy :
    RespectsRelevanceHierarchy bybeeSurveyedSlots := by decide

/-! ### Ch 5 dynamic network model — derived from English Fragment -/

/-! Bybee Ch 5 §8 (p. 124) illustrates the network architecture with
the Spanish *dormir* paradigm: three stem allomorphs (`dwerm`, `dorm`,
`durmy`) connected by morphological relations across persons/numbers/
tenses. We use the English irregular verb *eat/ate/eaten* as a smaller
instance — but rather than declaring fabricated `LexicalEntry` strings,
we **derive** the network from the actual `eat : VerbEntry` in
`Fragments/English/Predicates/Verbal.lean`. Per CLAUDE.md "derive don't
duplicate": changing `eat.formPast` in the Fragment automatically
updates this network; the connection between Fragment data and
Bybee-network claims is true by construction.

Token frequencies default to 0 in the bridge — Bybee's verified per-
lexeme counts (Francis & Kučera 1982) live in
`Morphology/UsageBased/Network.lean`'s `strongStillStrong`
/ `strongRegularized` datasets, which support its Ch 5 §6 irregularity-
vs-frequency theorem `strong_verbs_higher_frequency_than_regularized`
(Bybee p. 120, counts across Sweet's Anglo Saxon Primer Class I/II/VII). -/

open Morphology.UsageBased
open English.Predicates.Verbal

/-- Extract a verb's five inflected forms as Bybee `LexicalEntry`
    instances. Token frequencies default to 0; the Fragment doesn't
    carry per-form frequencies. -/
def verbToLexicalEntries (v : VerbEntry) : List (LexicalEntry Unit) :=
  [⟨v.form, (), 0⟩, ⟨v.form3sg, (), 0⟩, ⟨v.formPast, (), 0⟩,
   ⟨v.formPastPart, (), 0⟩, ⟨v.formPresPart, (), 0⟩]

/-- Construct the Bybee network of a verb's paradigm from its Fragment
    `VerbEntry`. All inflected forms receive pairwise semantic
    connections (they share the verb's meaning, modulated by tense/
    aspect/agreement). Pairwise phonological connections approximate
    Bybee's "shared phonological skeleton" relation; a real
    similarity metric would gate this more selectively (e.g. eat/ate
    share /e_t/ but not /eating/ proper). -/
def verbToBybeeNetwork (v : VerbEntry) : Network Unit :=
  let entries := verbToLexicalEntries v
  let forms := entries.map (·.form)
  let pairs := forms.flatMap (λ a => forms.map (λ b => (a, b)))
  let connections := pairs.flatMap (λ (a, b) =>
    if a = b then [] else
    [⟨a, b, .semantic⟩, ⟨a, b, .phonological⟩])
  { entries := entries, connections := connections }

/-- The Bybee network of the English irregular verb *eat* — derived
    from the Fragment, NOT stipulated. -/
def eatNetwork : Network Unit := verbToBybeeNetwork eat

/-- Sanity check: *eat*'s past form is present in the network as an entry,
    derived from the Fragment's `eat.formPast` field (no string literal).
    If `eat.formPast` changed in `Verbal.lean`, the `decide` tracks the
    new value. -/
theorem eat_past_in_network :
    ∃ e ∈ eatNetwork.entries, e.form = eat.formPast := by decide

/-- **Caveat on these relation theorems.** `verbToBybeeNetwork` connects
    *every* pair of paradigm forms with both a semantic and a phonological
    edge, so `HasMorphologicalRelation` holds for any two distinct forms of
    the same verb by construction — it does not yet apply a real
    shared-phonological-skeleton gate (see `verbToBybeeNetwork`). What the
    theorems below genuinely test is that the network is *built from the
    Fragment*: the related forms are `eat`'s actual fields (no string
    literals), and a form outside the paradigm is correctly unrelated.

    *eat* and its past form bear a morphological relation (parallel
    semantic + phonological connections, Ch 5 §5 p. 118), derived from
    `eat`'s Fragment fields — if `eat.formPast` changed, the statement
    would refer to the new value. -/
theorem eat_form_related_to_past_form :
    eatNetwork.HasMorphologicalRelation eat.form eat.formPast := by decide

/-- *eat* and its past-participle form are likewise related, again derived
    from the Fragment (`eat.formPastPart`) rather than a literal. -/
theorem eat_form_related_to_pastPart_form :
    eatNetwork.HasMorphologicalRelation eat.form eat.formPastPart := by decide

/-- Negative rejection test: a form outside *eat*'s paradigm bears no
    morphological relation to it. The relation genuinely requires both
    endpoints to be connected forms in the network — it is not vacuously
    true of arbitrary string pairs. -/
theorem eat_unrelated_to_nonparadigm_form :
    ¬ eatNetwork.HasMorphologicalRelation eat.form "swim" := by decide

end Bybee1985
