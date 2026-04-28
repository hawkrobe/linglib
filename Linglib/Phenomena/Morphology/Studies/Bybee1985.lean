import Linglib.Core.Morphology.MorphRule
import Linglib.Theories.Morphology.UsageBased.Network
import Linglib.Fragments.English.Predicates.Verbal
import Mathlib.Tactic.DeriveFintype

/-!
# Bybee (1985): Morphology — A Study of the Relation Between Meaning and Form
@cite{bybee-1985}

@cite{bybee-1985} (Typological Studies in Language 9, John Benjamins) reports
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
II aspect/tense/mood detail (Ch 6-9). See `Phenomena/Morphology/Studies/
HahnDegenFutrell2021.lean` for a downstream consumer of the §6 ordering
data via `RespectsRelevanceHierarchy`. Ch 5's **dynamic network model**
substrate now lives in `Theories/Morphology/UsageBased/Network.lean`;
§5 below uses it on an English sing/sang/sung instance.

-/

namespace Phenomena.Morphology.Studies.Bybee1985

open Core.Morphology

-- ============================================================================
-- §1: Bybee's Verbal Categories (Ch 2 §3, p. 20-23)
-- ============================================================================

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

-- ============================================================================
-- §2: Cross-Linguistic Frequency Data (Ch 2 §5, Figures 1 + 2, pp. 30-31)
-- ============================================================================

/-! Figure 1 (p. 30) reports the percentage of the 50-language sample with
**inflectional** expression of each category. Figure 2 (p. 31) reports the
same categories counting **both inflectional and derivational** affixes.
The raw counts (percentage × 50 / 100) are integers because the sample is
exactly 50 languages. -/

/-- Number of languages (out of 50) that have *inflectional* expression of
the given category. Verified directly against @cite{bybee-1985} Fig 1
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

-- ============================================================================
-- §3: Morpheme-Order Data (Ch 2 §6, pp. 34-35)
-- ============================================================================

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
    (orderPairs.head?.map (·.furtherCount) = some 0) ∧
    (orderPairs[1]?.map (·.furtherCount) = some 0) := by
  decide

/-- Mood-person ordering is genuinely freer: the mood-person pair is the
*only* one in the survey where the predicted-counter / total ratio
exceeds 1/10. -/
theorem mood_person_ordering_is_freer :
    ∀ p ∈ orderPairs, p.further = .personAgr ∧ p.closer = .mood
      ∨ 10 * p.furtherCount ≤ p.total := by
  decide

/-- Across all six tested pairs, the predicted direction outnumbers the
counter-direction in every case (Ch 2 §6 summary, p. 35: "striking
confirmation of the hierarchical ordering of aspect, tense, mood and
person"). -/
theorem predicted_outnumbers_counter :
    orderPairs.all (λ p => p.furtherCount < p.closerCount) = true := by
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

-- ============================================================================
-- §4: Connection to Substrate `MorphCategory.peripherality`
-- ============================================================================

/-! `Core/Lexical/MorphRule.lean::MorphCategory.peripherality` numerically
encodes Bybee's relevance hierarchy: lower number = closer to stem = more
relevant. The substrate is faithful to Bybee Ch 2 §3 (p. 20-23) for the
six core categories Bybee discusses (valence < voice < aspect < tense <
mood < agreement). The substrate adds extensions (`derivation`, `degree`,
`negation`, `nonfinite`) that are not part of Bybee's verbal hierarchy —
those are flagged in `MorphRule.lean`'s docstring as linglib extensions. -/

/-- Map Bybee's category enum to the substrate's `MorphCategory`. Object
agreement and number-as-agreement collapse to the substrate's
`.agreement` and `.number` respectively. -/
def toMorphCategory : BybeeCategory → MorphCategory
  | .valence       => .valence
  | .voice         => .voice
  | .aspect        => .aspect
  | .tense         => .tense
  | .mood          => .mood
  | .numberAgr     => .number
  | .personAgr     => .agreement
  | .personAgrObj  => .agreement
  | .genderAgr     => .agreement

/-- The substrate's `peripherality` ordering is **strictly monotonic** on
the six categories Bybee discusses in Ch 2 §3 (excluding the agreement
sub-types which collapse to a single rank). In other words, the
substrate faithfully reproduces Bybee's high-relevance-end ordering:
valence < voice < aspect < tense < mood < agreement. -/
theorem substrate_matches_bybee_hierarchy :
    List.Pairwise (· < ·)
      ([BybeeCategory.valence, .voice, .aspect, .tense, .mood, .personAgr].map
        (λ c => (toMorphCategory c).peripherality)) := by
  decide

/-- The §6 morpheme-order data is exactly what `RespectsRelevanceHierarchy`
predicts: when Bybee's predicted-closer category has lower
peripherality than the predicted-further one, the substrate predicate
agrees with the empirical-majority direction. -/
theorem orderPairs_consistent_with_substrate :
    orderPairs.all (λ p =>
      decide ((toMorphCategory p.closer).peripherality
              < (toMorphCategory p.further).peripherality)
      || decide ((toMorphCategory p.closer).peripherality
                 = (toMorphCategory p.further).peripherality))
    = true := by
  decide

-- ============================================================================
-- §5: Ch 5 Dynamic Network Model — derived from English Fragment
-- ============================================================================

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
`Theories/Morphology/UsageBased/Network.lean`'s `strongStillStrong`
/ `strongRegularized` datasets, which support the Ch 5 §6 irregularity-
vs-frequency theorem. -/

open Theories.Morphology.UsageBased
open Fragments.English.Predicates.Verbal

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

/-- Sanity check: *eat*'s past form is *ate* (verified via the network's
    presence test, which derives from the Fragment's `eat.formPast`
    field). If `eat.formPast` were changed in `Verbal.lean` from "ate"
    to anything else, this theorem would fail to type-check. -/
theorem eat_past_in_network :
    eatNetwork.entries.any (·.form == "ate") := by decide

/-- *eat* and *ate* bear a morphological relation in `eat`'s network
    (parallel semantic + phonological connections, Ch 5 §5 p. 118).
    Derived from `eat`'s Fragment fields — the connection between
    "eat" and "ate" exists *because* `eat.formPast = "ate"`. -/
theorem eat_ate_morphologically_related :
    eatNetwork.HasMorphologicalRelation "eat" "ate" := by decide

theorem eat_eaten_morphologically_related :
    eatNetwork.HasMorphologicalRelation "eat" "eaten" := by decide

theorem ate_eaten_morphologically_related :
    eatNetwork.HasMorphologicalRelation "ate" "eaten" := by decide

/-- Maximally derive-don't-duplicate: even the form *strings* come
    from Fragment fields. This theorem makes no string-literal
    reference to "eat" or "ate" — if the Fragment fields change,
    the theorem statement refers to whatever the new fields denote. -/
theorem eat_form_related_to_past_form :
    eatNetwork.HasMorphologicalRelation eat.form eat.formPast := by decide

/-- The empirical anchor for Ch 5 §6's central claim — that high-
    frequency Strong Verbs maintained their irregularity while low-
    frequency ones regularized — lives in the substrate file as
    `strong_verbs_higher_frequency_than_regularized` (Bybee p. 120,
    verified Francis & Kučera 1982 counts across Sweet's Anglo Saxon
    Primer Class I/II/VII). Re-stated here so the study file's
    coverage is self-documenting. -/
theorem ch5_section6_anchor_lives_in_substrate :
    (strongStillStrong.map (·.tokenFreq)).sum * strongRegularized.length
    > (strongRegularized.map (·.tokenFreq)).sum * strongStillStrong.length :=
  strong_verbs_higher_frequency_than_regularized

end Phenomena.Morphology.Studies.Bybee1985
