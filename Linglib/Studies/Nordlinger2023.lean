import Linglib.Syntax.Reciprocal
import Linglib.Studies.Siloni2012
import Linglib.Data.WALS.Features.F106A
import Linglib.Fragments.English.Pronouns
import Linglib.Syntax.Binding.Basic
import Linglib.Fragments.Swahili.Reciprocals

/-!
# Nordlinger (2023) [nordlinger-2023]

Reciprocal constructions: a typological-formal review.

Formalizes the apparatus of [nordlinger-2023]'s review of reciprocal
constructions, which summarizes earlier classificatory work
([konig-kokutani-2006], [maslova-2008], [evans-2008], [nedjalkov-2007a],
[siloni-2008], [siloni-2012], [dalrymple-et-al-1998], [evans-et-al-2011b])
and organizes the empirical picture around strategy/valency correlations
(§3.2) and Siloni's discontinuity asymmetry (§3.3).

The underlying primitives (`RecipStrategy`, `RecipValency`,
`RecipFormation`, `ReciprocalType`) live in `Syntax/Reciprocal.lean`,
anchored on the earlier sources the review synthesizes — which preserves
chronological dependency for `Studies/Siloni2012.lean`.

## Contents

- `RecipProfile` per-language extended reciprocal profiles (12 languages)
- Strategy-valency correlation theorems (§3.2)
- Siloni's discontinuity prediction checked against attested judgments (§3.3)
- WALS Ch 106 grounding for `RecipProfile` (via `lookupISO`)
- `ReciprocityType` semantic 6-way classification (§4)
- `RecipMarkerPolysemy` extended readings (§4.2)
- Fragment grounding for English reciprocals
-/

namespace Nordlinger2023

open Reciprocal

/-! ### Reciprocal profiles -/

/-- Extended reciprocal profile for a single language.

    Captures the morphosyntactic strategy, valency effect, formation
    locus, and attested discontinuity judgments from [nordlinger-2023]'s
    review, going beyond the WALS 4-way reflexive-reciprocal
    classification. -/
structure RecipProfile where
  language : String
  iso : String
  /-- Primary reciprocal strategy ([nordlinger-2023] §3.1 inventory) -/
  primaryStrategy : RecipStrategy
  /-- Secondary strategy, if the language uses a second, different one -/
  secondaryStrategy : Option RecipStrategy := none
  /-- Valency effect of the primary strategy -/
  valency : RecipValency
  /-- Formation locus of verb-marked reciprocals ([siloni-2012]) -/
  formation : Option RecipFormation := none
  /-- Attested availability of the discontinuous reciprocal construction
      ([nordlinger-2023] §3.3 judgments), independent of `formation` so
      Siloni's prediction can be checked rather than stipulated -/
  discontinuousAttested : Option Bool := none
  /-- Reciprocal-reflexive relationship (WALS Ch 106) -/
  reflexiveRelation : ReciprocalType
  deriving Repr, DecidableEq

-- Language data: 12 reciprocal profiles from [nordlinger-2023]

/-- English: bipartite NP *each other* (bivalent, distinct from reflexive;
    [nordlinger-2023] ex. 1b). Lexical reciprocals (*quarrel*, *meet*,
    ex. 7) are a secondary strategy; per [siloni-2012] these are
    lexicon-formed, but *kiss*/*hug* resist the discontinuous
    construction (fn. 32), so no formation-level discontinuity value is
    recorded. Expresses all six reciprocity types (ex. 44). -/
def rpEnglish : RecipProfile :=
  { language := "English", iso := "eng"
  , primaryStrategy := .bipartiteNP
  , secondaryStrategy := some .lexical
  , valency := .bivalent
  , reflexiveRelation := .distinctFromReflexive }

/-- Russian: bipartite NP *drug druga* 'other other-ACC'
    ([nordlinger-2023] ex. 9, grouped with English *each other* as the
    bipartite strategy) plus reflexive-identical verbal postfix *-sja*
    (monovalent; ex. 31). Unlike French *se* (a separable clitic),
    *-sja* is a bound suffix, so the secondary strategy is `verbalAffix`. -/
def rpRussian : RecipProfile :=
  { language := "Russian", iso := "rus"
  , primaryStrategy := .bipartiteNP
  , secondaryStrategy := some .verbalAffix
  , valency := .bivalent
  , reflexiveRelation := .mixed }

/-- Swahili: verbal affix *-an-* (monovalent, distinct from reflexive
    *-ji-*; [nordlinger-2023] ex. 12). Forms discontinuous reciprocals
    with comitative *na* (ex. 37 from [hurst-2012], ex. 40 from
    [dimitriadis-2004]), hence lexicon-formed under Siloni's typology as
    presented in §3.3 ([siloni-2012] itself does not discuss Swahili).
    The morphological rule is `Swahili.Reciprocals.reciprocalAffix`. -/
def rpSwahili : RecipProfile :=
  { language := "Swahili", iso := "swh"
  , primaryStrategy := .verbalAffix
  , valency := .monovalent
  , formation := some .lexical
  , discontinuousAttested := some true
  , reflexiveRelation := .distinctFromReflexive }

/-- Hungarian: verbal affix *-óz-* (monovalent; [nordlinger-2023]
    ex. 19, 30, citing [siloni-2008]). Lexicon-formed per [siloni-2012]'s
    own classification; forms discontinuous reciprocals with comitative
    *-val* (ex. 38, from [dimitriadis-2008]). -/
def rpHungarian : RecipProfile :=
  { language := "Hungarian", iso := "hun"
  , primaryStrategy := .verbalAffix
  , valency := .monovalent
  , formation := some .lexical
  , discontinuousAttested := some true
  , reflexiveRelation := .distinctFromReflexive }

/-- French: reciprocal clitic *se* (monovalent, reflexive-identical;
    [nordlinger-2023] ex. 28, 47) plus distinct bipartite *l'un l'autre*.
    The review argues (after [siloni-2008], [siloni-2012]) that *se* is
    not a reciprocal object: embedded *se*-reciprocals lack the "I"
    reading (ex. 35). Syntax-formed, and discontinuous reciprocals are
    ungrammatical (ex. 39). -/
def rpFrench : RecipProfile :=
  { language := "French", iso := "fra"
  , primaryStrategy := .recipClitic
  , secondaryStrategy := some .bipartiteNP
  , valency := .monovalent
  , formation := some .syntactic
  , discontinuousAttested := some false
  , reflexiveRelation := .mixed }

/-- Greek (Modern): nonactive voice morphology (monovalent, reflexive-
    identical in form) plus distinct constructions. Forms discontinuous
    reciprocals with *me* 'with': "O Giannis filithike me ti Maria"
    ([nordlinger-2023] ex. 27b, 36, from [dimitriadis-2008]) — hence
    lexicon-formed under Siloni's typology as presented in §3.3
    ([siloni-2012] itself does not discuss Greek). -/
def rpGreek : RecipProfile :=
  { language := "Modern Greek", iso := "ell"
  , primaryStrategy := .verbalAffix
  , valency := .monovalent
  , formation := some .lexical
  , discontinuousAttested := some true
  , reflexiveRelation := .mixed }

/-- German: dedicated reciprocal pronoun *einander* alongside reflexive
    *sich* in reciprocal use — the WALS "mixed" configuration. Both
    fill the object slot, preserving bivalent syntax. The enum has no
    case for reflexive-pronouns-used-reciprocally, so only the dedicated
    pronoun strategy is recorded. [siloni-2012] fn. 13 suggests German
    *sich*-reciprocals are syntactic reciprocal verbs; the review does
    not take this up, so no formation value is recorded. -/
def rpGerman : RecipProfile :=
  { language := "German", iso := "deu"
  , primaryStrategy := .recipPronoun
  , valency := .bivalent
  , reflexiveRelation := .mixed }

/-- Mandarin: compound verb strategy *dǎ-lái-dǎ-qù*
    (beat-come-beat-go = 'beat each other'), single subject NP.
    Distinct from reflexive. [nordlinger-2023] ex. 13 (citing
    [konig-kokutani-2006]); [evans-2008] treats verb compounding as a
    multiclausal strategy. -/
def rpMandarin : RecipProfile :=
  { language := "Mandarin", iso := "cmn"
  , primaryStrategy := .compoundVerb
  , valency := .monovalent
  , reflexiveRelation := .distinctFromReflexive }

/-- Wambaya: reciprocal clitic *-ngg-* (RR morpheme in the auxiliary),
    identical to reflexive. [nordlinger-2023] ex. 11 (citing
    [nordlinger-1998], p. 142). Coded bivalent because nominal subjects
    retain ergative marking under reciprocalization
    ([evans-et-al-2007]: transitivity is compromised but argument
    structure undisturbed); the NOM subject in ex. 11 is a free
    pronoun, which declines nominative/accusative regardless of
    transitivity ([nordlinger-1998]). -/
def rpWambaya : RecipProfile :=
  { language := "Wambaya", iso := "wmb"
  , primaryStrategy := .recipClitic
  , valency := .bivalent
  , reflexiveRelation := .identicalToReflexive }

/-- Icelandic: bipartite NP *hvort annað*, each part independently
    inflected for case (*annað* takes the argument-position case,
    *hvort* agrees with the antecedent). Bivalent — the accusative on
    *annað* shows the clause remains transitive.
    [nordlinger-2023] ex. 17 (citing [hurst-nordlinger-2021]). -/
def rpIcelandic : RecipProfile :=
  { language := "Icelandic", iso := "isl"
  , primaryStrategy := .bipartiteNP
  , valency := .bivalent
  , reflexiveRelation := .distinctFromReflexive }

/-- Chicheŵa: verbal affix *-an-* (monovalent).
    [nordlinger-2023] ex. 20 (citing [dalrymple-et-al-1994]). -/
def rpChichewa : RecipProfile :=
  { language := "Chicheŵa", iso := "nya"
  , primaryStrategy := .verbalAffix
  , valency := .monovalent
  , reflexiveRelation := .distinctFromReflexive }

/-- Czech: reciprocal clitic *se* (monovalent, reflexive-identical;
    [nordlinger-2023] ex. 29, citing [siloni-2008]), alongside the
    periphrastic *jeden druhého* 'each other' attested in
    [siloni-2012]'s Czech examples — so under WALS Ch 106 criteria the
    reflexive relation is `mixed` (WALS itself has no Czech row).
    Syntax-formed; discontinuous reciprocals are unavailable
    ([nordlinger-2023] p. 86, with French). -/
def rpCzech : RecipProfile :=
  { language := "Czech", iso := "ces"
  , primaryStrategy := .recipClitic
  , valency := .monovalent
  , formation := some .syntactic
  , discontinuousAttested := some false
  , reflexiveRelation := .mixed }

def allRecipProfiles : List RecipProfile :=
  [ rpEnglish, rpRussian, rpSwahili, rpHungarian, rpFrench
  , rpGreek, rpGerman, rpMandarin, rpWambaya, rpIcelandic
  , rpChichewa, rpCzech ]

/-! ### Strategy-valency correlation (§3.2) -/

/-- [nordlinger-2023] §3.2: NP/argument strategies tend to preserve
    valency (bivalent), while verb-marking strategies tend to reduce it.
    [nedjalkov-2007a] (p. 21) links this to the morphosyntactic type:
    morphological markers "reduce the valency of the underlying verb by
    deleting the direct or indirect object."

    In this sample: all nominal-strategy profiles are bivalent. The
    correlation is a tendency — outside the sample, Tonga combines
    verbal marking with two argument NPs ([maslova-2008]) and Malagasy
    verb-marked reciprocals stay bivalent at f-structure ([hurst-2012]). -/
theorem nominal_strategy_bivalent :
    (allRecipProfiles.filter fun p => p.primaryStrategy.isNominal).all
      fun p => p.valency == .bivalent := by decide

/-- Verbal affixes (Swahili *-an-*, Hungarian *-óz-*, Greek nonactive,
    Chicheŵa *-an-*) are uniformly monovalent in this sample. -/
theorem verbal_affix_monovalent :
    (allRecipProfiles.filter fun p => p.primaryStrategy == .verbalAffix).all
      fun p => p.valency == .monovalent := by decide

/-- Converse of `nominal_strategy_bivalent`: monovalent reciprocal
    strategies are never nominal (NP/argument) in this sample
    ([nedjalkov-2007a], p. 21; [nordlinger-2023] §3.2). -/
theorem monovalent_implies_verbal :
    (allRecipProfiles.filter fun p => p.valency == .monovalent).all
      fun p => !p.primaryStrategy.isNominal := by decide

/-! ### Siloni's discontinuity prediction (§3.3) -/

/-- [siloni-2008]/[siloni-2012] predict: discontinuous reciprocals
    (subject + comitative *with*-phrase) are possible only when the
    reciprocal verb is lexically formed.

    Checked against independently recorded judgments: every profile
    carrying both a formation locus and an attested discontinuity
    judgment ([nordlinger-2023] ex. 36–40) satisfies the prediction —
    Greek, Swahili, Hungarian (lexical, attested) vs French, Czech
    (syntactic, ungrammatical). -/
theorem siloni_discontinuity_prediction :
    allRecipProfiles.all fun p =>
      match p.formation, p.discontinuousAttested with
      | some f, some d => f.allowsDiscontinuous == d
      | _, _ => true := by decide

/-! ### WALS grounding -/

/-- Reciprocal profiles agree with WALS Ch 106 data where available.
    Lookups use ISO 639-3 codes via `Datapoint.lookupISO`, so the join
    between profile and WALS row is structural (no string-coincidence). -/
theorem rpEnglish_wals :
    (Data.WALS.F106A.lookupISO rpEnglish.iso).map (ofWALS106A ·.value) =
      some rpEnglish.reflexiveRelation := by decide
theorem rpRussian_wals :
    (Data.WALS.F106A.lookupISO rpRussian.iso).map (ofWALS106A ·.value) =
      some rpRussian.reflexiveRelation := by decide
theorem rpSwahili_wals :
    (Data.WALS.F106A.lookupISO rpSwahili.iso).map (ofWALS106A ·.value) =
      some rpSwahili.reflexiveRelation := by decide
theorem rpFrench_wals :
    (Data.WALS.F106A.lookupISO rpFrench.iso).map (ofWALS106A ·.value) =
      some rpFrench.reflexiveRelation := by decide
theorem rpGreek_wals :
    (Data.WALS.F106A.lookupISO rpGreek.iso).map (ofWALS106A ·.value) =
      some rpGreek.reflexiveRelation := by decide
theorem rpGerman_wals :
    (Data.WALS.F106A.lookupISO rpGerman.iso).map (ofWALS106A ·.value) =
      some rpGerman.reflexiveRelation := by decide
theorem rpMandarin_wals :
    (Data.WALS.F106A.lookupISO rpMandarin.iso).map (ofWALS106A ·.value) =
      some rpMandarin.reflexiveRelation := by decide
theorem rpWambaya_wals :
    (Data.WALS.F106A.lookupISO rpWambaya.iso).map (ofWALS106A ·.value) =
      some rpWambaya.reflexiveRelation := by decide

/-! ### Semantic reciprocity types (§4) -/

/-- Semantic type of reciprocal relation.

    [nordlinger-2023] §4 presents the semantic typology of
    [evans-et-al-2011b], who take as their starting point the symmetric
    relations identified by [dalrymple-et-al-1998] and distinguish six
    types of mutual relation ([nordlinger-2023] ex. 44,
    [evans-et-al-2011b] p. 8):

    - `strong`: every participant reciprocates with every other
      ("The members of this family love one another.")
    - `pairwise`: participants are paired off
      ("The people at the dinner party were married to one another.")
    - `chain`: sequential, each with the next
      ("The graduating students followed one another up onto the stage.")
    - `radial`: one central participant reciprocates with all others
      ("The teacher and her pupils intimidated one another.")
    - `melee`: widespread but not exhaustive reciprocation
      ("The drunks in the pub were punching one another.")
    - `ring`: circular chain, last links back to first
      ("The children chased each other round in a ring.") -/
inductive ReciprocityType where
  | strong
  | pairwise
  | chain
  | radial
  | melee
  | ring
  deriving DecidableEq, Repr

/-- Whether a reciprocity type requires every participant to be involved
    in at least one reciprocal pair. Radial IS participant-exhaustive —
    the center reciprocates with each peripheral — but is not
    pair-exhaustive (peripherals do not reciprocate with each other).
    Melee is the only type where some participants may be uninvolved. -/
def ReciprocityType.exhaustive : ReciprocityType → Bool
  | .strong   => true
  | .pairwise => true
  | .chain    => true
  | .radial   => true
  | .melee    => false
  | .ring     => true

/-- Whether a reciprocity type is symmetric: within each active pair,
    if A acts on B then B acts on A. Only strong and pairwise are:
    chain and ring are directional (A follows B does not entail B
    follows A), and [majid-et-al-2011] define radial as one participant
    acting *asymmetrically* with multiple others and melee as multiple
    *asymmetrical* interactions without full saturation. -/
def ReciprocityType.symmetric : ReciprocityType → Bool
  | .strong   => true
  | .pairwise => true
  | .chain    => false
  | .radial   => false
  | .melee    => false
  | .ring     => false

/-- The six reciprocity types English *each other* can express
    ([evans-et-al-2011b], p. 8; [nordlinger-2023] ex. 44). -/
def englishReciprocityTypes : List ReciprocityType :=
  [.strong, .pairwise, .chain, .radial, .melee, .ring]

/-- English *each other* expresses every reciprocity type — an empirical
    observation about English, not a structural property; some languages
    restrict which types their reciprocal construction can express. -/
theorem english_expresses_all_types :
    ∀ t : ReciprocityType, t ∈ englishReciprocityTypes := by
  intro t; cases t <;> decide

/-! ### Swahili fragment cross-reference (§3) -/

/-- The Swahili reciprocal suffix *-an-* ([nordlinger-2023] ex. 40,
    citing [dimitriadis-2004]) is formalized as a `MorphRule` in
    `Swahili.Reciprocals.reciprocalAffix`. The rule realizes
    valence reduction (transitive → intransitive), matching `rpSwahili`'s
    `verbalAffix` strategy + `monovalent` valency. -/
theorem rpSwahili_grounded_in_fragment :
    rpSwahili.primaryStrategy = .verbalAffix ∧
    rpSwahili.valency = .monovalent ∧
    Swahili.Reciprocals.reciprocalAffix.category = .valence :=
  ⟨rfl, rfl, rfl⟩

/-! ### Reciprocal marker polysemy (§4.2) -/

/-- Extended readings of reciprocal markers beyond core reciprocal
    meaning. [nordlinger-2023] §4.2: reciprocal markers are commonly
    polysemous with reflexive (34% of the WALS sample,
    [maslova-nedjalkov-2013]), collective/sociative, and iterative
    meanings. -/
inductive RecipMarkerPolysemy where
  /-- Core mutual action reading. -/
  | reciprocal
  /-- Same-participant reading (overlap with reflexives). -/
  | reflexive
  /-- Joint action without mutual entailment. -/
  | collective
  /-- Joint/associative action ('together'). -/
  | sociative
  /-- Repeated action ('again and again'). -/
  | iterative
  deriving DecidableEq, Repr

/-- Polysemy pattern: which readings a language's reciprocal
    marker(s) can express. -/
structure RecipPolysemyPattern where
  language : String
  readings : List RecipMarkerPolysemy
  deriving Repr

/-- French *se*: reciprocal + reflexive — "Pierre et Jean se sont
    habillés" is ambiguous between 'dressed themselves' and 'dressed
    each other' ([nordlinger-2023] ex. 47, citing [siloni-2012]). -/
def polysemyFrench : RecipPolysemyPattern :=
  { language := "French", readings := [.reciprocal, .reflexive] }

/-- Yakut *-üs*: reciprocal + collective/sociative — *ölör-üs* 'kill
    each other' or 'kill somebody together' ([nordlinger-2023] ex. 49,
    citing Nedjalkov 2007b). -/
def polysemyYakut : RecipPolysemyPattern :=
  { language := "Yakut", readings := [.reciprocal, .collective, .sociative] }

/-- East Futunan *fe-...-'aki*: reciprocal + iterative — *fe-tapa-'aki*
    'sparkle again and again' ([nordlinger-2023] ex. 50, citing
    Nedjalkov 2007b). -/
def polysemyEastFutunan : RecipPolysemyPattern :=
  { language := "East Futunan", readings := [.reciprocal, .iterative] }

/-- Wambaya *-ngg-* (RR): reciprocal + reflexive (identical forms,
    [nordlinger-1998]). -/
def polysemyWambaya : RecipPolysemyPattern :=
  { language := "Wambaya", readings := [.reciprocal, .reflexive] }

/-! ### Fragment connection: English reciprocal-reflexive distinction -/

open English.Pronouns in

/-- The English `RecipProfile` is grounded in the Fragment: English has
    reciprocal pronouns that are categorically different from reflexive
    pronouns, and the profile records *each other* as a bipartite NP
    strategy. The WALS substrate anchor for the reflexive-reciprocal
    distinction is `rpEnglish_wals`. -/
theorem english_profile_grounded :
    rpEnglish.primaryStrategy = .bipartiteNP ∧
    rpEnglish.valency = .bivalent ∧
    Binding.bindingClassOf eachOther.toWord = some .reciprocal ∧
    Binding.bindingClassOf eachOther.toWord ≠ some .reflexive := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide

/-! ### Cross-paper verification: Nordlinger 2023 vs Siloni 2012 -/

section SiloniAgreement
open Siloni2012

/-- [nordlinger-2023]'s `RecipProfile` formation classifications agree
    with [siloni-2012]'s `LangRecipVerb.formation` for languages
    discussed in both. The newer paper checks consistency with the older
    (chronological dependency). -/
theorem hungarian_agrees_with_siloni :
    rpHungarian.formation = some hungarian.formation := rfl

theorem french_agrees_with_siloni :
    rpFrench.formation = some french.formation := rfl

theorem czech_agrees_with_siloni :
    rpCzech.formation = some czech.formation := rfl

end SiloniAgreement

end Nordlinger2023
