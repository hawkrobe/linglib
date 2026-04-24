import Linglib.Phenomena.ArgumentStructure.Typology
import Linglib.Phenomena.ArgumentStructure.Studies.Siloni2012
import Linglib.Datasets.WALS.Features.F106A
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.Swahili.Reciprocals

/-!
# Nordlinger (2023) @cite{nordlinger-2023}

Reciprocal constructions: a typological-formal review.

This file formalizes the apparatus from Nordlinger's 2023 review article
on reciprocal constructions. The review summarizes earlier classificatory
work (König & Kokutani 2006, Maslova 2008, Evans 2008, Nedjalkov 2007a,
Siloni 2008/2012, Dalrymple et al. 1998, Evans et al. 2011) and adds
empirical predictions about strategy/valency correlations and Siloni's
discontinuity asymmetry.

The underlying primitives (`RecipStrategy`, `RecipValency`, `RecipFormation`,
`ReciprocalType`) live in `Phenomena.ArgumentStructure.Typology` because
they are anchored on the earlier sources Nordlinger reviews — keeping them
in the typology layer preserves chronological dependency for older study
files (notably `Studies/Siloni2012.lean`, which would otherwise need to
import a 2023 paper).

## Contents

- `RecipProfile` per-language extended reciprocal profiles (12 languages)
- Strategy-valency correlation theorems (§3.2)
- Siloni's discontinuity prediction (§3.3)
- WALS Ch 106 grounding for `RecipProfile` (via `lookupISO`)
- `ValenceProfile`/`RecipProfile` cross-validation
- `ReciprocityType` Dalrymple-et-al/Evans-et-al semantic 6-way classification (§4)
- `RecipMarkerPolysemy` extended readings (§4.2)
- Fragment grounding for English reciprocals
-/

namespace Phenomena.ArgumentStructure.Studies.Nordlinger2023

open Phenomena.ArgumentStructure.Typology

-- ============================================================================
-- Reciprocal Profiles (@cite{nordlinger-2023})
-- ============================================================================

/-- Extended reciprocal profile for a single language.

    Captures the morphosyntactic strategy, valency effect, and
    discontinuity licensing from @cite{nordlinger-2023}'s review,
    going beyond the WALS 4-way reflexive-reciprocal classification. -/
structure RecipProfile where
  language : String
  iso : String
  /-- Primary reciprocal strategy (Evans 2008 typology) -/
  primaryStrategy : RecipStrategy
  /-- Secondary strategy, if the language uses more than one -/
  secondaryStrategy : Option RecipStrategy := none
  /-- Valency effect of the primary strategy -/
  valency : RecipValency
  /-- Formation locus of verb-marked reciprocals (Siloni 2012) -/
  formation : Option RecipFormation := none
  /-- Reciprocal-reflexive relationship (WALS Ch 106) -/
  reflexiveRelation : ReciprocalType
  deriving Repr, DecidableEq

-- Language data: 12 reciprocal profiles from @cite{nordlinger-2023}

/-- English: bipartite NP "each other" (bivalent, distinct from reflexive).
    Also has lexical reciprocals ("quarrel", "meet") as secondary strategy.
    @cite{nordlinger-2023} ex. 1b, 7, 24; ex. 44 (all 6 reciprocity types). -/
def rp_english : RecipProfile :=
  { language := "English", iso := "eng"
  , primaryStrategy := .bipartiteNP
  , secondaryStrategy := some .lexical
  , valency := .bivalent
  , reflexiveRelation := .distinctFromReflexive }

/-- Russian: reciprocal pronoun "drug druga" (bivalent, distinct) plus
    reflexive-identical verbal postfix "-sja"/"-s'" (monovalent, identical).
    Unlike French "se" (a separable clitic), Russian "-sja" is a bound
    suffix — classified as `.verbalAffix` per Evans (2008).
    @cite{nordlinger-2023} ex. 9, 31. -/
def rp_russian : RecipProfile :=
  { language := "Russian", iso := "rus"
  , primaryStrategy := .recipPronoun
  , secondaryStrategy := some .verbalAffix
  , valency := .bivalent
  , reflexiveRelation := .mixed }

/-- Swahili: verbal affix "-ana" (monovalent, distinct from reflexive "-ji-").
    Can form discontinuous reciprocals with comitative "na"
    (Hurst 2012; @cite{nordlinger-2023} ex. 12, 37, 40).
    Lexically formed per Siloni's analysis. The morphological rule is
    formalized in `Fragments.Swahili.Reciprocals.reciprocalAffix`. -/
def rp_swahili : RecipProfile :=
  { language := "Swahili", iso := "swh"
  , primaryStrategy := .verbalAffix
  , valency := .monovalent
  , formation := some .lexical
  , reflexiveRelation := .distinctFromReflexive }

/-- Hungarian: verbal affix "-oz-" (monovalent, distinct).
    Can form discontinuous reciprocals with comitative "-val"/"-vel"
    (Dimitriadis 2008; @cite{nordlinger-2023} ex. 19, 30, 38).
    Lexically formed per Siloni's analysis. -/
def rp_hungarian : RecipProfile :=
  { language := "Hungarian", iso := "hun"
  , primaryStrategy := .verbalAffix
  , valency := .monovalent
  , formation := some .lexical
  , reflexiveRelation := .distinctFromReflexive }

/-- French: reflexive clitic "se" (monovalent, identical to reflexive) plus
    distinct "l'un l'autre" (bivalent, bipartite NP).
    "se" reciprocals are syntactically formed per Siloni (2008) and
    CANNOT form discontinuous reciprocals (@cite{nordlinger-2023} ex. 39).
    @cite{nordlinger-2023} ex. 28, 35, 39, 47.
    "se" is a clitic, not an affix — @cite{nordlinger-2023} p. 83:
    "the clitics *se* in French and Czech." -/
def rp_french : RecipProfile :=
  { language := "French", iso := "fra"
  , primaryStrategy := .recipClitic
  , secondaryStrategy := some .bipartiteNP
  , valency := .monovalent
  , formation := some .syntactic
  , reflexiveRelation := .mixed }

/-- Greek (Modern): nonactive voice morphology (monovalent, identical to
    reflexive in form) plus distinct constructions.
    CAN form discontinuous reciprocals with "me" (= 'with'):
    "O Giannis filithike me ti Maria" (@cite{nordlinger-2023} ex. 27b, 36).
    Lexically formed per Siloni's analysis. -/
def rp_greek : RecipProfile :=
  { language := "Modern Greek", iso := "ell"
  , primaryStrategy := .verbalAffix
  , valency := .monovalent
  , formation := some .lexical
  , reflexiveRelation := .mixed }

/-- German: reflexive pronoun "sich" (bivalent — fills object position,
    identical to reflexive) plus distinct reciprocal pronoun "einander"
    (bivalent, single-word pronoun). Both strategies preserve transitivity
    because the reciprocal form occupies the object slot.
    @cite{nordlinger-2023} via WALS Ch 106. -/
def rp_german : RecipProfile :=
  { language := "German", iso := "deu"
  , primaryStrategy := .recipPronoun
  , secondaryStrategy := some .recipPronoun
  , valency := .bivalent
  , reflexiveRelation := .mixed }

/-- Mandarin: compound verb strategy "dǎ-lái-dǎ-qù"
    (beat-come-beat-go = 'beat each other'). Distinct from reflexive.
    @cite{nordlinger-2023} ex. 13 (citing König & Kokutani 2006). -/
def rp_mandarin : RecipProfile :=
  { language := "Mandarin", iso := "cmn"
  , primaryStrategy := .compoundVerb
  , valency := .monovalent
  , reflexiveRelation := .distinctFromReflexive }

/-- Wambaya: reciprocal clitic "-ngg-" (RR morpheme in auxiliary).
    Identical to reflexive.
    @cite{nordlinger-2023} ex. 11 (citing Nordlinger 1998, p. 142). -/
def rp_wambaya : RecipProfile :=
  { language := "Wambaya", iso := "wmb"
  , primaryStrategy := .recipClitic
  , valency := .bivalent
  , reflexiveRelation := .identicalToReflexive }

/-- Icelandic: bipartite NP "hvor...annad" with independent case inflection
    on each part. Bivalent — retains full transitivity.
    @cite{nordlinger-2023} ex. 17 (citing Hurst & Nordlinger 2021). -/
def rp_icelandic : RecipProfile :=
  { language := "Icelandic", iso := "isl"
  , primaryStrategy := .bipartiteNP
  , valency := .bivalent
  , reflexiveRelation := .distinctFromReflexive }

/-- Chicheŵa: verbal affix "-an-" (monovalent).
    @cite{nordlinger-2023} ex. 20 (citing Dalrymple et al. 1994). -/
def rp_chichewa : RecipProfile :=
  { language := "Chicheŵa", iso := "nya"
  , primaryStrategy := .verbalAffix
  , valency := .monovalent
  , reflexiveRelation := .distinctFromReflexive }

/-- Czech: reflexive clitic "se" (monovalent, identical to reflexive).
    Syntactically formed per Siloni — cannot form discontinuous reciprocals.
    @cite{nordlinger-2023} ex. 29; Siloni (2008).
    "se" is a clitic — @cite{nordlinger-2023} p. 83. -/
def rp_czech : RecipProfile :=
  { language := "Czech", iso := "ces"
  , primaryStrategy := .recipClitic
  , valency := .monovalent
  , formation := some .syntactic
  , reflexiveRelation := .identicalToReflexive }

def allRecipProfiles : List RecipProfile :=
  [ rp_english, rp_russian, rp_swahili, rp_hungarian, rp_french
  , rp_greek, rp_german, rp_mandarin, rp_wambaya, rp_icelandic
  , rp_chichewa, rp_czech ]

-- ============================================================================
-- Reciprocal Strategy-Valency Correlation (@cite{nordlinger-2023}, §3.2)
-- ============================================================================

/-- @cite{nordlinger-2023} (§3.2): NP/argument strategies tend to
    preserve valency (bivalent), while verb-marking strategies tend to
    reduce valency (monovalent). Nedjalkov (2007a) links this to the
    morphosyntactic type: morphological markers "reduce the valency of
    the underlying verb by deleting the direct or indirect object."

    In our sample: all nominal-strategy profiles are bivalent. -/
theorem nominal_strategy_bivalent :
    (allRecipProfiles.filter fun p => p.primaryStrategy.isNominal).all
      fun p => p.valency == .bivalent := by native_decide

/-- Verbal affixes (Swahili "-ana", Hungarian "-oz-", Greek nonactive,
    Chicheŵa "-an-") are uniformly monovalent in our sample. -/
theorem verbal_affix_monovalent :
    (allRecipProfiles.filter fun p => p.primaryStrategy == .verbalAffix).all
      fun p => p.valency == .monovalent := by native_decide

/-- Converse of `nominal_strategy_bivalent`: monovalent reciprocal
    strategies are never nominal (NP/argument). This captures Nedjalkov
    (2007a, p. 21): morphological reciprocal markers "reduce the valency
    of the underlying verb." @cite{nordlinger-2023} §3.2. -/
theorem monovalent_implies_verbal :
    (allRecipProfiles.filter fun p => p.valency == .monovalent).all
      fun p => !p.primaryStrategy.isNominal := by native_decide

/-- Clitics (French/Czech "se") are also monovalent — the clitic
    absorbs the object argument. Wambaya "-ngg-" is the exception:
    bivalent despite being a clitic (ergative case preserves transitivity).
    @cite{nordlinger-2023} §3.2; Evans et al. (2007). -/
theorem clitic_mostly_monovalent :
    let clitics := allRecipProfiles.filter fun p => p.primaryStrategy == .recipClitic
    -- 2 of 3 clitics are monovalent (French, Czech); Wambaya is bivalent
    (clitics.filter fun p => p.valency == .monovalent).length = 2 ∧
    (clitics.filter fun p => p.valency == .bivalent).length = 1 := by native_decide

-- ============================================================================
-- Siloni's Discontinuity Prediction (@cite{nordlinger-2023}, §3.3)
-- ============================================================================

/-- Siloni (2008, 2012) predicts: discontinuous reciprocals (subject +
    comitative "with"-phrase) are possible only when the reciprocal verb
    is lexically formed, not syntactically formed.

    Lexically formed: Greek, Swahili, Hungarian — CAN be discontinuous.
    Syntactically formed: French, Czech — CANNOT be discontinuous.

    This is verified in our sample: every profile with a formation locus
    matches Siloni's prediction. -/
theorem siloni_discontinuity_prediction :
    (allRecipProfiles.filter fun p => p.formation.isSome).all fun p =>
      match p.formation with
      | some f => f.allowsDiscontinuous ==
          -- Lexically formed: Greek, Swahili, Hungarian = CAN
          -- Syntactically formed: French, Czech = CANNOT
          (p.iso == "ell" || p.iso == "swh" || p.iso == "hun")
      | none => true := by native_decide

/-- Profile count verification. -/
theorem recip_profile_count : allRecipProfiles.length = 12 := by native_decide

-- ============================================================================
-- WALS Grounding for Reciprocal Profiles
-- ============================================================================

/-- Reciprocal profiles agree with WALS Ch 106 data where available.
    Lookups use ISO 639-3 codes via `Datapoint.lookupISO`, so the join
    between profile and WALS row is structural (no string-coincidence). -/
theorem rp_english_wals :
    (Datasets.WALS.F106A.lookupISO rp_english.iso).map (fromWALS106A ·.value) =
      some rp_english.reflexiveRelation := by native_decide
theorem rp_russian_wals :
    (Datasets.WALS.F106A.lookupISO rp_russian.iso).map (fromWALS106A ·.value) =
      some rp_russian.reflexiveRelation := by native_decide
theorem rp_swahili_wals :
    (Datasets.WALS.F106A.lookupISO rp_swahili.iso).map (fromWALS106A ·.value) =
      some rp_swahili.reflexiveRelation := by native_decide
theorem rp_greek_wals :
    (Datasets.WALS.F106A.lookupISO rp_greek.iso).map (fromWALS106A ·.value) =
      some rp_greek.reflexiveRelation := by native_decide
theorem rp_german_wals :
    (Datasets.WALS.F106A.lookupISO rp_german.iso).map (fromWALS106A ·.value) =
      some rp_german.reflexiveRelation := by native_decide
theorem rp_mandarin_wals :
    (Datasets.WALS.F106A.lookupISO rp_mandarin.iso).map (fromWALS106A ·.value) =
      some rp_mandarin.reflexiveRelation := by native_decide
theorem rp_wambaya_wals :
    (Datasets.WALS.F106A.lookupISO rp_wambaya.iso).map (fromWALS106A ·.value) =
      some rp_wambaya.reflexiveRelation := by native_decide

-- ============================================================================
-- ValenceProfile-RecipProfile Cross-Validation
-- ============================================================================

/-- For languages with both a `ValenceProfile` (Typology) and a `RecipProfile`
    (this file), the reflexive-reciprocal classification must agree. -/
theorem english_profiles_agree :
    english.reciprocal = rp_english.reflexiveRelation := rfl
theorem russian_profiles_agree :
    russian.reciprocal = rp_russian.reflexiveRelation := rfl
theorem swahili_profiles_agree :
    swahili.reciprocal = rp_swahili.reflexiveRelation := rfl
theorem french_profiles_agree :
    french.reciprocal = rp_french.reflexiveRelation := rfl
theorem german_profiles_agree :
    german.reciprocal = rp_german.reflexiveRelation := rfl
theorem modernGreek_profiles_agree :
    modernGreek.reciprocal = rp_greek.reflexiveRelation := rfl

-- ============================================================================
-- Semantic Reciprocity Types (@cite{nordlinger-2023}, §4)
-- ============================================================================

/-- Semantic type of reciprocal relation.

    @cite{nordlinger-2023} (§4) summarizes the semantic typology from
    Dalrymple et al. (1998) and Evans et al. (2011), distinguishing six
    types of mutual relation that reciprocal constructions can encode:

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
    if A acts on B then B acts on A. Chain and ring are directional
    (A follows B does not entail B follows A). Radial IS symmetric —
    the teacher intimidates each pupil AND each pupil intimidates the
    teacher — it just doesn't cover all pairs. -/
def ReciprocityType.symmetric : ReciprocityType → Bool
  | .strong   => true
  | .pairwise => true
  | .chain    => false
  | .radial   => true
  | .melee    => true
  | .ring     => false

-- ============================================================================
-- Reciprocity Type Properties (@cite{nordlinger-2023}, §4)
-- ============================================================================

/-- Strong, pairwise, and radial are the three symmetric AND
    participant-exhaustive reciprocity types. Among these, only
    strong is also pair-exhaustive (every possible pair reciprocates). -/
theorem exhaustive_symmetric_types :
    ReciprocityType.strong.exhaustive = true ∧
    ReciprocityType.strong.symmetric = true ∧
    ReciprocityType.pairwise.exhaustive = true ∧
    ReciprocityType.pairwise.symmetric = true ∧
    ReciprocityType.radial.exhaustive = true ∧
    ReciprocityType.radial.symmetric = true := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Chain and ring are non-symmetric (directional) — they model
    sequential actions where A acts on B but B does not act on A.
    The difference: ring links the last element back to the first,
    chain does not. -/
theorem directional_types :
    ReciprocityType.chain.symmetric = false ∧
    ReciprocityType.ring.symmetric = false ∧
    ReciprocityType.chain.exhaustive = true ∧
    ReciprocityType.ring.exhaustive = true := ⟨rfl, rfl, rfl, rfl⟩

/-- Melee is the only non-exhaustive type — some group members
    may not participate at all. -/
theorem melee_unique_nonexhaustive :
    ReciprocityType.melee.exhaustive = false ∧
    ReciprocityType.melee.symmetric = true := ⟨rfl, rfl⟩

/-- English "each other" can express all six reciprocity types
    (Evans et al. 2011b, p. 8; @cite{nordlinger-2023} ex. 44).
    This is an empirical observation about English, not a structural
    property — some languages restrict which types their reciprocal
    construction can express. -/
def englishReciprocityTypes : List ReciprocityType :=
  [.strong, .pairwise, .chain, .radial, .melee, .ring]

theorem english_expresses_all_types :
    englishReciprocityTypes.length = 6 := rfl

-- ============================================================================
-- Swahili Reciprocal Cross-Reference (@cite{nordlinger-2023}, §3)
-- ============================================================================

/-- The Swahili reciprocal suffix "-an-" (@cite{nordlinger-2023} ex. 40,
    citing Dimitriadis 2004) is formalized as a `MorphRule` in
    `Fragments.Swahili.Reciprocals.reciprocalAffix`. The rule realizes
    valence reduction (transitive → intransitive), matching `rp_swahili`'s
    `verbalAffix` strategy + `monovalent` valency. -/
theorem rp_swahili_grounded_in_fragment :
    rp_swahili.primaryStrategy = .verbalAffix ∧
    rp_swahili.valency = .monovalent ∧
    Fragments.Swahili.Reciprocals.reciprocalAffix.category = .valence :=
  ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- Reciprocal Marker Polysemy (@cite{nordlinger-2023}, §4.2)
-- ============================================================================

/-- Extended readings of reciprocal markers beyond core reciprocal meaning.

    @cite{nordlinger-2023} (§4.2) notes that reciprocal markers are often
    polysemous, expressing related but non-reciprocal meanings. These
    extended uses include collective, sociative, and iterative readings,
    in addition to the reflexive overlap captured by WALS Ch 106. -/
inductive RecipMarkerPolysemy where
  | reciprocal   -- core mutual action reading
  | reflexive    -- same-participant reading (overlap with reflexives)
  | collective   -- joint action, no mutual entailment ("they gathered")
  | sociative    -- joint/associative action ("they walked together")
  | iterative    -- repeated action ("they kept hitting")
  deriving DecidableEq, Repr

/-- Polysemy pattern: which extended readings a language's reciprocal
    marker(s) can express. -/
structure RecipPolysemyPattern where
  language : String
  readings : List RecipMarkerPolysemy
  deriving Repr

/-- Russian "drug druga": reciprocal only (no collective/sociative). -/
def polysemy_russian : RecipPolysemyPattern :=
  { language := "Russian", readings := [.reciprocal] }

/-- French "se": reciprocal + reflexive + collective.
    "Les enfants se sont rassemblés" (collective, no mutual action). -/
def polysemy_french : RecipPolysemyPattern :=
  { language := "French", readings := [.reciprocal, .reflexive, .collective] }

/-- Wambaya "-ngg-" (RR): reciprocal + reflexive (identical forms). -/
def polysemy_wambaya : RecipPolysemyPattern :=
  { language := "Wambaya", readings := [.reciprocal, .reflexive] }

/-- Languages with reciprocal-reflexive identity show reflexive polysemy. -/
theorem reflexive_polysemy_tracks_wals :
    polysemy_wambaya.readings.any (· == .reflexive) = true ∧
    rp_wambaya.reflexiveRelation = .identicalToReflexive := ⟨rfl, rfl⟩

-- ============================================================================
-- Fragment Connection: English Reciprocal-Reflexive Distinction
-- ============================================================================

open Fragments.English.Pronouns in

/-- The English profiles (both `Typology.english : ValenceProfile` and
    `rp_english : RecipProfile`) are grounded in the Fragment: English has
    reciprocal pronouns that are categorically different from reflexive
    pronouns, and the profile records "each other" as a bipartite NP
    strategy. -/
theorem english_profile_grounded :
    english.reciprocal = .distinctFromReflexive ∧
    rp_english.primaryStrategy = .bipartiteNP ∧
    rp_english.valency = .bivalent ∧
    eachOther.pronounType = .reciprocal ∧
    eachOther.pronounType ≠ PronounType.reflexive := by
  exact ⟨rfl, rfl, rfl, rfl, by decide⟩

-- ============================================================================
-- Cross-Paper Verification: Nordlinger 2023 vs Siloni 2012
-- ============================================================================

section SiloniAgreement
open Siloni2012

/-- @cite{nordlinger-2023}'s `RecipProfile` formation classifications agree
    with @cite{siloni-2012}'s `LangRecipVerb.formation` for languages
    discussed in both. The newer paper checks consistency with the older
    (chronological dependency). -/
theorem hungarian_agrees_with_siloni :
    rp_hungarian.formation = some hungarian.formation := by native_decide

theorem french_agrees_with_siloni :
    rp_french.formation = some french.formation := by native_decide

theorem czech_agrees_with_siloni :
    rp_czech.formation = some czech.formation := by native_decide

end SiloniAgreement

/-- Swahili is classified as lexical here (per Nordlinger 2023's review).
    Siloni (2012) does not discuss Swahili directly, but the prediction
    is consistent: Swahili has verb-marked reciprocals (-ana) that
    license discontinuous constructions — a lexical property. -/
theorem swahili_consistent_with_siloni :
    rp_swahili.formation = some RecipFormation.lexical := by native_decide

/-- Greek is classified as lexical here. Consistent with Siloni:
    Greek allows discontinuous reciprocals with *me*. -/
theorem greek_consistent_with_siloni :
    rp_greek.formation = some RecipFormation.lexical := by native_decide

end Phenomena.ArgumentStructure.Studies.Nordlinger2023
