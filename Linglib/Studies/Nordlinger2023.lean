import Linglib.Syntax.Reciprocal
import Linglib.Studies.Siloni2012
import Linglib.Data.WALS.Features.F106A
import Linglib.Semantics.Plurality.Reciprocal
import Linglib.Fragments.English.Pronouns
import Linglib.Fragments.English.Reciprocals
import Linglib.Fragments.Chichewa.Reciprocals
import Linglib.Fragments.Romance.French.Reciprocals
import Linglib.Fragments.German.Reciprocals
import Linglib.Fragments.Greek.StandardModern.Reciprocals
import Linglib.Fragments.Hungarian.Reciprocals
import Linglib.Fragments.Icelandic.Reciprocals
import Linglib.Fragments.Mandarin.Reciprocals
import Linglib.Fragments.Slavic.Czech.Reciprocals
import Linglib.Fragments.Slavic.Russian.Reciprocals
import Linglib.Fragments.Swahili.Reciprocals
import Linglib.Fragments.Wambaya.Reciprocals
import Linglib.Syntax.Binding.Basic

/-!
# Nordlinger (2023) [nordlinger-2023]

Reciprocal constructions: a typological-formal review.

Formalizes the apparatus of [nordlinger-2023]'s review of reciprocal
constructions, which summarizes earlier classificatory work
([konig-kokutani-2006], [maslova-2008], [evans-2008], [nedjalkov-2007a],
[siloni-2008], [siloni-2012], [dalrymple-et-al-1998], [evans-et-al-2011b])
and organizes the empirical picture around strategy/valency correlations
(§3.2) and Siloni's discontinuity asymmetry (§3.3).

The underlying primitives (`Marker`, `Strategy`, `Valency`,
`Formation`, `ReflexiveRelation`) live in `Syntax/Reciprocal.lean`,
anchored on the earlier sources the review synthesizes — which preserves
chronological dependency for `Studies/Siloni2012.lean`. Each profile below
records a marker *inventory*; the primary strategy and the WALS Ch 106
reflexive-relation value are derived from it, and the WALS theorems check
the derived values against the external WALS rows.

## Contents

- `RecipProfile` per-language profiles (12 languages): marker inventory +
  observed valency, formation, and discontinuity judgments
- Strategy-valency correlation theorems (§3.2), including the derived
  default-valency check against `Strategy.defaultValency`
- Siloni's discontinuity prediction checked against attested judgments (§3.3)
- WALS Ch 106 grounding for the *derived* reflexive relation (via `lookupISO`)
- `ReciprocityType` semantic 6-way classification (§4), realized as the
  relation shapes of `Semantics.Plurality.Reciprocal`
- Polysemous markers beyond the profile sample (§4.2)
- Fragment grounding for English reciprocals
-/

namespace Nordlinger2023

open Reciprocal

/-- Convert a WALS 106A value to `ReflexiveRelation` (study-local: WALS
    grounding is this study's business, not the substrate's). -/
def ofWALS106A : Data.WALS.F106A.ReciprocalType → ReflexiveRelation
  | .noReciprocalConstruction => .noDedicated
  | .distinctFromReflexive    => .distinctFromReflexive
  | .mixed                    => .mixed
  | .identicalToReflexive     => .identicalToReflexive

/-! ### Reciprocal profiles -/

/-- Per-language reciprocal profile: the marker inventory (primary strategy
    first) plus the observed valency, formation locus, and discontinuity
    judgments from [nordlinger-2023]'s review. The primary strategy and the
    WALS Ch 106 reflexive relation are *derived* from the inventory. -/
structure RecipProfile where
  language : String
  iso : String
  /-- Marker inventory (primary strategy first), sourced from the
      language's `Fragments/{Lang}/Reciprocals.lean`. -/
  markers : List Marker
  /-- Observed valency of the primary construction -/
  valency : Valency
  /-- Formation locus of verb-marked reciprocals ([siloni-2012]) -/
  formation : Option Formation := none
  /-- Attested availability of the discontinuous reciprocal construction
      ([nordlinger-2023] §3.3 judgments), independent of `formation` so
      Siloni's prediction can be checked rather than stipulated -/
  discontinuousAttested : Option Bool := none
  deriving Repr, DecidableEq

/-- Primary strategy: the strategy of the inventory's first marker. -/
def RecipProfile.primaryStrategy (p : RecipProfile) : Option Strategy :=
  p.markers.head?.map (·.strategy)

/-- WALS Ch 106 reflexive relation, derived from the marker inventory. -/
def RecipProfile.reflexiveRelation (p : RecipProfile) : ReflexiveRelation :=
  ofInventory p.markers

-- Language data: 12 reciprocal profiles from [nordlinger-2023]

/-- English: bipartite NP *each other* (bivalent, distinct from reflexive;
    [nordlinger-2023] ex. 1b) plus lexical reciprocals (*quarrel*, *meet*,
    ex. 7). Per [siloni-2012] the lexical class is lexicon-formed, but
    *kiss*/*hug* resist the discontinuous construction (fn. 32), so no
    formation-level discontinuity value is recorded. Expresses all six
    reciprocity types (ex. 44). -/
def rpEnglish : RecipProfile :=
  { language := "English", iso := "eng"
  , markers := English.Reciprocals.markers
  , valency := .bivalent }

/-- Russian: bipartite NP *drug druga* 'other other-ACC'
    ([nordlinger-2023] ex. 9, grouped with English *each other* as the
    bipartite strategy) plus reflexive-identical verbal postfix *-sja*
    (monovalent; ex. 31). Unlike French *se* (a separable clitic),
    *-sja* is a bound suffix. Derived WALS value: mixed. -/
def rpRussian : RecipProfile :=
  { language := "Russian", iso := "rus"
  , markers := Russian.Reciprocals.markers
  , valency := .bivalent }

/-- Swahili: verbal affix *-an-* (monovalent, distinct from reflexive
    *-ji-*; [nordlinger-2023] ex. 12). Forms discontinuous reciprocals
    with comitative *na* (ex. 37 from [hurst-2012], ex. 40 from
    [dimitriadis-2004]), hence lexicon-formed under Siloni's typology as
    presented in §3.3 ([siloni-2012] itself does not discuss Swahili).
    The morphological rule is `Swahili.Reciprocals.reciprocalAffix`. -/
def rpSwahili : RecipProfile :=
  { language := "Swahili", iso := "swh"
  , markers := Swahili.Reciprocals.markers
  , valency := .monovalent
  , formation := some .lexical
  , discontinuousAttested := some true }

/-- Hungarian: verbal affix *-óz-* (monovalent; [nordlinger-2023]
    ex. 19, 30, citing [siloni-2008]). Lexicon-formed per [siloni-2012]'s
    own classification; forms discontinuous reciprocals with comitative
    *-val* (ex. 38, from [dimitriadis-2008]). -/
def rpHungarian : RecipProfile :=
  { language := "Hungarian", iso := "hun"
  , markers := Hungarian.Reciprocals.markers
  , valency := .monovalent
  , formation := some .lexical
  , discontinuousAttested := some true }

/-- French: reciprocal clitic *se* (monovalent, reflexive-identical;
    [nordlinger-2023] ex. 28, 47) plus distinct bipartite *l'un l'autre*.
    The review argues (after [siloni-2008], [siloni-2012]) that *se* is
    not a reciprocal object: embedded *se*-reciprocals lack the "I"
    reading (ex. 35). Syntax-formed, and discontinuous reciprocals are
    ungrammatical (ex. 39). -/
def rpFrench : RecipProfile :=
  { language := "French", iso := "fra"
  , markers := French.Reciprocals.markers
  , valency := .monovalent
  , formation := some .syntactic
  , discontinuousAttested := some false }

/-- Greek (Modern): nonactive voice morphology (monovalent, reflexive-
    identical in form) plus a distinct periphrastic reciprocal (*o enas
    ton allon* — its existence is implied by the WALS `mixed`
    classification, [maslova-nedjalkov-2013]). Forms discontinuous
    reciprocals with *me* 'with': "O Giannis filithike me ti Maria"
    ([nordlinger-2023] ex. 27b, 36, from [dimitriadis-2008]) — hence
    lexicon-formed under Siloni's typology as presented in §3.3
    ([siloni-2012] itself does not discuss Greek). -/
def rpGreek : RecipProfile :=
  { language := "Modern Greek", iso := "ell"
  , markers := Greek.StandardModern.Reciprocals.markers
  , valency := .monovalent
  , formation := some .lexical
  , discontinuousAttested := some true }

/-- German: dedicated reciprocal pronoun *einander* alongside reflexive
    *sich* in reciprocal use — the two markers' readings now encode the
    WALS "mixed" configuration. Both fill the object slot, preserving
    bivalent syntax. [siloni-2012] fn. 13 suggests German
    *sich*-reciprocals are syntactic reciprocal verbs; the review does
    not take this up, so no formation value is recorded. -/
def rpGerman : RecipProfile :=
  { language := "German", iso := "deu"
  , markers := German.Reciprocals.markers
  , valency := .bivalent }

/-- Mandarin: compound verb strategy *dǎ-lái-dǎ-qù*
    (beat-come-beat-go = 'beat each other'), single subject NP.
    Distinct from reflexive. [nordlinger-2023] ex. 13 (citing
    [konig-kokutani-2006]); [evans-2008] treats verb compounding as a
    multiclausal strategy. -/
def rpMandarin : RecipProfile :=
  { language := "Mandarin", iso := "cmn"
  , markers := Mandarin.Reciprocals.markers
  , valency := .monovalent }

/-- Wambaya: reciprocal clitic *-ngg-* (RR morpheme in the auxiliary),
    identical to reflexive. [nordlinger-2023] ex. 11 (citing
    [nordlinger-1998], p. 142). Bivalent: nominal subjects retain
    ergative marking under reciprocalization ([evans-et-al-2007]:
    transitivity is compromised but argument structure undisturbed);
    the NOM subject in ex. 11 is a free pronoun, which declines
    nominative/accusative regardless of transitivity
    ([nordlinger-1998]). -/
def rpWambaya : RecipProfile :=
  { language := "Wambaya", iso := "wmb"
  , markers := Wambaya.Reciprocals.markers
  , valency := .bivalent }

/-- Icelandic: bipartite NP *hvort annað*, each part independently
    inflected for case (*annað* takes the argument-position case,
    *hvort* agrees with the antecedent). Bivalent — the accusative on
    *annað* shows the clause remains transitive.
    [nordlinger-2023] ex. 17 (citing [hurst-nordlinger-2021]). -/
def rpIcelandic : RecipProfile :=
  { language := "Icelandic", iso := "isl"
  , markers := Icelandic.Reciprocals.markers
  , valency := .bivalent }

/-- Chicheŵa: verbal affix *-an-* (monovalent).
    [nordlinger-2023] ex. 20 (citing [dalrymple-et-al-1994]). -/
def rpChichewa : RecipProfile :=
  { language := "Chicheŵa", iso := "nya"
  , markers := Chichewa.Reciprocals.markers
  , valency := .monovalent }

/-- Czech: reciprocal clitic *se* (monovalent, reflexive-identical;
    [nordlinger-2023] ex. 29, citing [siloni-2008]), alongside the
    periphrastic *jeden druhého* 'each other' attested in
    [siloni-2012]'s Czech examples — the derived WALS value is
    therefore `mixed` (WALS itself has no Czech row). Syntax-formed;
    discontinuous reciprocals are unavailable ([nordlinger-2023] p. 86,
    with French). -/
def rpCzech : RecipProfile :=
  { language := "Czech", iso := "ces"
  , markers := Czech.Reciprocals.markers
  , valency := .monovalent
  , formation := some .syntactic
  , discontinuousAttested := some false }

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

    In this sample: all nominal-primary profiles are bivalent. The
    correlation is a tendency — outside the sample, Tonga combines
    verbal marking with two argument NPs ([maslova-2008]) and Malagasy
    verb-marked reciprocals stay bivalent at f-structure ([hurst-2012]). -/
theorem nominal_strategy_bivalent :
    (allRecipProfiles.filter fun p => p.primaryStrategy.any (·.isNominal)).all
      (fun p => p.valency == .bivalent) := by decide

/-- Verbal affixes (Swahili *-an-*, Hungarian *-óz-*, Greek nonactive,
    Chicheŵa *-an-*) are uniformly monovalent in this sample. -/
theorem verbal_affix_monovalent :
    (allRecipProfiles.filter
        fun p => p.primaryStrategy == some .verbalAffix).all
      (fun p => p.valency == .monovalent) := by decide

/-- Converse of `nominal_strategy_bivalent`: monovalent reciprocal
    strategies are never nominal (NP/argument) in this sample
    ([nedjalkov-2007a], p. 21; [nordlinger-2023] §3.2). -/
theorem monovalent_implies_verbal :
    (allRecipProfiles.filter fun p => p.valency == .monovalent).all
      (fun p => !p.primaryStrategy.any (·.isNominal)) := by decide

/-- Observed valency follows the strategy's default — derived in the
    substrate from `Alternation.reciprocalization`'s detransitivizing
    coding-frame effect — throughout the sample, except Wambaya, whose
    ergative-retaining RR clause stays bivalent ([evans-et-al-2007]). -/
theorem valency_follows_default_except_wambaya :
    allRecipProfiles.all fun p =>
      p.primaryStrategy.any (fun s => p.valency == s.defaultValency) ||
        p.iso == "wmb" := by decide

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

/-! ### WALS grounding

The reflexive-relation value is *derived* from each profile's marker
inventory (`ofInventory`), so these theorems check a computed value
against the external WALS row — inventory facts vs WALS coding, joined
structurally on ISO 639-3 via `Datapoint.lookupISO`. -/

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
    - `radial`: one central participant acts on all others
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

/-- The relation shape each configurational label denotes over a
    participant plurality — [majid-et-al-2011]'s extensional schemas as
    the exact-extension conditions of `Semantics.Plurality.Reciprocal`.
    Symmetry and participant-exhaustiveness are theorems there
    (`ChainConfig.not_pairSymmetricOn`,
    `RadialConfig.inclusiveAlternativeOrdering`, melee failing
    `InclusiveAlternativeOrdering` by definition, …), not stipulated
    features of the labels. -/
def ReciprocityType.Realizes {A : Type*} :
    ReciprocityType → (A → A → Prop) → Finset A → Prop
  | .strong,   R, X => Semantics.Plurality.Reciprocal.StrongReciprocity R X
  | .pairwise, R, X => Semantics.Plurality.Reciprocal.PairwiseConfig R X
  | .chain,    R, X => Semantics.Plurality.Reciprocal.ChainConfig R X
  | .radial,   R, X => Semantics.Plurality.Reciprocal.RadialConfig R X
  | .melee,    R, X => Semantics.Plurality.Reciprocal.MeleeConfig R X
  | .ring,     R, X => Semantics.Plurality.Reciprocal.RingConfig R X

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
    citing [dimitriadis-2004]): `rpSwahili`'s `verbalAffix` strategy with
    `monovalent` valency records the valence reduction (transitive →
    intransitive); the marker itself is `Swahili.Reciprocals.anSuffix`. -/
theorem rpSwahili_grounded_in_fragment :
    rpSwahili.primaryStrategy = some .verbalAffix ∧
    rpSwahili.valency = .monovalent :=
  ⟨rfl, rfl⟩

/-! ### Polysemous markers beyond the sample (§4.2)

Reflexive polysemy is carried by the profile inventories above (French
*se*, German *sich*, Wambaya *-ngg-*, Russian *-sja*) and drives their
derived WALS values. The review's further polysemy types are attested by
markers outside the 12-language sample. -/

/-- Yakut *-üs*: reciprocal + collective/sociative — *ölör-üs* 'kill
    each other' or 'kill somebody together' ([nordlinger-2023] ex. 49,
    citing [nedjalkov-2007b]). -/
def yakutUs : Marker :=
  { form := "-üs", strategy := .verbalAffix
  , readings := [.reciprocal, .collective, .sociative] }

/-- East Futunan *fe-...-ʼaki*: reciprocal + iterative — *fe-tapa-ʼaki*
    'sparkle again and again' ([nordlinger-2023] ex. 50, citing
    [nedjalkov-2007b]). -/
def eastFutunanFeAki : Marker :=
  { form := "fe-...-ʼaki", strategy := .verbalAffix
  , readings := [.reciprocal, .iterative] }

/-! ### Fragment connection: English reciprocal-reflexive distinction -/

open English.Pronouns in

/-- The English `RecipProfile` is grounded in the Fragment: English has
    reciprocal pronouns that are categorically different from reflexive
    pronouns, and the profile records *each other* as a bipartite NP
    strategy. The WALS substrate anchor for the reflexive-reciprocal
    distinction is `rpEnglish_wals`. -/
theorem english_profile_grounded :
    rpEnglish.primaryStrategy = some .bipartiteNP ∧
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
