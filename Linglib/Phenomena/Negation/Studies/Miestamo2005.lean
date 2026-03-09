import Linglib.Phenomena.Negation.Typology
import Linglib.Fragments.Finnish.Negation
import Linglib.Fragments.Italian.Negation
import Linglib.Fragments.German.Negation
import Linglib.Fragments.Japanese.Negation
import Linglib.Fragments.Turkish.Negation
import Linglib.Fragments.French.Negation
import Linglib.Fragments.Burmese.Negation
import Linglib.Fragments.Spanish.Negation
import Linglib.Fragments.Mandarin.Negation
import Linglib.Fragments.English.Negation
import Linglib.Fragments.Russian.Negation
import Linglib.Fragments.Czech.Negation
import Linglib.Fragments.Maori.Negation
import Linglib.Fragments.Hixkaryana.Negation

/-!
# Miestamo (2005): Standard Negation
@cite{miestamo-2005}

@cite{miestamo-2005} refines the WALS symmetric/asymmetric classification
(Ch 113-114) with two orthogonal theoretical distinctions:

## 1. Constructional vs Paradigmatic Asymmetry

WALS Ch 113 collapses these into a single "asymmetric" category, but Miestamo
decomposes asymmetry into two independent dimensions:

- **Constructional**: the syntactic *structure* of the negative clause differs
  from the affirmative beyond just adding the negation marker. E.g., Finnish
  uses a negative auxiliary + connegative, restructuring the clause.

- **Paradigmatic**: the *paradigm* (set of available formal distinctions) is
  different in the negative. E.g., Burmese *-bu* replaces all TAM suffixes,
  collapsing three distinctions to one.

These are orthogonal: a language can have constructional asymmetry with full
paradigmatic symmetry (Finnish), or paradigmatic asymmetry without major
constructional changes (Turkish aorist).

## 2. Derived vs Independent Asymmetry

- **Derived**: the asymmetry is a structural consequence of the negation
  marker's properties. A negative *verb* necessarily creates A/Fin because
  it takes over the finite verb slot — the asymmetry follows from the
  morphological type.

- **Independent**: the asymmetry is not structurally predictable from the
  negation marker type. E.g., Burmese TAM neutralization does not follow
  from having a circumfix — other circumfixing languages maintain TAM.

## WALS Consistency

Every datum here is consistent with the coarser WALS classification:
- Symmetric-only → no constructional or paradigmatic asymmetry
- Asymmetric A/Fin → constructional asymmetry (always)
- Asymmetric A/Cat → paradigmatic or constructional or both
- SymAsy → some constructions symmetric, others asymmetric
-/

namespace Phenomena.Negation.Studies.Miestamo2005

open Phenomena.Negation.Typology (NegSymmetry AsymmetrySubtype NegMorphemeType)

-- ============================================================================
-- § 1: Core Types
-- ============================================================================

/-- Miestamo's two dimensions of asymmetry. WALS Ch 113 collapses these
    into a single symmetric/asymmetric distinction. -/
inductive AsymmetryDimension where
  /-- The negative clause has a different syntactic structure than the
      affirmative, beyond just the negation marker. E.g., Finnish neg aux
      restructures the clause; Japanese *-nai* changes verb to i-adjective. -/
  | constructional
  /-- The negative paradigm has fewer formal distinctions than the
      affirmative. E.g., Burmese *-bu* neutralizes TAM; Turkish aorist
      uses a different marker. -/
  | paradigmatic
  deriving DecidableEq, Repr, BEq

/-- Whether the asymmetry is derived from the negation marker type
    or independent of it. -/
inductive AsymmetrySource where
  /-- The asymmetry follows structurally from the negation marker's
      properties. A negative verb necessarily creates A/Fin. -/
  | derived
  /-- The asymmetry is not predictable from the marker type alone.
      E.g., TAM neutralization in Burmese is independent of circumfixing. -/
  | independent
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- § 2: Extended Datum
-- ============================================================================

/-- A Miestamo-style negation profile extending the WALS classification. -/
structure MiestamoDatum where
  language : String
  /-- WALS Ch 112: morpheme type -/
  morphemeType : NegMorphemeType
  /-- WALS Ch 113: symmetric/asymmetric/both -/
  symmetry : NegSymmetry
  /-- WALS Ch 114: asymmetry subtype -/
  asymmetrySubtype : AsymmetrySubtype
  /-- Miestamo: which dimensions of asymmetry are present -/
  asymmetryDimensions : List AsymmetryDimension
  /-- Miestamo: is the asymmetry derived or independent? -/
  asymmetrySource : Option AsymmetrySource
  /-- Negation marker form(s), derived from Fragment where available -/
  negMarkers : List String
  /-- Brief description of the asymmetry (if any) -/
  asymmetryDescription : String := ""
  deriving Repr, BEq

-- ============================================================================
-- § 3: Per-Language Data (Fragment-derived where possible)
-- ============================================================================

/-- Finnish: constructional A/Fin, derived. Neg aux *ei* restructures clause.
    Form derived from `Fragments.Finnish.Negation.negParadigm`. -/
def finnish : MiestamoDatum :=
  { language := "Finnish"
  , morphemeType := .auxVerb
  , symmetry := .asymmetric
  , asymmetrySubtype := .finiteness
  , asymmetryDimensions := [.constructional]
  , asymmetrySource := some .derived
  , negMarkers := Fragments.Finnish.Negation.negParadigm.map (·.form)
  , asymmetryDescription := "Negative auxiliary becomes finite verb; " ++
      "lexical verb appears as connegative (A/Fin). " ++
      "Derived: neg aux being a verb structurally entails finiteness change." }

/-- German: symmetric, no asymmetry. Particle *nicht*.
    Form derived from `Fragments.German.Negation.negMarker`. -/
def german : MiestamoDatum :=
  { language := "German"
  , morphemeType := .particle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , asymmetryDimensions := []
  , asymmetrySource := none
  , negMarkers := [Fragments.German.Negation.negMarker]
  , asymmetryDescription := "Symmetric: adding nicht introduces no " ++
      "structural or paradigmatic changes." }

/-- Japanese: constructional + paradigmatic, A/Fin+A/Cat.
    Suffix *-nai* changes verb to i-adjective (constructional) and shifts
    tense marking to the suffix (paradigmatic).
    Form derived from `Fragments.Japanese.Negation.negSuffix`. -/
def japanese : MiestamoDatum :=
  { language := "Japanese"
  , morphemeType := .affix
  , symmetry := .asymmetric
  , asymmetrySubtype := .finAndCat
  , asymmetryDimensions := [.constructional, .paradigmatic]
  , asymmetrySource := some .independent
  , negMarkers := [Fragments.Japanese.Negation.negSuffix]
  , asymmetryDescription := "Constructional: -nai turns verb into i-adjective. " ++
      "Paradigmatic: tense/mood marked on -nai, not on stem. " ++
      "Independent: affix type does not predict category change." }

/-- Turkish: SymAsy with paradigmatic A/Cat (aorist only).
    Most constructions symmetric; aorist negative uses *-z* instead of *-(I)r*.
    Form derived from `Fragments.Turkish.Negation.negSuffix`. -/
def turkish : MiestamoDatum :=
  { language := "Turkish"
  , morphemeType := .affix
  , symmetry := .both
  , asymmetrySubtype := .otherCategories
  , asymmetryDimensions := [.paradigmatic]
  , asymmetrySource := some .independent
  , negMarkers := [Fragments.Turkish.Negation.negSuffix]
  , asymmetryDescription := "Paradigmatic: aorist marker -(I)r → -z under negation. " ++
      "Most other TAM constructions are symmetric. " ++
      "Independent: suffix type does not predict aorist change." }

/-- French: symmetric. Bipartite *ne...pas* introduces no structural change.
    Forms derived from `Fragments.French.Negation`. -/
def french : MiestamoDatum :=
  { language := "French"
  , morphemeType := .particle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , asymmetryDimensions := []
  , asymmetrySource := none
  , negMarkers := [Fragments.French.Negation.neClitic,
                    Fragments.French.Negation.pasReinforcer]
  , asymmetryDescription := "Symmetric: ne...pas adds negation without " ++
      "changing clause structure or paradigm. " ++
      "Jespersen cycle: ne dropping in colloquial speech." }

/-- Burmese: constructional + paradigmatic A/Cat, independent.
    Circumfix *ma-...-bu* replaces TAM markers.
    Forms derived from `Fragments.Burmese.Negation`. -/
def burmese : MiestamoDatum :=
  { language := "Burmese"
  , morphemeType := .doubleNeg
  , symmetry := .asymmetric
  , asymmetrySubtype := .otherCategories
  , asymmetryDimensions := [.constructional, .paradigmatic]
  , asymmetrySource := some .independent
  , negMarkers := [Fragments.Burmese.Negation.negPrefix,
                    Fragments.Burmese.Negation.negSuffix]
  , asymmetryDescription := "Constructional: circumfix changes word structure. " ++
      "Paradigmatic: -bu replaces TAM suffixes, neutralizing 3 distinctions to 1. " ++
      "Independent: circumfix type does not predict TAM neutralization." }

/-- Italian: symmetric. Particle *non*, no structural change.
    Form derived from `Fragments.Italian.Negation.negMarker`. -/
def italian : MiestamoDatum :=
  { language := "Italian"
  , morphemeType := .particle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , asymmetryDimensions := []
  , asymmetrySource := none
  , negMarkers := [Fragments.Italian.Negation.negMarker]
  , asymmetryDescription := "Symmetric: non adds negation without " ++
      "structural or paradigmatic change." }

/-- Spanish: symmetric. Particle *no*, no structural change.
    Form derived from `Fragments.Spanish.Negation.negMarker`. -/
def spanish : MiestamoDatum :=
  { language := "Spanish"
  , morphemeType := .particle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , asymmetryDimensions := []
  , asymmetrySource := none
  , negMarkers := [Fragments.Spanish.Negation.negMarker]
  , asymmetryDescription := "Symmetric: no adds negation without " ++
      "structural or paradigmatic change. " ++
      "Position-dependent n-word concord (parallels Italian)." }

/-- Mandarin Chinese: SymAsy with A/Fin. Two particles: 不 *bù* (general,
    symmetric) and 没(有) *méi(yǒu)* (perfective, asymmetric).
    The *bù*/*méi* split is paradigmatic: the choice of negator depends on
    aspect, unlike in the affirmative where a single verb form serves.
    Forms derived from `Fragments.Mandarin.Negation`. -/
def mandarin : MiestamoDatum :=
  { language := "Mandarin Chinese"
  , morphemeType := .particle
  , symmetry := .both
  , asymmetrySubtype := .finiteness
  , asymmetryDimensions := [.paradigmatic]
  , asymmetrySource := some .independent
  , negMarkers := [Fragments.Mandarin.Negation.buParticle,
                    Fragments.Mandarin.Negation.meiParticle]
  , asymmetryDescription := "Paradigmatic: the bù/méi split means the " ++
      "choice of negator depends on aspect (perfective vs non-perfective), " ++
      "a distinction not marked on the affirmative verb. " ++
      "Independent: particle type does not predict the split." }

/-- English: SymAsy with constructional A/Cat (do-support).
    With modals/be/have, negation is symmetric; with lexical verbs,
    *do*-support introduces a structural change (constructional asymmetry).
    Form derived from `Fragments.English.Negation.negMarker`. -/
def english : MiestamoDatum :=
  { language := "English"
  , morphemeType := .particle
  , symmetry := .both
  , asymmetrySubtype := .otherCategories
  , asymmetryDimensions := [.constructional]
  , asymmetrySource := some .independent
  , negMarkers := [Fragments.English.Negation.negMarker]
  , asymmetryDescription := "Constructional: do-support introduces auxiliary do " ++
      "with lexical verbs (He eats → He does not eat). " ++
      "Symmetric with modals/be/have. " ++
      "Independent: particle type does not predict do-support." }

/-- Russian: symmetric. Particle *не* (*ne*), no structural change.
    Form derived from `Fragments.Russian.Negation.negMarker`. -/
def russian : MiestamoDatum :=
  { language := "Russian"
  , morphemeType := .particle
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , asymmetryDimensions := []
  , asymmetrySource := none
  , negMarkers := [Fragments.Russian.Negation.negMarker]
  , asymmetryDescription := "Symmetric: не adds negation without " ++
      "structural or paradigmatic change. " ++
      "Obligatory negative concord (Slavic pattern)." }

/-- Czech: symmetric. Prefix *ne-*, no structural change.
    Form derived from `Fragments.Czech.Negation.negPrefix`. -/
def czech : MiestamoDatum :=
  { language := "Czech"
  , morphemeType := .affix
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , asymmetryDimensions := []
  , asymmetrySource := none
  , negMarkers := [Fragments.Czech.Negation.negPrefix]
  , asymmetryDescription := "Symmetric: ne- prefix adds negation without " ++
      "structural or paradigmatic change. " ++
      "Obligatory negative concord (Slavic pattern)." }

/-- Maori: constructional A/Fin, source unclear.
    *Kāhore* functions as a quasi-auxiliary, changing the finiteness
    structure. WALS classifies morpheme type as wordUnclear.
    Form derived from `Fragments.Maori.Negation.negWord`. -/
def maori : MiestamoDatum :=
  { language := "Maori"
  , morphemeType := .wordUnclear
  , symmetry := .asymmetric
  , asymmetrySubtype := .finiteness
  , asymmetryDimensions := [.constructional]
  , asymmetrySource := some .derived
  , negMarkers := [Fragments.Maori.Negation.negWord]
  , asymmetryDescription := "Constructional: kāhore takes the TAM position, " ++
      "verb appears in nominalized form (A/Fin). " ++
      "Derived: quasi-auxiliary status structurally entails finiteness change." }

/-- Hixkaryana: constructional A/Fin, independent.
    Suffix *-hira* deverbalizes the verb; a copula becomes the finite
    element. Form derived from `Fragments.Hixkaryana.Negation.negSuffix`. -/
def hixkaryana : MiestamoDatum :=
  { language := "Hixkaryana"
  , morphemeType := .affix
  , symmetry := .asymmetric
  , asymmetrySubtype := .finiteness
  , asymmetryDimensions := [.constructional]
  , asymmetrySource := some .independent
  , negMarkers := [Fragments.Hixkaryana.Negation.negSuffix]
  , asymmetryDescription := "Constructional: -hira deverbalizes the verb, " ++
      "copula becomes the finite element (A/Fin). " ++
      "Independent: affix type does not predict deverbalization." }

def allData : List MiestamoDatum :=
  [finnish, german, japanese, turkish, french, burmese, italian, spanish,
   mandarin, english, russian, czech, maori, hixkaryana]

-- ============================================================================
-- § 4: WALS Consistency
-- ============================================================================

section WALSConsistency

/-- Symmetric languages have no asymmetry dimensions. -/
theorem symmetric_no_dimensions :
    (allData.filter (·.symmetry == .symmetric)).all
      (fun d => d.asymmetryDimensions.isEmpty) = true := by
  native_decide

/-- Symmetric languages have no asymmetry source. -/
theorem symmetric_no_source :
    (allData.filter (·.symmetry == .symmetric)).all
      (fun d => d.asymmetrySource.isNone) = true := by
  native_decide

/-- Asymmetric languages have at least one asymmetry dimension. -/
theorem asymmetric_has_dimensions :
    (allData.filter (·.symmetry == .asymmetric)).all
      (fun d => !d.asymmetryDimensions.isEmpty) = true := by
  native_decide

/-- Asymmetric languages have an asymmetry source. -/
theorem asymmetric_has_source :
    (allData.filter (·.symmetry == .asymmetric)).all
      (fun d => d.asymmetrySource.isSome) = true := by
  native_decide

/-- SymAsy languages have at least one asymmetry dimension
    (for their asymmetric constructions). -/
theorem symasy_has_dimensions :
    (allData.filter (·.symmetry == .both)).all
      (fun d => !d.asymmetryDimensions.isEmpty) = true := by
  native_decide

/-- A/Fin with a *verbal* negator implies constructional asymmetry:
    the negative verb takes over the finite verb slot, necessarily
    restructuring the clause. A/Fin with a *particle* negator (Mandarin)
    can be paradigmatic-only — the bù/méi split is a paradigmatic
    distinction, not a structural one. -/
theorem afin_verbal_implies_constructional :
    (allData.filter (fun d =>
      (d.asymmetrySubtype == .finiteness ||
       d.asymmetrySubtype == .finAndCat ||
       d.asymmetrySubtype == .finAndNonReal) &&
      d.morphemeType == .auxVerb)).all
      (fun d => d.asymmetryDimensions.contains .constructional) = true := by
  native_decide

/-- Mandarin shows that A/Fin with a particle negator is paradigmatic-only:
    the bù/méi split is a paradigmatic distinction (which negator to use
    depends on aspect), not a constructional one (clause structure unchanged). -/
theorem mandarin_afin_paradigmatic_only :
    mandarin.asymmetrySubtype == .finiteness ∧
    mandarin.morphemeType == .particle ∧
    mandarin.asymmetryDimensions == [.paradigmatic] := by
  native_decide

/-- Symmetric-only (WALS) implies nonAssignable asymmetry subtype. -/
theorem symmetric_implies_nonassignable :
    (allData.filter (·.symmetry == .symmetric)).all
      (fun d => d.asymmetrySubtype == .nonAssignable) = true := by
  native_decide

/-- Morpheme types are consistent with WALS Typology profiles. -/
theorem finnish_morpheme_consistent :
    finnish.morphemeType = Typology.finnish.morphemeType := rfl
theorem german_morpheme_consistent :
    german.morphemeType = Typology.german.morphemeType := rfl
theorem japanese_morpheme_consistent :
    japanese.morphemeType = Typology.japanese.morphemeType := rfl
theorem turkish_morpheme_consistent :
    turkish.morphemeType = Typology.turkish.morphemeType := rfl
theorem italian_morpheme_consistent :
    italian.morphemeType = Typology.italian.morphemeType := rfl
theorem burmese_morpheme_consistent :
    burmese.morphemeType = Typology.burmese.morphemeType := rfl
theorem french_morpheme_consistent :
    french.morphemeType = Typology.french.morphemeType := rfl
theorem spanish_morpheme_consistent :
    spanish.morphemeType = Typology.spanish.morphemeType := rfl
theorem mandarin_morpheme_consistent :
    mandarin.morphemeType = Typology.mandarin.morphemeType := rfl
theorem english_morpheme_consistent :
    english.morphemeType = Typology.english.morphemeType := rfl
theorem russian_morpheme_consistent :
    russian.morphemeType = Typology.russian.morphemeType := rfl
theorem czech_morpheme_consistent :
    czech.morphemeType = Typology.czech.morphemeType := rfl
theorem maori_morpheme_consistent :
    maori.morphemeType = Typology.maori.morphemeType := rfl
theorem hixkaryana_morpheme_consistent :
    hixkaryana.morphemeType = Typology.hixkaryana.morphemeType := rfl

/-- Symmetry values are consistent with WALS Typology profiles. -/
theorem finnish_symmetry_consistent :
    finnish.symmetry = Typology.finnish.symmetry := rfl
theorem german_symmetry_consistent :
    german.symmetry = Typology.german.symmetry := rfl
theorem japanese_symmetry_consistent :
    japanese.symmetry = Typology.japanese.symmetry := rfl
theorem turkish_symmetry_consistent :
    turkish.symmetry = Typology.turkish.symmetry := rfl
theorem italian_symmetry_consistent :
    italian.symmetry = Typology.italian.symmetry := rfl
theorem burmese_symmetry_consistent :
    burmese.symmetry = Typology.burmese.symmetry := rfl
theorem french_symmetry_consistent :
    french.symmetry = Typology.french.symmetry := rfl
theorem spanish_symmetry_consistent :
    spanish.symmetry = Typology.spanish.symmetry := rfl
theorem mandarin_symmetry_consistent :
    mandarin.symmetry = Typology.mandarin.symmetry := rfl
theorem english_symmetry_consistent :
    english.symmetry = Typology.english.symmetry := rfl
theorem russian_symmetry_consistent :
    russian.symmetry = Typology.russian.symmetry := rfl
theorem czech_symmetry_consistent :
    czech.symmetry = Typology.czech.symmetry := rfl
theorem maori_symmetry_consistent :
    maori.symmetry = Typology.maori.symmetry := rfl
theorem hixkaryana_symmetry_consistent :
    hixkaryana.symmetry = Typology.hixkaryana.symmetry := rfl

/-- Asymmetry subtypes are consistent with WALS Typology profiles. -/
theorem finnish_subtype_consistent :
    finnish.asymmetrySubtype = Typology.finnish.asymmetrySubtype := rfl
theorem german_subtype_consistent :
    german.asymmetrySubtype = Typology.german.asymmetrySubtype := rfl
theorem japanese_subtype_consistent :
    japanese.asymmetrySubtype = Typology.japanese.asymmetrySubtype := rfl
theorem turkish_subtype_consistent :
    turkish.asymmetrySubtype = Typology.turkish.asymmetrySubtype := rfl
theorem italian_subtype_consistent :
    italian.asymmetrySubtype = Typology.italian.asymmetrySubtype := rfl
theorem burmese_subtype_consistent :
    burmese.asymmetrySubtype = Typology.burmese.asymmetrySubtype := rfl
theorem french_subtype_consistent :
    french.asymmetrySubtype = Typology.french.asymmetrySubtype := rfl
theorem spanish_subtype_consistent :
    spanish.asymmetrySubtype = Typology.spanish.asymmetrySubtype := rfl
theorem mandarin_subtype_consistent :
    mandarin.asymmetrySubtype = Typology.mandarin.asymmetrySubtype := rfl
theorem english_subtype_consistent :
    english.asymmetrySubtype = Typology.english.asymmetrySubtype := rfl
theorem russian_subtype_consistent :
    russian.asymmetrySubtype = Typology.russian.asymmetrySubtype := rfl
theorem czech_subtype_consistent :
    czech.asymmetrySubtype = Typology.czech.asymmetrySubtype := rfl
theorem maori_subtype_consistent :
    maori.asymmetrySubtype = Typology.maori.asymmetrySubtype := rfl
theorem hixkaryana_subtype_consistent :
    hixkaryana.asymmetrySubtype = Typology.hixkaryana.asymmetrySubtype := rfl

end WALSConsistency

-- ============================================================================
-- § 5: Fragment Bridges
-- ============================================================================

section FragmentBridges

/-- Finnish negation markers derive from the Fragment paradigm. -/
theorem finnish_markers_from_fragment :
    finnish.negMarkers =
      Fragments.Finnish.Negation.negParadigm.map (·.form) := rfl

/-- Finnish has 6 neg aux forms (3 persons x 2 numbers). -/
theorem finnish_marker_count :
    finnish.negMarkers.length = 6 := by native_decide

/-- German negation marker derives from Fragment. -/
theorem german_marker_from_fragment :
    german.negMarkers = [Fragments.German.Negation.negMarker] := rfl

/-- German marker is *nicht*. -/
theorem german_marker_is_nicht :
    german.negMarkers = ["nicht"] := rfl

/-- Japanese negation marker derives from Fragment. -/
theorem japanese_marker_from_fragment :
    japanese.negMarkers = [Fragments.Japanese.Negation.negSuffix] := rfl

/-- Japanese marker is *-nai*. -/
theorem japanese_marker_is_nai :
    japanese.negMarkers = ["-nai"] := rfl

/-- Turkish negation marker derives from Fragment. -/
theorem turkish_marker_from_fragment :
    turkish.negMarkers = [Fragments.Turkish.Negation.negSuffix] := rfl

/-- Turkish marker is *-mA-*. -/
theorem turkish_marker_is_mA :
    turkish.negMarkers = ["-mA-"] := rfl

/-- French negation markers derive from Fragment. -/
theorem french_markers_from_fragment :
    french.negMarkers = [Fragments.French.Negation.neClitic,
                          Fragments.French.Negation.pasReinforcer] := rfl

/-- French markers are *ne* and *pas*. -/
theorem french_markers_are_ne_pas :
    french.negMarkers = ["ne", "pas"] := rfl

/-- Burmese negation markers derive from Fragment. -/
theorem burmese_markers_from_fragment :
    burmese.negMarkers = [Fragments.Burmese.Negation.negPrefix,
                           Fragments.Burmese.Negation.negSuffix] := rfl

/-- Burmese markers are *ma-* and *-bu*. -/
theorem burmese_markers_are_ma_bu :
    burmese.negMarkers = ["ma-", "-bu"] := rfl

/-- Italian negation marker derives from Fragment. -/
theorem italian_marker_from_fragment :
    italian.negMarkers = [Fragments.Italian.Negation.negMarker] := rfl

/-- Italian marker is *non*. -/
theorem italian_marker_is_non :
    italian.negMarkers = ["non"] := rfl

/-- Spanish negation marker derives from Fragment. -/
theorem spanish_marker_from_fragment :
    spanish.negMarkers = [Fragments.Spanish.Negation.negMarker] := rfl

/-- Spanish marker is *no*. -/
theorem spanish_marker_is_no :
    spanish.negMarkers = ["no"] := rfl

/-- Mandarin negation markers derive from Fragment. -/
theorem mandarin_markers_from_fragment :
    mandarin.negMarkers = [Fragments.Mandarin.Negation.buParticle,
                            Fragments.Mandarin.Negation.meiParticle] := rfl

/-- Mandarin markers are *bù* and *méi*. -/
theorem mandarin_markers_are_bu_mei :
    mandarin.negMarkers = ["bù", "méi"] := rfl

/-- English negation marker derives from Fragment. -/
theorem english_marker_from_fragment :
    english.negMarkers = [Fragments.English.Negation.negMarker] := rfl

/-- English marker is *not*. -/
theorem english_marker_is_not :
    english.negMarkers = ["not"] := rfl

/-- Russian negation marker derives from Fragment. -/
theorem russian_marker_from_fragment :
    russian.negMarkers = [Fragments.Russian.Negation.negMarker] := rfl

/-- Russian marker is *не*. -/
theorem russian_marker_is_ne :
    russian.negMarkers = ["не"] := rfl

/-- Czech negation marker derives from Fragment. -/
theorem czech_marker_from_fragment :
    czech.negMarkers = [Fragments.Czech.Negation.negPrefix] := rfl

/-- Czech marker is *ne-*. -/
theorem czech_marker_is_ne :
    czech.negMarkers = ["ne-"] := rfl

/-- Maori negation word derives from Fragment. -/
theorem maori_marker_from_fragment :
    maori.negMarkers = [Fragments.Maori.Negation.negWord] := rfl

/-- Maori marker is *kāhore*. -/
theorem maori_marker_is_kahore :
    maori.negMarkers = ["kāhore"] := rfl

/-- Hixkaryana negation suffix derives from Fragment. -/
theorem hixkaryana_marker_from_fragment :
    hixkaryana.negMarkers = [Fragments.Hixkaryana.Negation.negSuffix] := rfl

/-- Hixkaryana marker is *-hira*. -/
theorem hixkaryana_marker_is_hira :
    hixkaryana.negMarkers = ["-hira"] := rfl

end FragmentBridges

-- ============================================================================
-- § 6: Theoretical Predictions
-- ============================================================================

section Predictions

/-- Derived asymmetry: negative auxiliary verbs always produce
    constructional A/Fin asymmetry. The asymmetry is derived because
    a verb-type negator structurally entails finiteness restructuring. -/
theorem neg_aux_implies_derived_constructional :
    (allData.filter (·.morphemeType == .auxVerb)).all
      (fun d => d.asymmetrySource == some .derived ∧
                d.asymmetryDimensions.contains .constructional) = true := by
  native_decide

/-- Particles that are symmetric-only have no asymmetry dimensions.
    Mandarin is the exception: it is SymAsy because the bù/méi split
    introduces paradigmatic asymmetry despite both being particles. -/
theorem symmetric_particles_no_dimensions :
    (allData.filter (fun d => d.morphemeType == .particle &&
      d.symmetry == .symmetric)).all
      (fun d => d.asymmetryDimensions.isEmpty) = true := by
  native_decide

/-- Affixes can produce symmetric, asymmetric, or SymAsy negation. -/
theorem affixes_variable :
    (allData.filter (·.morphemeType == .affix)).map (·.symmetry) =
      [.asymmetric, .both, .symmetric, .asymmetric] := rfl

/-- Constructional asymmetry (only) implies the paradigm is maintained:
    Finnish has A/Fin constructional asymmetry but no paradigmatic gaps. -/
theorem finnish_no_paradigmatic_asymmetry :
    finnish.asymmetryDimensions = [.constructional] := rfl

/-- Burmese has both dimensions of asymmetry: the circumfix changes
    structure (constructional) and neutralizes TAM (paradigmatic). -/
theorem burmese_both_dimensions :
    burmese.asymmetryDimensions = [.constructional, .paradigmatic] := rfl

/-- Turkish has paradigmatic-only asymmetry: the aorist marker changes
    but the clause structure does not. -/
theorem turkish_paradigmatic_only :
    turkish.asymmetryDimensions = [.paradigmatic] := rfl

end Predictions

-- ============================================================================
-- § 7: Fragment Cross-Validation
-- ============================================================================

section CrossValidation

/-- Finnish Fragment inflection distribution is consistent with
    constructional A/Fin: categories split across neg aux and main verb. -/
theorem finnish_split_confirms_constructional :
    let dist := Fragments.Finnish.Negation.finnishNegDistribution
    dist.onNegAux.length > 0 ∧ dist.onMainVerb.length > 0 ∧
    finnish.asymmetryDimensions.contains .constructional := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-- Japanese Fragment distribution confirms constructional + paradigmatic:
    tense moves from stem to suffix (both structural and paradigmatic change). -/
theorem japanese_distribution_confirms_asymmetry :
    let dist := Fragments.Japanese.Negation.japaneseNegDistribution
    dist.affirmativeOnStem.contains "tense" = true ∧
    dist.negativeOnStem.contains "tense" = false ∧
    dist.negativeOnSuffix.contains "tense" = true ∧
    japanese.asymmetryDimensions.contains .constructional ∧
    japanese.asymmetryDimensions.contains .paradigmatic := by
  exact ⟨by native_decide, by native_decide, by native_decide,
         by native_decide, by native_decide⟩

/-- Turkish Fragment confirms SymAsy: 4 of 5 constructions are symmetric,
    only the aorist is asymmetric. -/
theorem turkish_fragment_confirms_symasy :
    (Fragments.Turkish.Negation.gelParadigm.filter (·.symmetric)).length = 4 ∧
    (Fragments.Turkish.Negation.gelParadigm.filter (fun e => !e.symmetric)).length = 1 ∧
    turkish.symmetry == .both := by
  exact ⟨by native_decide, by native_decide, rfl⟩

/-- German Fragment confirms symmetric: all tenses available, negation is
    just adding *nicht*. -/
theorem german_fragment_confirms_symmetric :
    Fragments.German.Negation.allExamples.length = 5 ∧
    german.asymmetryDimensions.isEmpty := by
  exact ⟨by native_decide, rfl⟩

/-- Burmese Fragment confirms paradigmatic asymmetry: TAM neutralized
    (3 affirmative distinctions → 1 negative form). -/
theorem burmese_fragment_confirms_paradigmatic :
    Fragments.Burmese.Negation.burmeseTAM.affirmativeTAM.length = 3 ∧
    Fragments.Burmese.Negation.burmeseTAM.negativeTAM.length = 1 ∧
    burmese.asymmetryDimensions.contains .paradigmatic := by
  exact ⟨rfl, rfl, by native_decide⟩

/-- French Fragment confirms symmetric: all tenses available under negation. -/
theorem french_fragment_confirms_symmetric :
    Fragments.French.Negation.allExamples.length = 5 ∧
    french.asymmetryDimensions.isEmpty := by
  exact ⟨by native_decide, rfl⟩

/-- Spanish Fragment confirms symmetric: all tenses available, *no* adds
    negation without structural change. -/
theorem spanish_fragment_confirms_symmetric :
    Fragments.Spanish.Negation.allExamples.length = 5 ∧
    spanish.asymmetryDimensions.isEmpty := by
  exact ⟨by native_decide, rfl⟩

/-- Mandarin Fragment confirms SymAsy: 3 bù (symmetric) + 2 méi (asymmetric)
    constructions, matching the paradigmatic-only classification. -/
theorem mandarin_fragment_confirms_symasy :
    (Fragments.Mandarin.Negation.allExamples.filter (·.symmetric)).length = 3 ∧
    (Fragments.Mandarin.Negation.allExamples.filter (fun e => !e.symmetric)).length = 2 ∧
    mandarin.symmetry == .both ∧
    mandarin.asymmetryDimensions == [.paradigmatic] := by
  exact ⟨by native_decide, by native_decide, rfl, rfl⟩

/-- Mandarin méi-yǒu connects to AspectComparison: the same particle is
    formalized as a cross-domain negative perfective there. -/
theorem mandarin_meiyou_cross_module :
    Fragments.Mandarin.AspectComparison.meiyou.hanzi = "没有" ∧
    Fragments.Mandarin.AspectComparison.meiyou.pinyin = "méi-yǒu" :=
  ⟨rfl, rfl⟩

/-- English Fragment confirms SymAsy: 3 symmetric (modal, copula, aux have)
    + 2 asymmetric (lexical verb with do-support). -/
theorem english_fragment_confirms_symasy :
    (Fragments.English.Negation.allExamples.filter (·.symmetric)).length = 3 ∧
    (Fragments.English.Negation.allExamples.filter (fun e => !e.symmetric)).length = 2 ∧
    english.symmetry == .both := by
  exact ⟨by native_decide, by native_decide, rfl⟩

/-- English do-support is exactly the asymmetric constructions. -/
theorem english_dosupport_is_asymmetry :
    Fragments.English.Negation.allExamples.all
      (fun e => e.symmetric == !e.doSupport) = true := by
  native_decide

/-- Russian Fragment confirms symmetric: all constructions available,
    *не* adds negation without structural change. -/
theorem russian_fragment_confirms_symmetric :
    Fragments.Russian.Negation.allExamples.length = 4 ∧
    russian.asymmetryDimensions.isEmpty := by
  exact ⟨by native_decide, rfl⟩

/-- Russian negative concord: all n-words co-occur with *не*. -/
theorem russian_concord_confirms_cooccur :
    Fragments.Russian.Negation.allConcordExamples.all
      (fun e => (e.sentence.splitOn "не").length > 1) = true := by
  native_decide

/-- Czech Fragment confirms symmetric: all constructions available,
    prefix *ne-* adds negation without structural change. -/
theorem czech_fragment_confirms_symmetric :
    Fragments.Czech.Negation.allExamples.length = 4 ∧
    czech.asymmetryDimensions.isEmpty := by
  exact ⟨by native_decide, rfl⟩

/-- Czech negative concord: all n-words co-occur with *ne-* prefix. -/
theorem czech_concord_confirms_cooccur :
    Fragments.Czech.Negation.allConcordExamples.all
      (fun e => (e.sentence.splitOn "ne").length > 1) = true := by
  native_decide

/-- Maori Fragment confirms asymmetric: all constructions are A/Fin. -/
theorem maori_fragment_confirms_asymmetric :
    Fragments.Maori.Negation.allExamples.all (fun e => !e.symmetric) = true ∧
    maori.asymmetryDimensions.contains .constructional := by
  exact ⟨by native_decide, by native_decide⟩

/-- Hixkaryana Fragment confirms asymmetric A/Fin with copula finite. -/
theorem hixkaryana_fragment_confirms_asymmetric :
    Fragments.Hixkaryana.Negation.allExamples.all (fun e => !e.symmetric) = true ∧
    Fragments.Hixkaryana.Negation.allExamples.all (·.copulaFinite) = true ∧
    hixkaryana.asymmetryDimensions.contains .constructional := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

end CrossValidation

-- ============================================================================
-- § 8: Summary Statistics
-- ============================================================================

theorem sample_size : allData.length = 14 := by native_decide

theorem symmetric_count :
    (allData.filter (·.symmetry == .symmetric)).length = 6 := by native_decide
theorem asymmetric_count :
    (allData.filter (·.symmetry == .asymmetric)).length = 5 := by native_decide
theorem symasy_count :
    (allData.filter (·.symmetry == .both)).length = 3 := by native_decide

theorem constructional_count :
    (allData.filter (fun d => d.asymmetryDimensions.contains .constructional)).length = 6 := by
  native_decide
theorem paradigmatic_count :
    (allData.filter (fun d => d.asymmetryDimensions.contains .paradigmatic)).length = 4 := by
  native_decide
theorem both_dimensions_count :
    (allData.filter (fun d =>
      d.asymmetryDimensions.contains .constructional &&
      d.asymmetryDimensions.contains .paradigmatic)).length = 2 := by
  native_decide

theorem derived_count :
    (allData.filter (·.asymmetrySource == some .derived)).length = 2 := by native_decide
theorem independent_count :
    (allData.filter (·.asymmetrySource == some .independent)).length = 6 := by native_decide

end Phenomena.Negation.Studies.Miestamo2005
