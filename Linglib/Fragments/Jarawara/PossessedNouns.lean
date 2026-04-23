import Linglib.Theories.Morphology.DM.NominalStructure
import Linglib.Phenomena.Possession.Typology
import Linglib.Core.Lexical.Word
import Linglib.Features.Gender

/-!
# Jarawara Possessed Nouns @cite{adamson-2024} @cite{dixon-2004}

Inalienably possessed noun classes and the *mano* 'arm' paradigm
in Jarawara (Arawan), drawn from @cite{adamson-2024} §3.2 and
@cite{dixon-2004}.

## Key facts

- Jarawara has two genders: masculine (marked, [+MASC] on n) and
  feminine (unmarked, plain n)
- All ~175 iPossessable nouns are feminine when used "free" (without
  a possessor), consistent with being licensed by plain n
- iPossession is expressed by direct juxtaposition; aPossession uses
  the marker *kaa*
- The "masculine"/"feminine" alternations on possessed nouns reflect
  φ-agreement with the iPossessor, not gender assignment

## Semantic Classification (@cite{dixon-2004} p. 311)

The iPossessable class maps onto the upper portion of the
cross-linguistic inalienability hierarchy from `Possession.Typology`.
-/

namespace Fragments.Jarawara

open Phenomena.Possession.Typology

-- ============================================================================
-- § 1: Semantic Classes of iPossessable Nouns (Table 3)
-- ============================================================================

/-- Semantic classification of Jarawara iPossessable nouns
    (@cite{dixon-2004} p. 311; @cite{adamson-2024} Table 3). -/
structure PossessedNounClass where
  label : String
  memberCount : Nat
  examples : List (String × String)  -- (Jarawara form, English gloss)
  /-- Nearest match on the cross-linguistic inalienability hierarchy. -/
  inalienabilityRank : InalienabilityRank
  deriving Repr

def orientation : PossessedNounClass :=
  { label := "Orientation"
  , memberCount := 17
  , examples := [("mese/mese", "top surface of"),
                 ("tori/toro", "inside of")]
  , inalienabilityRank := .spatialRelation }

def wholeAndPart : PossessedNounClass :=
  { label := "Whole and part"
  , memberCount := 14
  , examples := [("boni/bono", "whole thing"),
                 ("kote/kote", "piece")]
  , inalienabilityRank := .partWhole }

def bodyParts : PossessedNounClass :=
  { label := "Body parts"
  , memberCount := 62
  , examples := [("noki/noko", "eye/face"),
                 ("tame/teme", "foot"),
                 ("jifori/jifori", "tail")]
  , inalienabilityRank := .bodyPart }

def partsOfPlants : PossessedNounClass :=
  { label := "Parts of plants"
  , memberCount := 19
  , examples := [("mowe/mowe", "flower"),
                 ("mati/matone", "cord, rope")]
  , inalienabilityRank := .partWhole }

def physicalCharacteristics : PossessedNounClass :=
  { label := "Physical characteristics/properties"
  , memberCount := 18
  , examples := [("kakitiri/kakitiri", "itch"),
                 ("mahi/maho", "smell")]
  , inalienabilityRank := .culturalItem }

def noiseAndLanguage : PossessedNounClass :=
  { label := "Noise and language"
  , memberCount := 4
  , examples := [("moni/moni", "noise"),
                 ("ini/ino", "name")]
  , inalienabilityRank := .culturalItem }

def imageAndDream : PossessedNounClass :=
  { label := "Image and dream"
  , memberCount := 5
  , examples := [("hani/hano", "design/picture"),
                 ("watari/watari(ne)", "dream")]
  , inalienabilityRank := .culturalItem }

def association : PossessedNounClass :=
  { label := "Association"
  , memberCount := 9
  , examples := [("tehe/tehene", "something mixed with"),
                 ("tase/tesene", "companion of")]
  , inalienabilityRank := .culturalItem }

def containers : PossessedNounClass :=
  { label := "Containers and other artefacts"
  , memberCount := 7
  , examples := [("wije/wijene", "vessel, container"),
                 ("atori/atori", "ornament")]
  , inalienabilityRank := .culturalItem }

def waterFireLight : PossessedNounClass :=
  { label := "Water, fire, and light"
  , memberCount := 11
  , examples := [("jiji/jifone", "fire, firewood"),
                 ("fehe/fehene", "liquid, juice, sap, water")]
  , inalienabilityRank := .culturalItem }

def food : PossessedNounClass :=
  { label := "Food"
  , memberCount := 3
  , examples := [("tafe/tefe", "food"),
                 ("saharine/saharine", "broth, mush")]
  , inalienabilityRank := .culturalItem }

def place : PossessedNounClass :=
  { label := "Place"
  , memberCount := 6
  , examples := [("hawi/hawine", "path"),
                 ("tame/temene", "grave")]
  , inalienabilityRank := .spatialRelation }

/-- All 12 semantic classes of iPossessable nouns. -/
def allClasses : List PossessedNounClass :=
  [orientation, wholeAndPart, bodyParts, partsOfPlants,
   physicalCharacteristics, noiseAndLanguage, imageAndDream,
   association, containers, waterFireLight, food, place]

/-- Total iPossessable nouns: ~175 (@cite{dixon-2004} p. 310). -/
theorem total_ipossessable :
    (allClasses.map (·.memberCount)).foldl (· + ·) 0 = 175 := by native_decide

-- ============================================================================
-- § 2: *mano* 'arm' Paradigm (Table 5; @cite{dixon-2004} p. 315)
-- ============================================================================

/-- Person–number features of a Jarawara possessor. -/
inductive Person where | first | second | third deriving DecidableEq, Repr
inductive PossGender where | masc | fem deriving DecidableEq, Repr

/-- Bridge to cross-linguistic surface gender. -/
def PossGender.toSurfaceGender : PossGender → Features.SurfaceGender
  | .masc => .masculine
  | .fem  => .feminine

/-- A possessor with full φ-features. Third person distinguishes gender;
    first and second person can be singular or plural, with clusivity
    for first person plural. -/
structure Possessor where
  person : Person
  number : Number
  gender : Option PossGender := none  -- only for 3rd person
  deriving DecidableEq, Repr

/-- Possessed noun form: "masculine" (mano) or "feminine" (mani).
    These labels follow @cite{dixon-2004}'s terminology; they reflect
    φ-agreement with the possessor, not the noun's own gender
    (which is always feminine). -/
inductive PossessedForm where | mascForm | femForm
  deriving DecidableEq, Repr

/-! ### Derived mano paradigm (@cite{adamson-2024} Appendix B)

The mano/mani alternation is derived from three components:

1. **MARKED features**: [PARTICIPANT] (1st/2nd person) and [MASC]
   (masculine possessor gender) are both MARKED.
2. **Impoverishment** (ex. 63): [MASC] → ∅ / [PL] and
   [MASC] → ∅ / [PARTICIPANT]. Impoverishment deletes [MASC] when
   [PL] or [PARTICIPANT] is present.
3. **VI** (A7): √MANV ↔ *mano* / [MARKED]; √MANV ↔ *mani* (elsewhere).

The derivation:
- 1st/2nd (any number): [PARTICIPANT] is MARKED → *mano*
- 3.M.SG: [MASC] survives (no [PL], no [PARTICIPANT]) → *mano*
- 3.F.SG: no MARKED feature → *mani*
- 3.M.PL: [MASC] deleted by impoverishment / [PL]; no [PARTICIPANT] → *mani*
- 3.F.PL / 3.PL: no MARKED feature → *mani*
-/

/-- Whether the possessor is a speech act participant ([PARTICIPANT]). -/
def Possessor.isParticipant (p : Possessor) : Bool :=
  p.person != .third

/-- Whether the possessor has [MASC] that survives impoverishment.
    [MASC] is deleted when [PL] or [PARTICIPANT] is present. -/
def Possessor.mascSurvivesImpoverishment (p : Possessor) : Bool :=
  match p.gender with
  | some .masc => !p.isParticipant && p.number == .sg
  | _          => false

/-- Whether any MARKED feature remains after impoverishment.
    MARKED = [PARTICIPANT] or [MASC] (if it survives). -/
def Possessor.hasMarkedFeature (p : Possessor) : Bool :=
  p.isParticipant || p.mascSurvivesImpoverishment

/-- The possessed form of *mano* 'arm', derived from MARKED features,
    impoverishment, and VI (A7). -/
def manoForm (p : Possessor) : PossessedForm :=
  if p.hasMarkedFeature then .mascForm else .femForm

/-- Table 5/6 verification: each possessor combination. -/
theorem mano_1sg : manoForm ⟨.first, .sg, none⟩ = .mascForm := rfl
theorem mano_2sg : manoForm ⟨.second, .sg, none⟩ = .mascForm := rfl
theorem mano_1pl : manoForm ⟨.first, .pl, none⟩ = .mascForm := rfl
theorem mano_2pl : manoForm ⟨.second, .pl, none⟩ = .mascForm := rfl
theorem mano_3m_sg : manoForm ⟨.third, .sg, some .masc⟩ = .mascForm := rfl
theorem mano_3f_sg : manoForm ⟨.third, .sg, some .fem⟩ = .femForm := rfl
theorem mano_3pl : manoForm ⟨.third, .pl, none⟩ = .femForm := rfl
/-- 3.M.PL: [MASC] is deleted by impoverishment in context of [PL],
    and 3rd person is not [PARTICIPANT], so no MARKED feature remains. -/
theorem mano_3m_pl : manoForm ⟨.third, .pl, some .masc⟩ = .femForm := rfl
/-- 3.F.PL: no [MASC], 3rd person not [PARTICIPANT] → elsewhere. -/
theorem mano_3f_pl : manoForm ⟨.third, .pl, some .fem⟩ = .femForm := rfl

-- ============================================================================
-- § 3: Free vs Possessed Forms (Table 4; @cite{dixon-2004} p. 312)
-- ============================================================================

/-- A subset of nouns with attested free and iPossessed forms.
    Free forms are all feminine (@cite{dixon-2004} pp. 80, 285). -/
structure FreeVsPossessed where
  free : String
  iPossessed : String
  gloss : String
  deriving DecidableEq, Repr

def freeVsPossessedForms : List FreeVsPossessed :=
  [ ⟨"faha",  "fehe/fehe-ne",    "water / liquid, juice, sap, water"⟩
  , ⟨"mato",  "mati/mato-ne",    "cord, rope, vine / cord, rope"⟩
  , ⟨"hawi",  "hawi/hawi-ne",    "path / path"⟩
  , ⟨"tona",  "tone/tone",       "bone / bone"⟩
  , ⟨"neme",  "neme/neme",       "sky / top part of"⟩
  , ⟨"bofe",  "bofe/bofe",       "ground / bottom part of"⟩
  , ⟨"tama",  "tame/teme-ne",    "grave/hole / grave/hole for"⟩ ]

-- ============================================================================
-- § 4: Bridge to Inalienability Hierarchy
-- ============================================================================

/-- All Jarawara iPossessable classes fall at or above `culturalItem` on
    the cross-linguistic inalienability hierarchy. The three highest-ranked
    categories (body parts, spatial relations, part-whole) account for
    112/175 = 64% of all iPossessable nouns. -/
theorem all_classes_inalienable :
    allClasses.all (·.inalienabilityRank.toNat ≥ InalienabilityRank.culturalItem.toNat)
    = true := by native_decide

/-- The four highest-ranked inalienable categories (body parts, spatial
    relations, part-whole, and kinship-adjacent) account for the majority:
    62 (body parts) + 17 (orientation) + 14 (whole/part) + 19 (plant parts)
    + 6 (place) = 118 / 175. -/
theorem core_inalienable_majority :
    let core := allClasses.filter (·.inalienabilityRank.toNat ≥
                  InalienabilityRank.partWhole.toNat)
    (core.map (·.memberCount)).foldl (· + ·) 0 = 118 := by native_decide

end Fragments.Jarawara
