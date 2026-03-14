import Linglib.Theories.Morphology.DM.NominalStructure
import Linglib.Phenomena.Possession.Typology

/-!
# Jarawara Possessed Nouns @cite{adamson-2024}

Inalienably possessed noun classes and the *mano* 'arm' paradigm
in Jarawara (Arawan), drawn from @cite{adamson-2024} §3.2 and
Dixon 2004.

## Key facts

- Jarawara has two genders: masculine (marked, [+MASC] on n) and
  feminine (unmarked, plain n)
- All ~175 iPossessable nouns are feminine when used "free" (without
  a possessor), consistent with being licensed by plain n
- iPossession is expressed by direct juxtaposition; aPossession uses
  the marker *kaa*
- The "masculine"/"feminine" alternations on possessed nouns reflect
  φ-agreement with the iPossessor, not gender assignment

## Semantic Classification (Dixon 2004:311)

The iPossessable class maps onto the upper portion of the
cross-linguistic inalienability hierarchy from `Possession.Typology`.
-/

namespace Fragments.Jarawara

open Phenomena.Possession.Typology

-- ============================================================================
-- § 1: Semantic Classes of iPossessable Nouns (Table 3)
-- ============================================================================

/-- Semantic classification of Jarawara iPossessable nouns
    (Dixon 2004:311; @cite{adamson-2024} Table 3). -/
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

/-- Total iPossessable nouns: ~175 (Dixon 2004:310). -/
theorem total_ipossessable :
    (allClasses.map (·.memberCount)).foldl (· + ·) 0 = 175 := by native_decide

-- ============================================================================
-- § 2: *mano* 'arm' Paradigm (Table 5; Dixon 2004:315)
-- ============================================================================

/-- Person–number features of a Jarawara possessor. -/
inductive Person where | first | second | third deriving DecidableEq, BEq, Repr
inductive Number where | sg | pl deriving DecidableEq, BEq, Repr
inductive PossGender where | masc | fem deriving DecidableEq, BEq, Repr

/-- A possessor with full φ-features. Third person distinguishes gender;
    first and second person can be singular or plural, with clusivity
    for first person plural. -/
structure Possessor where
  person : Person
  number : Number
  gender : Option PossGender := none  -- only for 3rd person
  deriving DecidableEq, BEq, Repr

/-- Possessed noun form: "masculine" (mano) or "feminine" (mani).
    These labels follow Dixon's (2004) terminology; they reflect
    φ-agreement with the possessor, not the noun's own gender
    (which is always feminine). -/
inductive PossessedForm where | mascForm | femForm
  deriving DecidableEq, BEq, Repr

/-- The possessed form of *mano* 'arm', from Table 5.

    The form tracks the possessor's gender for 3rd person:
    3.M → masculine form; 3.F / 3.PL → feminine form.
    1st/2nd person always get the masculine form. -/
def manoForm (p : Possessor) : PossessedForm :=
  match p.person, p.number, p.gender with
  | .third, .sg, some .fem  => .femForm   -- Jane mani
  | .third, .pl, _          => .femForm   -- mee mani
  | _, _, _                  => .mascForm  -- all others: mano

/-- Table 5 verification: each possessor combination. -/
theorem mano_1sg : manoForm ⟨.first, .sg, none⟩ = .mascForm := rfl
theorem mano_2sg : manoForm ⟨.second, .sg, none⟩ = .mascForm := rfl
theorem mano_1pl : manoForm ⟨.first, .pl, none⟩ = .mascForm := rfl
theorem mano_2pl : manoForm ⟨.second, .pl, none⟩ = .mascForm := rfl
theorem mano_3m_sg : manoForm ⟨.third, .sg, some .masc⟩ = .mascForm := rfl
theorem mano_3f_sg : manoForm ⟨.third, .sg, some .fem⟩ = .femForm := rfl
theorem mano_3pl : manoForm ⟨.third, .pl, none⟩ = .femForm := rfl

-- ============================================================================
-- § 3: Free vs Possessed Forms (Table 4; Dixon 2004:312)
-- ============================================================================

/-- A subset of nouns with attested free and iPossessed forms.
    Free forms are all feminine (Dixon 2004:80, 285). -/
structure FreeVsPossessed where
  free : String
  iPossessed : String
  gloss : String
  deriving DecidableEq, BEq, Repr

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

/-- The three core inalienable categories account for the majority. -/
theorem core_inalienable_majority :
    let core := allClasses.filter (·.inalienabilityRank.toNat ≥
                  InalienabilityRank.spatialRelation.toNat)
    (core.map (·.memberCount)).foldl (· + ·) 0 = 112 := by native_decide

end Fragments.Jarawara
