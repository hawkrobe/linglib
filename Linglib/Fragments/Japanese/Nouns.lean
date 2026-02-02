/-
# Japanese Noun Lexicon Fragment

Japanese-specific noun entries and NP structure.

## Bare Arguments in Japanese

Japanese is a [+arg, -pred] language (like Mandarin):
- No definite/indefinite articles
- No obligatory number morphology (though plural markers exist)
- Classifiers required for counting
- Bare nouns freely occur as arguments

"Inu-ga hoeta" (犬が吠えた, dog-NOM barked) can mean:
- "The dog barked" (definite)
- "Dogs barked" (kind/generic)
- "A dog barked" (indefinite)

## Differences from Mandarin

- Japanese has optional plural markers (-tachi for people, -ra informal)
- Case particles (ga, o, ni) mark grammatical relations
- Topic marker -wa creates information structure distinctions

## References

- Chierchia (1998). Reference to Kinds Across Languages.
- Kuno (1973). The Structure of the Japanese Language.
- Nakanishi & Tomioka (2004). Japanese Plurals are Exceptional.
-/

import Linglib.Core.Basic
import Linglib.Theories.Montague.Lexicon.Kinds

namespace Fragments.Japanese.Nouns

open Montague.Lexicon.Kinds (BlockingPrinciple NominalMapping)

-- ============================================================================
-- Japanese NP Structure
-- ============================================================================

/--
A lexical entry for a Japanese noun.

Japanese nouns have optional plural marking (-tachi for people).
-/
structure NounEntry where
  /-- The noun form (kanji/hiragana) -/
  form : String
  /-- Romaji romanization -/
  romaji : String := ""
  /-- Optional plural form (mainly for people: -tachi) -/
  pluralForm : Option String := none
  /-- Classifier used with this noun -/
  classifier : Option String := some "つ"  -- Default general classifier
  /-- Is this a proper name? -/
  proper : Bool := false
  deriving Repr, BEq

/-- Japanese case particles -/
inductive CaseParticle where
  | ga   -- Nominative (subject marker)
  | wo   -- Accusative (object marker, written を)
  | ni   -- Dative/locative
  | de   -- Instrumental/locative
  | no   -- Genitive
  | wa   -- Topic marker (not strictly case)
  deriving DecidableEq, Repr, BEq

/--
Japanese NP structure.

Japanese NPs don't have articles but have case particles.
-/
structure NP where
  /-- The underlying noun -/
  noun : NounEntry
  /-- Is this a bare NP (no demonstrative/numeral)? -/
  isBare : Bool
  /-- Case particle (if any) -/
  caseParticle : Option CaseParticle := none
  /-- Demonstrative (if any): この/その/あの -/
  demonstrative : Option String := none
  /-- Numeral (if any) -/
  numeral : Option Nat := none
  /-- Use plural form? -/
  usePlural : Bool := false
  deriving Repr, BEq

-- ============================================================================
-- Japanese Blocking Configuration
-- ============================================================================

/--
Japanese has no articles, so no type shifts are blocked.
-/
def japaneseBlocking : BlockingPrinciple :=
  { determiners := []
  , iotaBlocked := false
  , existsBlocked := false
  , downBlocked := false }

/-- Japanese is a [+arg] language -/
def japaneseMapping : NominalMapping := .argOnly

-- ============================================================================
-- NP Constructors
-- ============================================================================

/-- Create a bare NP -/
def bareNP (n : NounEntry) : NP :=
  { noun := n, isBare := true }

/-- Create an NP with nominative case (ga) -/
def gaNP (n : NounEntry) : NP :=
  { noun := n, isBare := true, caseParticle := some .ga }

/-- Create an NP with accusative case (wo) -/
def woNP (n : NounEntry) : NP :=
  { noun := n, isBare := true, caseParticle := some .wo }

/-- Create an NP with topic marker (wa) -/
def waNP (n : NounEntry) : NP :=
  { noun := n, isBare := true, caseParticle := some .wa }

/-- Create an NP with demonstrative この (kono, this) -/
def konoNP (n : NounEntry) : NP :=
  { noun := n, isBare := false, demonstrative := some "この" }

/-- Create an NP with demonstrative その (sono, that) -/
def sonoNP (n : NounEntry) : NP :=
  { noun := n, isBare := false, demonstrative := some "その" }

-- ============================================================================
-- Common Nouns
-- ============================================================================

def inu : NounEntry := { form := "犬", romaji := "inu", classifier := some "匹" }  -- dog
def neko : NounEntry := { form := "猫", romaji := "neko", classifier := some "匹" }  -- cat
def hito : NounEntry := { form := "人", romaji := "hito", pluralForm := some "人たち", classifier := some "人" }  -- person
def hon : NounEntry := { form := "本", romaji := "hon", classifier := some "冊" }  -- book
def kuruma : NounEntry := { form := "車", romaji := "kuruma", classifier := some "台" }  -- car
def tori : NounEntry := { form := "鳥", romaji := "tori", classifier := some "羽" }  -- bird
def hana : NounEntry := { form := "花", romaji := "hana", classifier := some "本" }  -- flower
def mizu : NounEntry := { form := "水", romaji := "mizu", classifier := none }  -- water (mass)
def gohan : NounEntry := { form := "ご飯", romaji := "gohan", classifier := none }  -- rice/meal (mass)
def musume : NounEntry := { form := "娘", romaji := "musume", pluralForm := some "娘たち" }  -- daughter
def musuko : NounEntry := { form := "息子", romaji := "musuko", pluralForm := some "息子たち" }  -- son
def gakusei : NounEntry := { form := "学生", romaji := "gakusei", pluralForm := some "学生たち" }  -- student
def sensei : NounEntry := { form := "先生", romaji := "sensei", pluralForm := some "先生たち" }  -- teacher
def tomodachi : NounEntry := { form := "友達", romaji := "tomodachi" }  -- friend

-- ============================================================================
-- Proper Names
-- ============================================================================

def taro : NounEntry := { form := "太郎", romaji := "Tarō", proper := true }
def hanako : NounEntry := { form := "花子", romaji := "Hanako", proper := true }
def yamada : NounEntry := { form := "山田", romaji := "Yamada", proper := true }
def tanaka : NounEntry := { form := "田中", romaji := "Tanaka", proper := true }

-- ============================================================================
-- Lookup
-- ============================================================================

def allNouns : List NounEntry := [
  inu, neko, hito, hon, kuruma, tori, hana, mizu, gohan,
  musume, musuko, gakusei, sensei, tomodachi,
  taro, hanako, yamada, tanaka
]

def lookup (form : String) : Option NounEntry :=
  allNouns.find? fun n => n.form == form || n.pluralForm == some form

-- ============================================================================
-- Bare Argument Licensing
-- ============================================================================

/-- In Japanese, all bare NPs are licensed -/
def bareNPLicensed : Bool := true

-- Verify
example : bareNPLicensed = true := rfl

-- ============================================================================
-- Example NPs
-- ============================================================================

/-- "犬" as bare NP -/
def inuNP : NP := bareNP inu

/-- "犬が" (dog-NOM) -/
def inuGa : NP := gaNP inu

/-- "犬を" (dog-ACC) -/
def inuWo : NP := woNP inu

/-- "この犬" (this dog) -/
def konoInu : NP := konoNP inu

-- Examples verifying structure
example : inuNP.isBare = true := rfl
example : inuGa.caseParticle = some .ga := rfl
example : konoInu.isBare = false := rfl

end Fragments.Japanese.Nouns
