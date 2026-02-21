import Linglib.Core.Word
import Linglib.Core.NounCategorization
import Linglib.Fragments.Japanese.Classifiers
import Linglib.Theories.Semantics.Lexical.Noun.Kind.Chierchia1998

/-!
# Japanese Noun Lexicon Fragment

Japanese-specific noun entries and NP structure. Japanese is [+arg, -pred]:
no articles, optional number morphology, classifiers for counting, bare
nouns freely occur as arguments with multiple interpretations.

Classifiers are typed `ClassifierEntry` values from the classifier lexicon
(`Fragments.Japanese.Classifiers`).
-/

namespace Fragments.Japanese.Nouns

open Core.NounCategorization (ClassifierEntry)
open Fragments.Japanese.Classifiers
open Semantics.Lexical.Noun.Kind.Chierchia1998 (BlockingPrinciple NominalMapping)

/-- A lexical entry for a Japanese noun. -/
structure NounEntry where
  form : String
  romaji : String := ""
  pluralForm : Option String := none
  classifier : Option ClassifierEntry := some tsu
  proper : Bool := false
  deriving Repr, BEq

/-- Japanese case particles. -/
inductive CaseParticle where
  | ga | wo | ni | de | no | wa
  deriving DecidableEq, Repr, BEq

/-- Japanese NP structure (no articles, but has case particles). -/
structure NP where
  noun : NounEntry
  isBare : Bool
  caseParticle : Option CaseParticle := none
  demonstrative : Option String := none
  numeral : Option Nat := none
  usePlural : Bool := false
  deriving Repr, BEq

/-- Japanese has no articles, so no type shifts are blocked. -/
def japaneseBlocking : BlockingPrinciple :=
  { determiners := []
  , iotaBlocked := false
  , existsBlocked := false
  , downBlocked := false }

def japaneseMapping : NominalMapping := .argOnly

def bareNP (n : NounEntry) : NP :=
  { noun := n, isBare := true }

def gaNP (n : NounEntry) : NP :=
  { noun := n, isBare := true, caseParticle := some .ga }

def woNP (n : NounEntry) : NP :=
  { noun := n, isBare := true, caseParticle := some .wo }

def waNP (n : NounEntry) : NP :=
  { noun := n, isBare := true, caseParticle := some .wa }

def konoNP (n : NounEntry) : NP :=
  { noun := n, isBare := false, demonstrative := some "この" }

def sonoNP (n : NounEntry) : NP :=
  { noun := n, isBare := false, demonstrative := some "その" }

-- ============================================================================
-- Common nouns
-- ============================================================================

-- Animals (匹 hiki — small animals)
def inu : NounEntry := { form := "犬", romaji := "inu", classifier := some hiki }
def neko : NounEntry := { form := "猫", romaji := "neko", classifier := some hiki }

-- People (人 nin)
def hito : NounEntry := { form := "人", romaji := "hito", pluralForm := some "人たち", classifier := some nin }

-- Objects (various classifiers)
def hon : NounEntry := { form := "本", romaji := "hon", classifier := some satsu }
def kuruma : NounEntry := { form := "車", romaji := "kuruma", classifier := some dai }
def tori : NounEntry := { form := "鳥", romaji := "tori", classifier := some wa }
def hana : NounEntry := { form := "花", romaji := "hana", classifier := some hon' }

-- Mass nouns (no classifier)
def mizu : NounEntry := { form := "水", romaji := "mizu", classifier := none }
def gohan : NounEntry := { form := "ご飯", romaji := "gohan", classifier := none }

-- People with optional plurals
def musume : NounEntry := { form := "娘", romaji := "musume", pluralForm := some "娘たち" }
def musuko : NounEntry := { form := "息子", romaji := "musuko", pluralForm := some "息子たち" }
def gakusei : NounEntry := { form := "学生", romaji := "gakusei", pluralForm := some "学生たち" }
def sensei : NounEntry := { form := "先生", romaji := "sensei", pluralForm := some "先生たち" }
def tomodachi : NounEntry := { form := "友達", romaji := "tomodachi" }

-- Proper names
def taro : NounEntry := { form := "太郎", romaji := "Tarō", proper := true }
def hanako : NounEntry := { form := "花子", romaji := "Hanako", proper := true }
def yamada : NounEntry := { form := "山田", romaji := "Yamada", proper := true }
def tanaka : NounEntry := { form := "田中", romaji := "Tanaka", proper := true }

-- ============================================================================
-- Lexicon
-- ============================================================================

def allNouns : List NounEntry := [
  inu, neko, hito, hon, kuruma, tori, hana, mizu, gohan,
  musume, musuko, gakusei, sensei, tomodachi,
  taro, hanako, yamada, tanaka
]

def lookup (form : String) : Option NounEntry :=
  allNouns.find? λ n => n.form == form || n.pluralForm == some form

def bareNPLicensed : Bool := true

example : bareNPLicensed = true := rfl

-- ============================================================================
-- Verification
-- ============================================================================

/-- Small animals take 匹. -/
theorem animals_take_hiki :
    [inu, neko].all (·.classifier == some hiki) = true := by native_decide

/-- Birds take 羽. -/
theorem birds_take_wa : tori.classifier = some wa := rfl

/-- Books take 冊. -/
theorem books_take_satsu : hon.classifier = some satsu := rfl

/-- Vehicles/machines take 台. -/
theorem vehicles_take_dai : kuruma.classifier = some dai := rfl

/-- People take 人. -/
theorem people_take_nin : hito.classifier = some nin := rfl

/-- Mass nouns have no classifier. -/
theorem mass_nouns_no_classifier :
    [mizu, gohan].all (·.classifier == none) = true := by native_decide

-- ============================================================================
-- Example NPs
-- ============================================================================

def inuNP : NP := bareNP inu
def inuGa : NP := gaNP inu
def inuWo : NP := woNP inu
def konoInu : NP := konoNP inu

example : inuNP.isBare = true := rfl
example : inuGa.caseParticle = some .ga := rfl
example : konoInu.isBare = false := rfl

end Fragments.Japanese.Nouns
