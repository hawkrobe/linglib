import Linglib.Core.Basic
import Linglib.Core.NounCategorization
import Linglib.Fragments.Mandarin.Classifiers
import Linglib.Theories.Semantics.Lexical.Noun.Kind.Chierchia1998

/-!
# Mandarin Chinese Noun Lexicon Fragment

Mandarin-specific noun entries. Mandarin is [+arg, -pred] (Chierchia 1998):
all nouns are kind-denoting by default, no number morphology, no articles,
classifiers required for counting, bare nouns freely occur as arguments.

Classifiers are now typed `ClassifierEntry` values from the classifier
lexicon (`Fragments.Mandarin.Classifiers`), replacing the previous
unstructured `Option String` representation. This enables verification
of Aikhenvald's semantic generalizations about classifier selection.
-/

namespace Fragments.Mandarin.Nouns

open Core.NounCategorization (ClassifierEntry)
open Fragments.Mandarin.Classifiers
open Semantics.Lexical.Noun.Kind.Chierchia1998 (BlockingPrinciple NominalMapping)

/-- A lexical entry for a Mandarin noun.

    The `classifier` field points to a typed `ClassifierEntry` from the
    classifier lexicon, carrying semantic information about why that
    classifier is selected (animacy, shape, function, etc.). -/
structure NounEntry where
  form : String
  pinyin : String := ""
  classifier : Option ClassifierEntry := some ge
  proper : Bool := false
  deriving Repr, BEq

/-- Mandarin NP structure (no grammatical number or articles). -/
structure NP where
  noun : NounEntry
  isBare : Bool
  demonstrative : Option String := none
  numeral : Option Nat := none
  classifierOverride : Option ClassifierEntry := none
  deriving Repr, BEq

def NP.classifier (np : NP) : Option ClassifierEntry :=
  np.classifierOverride <|> np.noun.classifier

/-- The form string of the classifier (for display). -/
def NP.classifierForm (np : NP) : Option String :=
  np.classifier.map (·.form)

/-- Mandarin has no articles, so no type shifts are blocked. -/
def mandarinBlocking : BlockingPrinciple :=
  { determiners := []
  , iotaBlocked := false
  , existsBlocked := false
  , downBlocked := false }

def mandarinMapping : NominalMapping := .argOnly

def bareNP (n : NounEntry) : NP :=
  { noun := n, isBare := true }

def zheNP (n : NounEntry) : NP :=
  { noun := n, isBare := false, demonstrative := some "这" }

def naNP (n : NounEntry) : NP :=
  { noun := n, isBare := false, demonstrative := some "那" }

def numNP (n : NounEntry) (num : Nat) : NP :=
  { noun := n, isBare := false, numeral := some num }

-- ============================================================================
-- Common nouns
-- ============================================================================

-- Animals (只 zhī — small animals)
def gou : NounEntry := { form := "狗", pinyin := "gǒu", classifier := some zhi }
def mao : NounEntry := { form := "猫", pinyin := "māo", classifier := some zhi }
def niao : NounEntry := { form := "鸟", pinyin := "niǎo", classifier := some zhi }

-- People (个 gè default / 位 wèi honorific)
def ren : NounEntry := { form := "人", pinyin := "rén", classifier := some ge }
def xuesheng : NounEntry := { form := "学生", pinyin := "xuésheng", classifier := some ge }
def pengyou : NounEntry := { form := "朋友", pinyin := "péngyou", classifier := some ge }
def laoshi : NounEntry := { form := "老师", pinyin := "lǎoshī", classifier := some wei }
def nuer : NounEntry := { form := "女儿", pinyin := "nǚ'ér", classifier := some ge }
def erzi : NounEntry := { form := "儿子", pinyin := "érzi", classifier := some ge }

-- Objects (various classifiers by shape/function)
def shu : NounEntry := { form := "书", pinyin := "shū", classifier := some ben }
def che : NounEntry := { form := "车", pinyin := "chē", classifier := some liang }
def hua : NounEntry := { form := "花", pinyin := "huā", classifier := some duo }

-- Mass nouns (no classifier)
def shui : NounEntry := { form := "水", pinyin := "shuǐ", classifier := none }
def fan : NounEntry := { form := "饭", pinyin := "fàn", classifier := none }

-- Part-whole nouns
def zuoyi : NounEntry := { form := "座椅", pinyin := "zuòyǐ", classifier := some ge }
def fangxiangpan : NounEntry := { form := "方向盘", pinyin := "fāngxiàngpán", classifier := some ge }
def lunzi : NounEntry := { form := "轮子", pinyin := "lúnzi", classifier := some ge }
def fengmian : NounEntry := { form := "封面", pinyin := "fēngmiàn", classifier := some ge }

-- Relational nouns (位 wèi for human, honorific)
def zuozhe : NounEntry := { form := "作者", pinyin := "zuòzhě", classifier := some wei }
def muqin : NounEntry := { form := "母亲", pinyin := "mǔqīn", classifier := some wei }
def fuqin : NounEntry := { form := "父亲", pinyin := "fùqīn", classifier := some wei }
def laobanniang : NounEntry := { form := "老板娘", pinyin := "lǎobǎnniáng", classifier := some wei }
def laoban : NounEntry := { form := "老板", pinyin := "lǎobǎn", classifier := some wei }

-- Proper names
def zhangsan : NounEntry := { form := "张三", pinyin := "Zhāng Sān", proper := true }
def lisi : NounEntry := { form := "李四", pinyin := "Lǐ Sì", proper := true }
def xiaoming : NounEntry := { form := "小明", pinyin := "Xiǎo Míng", proper := true }

-- ============================================================================
-- Lexicon
-- ============================================================================

def allNouns : List NounEntry := [
  gou, mao, niao, ren, xuesheng, pengyou, laoshi, nuer, erzi,
  shu, che, hua, shui, fan,
  zuoyi, fangxiangpan, lunzi, fengmian,
  zuozhe, muqin, fuqin, laobanniang, laoban,
  zhangsan, lisi, xiaoming
]

def lookup (form : String) : Option NounEntry :=
  allNouns.find? λ n => n.form == form

def bareNPLicensed : Bool := true

example : bareNPLicensed = true := rfl

-- ============================================================================
-- Verification: classifier selection is semantically coherent
-- ============================================================================

/-- All animal nouns take the animal classifier 只. -/
theorem animals_take_zhi :
    [gou, mao, niao].all (·.classifier == some zhi) = true := by native_decide

/-- Honorific-human nouns take 位. -/
theorem honorific_humans_take_wei :
    [laoshi, zuozhe, muqin, fuqin].all (·.classifier == some wei) = true := by
  native_decide

/-- Books take the bound-volume classifier 本. -/
theorem books_take_ben : shu.classifier = some ben := rfl

/-- Vehicles take the vehicle classifier 辆. -/
theorem vehicles_take_liang : che.classifier = some liang := rfl

/-- Mass nouns have no classifier. -/
theorem mass_nouns_no_classifier :
    [shui, fan].all (·.classifier == none) = true := by native_decide

-- ============================================================================
-- Example NPs
-- ============================================================================

def gouNP : NP := bareNP gou
def shuiNP : NP := bareNP shui
def zheGou : NP := zheNP gou
def sanBenShu : NP := numNP shu 3

example : gouNP.isBare = true := rfl
example : zheGou.isBare = false := rfl
example : sanBenShu.numeral = some 3 := rfl
example : gouNP.classifierForm = some "只" := rfl
example : sanBenShu.classifierForm = some "本" := rfl

end Fragments.Mandarin.Nouns
