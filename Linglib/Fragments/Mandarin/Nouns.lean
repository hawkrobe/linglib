/-
# Mandarin Chinese Noun Lexicon Fragment

Mandarin-specific noun entries and NP structure.

## Bare Arguments in Mandarin

Mandarin is a [+arg, -pred] language (Chierchia 1998):
- ALL nouns are kind-denoting by default
- No singular/plural morphology (no grammatical number)
- No definite/indefinite articles
- Classifiers required for counting/individuation
- Bare nouns freely occur as arguments

"Gǒu jiào le" (狗叫了, dog bark PERF) can mean:
- "The dog barked" (definite)
- "Dogs barked" (kind/generic)
- "A dog barked" (indefinite)

The interpretation is determined by context, not by overt morphology.

## References

- Chierchia (1998). Reference to Kinds Across Languages.
- Li & Thompson (1981). Mandarin Chinese: A Functional Reference Grammar.
-/

import Linglib.Core.Basic
import Linglib.Theories.Montague.Noun.Kind.Chierchia1998

namespace Fragments.Mandarin.Nouns

open Montague.Noun.Kind.Chierchia1998 (BlockingPrinciple NominalMapping)

-- ============================================================================
-- Mandarin NP Structure
-- ============================================================================

/--
A lexical entry for a Mandarin noun.

Note: Mandarin nouns don't have plural forms. All nouns are "mass-like"
in the sense of Chierchia (1998) - they denote kinds directly.
-/
structure NounEntry where
  /-- The noun form (hanzi) -/
  form : String
  /-- Pinyin romanization -/
  pinyin : String := ""
  /-- Classifier used with this noun -/
  classifier : Option String := some "个"  -- Default general classifier
  /-- Is this a proper name? -/
  proper : Bool := false
  deriving Repr, BEq

/--
Mandarin NP structure.

Mandarin NPs don't have grammatical number or articles.
They can have:
- Demonstratives: 这/那 (zhè/nà, this/that)
- Classifiers: required for counting
- Numerals: combined with classifiers
-/
structure NP where
  /-- The underlying noun -/
  noun : NounEntry
  /-- Is this a bare NP (no demonstrative/numeral)? -/
  isBare : Bool
  /-- Demonstrative (if any) -/
  demonstrative : Option String := none
  /-- Numeral (if any) -/
  numeral : Option Nat := none
  /-- Explicit classifier (if different from noun's default) -/
  classifierOverride : Option String := none
  deriving Repr, BEq

/-- Get the classifier for this NP -/
def NP.classifier (np : NP) : Option String :=
  np.classifierOverride <|> np.noun.classifier

-- ============================================================================
-- Mandarin Blocking Configuration
-- ============================================================================

/--
Mandarin has no articles, so no type shifts are blocked.

All nouns can freely occur as arguments with various readings:
- Kind/generic: "Gǒu shì dòngwù" (Dogs are animals)
- Definite: "Gǒu zài wàimiàn" (The dog is outside)
- Indefinite: "Wǒ kàn dào gǒu le" (I saw a dog)

The interpretation comes from context, prosody, and information structure.
-/
def mandarinBlocking : BlockingPrinciple :=
  { determiners := []  -- No articles
  , iotaBlocked := false  -- No "the" → ι available covertly
  , existsBlocked := false  -- No "a" → ∃ available covertly
  , downBlocked := false }  -- ∩ always available

/-- Mandarin is a [+arg, -pred] language -/
def mandarinMapping : NominalMapping := .argOnly

-- ============================================================================
-- NP Constructors
-- ============================================================================

/-- Create a bare NP -/
def bareNP (n : NounEntry) : NP :=
  { noun := n, isBare := true }

/-- Create an NP with demonstrative 这 (zhè, this) -/
def zheNP (n : NounEntry) : NP :=
  { noun := n, isBare := false, demonstrative := some "这" }

/-- Create an NP with demonstrative 那 (nà, that) -/
def naNP (n : NounEntry) : NP :=
  { noun := n, isBare := false, demonstrative := some "那" }

/-- Create an NP with a numeral -/
def numNP (n : NounEntry) (num : Nat) : NP :=
  { noun := n, isBare := false, numeral := some num }

-- ============================================================================
-- Common Nouns
-- ============================================================================

def gou : NounEntry := { form := "狗", pinyin := "gǒu", classifier := some "只" }  -- dog
def mao : NounEntry := { form := "猫", pinyin := "māo", classifier := some "只" }  -- cat
def ren : NounEntry := { form := "人", pinyin := "rén", classifier := some "个" }  -- person
def shu : NounEntry := { form := "书", pinyin := "shū", classifier := some "本" }  -- book
def che : NounEntry := { form := "车", pinyin := "chē", classifier := some "辆" }  -- car
def niao : NounEntry := { form := "鸟", pinyin := "niǎo", classifier := some "只" }  -- bird
def hua : NounEntry := { form := "花", pinyin := "huā", classifier := some "朵" }  -- flower
def shui : NounEntry := { form := "水", pinyin := "shuǐ", classifier := none }  -- water (mass)
def fan : NounEntry := { form := "饭", pinyin := "fàn", classifier := none }  -- rice/meal (mass)
def nuer : NounEntry := { form := "女儿", pinyin := "nǚ'ér", classifier := some "个" }  -- daughter
def erzi : NounEntry := { form := "儿子", pinyin := "érzi", classifier := some "个" }  -- son
def xuesheng : NounEntry := { form := "学生", pinyin := "xuésheng", classifier := some "个" }  -- student
def laoshi : NounEntry := { form := "老师", pinyin := "lǎoshī", classifier := some "位" }  -- teacher (polite cl.)
def pengyou : NounEntry := { form := "朋友", pinyin := "péngyou", classifier := some "个" }  -- friend

-- ============================================================================
-- Bridging-Relevant Nouns (Ahn & Zhu 2025)
-- ============================================================================

/-!
## Part-Whole Nouns

These nouns denote parts of larger wholes, enabling part-whole bridging:
"我买了一辆车。座椅坏了。" (I bought a car. The seat was broken.)

In part-whole bridging, uniqueness is mediated by the whole:
- There is typically ONE seat (of the relevant kind) per car
- Uniqueness presupposition satisfied via mereological relation
-/

def zuoyi : NounEntry := { form := "座椅", pinyin := "zuòyǐ", classifier := some "个" }  -- seat
def fangxiangpan : NounEntry := { form := "方向盘", pinyin := "fāngxiàngpán", classifier := some "个" }  -- steering wheel
def lunzi : NounEntry := { form := "轮子", pinyin := "lúnzi", classifier := some "个" }  -- wheel
def fengmian : NounEntry := { form := "封面", pinyin := "fēngmiàn", classifier := some "个" }  -- cover (of book)

/-!
## Relational Nouns

These nouns denote entities defined by a relation to another entity,
enabling relational bridging:
"我读了一本书。作者很有名。" (I read a book. The author was famous.)

In relational bridging, familiarity (not uniqueness) is the key:
- The author must be contextually salient
- Mandarin bare nouns and *na*+CL both license this

**Ahn & Zhu's Analysis of *na***:
⟦na⟧ = λsr.λP.λz : ιx[π(P)(z)(x)(sr)]
- Introduces an external relatum sr
- Acts as a relationalizing operator
- Allows relational bridging for all noun types
-/

def zuozhe : NounEntry := { form := "作者", pinyin := "zuòzhě", classifier := some "位" }  -- author
def muqin : NounEntry := { form := "母亲", pinyin := "mǔqīn", classifier := some "位" }  -- mother
def fuqin : NounEntry := { form := "父亲", pinyin := "fùqīn", classifier := some "位" }  -- father
def laobanniang : NounEntry := { form := "老板娘", pinyin := "lǎobǎnniáng", classifier := some "位" }  -- proprietress
def laoban : NounEntry := { form := "老板", pinyin := "lǎobǎn", classifier := some "位" }  -- boss/owner

-- ============================================================================
-- Proper Names
-- ============================================================================

def zhangsan : NounEntry := { form := "张三", pinyin := "Zhāng Sān", proper := true }
def lisi : NounEntry := { form := "李四", pinyin := "Lǐ Sì", proper := true }
def xiaoming : NounEntry := { form := "小明", pinyin := "Xiǎo Míng", proper := true }

-- ============================================================================
-- Lookup
-- ============================================================================

def allNouns : List NounEntry := [
  gou, mao, ren, shu, che, niao, hua, shui, fan,
  nuer, erzi, xuesheng, laoshi, pengyou,
  -- Part-whole nouns (Ahn & Zhu 2025)
  zuoyi, fangxiangpan, lunzi, fengmian,
  -- Relational nouns (Ahn & Zhu 2025)
  zuozhe, muqin, fuqin, laobanniang, laoban,
  -- Proper names
  zhangsan, lisi, xiaoming
]

def lookup (form : String) : Option NounEntry :=
  allNouns.find? fun n => n.form == form

-- ============================================================================
-- Bare Argument Licensing
-- ============================================================================

/-- In Mandarin, all bare NPs are licensed -/
def bareNPLicensed : Bool := true

-- Verify
example : bareNPLicensed = true := rfl

-- ============================================================================
-- Example NPs
-- ============================================================================

/-- "狗" as bare NP -/
def gouNP : NP := bareNP gou

/-- "水" as bare NP -/
def shuiNP : NP := bareNP shui

/-- "这狗" (this dog) -/
def zheGou : NP := zheNP gou

/-- "三本书" (three books) -/
def sanBenShu : NP := numNP shu 3

-- Examples verifying structure
example : gouNP.isBare = true := rfl
example : zheGou.isBare = false := rfl
example : sanBenShu.numeral = some 3 := rfl

end Fragments.Mandarin.Nouns
