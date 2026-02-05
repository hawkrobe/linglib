import Linglib.Core.Basic
import Linglib.Theories.TruthConditional.Noun.Kind.Chierchia1998

/-!
# Mandarin Chinese Noun Lexicon Fragment

Mandarin-specific noun entries. Mandarin is [+arg, -pred] (Chierchia 1998):
all nouns are kind-denoting by default, no number morphology, no articles,
classifiers required for counting, bare nouns freely occur as arguments.
-/

namespace Fragments.Mandarin.Nouns

open TruthConditional.Noun.Kind.Chierchia1998 (BlockingPrinciple NominalMapping)

/-- A lexical entry for a Mandarin noun (no plural forms, kind-denoting). -/
structure NounEntry where
  form : String
  pinyin : String := ""
  classifier : Option String := some "个"
  proper : Bool := false
  deriving Repr, BEq

/-- Mandarin NP structure (no grammatical number or articles). -/
structure NP where
  noun : NounEntry
  isBare : Bool
  demonstrative : Option String := none
  numeral : Option Nat := none
  classifierOverride : Option String := none
  deriving Repr, BEq

def NP.classifier (np : NP) : Option String :=
  np.classifierOverride <|> np.noun.classifier

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

-- Common nouns
def gou : NounEntry := { form := "狗", pinyin := "gǒu", classifier := some "只" }
def mao : NounEntry := { form := "猫", pinyin := "māo", classifier := some "只" }
def ren : NounEntry := { form := "人", pinyin := "rén", classifier := some "个" }
def shu : NounEntry := { form := "书", pinyin := "shū", classifier := some "本" }
def che : NounEntry := { form := "车", pinyin := "chē", classifier := some "辆" }
def niao : NounEntry := { form := "鸟", pinyin := "niǎo", classifier := some "只" }
def hua : NounEntry := { form := "花", pinyin := "huā", classifier := some "朵" }
def shui : NounEntry := { form := "水", pinyin := "shuǐ", classifier := none }
def fan : NounEntry := { form := "饭", pinyin := "fàn", classifier := none }
def nuer : NounEntry := { form := "女儿", pinyin := "nǚ'ér", classifier := some "个" }
def erzi : NounEntry := { form := "儿子", pinyin := "érzi", classifier := some "个" }
def xuesheng : NounEntry := { form := "学生", pinyin := "xuésheng", classifier := some "个" }
def laoshi : NounEntry := { form := "老师", pinyin := "lǎoshī", classifier := some "位" }
def pengyou : NounEntry := { form := "朋友", pinyin := "péngyou", classifier := some "个" }

-- Part-whole nouns (Ahn & Zhu 2025)
def zuoyi : NounEntry := { form := "座椅", pinyin := "zuòyǐ", classifier := some "个" }
def fangxiangpan : NounEntry := { form := "方向盘", pinyin := "fāngxiàngpán", classifier := some "个" }
def lunzi : NounEntry := { form := "轮子", pinyin := "lúnzi", classifier := some "个" }
def fengmian : NounEntry := { form := "封面", pinyin := "fēngmiàn", classifier := some "个" }

-- Relational nouns (Ahn & Zhu 2025)
def zuozhe : NounEntry := { form := "作者", pinyin := "zuòzhě", classifier := some "位" }
def muqin : NounEntry := { form := "母亲", pinyin := "mǔqīn", classifier := some "位" }
def fuqin : NounEntry := { form := "父亲", pinyin := "fùqīn", classifier := some "位" }
def laobanniang : NounEntry := { form := "老板娘", pinyin := "lǎobǎnniáng", classifier := some "位" }
def laoban : NounEntry := { form := "老板", pinyin := "lǎobǎn", classifier := some "位" }

-- Proper names
def zhangsan : NounEntry := { form := "张三", pinyin := "Zhāng Sān", proper := true }
def lisi : NounEntry := { form := "李四", pinyin := "Lǐ Sì", proper := true }
def xiaoming : NounEntry := { form := "小明", pinyin := "Xiǎo Míng", proper := true }

def allNouns : List NounEntry := [
  gou, mao, ren, shu, che, niao, hua, shui, fan,
  nuer, erzi, xuesheng, laoshi, pengyou,
  zuoyi, fangxiangpan, lunzi, fengmian,
  zuozhe, muqin, fuqin, laobanniang, laoban,
  zhangsan, lisi, xiaoming
]

def lookup (form : String) : Option NounEntry :=
  allNouns.find? λ n => n.form == form

def bareNPLicensed : Bool := true

example : bareNPLicensed = true := rfl

def gouNP : NP := bareNP gou
def shuiNP : NP := bareNP shui
def zheGou : NP := zheNP gou
def sanBenShu : NP := numNP shu 3

example : gouNP.isBare = true := rfl
example : zheGou.isBare = false := rfl
example : sanBenShu.numeral = some 3 := rfl

end Fragments.Mandarin.Nouns
