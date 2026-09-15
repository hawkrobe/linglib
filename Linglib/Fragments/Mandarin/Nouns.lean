import Linglib.Syntax.Category.Noun.Basic
import Linglib.Fragments.Mandarin.Classifiers
import Linglib.Semantics.Genericity.NominalMappingParameter

/-!
# Mandarin nouns

The Mandarin noun as a lexical entry: the root `Noun` with its pinyin, the classifier it counts
with, and whether it is a proper name. Mandarin is [+arg, −pred] ([chierchia-1998]): nouns
denote kinds, there is no number morphology and no article, so no covert shift is blocked and
every bare noun is an argument; counting goes through a classifier
(`Mandarin.Classifiers`).

## References

* [chierchia-1998]
-/

namespace Mandarin.Nouns

open Mandarin.Classifiers
open Genericity

/-- A Mandarin noun: the root entry with its pinyin, the classifier it counts with, if any, and
whether it is a proper name. -/
structure Noun extends _root_.Noun where
  /-- The pinyin. -/
  pinyin : String
  /-- The classifier the noun counts with; none for a mass noun. -/
  classifier : Option Classifier := some ge
  /-- Whether the entry is a proper name. -/
  proper : Bool := false
  deriving DecidableEq, Repr

/-! ### Common nouns -/

def gou : Noun := { form := "狗", gloss := "dog", pinyin := "gǒu", classifier := some zhi }
def mao : Noun := { form := "猫", gloss := "cat", pinyin := "māo", classifier := some zhi }
def niao : Noun := { form := "鸟", gloss := "bird", pinyin := "niǎo", classifier := some zhi }
def ren : Noun := { form := "人", gloss := "person", pinyin := "rén" }
def xuesheng : Noun := { form := "学生", gloss := "student", pinyin := "xuésheng" }
def pengyou : Noun := { form := "朋友", gloss := "friend", pinyin := "péngyou" }
def laoshi : Noun :=
  { form := "老师", gloss := "teacher", pinyin := "lǎoshī", classifier := some wei }
def nuer : Noun := { form := "女儿", gloss := "daughter", pinyin := "nǚ'ér" }
def erzi : Noun := { form := "儿子", gloss := "son", pinyin := "érzi" }
def shu : Noun := { form := "书", gloss := "book", pinyin := "shū", classifier := some ben }
def che : Noun := { form := "车", gloss := "vehicle", pinyin := "chē", classifier := some liang }
def hua : Noun := { form := "花", gloss := "flower", pinyin := "huā", classifier := some duo }
def shui : Noun := { form := "水", gloss := "water", pinyin := "shuǐ", classifier := none }
def fan : Noun := { form := "饭", gloss := "cooked rice", pinyin := "fàn", classifier := none }

/-! ### Part nouns and relational nouns -/

def zuoyi : Noun := { form := "座椅", gloss := "seat", pinyin := "zuòyǐ" }
def fangxiangpan : Noun := { form := "方向盘", gloss := "steering wheel", pinyin := "fāngxiàngpán" }
def lunzi : Noun := { form := "轮子", gloss := "wheel", pinyin := "lúnzi" }
def fengmian : Noun := { form := "封面", gloss := "cover", pinyin := "fēngmiàn" }
def zuozhe : Noun := { form := "作者", gloss := "author", pinyin := "zuòzhě", classifier := some wei }
def muqin : Noun := { form := "母亲", gloss := "mother", pinyin := "mǔqīn", classifier := some wei }
def fuqin : Noun := { form := "父亲", gloss := "father", pinyin := "fùqīn", classifier := some wei }
def laobanniang : Noun :=
  { form := "老板娘", gloss := "proprietress", pinyin := "lǎobǎnniáng", classifier := some wei }
def laoban : Noun := { form := "老板", gloss := "boss", pinyin := "lǎobǎn", classifier := some wei }

/-! ### Proper names -/

/-- A personal name. -/
private def name (form pinyin : String) : Noun :=
  { form, gloss := pinyin, pinyin, classifier := none, proper := true }

def zhangsan : Noun := name "张三" "Zhāng Sān"
def lisi : Noun := name "李四" "Lǐ Sì"
def xiaoming : Noun := name "小明" "Xiǎo Míng"

/-! ### The Nominal Mapping Parameter -/

/-- Mandarin is [+arg, −pred]: nouns denote kinds, and with no articles
(`Mandarin.Determiners.inventory`) no covert shift is blocked ([chierchia-1998]). -/
def nominalMapping : NominalMapping := .argOnly

end Mandarin.Nouns
