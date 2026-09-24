module

public import Linglib.Syntax.Category.Classifier.Basic
public import Mathlib.Data.Finset.Insert

/-!
# Japanese numeral classifiers

Japanese counts with a classifier suffixed to the numeral and chosen by the semantics of the noun:
*-nin* for people, *-hiki* for small animals, *-hon* for long thin things, *-mai* for flat ones,
*-satsu* for bound volumes. The native *-tsu* has no meaning of its own and serves as the residue
and default classifier for inanimates, and the Sino-Japanese *-ko*, also a residue classifier,
counts smallish concrete inanimates. Downing's questionnaire gives the inventory below, the
classifiers all or most of the respondents used, to which Sudo's *-kumi* 'pair' and *-daasu*
'dozen', which count non-atomic individuals, are added. The two *ken* are told apart by their
characters. Allomorphy (*ippon*, *sanbon*, *roppon*) and the native and Sino-Japanese numeral series
are not recorded.

## Main definitions

* `Japanese.Classifiers.classifiers` — the classifiers entered here

Which nouns each classifier counts is recorded on the nouns (`Japanese.Nouns`).

## References

* [downing-1996]
* [sudo-2016]
* [aikhenvald-2000]
-/

@[expose] public section

namespace Japanese.Classifiers

/-- *-tsu* つ, the general classifier of inanimates. -/
def tsu : Classifier := { form := "tsu", script := some "つ" }

/-- *-nin* 人, persons. -/
def nin : Classifier := { form := "nin", script := some "人" }

/-- *-mei* 名, persons, formal. -/
def mei : Classifier := { form := "mei", script := some "名" }

/-- *-hiki* 匹, small animals. -/
def hiki : Classifier := { form := "hiki", script := some "匹" }

/-- *-tō* 頭, large animals. -/
def tou : Classifier := { form := "tō", script := some "頭" }

/-- *-hon* 本, long thin things. -/
def hon : Classifier := { form := "hon", script := some "本" }

/-- *-mai* 枚, flat thin things. -/
def mai : Classifier := { form := "mai", script := some "枚" }

/-- *-ko* 個, smallish concrete inanimates. -/
def ko : Classifier := { form := "ko", script := some "個" }

/-- *-satsu* 冊, bound volumes. -/
def satsu : Classifier := { form := "satsu", script := some "冊" }

/-- *-tsubu* 粒, grains. -/
def tsubu : Classifier := { form := "tsubu", script := some "粒" }

/-- *-dai* 台, machines and vehicles. -/
def dai : Classifier := { form := "dai", script := some "台" }

/-- *-ken* 軒, buildings. -/
def kenBuilding : Classifier := { form := "ken", script := some "軒" }

/-- *-ken* 件, incidents and matters. -/
def kenIncident : Classifier := { form := "ken", script := some "件" }

/-- *-ki* 機, aircraft. -/
def ki : Classifier := { form := "ki", script := some "機" }

/-- *-ku* 句, verses. -/
def ku : Classifier := { form := "ku", script := some "句" }

/-- *-kyoku* 曲, pieces of music. -/
def kyoku : Classifier := { form := "kyoku", script := some "曲" }

/-- *-mon* 問, questions. -/
def mon : Classifier := { form := "mon", script := some "問" }

/-- *-mune* 棟, buildings, by the ridge of the roof. -/
def mune : Classifier := { form := "mune", script := some "棟" }

/-- *-seki* 隻, large boats. -/
def seki : Classifier := { form := "seki", script := some "隻" }

/-- *-soku* 足, pairs of footwear. -/
def soku : Classifier := { form := "soku", script := some "足" }

/-- *-sō* 艘, small boats. -/
def soo : Classifier := { form := "sō", script := some "艘" }

/-- *-ten* 点, points and items. -/
def ten : Classifier := { form := "ten", script := some "点" }

/-- *-tōri* 通り, methods and ways. -/
def toori : Classifier := { form := "tōri", script := some "通り" }

/-- *-tsū* 通, letters and documents. -/
def tsuu : Classifier := { form := "tsū", script := some "通" }

/-- *-kabu* 株, rooted plants. -/
def kabu : Classifier := { form := "kabu", script := some "株" }

/-- *-shoku* 食, meals. -/
def shoku : Classifier := { form := "shoku", script := some "食" }

/-- *-teki* 滴, drops. -/
def teki : Classifier := { form := "teki", script := some "滴" }

/-- *-sao* 竿, poles. -/
def sao : Classifier := { form := "sao", script := some "竿" }

/-- *-wa* 羽, birds. -/
def wa : Classifier := { form := "wa", script := some "羽" }

/-- *-furi* 振, swords. -/
def furi : Classifier := { form := "furi", script := some "振" }

/-- *-zen* 膳, pairs of chopsticks. -/
def zen : Classifier := { form := "zen", script := some "膳" }

/-- *-kyaku* 脚, furniture with legs. -/
def kyaku : Classifier := { form := "kyaku", script := some "脚" }

/-- *-rin* 輪, flowers and wheels. -/
def rin : Classifier := { form := "rin", script := some "輪" }

/-- *-kumi* 組, pairs. -/
def kumi : Classifier := { form := "kumi", script := some "組" }

/-- *-dāsu* ダース, dozens. -/
def daasu : Classifier := { form := "dāsu", script := some "ダース" }

/-- The classifiers. -/
def classifiers : Finset Classifier :=
  {tsu, nin, mei, hiki, tou, hon, mai, ko, satsu, tsubu, dai, kenBuilding, kenIncident, ki, ku,
    kyoku, mon, mune, seki, soku, soo, ten, toori, tsuu, kabu, shoku, teki, sao, wa, furi, zen,
    kyaku, rin, kumi, daasu}

end Japanese.Classifiers
