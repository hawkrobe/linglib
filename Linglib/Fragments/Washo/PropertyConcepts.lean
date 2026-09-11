import Linglib.Semantics.Root.PropertyConcept

/-!
# Washo property concepts

The seventy property-concept stems of [hanink-koontz-garboden-2025]'s appendix, each with
[dixon-1982]'s semantic category and the shape of the stative verb it forms: a bare root inflected
like any intransitive, a root that needs the attributive-agentive suffix *-iʔ* ([jacobsen-1964]),
or a reduplicated root flanked by the attributive prefix *ʔil-* and *-iʔ* ([jacobsen-1980]). The
paper takes most stems from the Washo Archive, a few from [bochnak-2013], [bochnak-rhomieux-2013],
[jacobsen-1980], and a tribal dictionary; the reduplicated stems are cited in their reduplicated
form. Orthography follows [jacobsen-1964]: *:* marks length, *ʔ* the glottal stop, *ɨ* the high
central vowel, *’* glottalization, and capital *L* and *M* voiceless sonorants.

## References

* [hanink-koontz-garboden-2025]
* [dixon-1982]
* [jacobsen-1964]
* [jacobsen-1980]
* [bochnak-2013]
* [bochnak-rhomieux-2013]
-/

namespace Washo.PropertyConcepts

open Semantics

/-- The shape of the stative verb a property-concept stem forms. -/
inductive Shape where
  /-- The bare root, with subject agreement and mood only: *ʔíhuk’i* 'it is dry'. -/
  | bare
  /-- The root with the suffix *-iʔ*: *ʔí:yeliʔi* 'it is big'. -/
  | suffixed
  /-- The reduplicated root with the prefix *ʔil-* and the suffix *-iʔ*: *ʔilkáykayiʔi* 'he is
  tall'. -/
  | prefixed
  deriving DecidableEq, Repr, Fintype

/-- A property-concept stem. -/
structure Entry where
  stem : String
  gloss : String
  category : PropertyConcept.Class
  shape : Shape
  deriving DecidableEq, Repr

/-! ### Age -/

def MiLe : Entry := ⟨"MiLe", "old", .age, .bare⟩
def ešlut : Entry := ⟨"ešlut’", "young", .age, .suffixed⟩

/-! ### Color -/

def leleg : Entry := ⟨"leleg", "red", .color, .prefixed⟩
def pilpil : Entry := ⟨"p’ilp’il", "blue", .color, .prefixed⟩
def popo : Entry := ⟨"popo", "white", .color, .prefixed⟩
def šošoŋ : Entry := ⟨"šošoŋ", "brown", .color, .prefixed⟩
def yiŋyiŋ : Entry := ⟨"ʔyɨŋʔyɨŋ", "varicolored", .color, .prefixed⟩

/-! ### Dimension -/

def beheziŋ : Entry := ⟨"beheziŋ", "small", .dimension, .bare⟩
def wgohat : Entry := ⟨"wgohat", "wide", .dimension, .bare⟩
def lupdep : Entry := ⟨"ʔlupdep", "thin (of object)", .dimension, .bare⟩
def udaw : Entry := ⟨"ʔudaw", "tall (of object)", .dimension, .bare⟩
def iyel : Entry := ⟨"i:yel", "big", .dimension, .suffixed⟩
def hamham : Entry := ⟨"hamham", "light (in weight)", .dimension, .prefixed⟩
def šišiš : Entry := ⟨"šɨšɨš", "heavy", .dimension, .prefixed⟩

/-! ### Human propensity -/

def bišapu : Entry := ⟨"bišapuʔ", "hungry", .humanPropensity, .bare⟩
def gumbiis : Entry := ⟨"gumbiʔis", "proud", .humanPropensity, .bare⟩
def gumyol : Entry := ⟨"gumyoʔl", "tired", .humanPropensity, .bare⟩
def kiwil : Entry := ⟨"k’iwɨl", "sharp-thinking", .humanPropensity, .bare⟩
def Lokaš : Entry := ⟨"Lokaš", "afraid", .humanPropensity, .bare⟩
def meleyik : Entry := ⟨"meleyɨk", "inebriated", .humanPropensity, .bare⟩
def melotik : Entry := ⟨"melot’ik", "thirsty", .humanPropensity, .bare⟩
def šašiw : Entry := ⟨"šašɨw", "afraid", .humanPropensity, .bare⟩
def tesu : Entry := ⟨"t’e:su", "jealous", .humanPropensity, .bare⟩
def yaha : Entry := ⟨"yaha", "sick/hurt", .humanPropensity, .bare⟩
def yomuŋ : Entry := ⟨"yomuŋ", "full (from eating)", .humanPropensity, .bare⟩
def yumil : Entry := ⟨"yumɨl", "full (from eating)", .humanPropensity, .bare⟩
def gumsutim : Entry := ⟨"gumsut’ɨm", "brave", .humanPropensity, .suffixed⟩
def musiw : Entry := ⟨"musiw", "generous", .humanPropensity, .suffixed⟩
def tamugayl : Entry := ⟨"tamugayʔl", "bored", .humanPropensity, .suffixed⟩

/-! ### Value -/

def aŋaw : Entry := ⟨"ʔaŋaw", "good", .value, .bare⟩
def muaŋ : Entry := ⟨"mu:ʔaŋ", "tasty", .value, .suffixed⟩
def nuš : Entry := ⟨"ʔnu:š", "poor condition", .value, .suffixed⟩
def umbiic : Entry := ⟨"ʔumbiʔic’", "expensive", .value, .suffixed⟩

/-! ### Physical property -/

def golgoš : Entry := ⟨"golgoš", "short and fat", .physicalProperty, .bare⟩
def ibik : Entry := ⟨"ibik’", "ripe", .physicalProperty, .bare⟩
def ihuk : Entry := ⟨"ihuk’", "dry", .physicalProperty, .bare⟩
def keše : Entry := ⟨"k’eše", "alive", .physicalProperty, .bare⟩
def metu : Entry := ⟨"metuʔ", "cold", .physicalProperty, .bare⟩
def mipil : Entry := ⟨"mi:p’ɨl", "full", .physicalProperty, .bare⟩
def mosot : Entry := ⟨"mosot", "wet", .physicalProperty, .bare⟩
def mucucu : Entry := ⟨"muc’uc’u", "sweet", .physicalProperty, .bare⟩
def wihl : Entry := ⟨"wɨhl", "cold", .physicalProperty, .bare⟩
def yakaš : Entry := ⟨"yak’aš", "warm", .physicalProperty, .bare⟩
def yasaŋ : Entry := ⟨"yasaŋ", "hot", .physicalProperty, .bare⟩
def yayaŋ : Entry := ⟨"ʔyaʔyaŋ", "naked", .physicalProperty, .bare⟩
def gucu : Entry := ⟨"guc’u", "torn", .physicalProperty, .suffixed⟩
def gumbeyécik : Entry := ⟨"gumbeyéc’ɨk", "closed", .physicalProperty, .suffixed⟩
def kakt : Entry := ⟨"kakt", "quiet", .physicalProperty, .suffixed⟩
def Loyaw : Entry := ⟨"Loyaw", "dark", .physicalProperty, .suffixed⟩
def nuuš : Entry := ⟨"nuʔuš", "stinky", .physicalProperty, .suffixed⟩
def wkuli : Entry := ⟨"wkuliʔ", "solid", .physicalProperty, .suffixed⟩
def yacim : Entry := ⟨"yac’im", "smoky", .physicalProperty, .suffixed⟩
def babab : Entry := ⟨"ba:bab", "spotted", .physicalProperty, .prefixed⟩
def huhu : Entry := ⟨"hu:hu", "striped", .physicalProperty, .prefixed⟩
def kawkaw : Entry := ⟨"k’awk’aw", "closed", .physicalProperty, .prefixed⟩
def kunkun : Entry := ⟨"k’unk’un", "bent", .physicalProperty, .prefixed⟩
def kaykay : Entry := ⟨"kaykay", "tall", .physicalProperty, .prefixed⟩
def kuškuš : Entry := ⟨"kuškuš", "short and fat", .physicalProperty, .prefixed⟩
def lotlot : Entry := ⟨"lotlot", "soft", .physicalProperty, .prefixed⟩
def mukmuk : Entry := ⟨"mukmuk", "chubby", .physicalProperty, .prefixed⟩
def naynay : Entry := ⟨"naynay", "muddy", .physicalProperty, .prefixed⟩
def pepel : Entry := ⟨"p’ep’el", "bitter", .physicalProperty, .prefixed⟩
def pipi : Entry := ⟨"p’ɨp’ɨ", "thin", .physicalProperty, .prefixed⟩
def šapšap : Entry := ⟨"šapšap", "fuzzy", .physicalProperty, .prefixed⟩
def šišip : Entry := ⟨"ši:šip", "straight", .physicalProperty, .prefixed⟩
def sinsin : Entry := ⟨"sɨnsɨn", "thin", .physicalProperty, .prefixed⟩
def siwsiw : Entry := ⟨"siwsiw", "smooth", .physicalProperty, .prefixed⟩
def tetep : Entry := ⟨"t’et’ep", "fat", .physicalProperty, .prefixed⟩
def tintin : Entry := ⟨"t’ɨnt’ɨn", "rough", .physicalProperty, .prefixed⟩
def witwit : Entry := ⟨"witwit", "stiff", .physicalProperty, .prefixed⟩

/-- The seventy stems of the appendix. -/
def all : List Entry :=
  [MiLe, ešlut, leleg, pilpil, popo, šošoŋ, yiŋyiŋ, beheziŋ, wgohat, lupdep, udaw, iyel, hamham,
    šišiš, bišapu, gumbiis, gumyol, kiwil, Lokaš, meleyik, melotik, šašiw, tesu, yaha, yomuŋ,
    yumil, gumsutim, musiw, tamugayl, aŋaw, muaŋ, nuš, umbiic, golgoš, ibik, ihuk, keše, metu,
    mipil, mosot, mucucu, wihl, yakaš, yasaŋ, yayaŋ, gucu, gumbeyécik, kakt, Loyaw, nuuš, wkuli,
    yacim, babab, huhu, kawkaw, kunkun, kaykay, kuškuš, lotlot, mukmuk, naynay, pepel, pipi,
    šapšap, šišip, sinsin, siwsiw, tetep, tintin, witwit]

end Washo.PropertyConcepts
