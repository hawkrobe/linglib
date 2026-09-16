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

namespace Washo

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
structure PropertyConcept where
  stem : String
  gloss : String
  category : PropertyConcept.Class
  shape : Shape
  deriving DecidableEq, Repr

/-! ### Age -/

def MiLe : PropertyConcept := ⟨"MiLe", "old", .age, .bare⟩
def ešlut : PropertyConcept := ⟨"ešlut’", "young", .age, .suffixed⟩

/-! ### Color -/

def leleg : PropertyConcept := ⟨"leleg", "red", .color, .prefixed⟩
def pilpil : PropertyConcept := ⟨"p’ilp’il", "blue", .color, .prefixed⟩
def popo : PropertyConcept := ⟨"popo", "white", .color, .prefixed⟩
def šošoŋ : PropertyConcept := ⟨"šošoŋ", "brown", .color, .prefixed⟩
def yiŋyiŋ : PropertyConcept := ⟨"ʔyɨŋʔyɨŋ", "varicolored", .color, .prefixed⟩

/-! ### Dimension -/

def beheziŋ : PropertyConcept := ⟨"beheziŋ", "small", .dimension, .bare⟩
def wgohat : PropertyConcept := ⟨"wgohat", "wide", .dimension, .bare⟩
def lupdep : PropertyConcept := ⟨"ʔlupdep", "thin (of object)", .dimension, .bare⟩
def udaw : PropertyConcept := ⟨"ʔudaw", "tall (of object)", .dimension, .bare⟩
def iyel : PropertyConcept := ⟨"i:yel", "big", .dimension, .suffixed⟩
def hamham : PropertyConcept := ⟨"hamham", "light (in weight)", .dimension, .prefixed⟩
def šišiš : PropertyConcept := ⟨"šɨšɨš", "heavy", .dimension, .prefixed⟩

/-! ### Human propensity -/

def bišapu : PropertyConcept := ⟨"bišapuʔ", "hungry", .humanPropensity, .bare⟩
def gumbiis : PropertyConcept := ⟨"gumbiʔis", "proud", .humanPropensity, .bare⟩
def gumyol : PropertyConcept := ⟨"gumyoʔl", "tired", .humanPropensity, .bare⟩
def kiwil : PropertyConcept := ⟨"k’iwɨl", "sharp-thinking", .humanPropensity, .bare⟩
def Lokaš : PropertyConcept := ⟨"Lokaš", "afraid", .humanPropensity, .bare⟩
def meleyik : PropertyConcept := ⟨"meleyɨk", "inebriated", .humanPropensity, .bare⟩
def melotik : PropertyConcept := ⟨"melot’ik", "thirsty", .humanPropensity, .bare⟩
def šašiw : PropertyConcept := ⟨"šašɨw", "afraid", .humanPropensity, .bare⟩
def tesu : PropertyConcept := ⟨"t’e:su", "jealous", .humanPropensity, .bare⟩
def yaha : PropertyConcept := ⟨"yaha", "sick/hurt", .humanPropensity, .bare⟩
def yomuŋ : PropertyConcept := ⟨"yomuŋ", "full (from eating)", .humanPropensity, .bare⟩
def yumil : PropertyConcept := ⟨"yumɨl", "full (from eating)", .humanPropensity, .bare⟩
def gumsutim : PropertyConcept := ⟨"gumsut’ɨm", "brave", .humanPropensity, .suffixed⟩
def musiw : PropertyConcept := ⟨"musiw", "generous", .humanPropensity, .suffixed⟩
def tamugayl : PropertyConcept := ⟨"tamugayʔl", "bored", .humanPropensity, .suffixed⟩

/-! ### Value -/

def aŋaw : PropertyConcept := ⟨"ʔaŋaw", "good", .value, .bare⟩
def muaŋ : PropertyConcept := ⟨"mu:ʔaŋ", "tasty", .value, .suffixed⟩
def nuš : PropertyConcept := ⟨"ʔnu:š", "poor condition", .value, .suffixed⟩
def umbiic : PropertyConcept := ⟨"ʔumbiʔic’", "expensive", .value, .suffixed⟩

/-! ### Physical property -/

def golgoš : PropertyConcept := ⟨"golgoš", "short and fat", .physicalProperty, .bare⟩
def ibik : PropertyConcept := ⟨"ibik’", "ripe", .physicalProperty, .bare⟩
def ihuk : PropertyConcept := ⟨"ihuk’", "dry", .physicalProperty, .bare⟩
def keše : PropertyConcept := ⟨"k’eše", "alive", .physicalProperty, .bare⟩
def metu : PropertyConcept := ⟨"metuʔ", "cold", .physicalProperty, .bare⟩
def mipil : PropertyConcept := ⟨"mi:p’ɨl", "full", .physicalProperty, .bare⟩
def mosot : PropertyConcept := ⟨"mosot", "wet", .physicalProperty, .bare⟩
def mucucu : PropertyConcept := ⟨"muc’uc’u", "sweet", .physicalProperty, .bare⟩
def wihl : PropertyConcept := ⟨"wɨhl", "cold", .physicalProperty, .bare⟩
def yakaš : PropertyConcept := ⟨"yak’aš", "warm", .physicalProperty, .bare⟩
def yasaŋ : PropertyConcept := ⟨"yasaŋ", "hot", .physicalProperty, .bare⟩
def yayaŋ : PropertyConcept := ⟨"ʔyaʔyaŋ", "naked", .physicalProperty, .bare⟩
def gucu : PropertyConcept := ⟨"guc’u", "torn", .physicalProperty, .suffixed⟩
def gumbeyécik : PropertyConcept := ⟨"gumbeyéc’ɨk", "closed", .physicalProperty, .suffixed⟩
def kakt : PropertyConcept := ⟨"kakt", "quiet", .physicalProperty, .suffixed⟩
def Loyaw : PropertyConcept := ⟨"Loyaw", "dark", .physicalProperty, .suffixed⟩
def nuuš : PropertyConcept := ⟨"nuʔuš", "stinky", .physicalProperty, .suffixed⟩
def wkuli : PropertyConcept := ⟨"wkuliʔ", "solid", .physicalProperty, .suffixed⟩
def yacim : PropertyConcept := ⟨"yac’im", "smoky", .physicalProperty, .suffixed⟩
def babab : PropertyConcept := ⟨"ba:bab", "spotted", .physicalProperty, .prefixed⟩
def huhu : PropertyConcept := ⟨"hu:hu", "striped", .physicalProperty, .prefixed⟩
def kawkaw : PropertyConcept := ⟨"k’awk’aw", "closed", .physicalProperty, .prefixed⟩
def kunkun : PropertyConcept := ⟨"k’unk’un", "bent", .physicalProperty, .prefixed⟩
def kaykay : PropertyConcept := ⟨"kaykay", "tall", .physicalProperty, .prefixed⟩
def kuškuš : PropertyConcept := ⟨"kuškuš", "short and fat", .physicalProperty, .prefixed⟩
def lotlot : PropertyConcept := ⟨"lotlot", "soft", .physicalProperty, .prefixed⟩
def mukmuk : PropertyConcept := ⟨"mukmuk", "chubby", .physicalProperty, .prefixed⟩
def naynay : PropertyConcept := ⟨"naynay", "muddy", .physicalProperty, .prefixed⟩
def pepel : PropertyConcept := ⟨"p’ep’el", "bitter", .physicalProperty, .prefixed⟩
def pipi : PropertyConcept := ⟨"p’ɨp’ɨ", "thin", .physicalProperty, .prefixed⟩
def šapšap : PropertyConcept := ⟨"šapšap", "fuzzy", .physicalProperty, .prefixed⟩
def šišip : PropertyConcept := ⟨"ši:šip", "straight", .physicalProperty, .prefixed⟩
def sinsin : PropertyConcept := ⟨"sɨnsɨn", "thin", .physicalProperty, .prefixed⟩
def siwsiw : PropertyConcept := ⟨"siwsiw", "smooth", .physicalProperty, .prefixed⟩
def tetep : PropertyConcept := ⟨"t’et’ep", "fat", .physicalProperty, .prefixed⟩
def tintin : PropertyConcept := ⟨"t’ɨnt’ɨn", "rough", .physicalProperty, .prefixed⟩
def witwit : PropertyConcept := ⟨"witwit", "stiff", .physicalProperty, .prefixed⟩

/-- The seventy stems of the appendix. -/
def propertyConcepts : List PropertyConcept :=
  [MiLe, ešlut, leleg, pilpil, popo, šošoŋ, yiŋyiŋ, beheziŋ, wgohat, lupdep, udaw, iyel, hamham,
    šišiš, bišapu, gumbiis, gumyol, kiwil, Lokaš, meleyik, melotik, šašiw, tesu, yaha, yomuŋ,
    yumil, gumsutim, musiw, tamugayl, aŋaw, muaŋ, nuš, umbiic, golgoš, ibik, ihuk, keše, metu,
    mipil, mosot, mucucu, wihl, yakaš, yasaŋ, yayaŋ, gucu, gumbeyécik, kakt, Loyaw, nuuš, wkuli,
    yacim, babab, huhu, kawkaw, kunkun, kaykay, kuškuš, lotlot, mukmuk, naynay, pepel, pipi,
    šapšap, šišip, sinsin, siwsiw, tetep, tintin, witwit]

end Washo
