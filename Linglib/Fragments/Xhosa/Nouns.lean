import Linglib.Features.Prominence
import Linglib.Fragments.Xhosa.Basic

/-!
# Xhosa nouns

Nouns of the class system, each with its singular class and the kind of entity it denotes: the
lexicon behind the conjoined-subject agreement data of [carstens-2026] and
[taraldsen-et-al-2018], and the deverbal nouns in the nominalizing final vowels -i and -o of
[mletshe-2019] behind [halpert-hammerly-2026]'s stacked class prefixes. Forms are cited with
the augment. Class 1a nouns, *u-L*, *u-loliwe* 'train', *u-nonkala* 'crab', are entered under
class 1, from which they differ only in the nominal prefix.

## References

* [carstens-2026]
* [taraldsen-et-al-2018]
* [mletshe-2019]
* [halpert-hammerly-2026]
-/

namespace Xhosa

/-- A noun: its singular class and the animacy of what it denotes. -/
structure NounEntry where
  form : String
  gloss : String
  cls : NounClass
  animacy : Features.Prominence.AnimacyLevel
  deriving DecidableEq, Repr

namespace Nouns

def ummi : NounEntry := ⟨"ummi", "citizen", .cl1, .human⟩
def umongameli : NounEntry := ⟨"umongameli", "president", .cl1, .human⟩
def umntwana : NounEntry := ⟨"umntwana", "child", .cl1, .human⟩
def umfazi : NounEntry := ⟨"umfazi", "woman", .cl1, .human⟩
def uL : NounEntry := ⟨"uL", "the letter L", .cl1, .inanimate⟩
def uM : NounEntry := ⟨"uM", "the letter M", .cl1, .inanimate⟩
def uloliwe : NounEntry := ⟨"uloliwe", "train", .cl1, .inanimate⟩
def umatshini : NounEntry := ⟨"umatshini", "machine", .cl1, .inanimate⟩
def ubhaka : NounEntry := ⟨"ubhaka", "backpack", .cl1, .inanimate⟩
def unonkala : NounEntry := ⟨"unonkala", "crab", .cl1, .animate⟩
def ukrebe : NounEntry := ⟨"ukrebe", "shark", .cl1, .animate⟩
def umgewu : NounEntry := ⟨"umgewu", "criminal", .cl3, .human⟩
def umlwelwe : NounEntry := ⟨"umlwelwe", "sick person", .cl3, .human⟩
def umgulukudu : NounEntry := ⟨"umgulukudu", "gangster", .cl3, .human⟩
def umnqwazi : NounEntry := ⟨"umnqwazi", "hat", .cl3, .inanimate⟩
def umpu : NounEntry := ⟨"umpu", "gun", .cl3, .inanimate⟩
def umhlonyane : NounEntry := ⟨"umhlonyane", "wormwood tree", .cl3, .inanimate⟩
def umnquma : NounEntry := ⟨"umnquma", "wild olive", .cl3, .inanimate⟩
def umkhonto : NounEntry := ⟨"umkhonto", "spear", .cl3, .inanimate⟩
def umbhobho : NounEntry := ⟨"umbhobho", "pipe", .cl3, .inanimate⟩
def umnqathe : NounEntry := ⟨"umnqathe", "carrot", .cl3, .inanimate⟩
def umvundla : NounEntry := ⟨"umvundla", "rabbit", .cl3, .animate⟩
def umqhagi : NounEntry := ⟨"umqhagi", "rooster", .cl3, .animate⟩
def igqwetha : NounEntry := ⟨"igqwetha", "lawyer", .cl5, .human⟩
def isela : NounEntry := ⟨"isela", "thief", .cl5, .human⟩
def igorha : NounEntry := ⟨"igorha", "hero", .cl5, .human⟩
def ikhoboka : NounEntry := ⟨"ikhoboka", "slave", .cl5, .human⟩
def ipolisa : NounEntry := ⟨"ipolisa", "policeman", .cl5, .human⟩
def iqanda : NounEntry := ⟨"iqanda", "egg", .cl5, .inanimate⟩
def icepe : NounEntry := ⟨"icepe", "spoon", .cl5, .inanimate⟩
def ilitye : NounEntry := ⟨"ilitye", "stone", .cl5, .inanimate⟩
def icici : NounEntry := ⟨"icici", "earring", .cl5, .inanimate⟩
def ihobe : NounEntry := ⟨"ihobe", "dove", .cl5, .animate⟩
def isibane : NounEntry := ⟨"isibane", "lamp", .cl7, .inanimate⟩
def isitya : NounEntry := ⟨"isitya", "dish", .cl7, .inanimate⟩
def isiXhosa : NounEntry := ⟨"isiXhosa", "Xhosa", .cl7, .inanimate⟩
def isiZulu : NounEntry := ⟨"isiZulu", "Zulu", .cl7, .inanimate⟩
def isanuse : NounEntry := ⟨"isanuse", "diviner", .cl7, .human⟩
def isazi : NounEntry := ⟨"isazi", "scholar", .cl7, .human⟩
def isangoma : NounEntry := ⟨"isangoma", "healer", .cl7, .human⟩
def isibhanxa : NounEntry := ⟨"isibhanxa", "fool", .cl7, .human⟩
def isikhova : NounEntry := ⟨"isikhova", "owl", .cl7, .animate⟩
def intombi : NounEntry := ⟨"intombi", "girl", .cl9, .human⟩
def imbongi : NounEntry := ⟨"imbongi", "poet", .cl9, .human⟩
def ingcaphephe : NounEntry := ⟨"ingcaphephe", "expert", .cl9, .human⟩
def ingcali : NounEntry := ⟨"ingcali", "specialist", .cl9, .human⟩
def incwadi : NounEntry := ⟨"incwadi", "book", .cl9, .inanimate⟩
def ipeni : NounEntry := ⟨"ipeni", "pen", .cl9, .inanimate⟩
def indlovu : NounEntry := ⟨"indlovu", "elephant", .cl9, .animate⟩
def ingwe : NounEntry := ⟨"ingwe", "leopard", .cl9, .animate⟩

/-! ### Deverbal nouns

Nominalizations of *thiml-* 'sneeze' and *khohlel-* 'cough' ([mletshe-2019]): the final vowel -i
forms animate nouns, in class 1 or class 7, and -o and -a inanimate ones. -/

def umthimli : NounEntry := ⟨"umthimli", "sneezer", .cl1, .human⟩
def umthimlo : NounEntry := ⟨"umthimlo", "manner of sneezing", .cl3, .inanimate⟩
def isithimli : NounEntry := ⟨"isithimli", "severe sneezer", .cl7, .human⟩
def umkhohleli : NounEntry := ⟨"umkhohleli", "coughing person", .cl1, .human⟩
def isikhohleli : NounEntry := ⟨"isikhohleli", "coughing person", .cl7, .human⟩
def isikhohlela : NounEntry := ⟨"isikhohlela", "phlegm", .cl7, .inanimate⟩

def all : List NounEntry :=
  [ummi, umongameli, umntwana, umfazi, uL, uM, uloliwe, umatshini, ubhaka, unonkala, ukrebe,
    umgewu, umlwelwe, umgulukudu, umnqwazi, umpu, umhlonyane, umnquma, umkhonto, umbhobho,
    umnqathe, umvundla, umqhagi, igqwetha, isela, igorha, ikhoboka, ipolisa, iqanda, icepe,
    ilitye, icici, ihobe, isibane, isitya, isiXhosa, isiZulu, isanuse, isazi, isangoma,
    isibhanxa, isikhova, intombi, imbongi, ingcaphephe, ingcali, incwadi, ipeni, indlovu, ingwe,
    umthimli, umthimlo, isithimli, umkhohleli, isikhohleli, isikhohlela]

end Nouns

end Xhosa
