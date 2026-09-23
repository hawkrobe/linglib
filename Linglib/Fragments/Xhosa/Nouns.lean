module

public import Linglib.Semantics.Reference.Prominence
public import Linglib.Syntax.Category.Noun.Basic
public import Linglib.Fragments.Xhosa.Basic

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

@[expose] public section

namespace Xhosa

/-- A noun: the root entry with its singular class and the animacy of what it denotes. -/
structure Noun extends _root_.Noun where
  /-- The singular class. -/
  cls : NounClass
  /-- The animacy of what the noun denotes. -/
  animacy : Reference.Prominence.AnimacyLevel
  deriving DecidableEq, Repr

namespace Nouns

def ummi : Noun := ⟨⟨"ummi", "citizen"⟩, .cl1, .human⟩
def umongameli : Noun := ⟨⟨"umongameli", "president"⟩, .cl1, .human⟩
def umntwana : Noun := ⟨⟨"umntwana", "child"⟩, .cl1, .human⟩
def umfazi : Noun := ⟨⟨"umfazi", "woman"⟩, .cl1, .human⟩
def uL : Noun := ⟨⟨"uL", "the letter L"⟩, .cl1, .inanimate⟩
def uM : Noun := ⟨⟨"uM", "the letter M"⟩, .cl1, .inanimate⟩
def uloliwe : Noun := ⟨⟨"uloliwe", "train"⟩, .cl1, .inanimate⟩
def umatshini : Noun := ⟨⟨"umatshini", "machine"⟩, .cl1, .inanimate⟩
def ubhaka : Noun := ⟨⟨"ubhaka", "backpack"⟩, .cl1, .inanimate⟩
def unonkala : Noun := ⟨⟨"unonkala", "crab"⟩, .cl1, .animate⟩
def ukrebe : Noun := ⟨⟨"ukrebe", "shark"⟩, .cl1, .animate⟩
def umgewu : Noun := ⟨⟨"umgewu", "criminal"⟩, .cl3, .human⟩
def umlwelwe : Noun := ⟨⟨"umlwelwe", "sick person"⟩, .cl3, .human⟩
def umgulukudu : Noun := ⟨⟨"umgulukudu", "gangster"⟩, .cl3, .human⟩
def umnqwazi : Noun := ⟨⟨"umnqwazi", "hat"⟩, .cl3, .inanimate⟩
def umpu : Noun := ⟨⟨"umpu", "gun"⟩, .cl3, .inanimate⟩
def umhlonyane : Noun := ⟨⟨"umhlonyane", "wormwood tree"⟩, .cl3, .inanimate⟩
def umnquma : Noun := ⟨⟨"umnquma", "wild olive"⟩, .cl3, .inanimate⟩
def umkhonto : Noun := ⟨⟨"umkhonto", "spear"⟩, .cl3, .inanimate⟩
def umbhobho : Noun := ⟨⟨"umbhobho", "pipe"⟩, .cl3, .inanimate⟩
def umnqathe : Noun := ⟨⟨"umnqathe", "carrot"⟩, .cl3, .inanimate⟩
def umvundla : Noun := ⟨⟨"umvundla", "rabbit"⟩, .cl3, .animate⟩
def umqhagi : Noun := ⟨⟨"umqhagi", "rooster"⟩, .cl3, .animate⟩
def igqwetha : Noun := ⟨⟨"igqwetha", "lawyer"⟩, .cl5, .human⟩
def isela : Noun := ⟨⟨"isela", "thief"⟩, .cl5, .human⟩
def igorha : Noun := ⟨⟨"igorha", "hero"⟩, .cl5, .human⟩
def ikhoboka : Noun := ⟨⟨"ikhoboka", "slave"⟩, .cl5, .human⟩
def ipolisa : Noun := ⟨⟨"ipolisa", "policeman"⟩, .cl5, .human⟩
def iqanda : Noun := ⟨⟨"iqanda", "egg"⟩, .cl5, .inanimate⟩
def icepe : Noun := ⟨⟨"icepe", "spoon"⟩, .cl5, .inanimate⟩
def ilitye : Noun := ⟨⟨"ilitye", "stone"⟩, .cl5, .inanimate⟩
def icici : Noun := ⟨⟨"icici", "earring"⟩, .cl5, .inanimate⟩
def ihobe : Noun := ⟨⟨"ihobe", "dove"⟩, .cl5, .animate⟩
def isibane : Noun := ⟨⟨"isibane", "lamp"⟩, .cl7, .inanimate⟩
def isitya : Noun := ⟨⟨"isitya", "dish"⟩, .cl7, .inanimate⟩
def isiXhosa : Noun := ⟨⟨"isiXhosa", "Xhosa"⟩, .cl7, .inanimate⟩
def isiZulu : Noun := ⟨⟨"isiZulu", "Zulu"⟩, .cl7, .inanimate⟩
def isanuse : Noun := ⟨⟨"isanuse", "diviner"⟩, .cl7, .human⟩
def isazi : Noun := ⟨⟨"isazi", "scholar"⟩, .cl7, .human⟩
def isangoma : Noun := ⟨⟨"isangoma", "healer"⟩, .cl7, .human⟩
def isibhanxa : Noun := ⟨⟨"isibhanxa", "fool"⟩, .cl7, .human⟩
def isikhova : Noun := ⟨⟨"isikhova", "owl"⟩, .cl7, .animate⟩
def intombi : Noun := ⟨⟨"intombi", "girl"⟩, .cl9, .human⟩
def imbongi : Noun := ⟨⟨"imbongi", "poet"⟩, .cl9, .human⟩
def ingcaphephe : Noun := ⟨⟨"ingcaphephe", "expert"⟩, .cl9, .human⟩
def ingcali : Noun := ⟨⟨"ingcali", "specialist"⟩, .cl9, .human⟩
def incwadi : Noun := ⟨⟨"incwadi", "book"⟩, .cl9, .inanimate⟩
def ipeni : Noun := ⟨⟨"ipeni", "pen"⟩, .cl9, .inanimate⟩
def indlovu : Noun := ⟨⟨"indlovu", "elephant"⟩, .cl9, .animate⟩
def ingwe : Noun := ⟨⟨"ingwe", "leopard"⟩, .cl9, .animate⟩

/-! ### Deverbal nouns

Nominalizations of *thiml-* 'sneeze' and *khohlel-* 'cough' ([mletshe-2019]): the final vowel -i
forms animate nouns, in class 1 or class 7, and -o and -a inanimate ones. -/

def umthimli : Noun := ⟨⟨"umthimli", "sneezer"⟩, .cl1, .human⟩
def umthimlo : Noun := ⟨⟨"umthimlo", "manner of sneezing"⟩, .cl3, .inanimate⟩
def isithimli : Noun := ⟨⟨"isithimli", "severe sneezer"⟩, .cl7, .human⟩
def umkhohleli : Noun := ⟨⟨"umkhohleli", "coughing person"⟩, .cl1, .human⟩
def isikhohleli : Noun := ⟨⟨"isikhohleli", "coughing person"⟩, .cl7, .human⟩
def isikhohlela : Noun := ⟨⟨"isikhohlela", "phlegm"⟩, .cl7, .inanimate⟩

def all : List Noun :=
  [ummi, umongameli, umntwana, umfazi, uL, uM, uloliwe, umatshini, ubhaka, unonkala, ukrebe,
    umgewu, umlwelwe, umgulukudu, umnqwazi, umpu, umhlonyane, umnquma, umkhonto, umbhobho,
    umnqathe, umvundla, umqhagi, igqwetha, isela, igorha, ikhoboka, ipolisa, iqanda, icepe,
    ilitye, icici, ihobe, isibane, isitya, isiXhosa, isiZulu, isanuse, isazi, isangoma,
    isibhanxa, isikhova, intombi, imbongi, ingcaphephe, ingcali, incwadi, ipeni, indlovu, ingwe,
    umthimli, umthimlo, isithimli, umkhohleli, isikhohleli, isikhohlela]

end Nouns

end Xhosa
