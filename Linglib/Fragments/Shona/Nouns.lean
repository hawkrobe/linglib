module

public import Linglib.Semantics.Reference.Prominence
public import Linglib.Syntax.Category.Noun.Basic
public import Linglib.Fragments.Shona.Basic

/-!
# Shona nouns

Nouns of the class system, each with its singular class and the kind of entity it denotes: the
lexicon behind the conjoined-subject agreement data of [carstens-2026]. The class 12
diminutives *ka-sikana* 'small girl', *ka-mba* 'small house' are entered as nouns of class 12.

## References

* [carstens-2026]
-/

@[expose] public section

namespace Shona

/-- A noun: the root entry with its singular class and the animacy of what it denotes. -/
structure Noun extends _root_.Noun where
  /-- The singular class. -/
  cls : NounClass
  /-- The animacy of what the noun denotes. -/
  animacy : Reference.Prominence.AnimacyLevel
  deriving DecidableEq, Repr

namespace Nouns

def murume : Noun := ⟨⟨"murume", "man"⟩, .cl1, .human⟩
def mukadzi : Noun := ⟨⟨"mukadzi", "woman"⟩, .cl1, .human⟩
def musikana : Noun := ⟨⟨"musikana", "girl"⟩, .cl1, .human⟩
def munwe : Noun := ⟨⟨"munwe", "finger"⟩, .cl3, .inanimate⟩
def muromo : Noun := ⟨⟨"muromo", "mouth"⟩, .cl3, .inanimate⟩
def dombo : Noun := ⟨⟨"dombo", "stone"⟩, .cl5, .inanimate⟩
def zai : Noun := ⟨⟨"zai", "egg"⟩, .cl5, .inanimate⟩
def benzi : Noun := ⟨⟨"benzi", "fool"⟩, .cl5, .human⟩
def dinga : Noun := ⟨⟨"dinga", "dimwit"⟩, .cl5, .human⟩
def chingwa : Noun := ⟨⟨"chingwa", "bread"⟩, .cl7, .inanimate⟩
def chibage : Noun := ⟨⟨"chibage", "maize"⟩, .cl7, .inanimate⟩
def chidhakwa : Noun := ⟨⟨"chidhakwa", "drunkard"⟩, .cl7, .human⟩
def chikomana : Noun := ⟨⟨"chikomana", "small boy"⟩, .cl7, .human⟩
def nherera : Noun := ⟨⟨"nherera", "orphan"⟩, .cl9, .human⟩
def nyanzvi : Noun := ⟨⟨"nyanzvi", "expert"⟩, .cl9, .human⟩
def imbwa : Noun := ⟨⟨"imbwa", "dog"⟩, .cl9, .animate⟩
def mhou : Noun := ⟨⟨"mhou", "cow"⟩, .cl9, .animate⟩
def mhuno : Noun := ⟨⟨"mhuno", "nose"⟩, .cl9, .inanimate⟩
def nzeve : Noun := ⟨⟨"nzeve", "ear"⟩, .cl9, .inanimate⟩
def mbiya : Noun := ⟨⟨"mbiya", "bowl"⟩, .cl9, .inanimate⟩
def sando : Noun := ⟨⟨"sando", "hammer"⟩, .cl9, .inanimate⟩
def nyota : Noun := ⟨⟨"nyota", "thirst"⟩, .cl9, .inanimate⟩
def nzara : Noun := ⟨⟨"nzara", "hunger"⟩, .cl9, .inanimate⟩
def rukova : Noun := ⟨⟨"rukova", "stream"⟩, .cl11, .inanimate⟩
def uta : Noun := ⟨⟨"uta", "bow"⟩, .cl14, .inanimate⟩
def utanho : Noun := ⟨⟨"utanho", "ladder"⟩, .cl14, .inanimate⟩
def kasikana : Noun := ⟨⟨"kasikana", "small girl"⟩, .cl12, .human⟩
def kakomana : Noun := ⟨⟨"kakomana", "small boy"⟩, .cl12, .human⟩
def kamba : Noun := ⟨⟨"kamba", "small house"⟩, .cl12, .inanimate⟩
def kamotokari : Noun := ⟨⟨"kamotokari", "small car"⟩, .cl12, .inanimate⟩

def all : List Noun :=
  [murume, mukadzi, musikana, munwe, muromo, dombo, zai, benzi, dinga, chingwa, chibage,
    chidhakwa, chikomana, nherera, nyanzvi, imbwa, mhou, mhuno, nzeve, mbiya, sando, nyota,
    nzara, rukova, uta, utanho, kasikana, kakomana, kamba, kamotokari]

end Nouns

end Shona
