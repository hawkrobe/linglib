import Linglib.Features.Prominence
import Linglib.Fragments.Shona.Basic

/-!
# Shona nouns

Nouns of the class system, each with its singular class and the kind of entity it denotes: the
lexicon behind the conjoined-subject agreement data of [carstens-2026]. The class 12
diminutives *ka-sikana* 'small girl', *ka-mba* 'small house' are entered as nouns of class 12.

## References

* [carstens-2026]
-/

namespace Shona

/-- A noun: its singular class and the animacy of what it denotes. -/
structure NounEntry where
  form : String
  gloss : String
  cls : NounClass
  animacy : Features.Prominence.AnimacyLevel
  deriving DecidableEq, Repr

namespace Nouns

def murume : NounEntry := ⟨"murume", "man", .cl1, .human⟩
def mukadzi : NounEntry := ⟨"mukadzi", "woman", .cl1, .human⟩
def musikana : NounEntry := ⟨"musikana", "girl", .cl1, .human⟩
def munwe : NounEntry := ⟨"munwe", "finger", .cl3, .inanimate⟩
def muromo : NounEntry := ⟨"muromo", "mouth", .cl3, .inanimate⟩
def dombo : NounEntry := ⟨"dombo", "stone", .cl5, .inanimate⟩
def zai : NounEntry := ⟨"zai", "egg", .cl5, .inanimate⟩
def benzi : NounEntry := ⟨"benzi", "fool", .cl5, .human⟩
def dinga : NounEntry := ⟨"dinga", "dimwit", .cl5, .human⟩
def chingwa : NounEntry := ⟨"chingwa", "bread", .cl7, .inanimate⟩
def chibage : NounEntry := ⟨"chibage", "maize", .cl7, .inanimate⟩
def chidhakwa : NounEntry := ⟨"chidhakwa", "drunkard", .cl7, .human⟩
def chikomana : NounEntry := ⟨"chikomana", "small boy", .cl7, .human⟩
def nherera : NounEntry := ⟨"nherera", "orphan", .cl9, .human⟩
def nyanzvi : NounEntry := ⟨"nyanzvi", "expert", .cl9, .human⟩
def imbwa : NounEntry := ⟨"imbwa", "dog", .cl9, .animate⟩
def mhou : NounEntry := ⟨"mhou", "cow", .cl9, .animate⟩
def mhuno : NounEntry := ⟨"mhuno", "nose", .cl9, .inanimate⟩
def nzeve : NounEntry := ⟨"nzeve", "ear", .cl9, .inanimate⟩
def mbiya : NounEntry := ⟨"mbiya", "bowl", .cl9, .inanimate⟩
def sando : NounEntry := ⟨"sando", "hammer", .cl9, .inanimate⟩
def nyota : NounEntry := ⟨"nyota", "thirst", .cl9, .inanimate⟩
def nzara : NounEntry := ⟨"nzara", "hunger", .cl9, .inanimate⟩
def rukova : NounEntry := ⟨"rukova", "stream", .cl11, .inanimate⟩
def uta : NounEntry := ⟨"uta", "bow", .cl14, .inanimate⟩
def utanho : NounEntry := ⟨"utanho", "ladder", .cl14, .inanimate⟩
def kasikana : NounEntry := ⟨"kasikana", "small girl", .cl12, .human⟩
def kakomana : NounEntry := ⟨"kakomana", "small boy", .cl12, .human⟩
def kamba : NounEntry := ⟨"kamba", "small house", .cl12, .inanimate⟩
def kamotokari : NounEntry := ⟨"kamotokari", "small car", .cl12, .inanimate⟩

def all : List NounEntry :=
  [murume, mukadzi, musikana, munwe, muromo, dombo, zai, benzi, dinga, chingwa, chibage,
    chidhakwa, chikomana, nherera, nyanzvi, imbwa, mhou, mhuno, nzeve, mbiya, sando, nyota,
    nzara, rukova, uta, utanho, kasikana, kakomana, kamba, kamotokari]

end Nouns

end Shona
