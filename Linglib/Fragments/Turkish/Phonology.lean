import Linglib.Phonology.Harmony.System
import Linglib.Phonology.Subregular.LocalRewrite

/-!
# Turkish phonology

This file defines the segments of Turkish, its two vowel harmonies, the voicing of a
suffix-initial stop, and the surface form of a suffixed word, following the reference grammar
of Göksel and Kerslake.

Turkish has one vowel for each combination of [back], [round] and [high]. Fronting harmony
copies [back] from the preceding vowel to a suffix vowel, and rounding harmony copies [round]
to a high suffix vowel (Chapter 3). Suffix vowels are archiphonemes. The A of A-type suffixes
is non-high and unrounded but unspecified for [back] (§3.2.2), and the I of I-type suffixes is
high and unspecified for both features (§3.2.1). The targets of each harmony are therefore the
vowels lacking its feature, and a suffix vowel specified for it, such as the `o` of -(I)yor, is
skipped and triggers what follows (§3.4). Consonants are off both tiers, except that the
palatal l of loans such as *gol*, which Clements and Sezer discuss, carries [−back] and fronts
the suffix (§3.4). The suffix-initial D of -DI and -DA copies [voice] from the preceding
segment (§6.1.2).

Before -(I)yor a vowel-final stem keeps one high vowel. A final high vowel stands and the
suffix's `I` is lost, as in *eri-yor*. A final `a` or `e` becomes high and then harmonizes, as
in *anlıyor* from *anla-* and the negative *-mIyor* from *-mA* (§8.2.2, §8.2.3.3). The surface
form of a word resolves that hiatus and then applies the three alternations. The spelling is
phonemic, each letter writing one segment.

## Main definitions

* `a`, `e`, `ı`, `i`, `o`, `ö`, `u`, `ü`: the vowels; `A`, `I`: the suffix archiphonemes.
* `fronting`, `rounding`, `voicing`: the two vowel harmonies and D-voicing, as
  `Phonology.Harmony.System`s. The suffixes they apply to are the exponent forms of
  `Turkish.Morphotactics`.
* `stemVowelElision`, `suffixVowelElision`: the resolution of hiatus before -(I)yor, as
  `Subregular.LocalRewrite.Rule`s.
* `surface`: the surface form of an underlying word.
* `ofChar`, `ofString?`: the segments that a spelled word writes.

## Implementation notes

The grammar states the change before -(I)yor as a raising of the stem's `a` or `e`, with the
suffix's `I` absent after a vowel. Over archiphonemes the raised vowel, high and unspecified
for the harmonic features, is the suffix's own `I`, so the change is written as the loss of
the stem vowel before `I`. The letters *ç*, *f*, *ğ* and *j* write segments outside the
inventory and have no value under `ofChar`. The grammar's examples are derived in
`Studies/GokselKerslake2005.lean`.

## References

* [A. Göksel and C. Kerslake, *Turkish: A Comprehensive Grammar* (2005)][goksel-kerslake-2005]
* [G. N. Clements and E. Sezer, *Vowel and consonant disharmony in Turkish*][clements-sezer-1982]
-/

open Phonology Phonology.Harmony Subregular.LocalRewrite

namespace Turkish.Phonology

/-! ### Segments -/

/-- `vowel back round high` is the vowel with the given [back], [round] and [high] values. -/
private def vowel (back round high : Bool) : Segment :=
  Segment.ofSpecs [(.syllabic, true), (.dorsal, true), (.voice, true),
    (.back, back), (.round, round), (.high, high)]

def a : Segment := vowel true false false
def e : Segment := vowel false false false
def ı : Segment := vowel true false true
def i : Segment := vowel false false true
def o : Segment := vowel true true false
def ö : Segment := vowel false true false
def u : Segment := vowel true true true
def ü : Segment := vowel false true true

/-- `vowels` lists the eight vowels. -/
def vowels : List Segment := [a, e, ı, i, o, ö, u, ü]

/-- `A` is the vowel of A-type suffixes such as -lAr and -mA. It is unrounded and non-high, and
fronting harmony supplies its backness (§3.2.2). -/
def A : Segment :=
  Segment.ofSpecs [(.syllabic, true), (.dorsal, true), (.voice, true),
    (.high, false), (.round, false)]

/-- `I` is the vowel of I-type suffixes such as -(I)m and -mIş. It is high, and the two
harmonies supply its backness and rounding (§3.2.1). -/
def I : Segment :=
  Segment.ofSpecs [(.syllabic, true), (.dorsal, true), (.voice, true), (.high, true)]

/-- `consonant specs` is the non-syllabic segment with the specifications `specs`. -/
private def consonant (specs : List (Phonology.Feature × Bool)) : Segment :=
  Segment.ofSpecs ((.syllabic, false) :: specs)

def p : Segment := consonant [(.consonantal, true), (.sonorant, false), (.continuant, false),
  (.labial, true), (.voice, false)]
def b : Segment := consonant [(.consonantal, true), (.sonorant, false), (.continuant, false),
  (.labial, true), (.voice, true)]
def t : Segment := consonant [(.consonantal, true), (.sonorant, false), (.continuant, false),
  (.coronal, true), (.anterior, true), (.voice, false)]
def d : Segment := consonant [(.consonantal, true), (.sonorant, false), (.continuant, false),
  (.coronal, true), (.anterior, true), (.voice, true)]
/-- `D` is the suffix-initial stop of -DI and -DA, which is `t` after a voiceless consonant
and `d` otherwise (§6.1.2). -/
def D : Segment := consonant [(.consonantal, true), (.sonorant, false), (.continuant, false),
  (.coronal, true), (.anterior, true)]
def k : Segment := consonant [(.consonantal, true), (.sonorant, false), (.continuant, false),
  (.dorsal, true), (.voice, false)]
def g : Segment := consonant [(.consonantal, true), (.sonorant, false), (.continuant, false),
  (.dorsal, true), (.voice, true)]
/-- `K` is the final consonant of -(y)AcAK, which is `k`, or `ğ` before a vowel (Chapter 2). -/
def K : Segment := consonant [(.consonantal, true), (.sonorant, false), (.dorsal, true),
  (.voice, false)]
def c : Segment := consonant [(.consonantal, true), (.sonorant, false), (.continuant, false),
  (.delayedRelease, true), (.coronal, true), (.anterior, false), (.voice, true)]
def s : Segment := consonant [(.consonantal, true), (.sonorant, false), (.continuant, true),
  (.strident, true), (.coronal, true), (.anterior, true), (.voice, false)]
def z : Segment := consonant [(.consonantal, true), (.sonorant, false), (.continuant, true),
  (.strident, true), (.coronal, true), (.anterior, true), (.voice, true)]
def ş : Segment := consonant [(.consonantal, true), (.sonorant, false), (.continuant, true),
  (.strident, true), (.coronal, true), (.anterior, false), (.voice, false)]
def v : Segment := consonant [(.consonantal, true), (.sonorant, false), (.continuant, true),
  (.labial, true), (.voice, true)]
def h : Segment := consonant [(.consonantal, false), (.sonorant, false), (.continuant, true),
  (.spreadGlottis, true), (.voice, false)]
def m : Segment := consonant [(.consonantal, true), (.sonorant, true), (.nasal, true),
  (.labial, true), (.voice, true)]
def n : Segment := consonant [(.consonantal, true), (.sonorant, true), (.nasal, true),
  (.coronal, true), (.voice, true)]
def l : Segment := consonant [(.consonantal, true), (.sonorant, true), (.lateral, true),
  (.coronal, true), (.voice, true)]
/-- `l'` is the palatal l of loans such as *gol* and *hal*. It is [−back] and so triggers
fronting harmony (§3.4 (iv)). -/
def l' : Segment := consonant [(.consonantal, true), (.sonorant, true), (.lateral, true),
  (.coronal, true), (.voice, true), (.back, false)]
def r : Segment := consonant [(.consonantal, true), (.sonorant, true), (.tap, true),
  (.coronal, true), (.voice, true)]
def y : Segment := consonant [(.consonantal, false), (.sonorant, true), (.approximant, true),
  (.continuant, true), (.voice, true)]

/-! ### Alternations -/

/-- Under fronting harmony a suffix vowel unspecified for [back] takes the value of the
preceding segment specified for it, a vowel or a palatal `l'`. All other consonants are off
the tier (§3.1, §3.2). -/
def fronting : System Segment :=
  System.mk' (feature := .back)
    (IsTarget      := fun s ↦ s.HasValue .syllabic true ∧ s .back = none)
    (IsTransparent := fun s ↦ s .back = none ∧ ¬ s.HasValue .syllabic true)

/-- Under rounding harmony a high suffix vowel unspecified for [round] takes the value of the
preceding vowel. Consonants are off the tier (§3.1, §3.2.1). -/
def rounding : System Segment :=
  System.mk' (feature := .round)
    (IsTarget      := fun s ↦ s.HasValue .syllabic true ∧ s.HasValue .high true ∧
      s .round = none)
    (IsTransparent := fun s ↦ ¬ s.HasValue .syllabic true)

/-- A suffix-initial `D` takes the [voice] of the preceding segment (§6.1.2). -/
def voicing : System Segment :=
  System.mk' (feature := .voice)
    (IsTarget      := fun s ↦ s .voice = none)
    (IsTransparent := fun _ ↦ False)

/-! ### Hiatus before -(I)yor -/

/-- A stem-final `a` or `e` is lost before the `I` of -(I)yor, which then harmonizes, so that
*anla-* gives *anlıyor* and the negative -mA gives -mIyor (§8.2.2, §8.2.3.3). -/
def stemVowelElision : Rule where
  target := A
  effect := .delete
  rightContext := [.seg I, .seg y]

/-- After a stem-final high vowel the `I` of -(I)yor is lost, as in *eri-yor* and *kuru-yor*
(§8.2.3.3). -/
def suffixVowelElision : Rule where
  target := I
  effect := .delete
  leftContext := [.seg I]
  rightContext := [.seg y]

/-! ### Surface forms -/

/-- The surface form of an underlying word resolves hiatus before -(I)yor and then applies
the search-and-copy runs of fronting, rounding and voicing in turn. -/
def surface (w : List Segment) : List Segment :=
  voicing.searchCopy.apply (rounding.searchCopy.apply (fronting.searchCopy.apply
    (derive [stemVowelElision, suffixVowelElision] w)))

/-! ### Spelling -/

/-- `ofChar c` is the segment that the letter `c` writes. The palatal `l'` is spelled like
`l` and so is the value of no letter. -/
def ofChar : Char → Option Segment
  | 'a' => some a | 'e' => some e | 'ı' => some ı | 'i' => some i
  | 'o' => some o | 'ö' => some ö | 'u' => some u | 'ü' => some ü
  | 'p' => some p | 'b' => some b | 't' => some t | 'd' => some d | 'k' => some k
  | 'g' => some g | 'c' => some c | 's' => some s | 'z' => some z | 'ş' => some ş
  | 'v' => some v | 'h' => some h | 'm' => some m | 'n' => some n | 'l' => some l
  | 'r' => some r | 'y' => some y
  | _ => none

/-- `ofString? s` is the string of segments that the spelled word `s` writes, if every letter
writes one. -/
def ofString? (s : String) : Option (List Segment) := s.toList.mapM ofChar

end Turkish.Phonology
