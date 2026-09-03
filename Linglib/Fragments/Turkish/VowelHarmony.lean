import Linglib.Phonology.Subregular.Harmony

/-!
# Turkish vowel harmony

Turkish has one vowel for each combination of [back], [round] and [high], and two
harmonies over them ([goksel-kerslake-2005] Chapter 3): fronting harmony copies
[back] from the preceding vowel to a suffix vowel, rounding harmony copies [round]
to a high suffix vowel. Suffix vowels are archiphonemes: the A of A-type suffixes is
non-high and unrounded but unspecified for [back] (§3.2.2), the I of I-type suffixes
is high and unspecified for both (§3.2.1). So the targets of each harmony are the
vowels lacking its feature, and a suffix vowel specified for it, such as the `o` of
-(I)yor, is skipped and triggers what follows (§3.4). Consonants are off both tiers,
except that the palatal l of loans such as *gol* carries [−back] and fronts the
suffix (§3.4, [clements-sezer-1982]). The suffix-initial D of -DI and -DA copies
[voice] from the preceding segment (§6.1.2).

The alternations are `Subregular.Harmony.System`s over `Phonology.Segment`; a
suffixed word's surface form is their `System.transduceWord`. The grammar's examples
are derived in `Studies/GokselKerslake2005.lean`.

## Main definitions

* `a`, `e`, `ı`, `i`, `o`, `ö`, `u`, `ü` — the vowels; `A`, `I` — the suffix archiphonemes.
* `fronting`, `rounding`, `voicing` — the two vowel harmonies and D-voicing.
* `surface` — the three alternations applied to a word.

## References

* [A. Göksel and C. Kerslake, *Turkish: A Comprehensive Grammar* (2005)][goksel-kerslake-2005]
* [G. N. Clements and E. Sezer, *Vowel and consonant disharmony in Turkish*][clements-sezer-1982]
-/

namespace Turkish.VowelHarmony

open Phonology (Segment)
open Subregular.Harmony (System)

/-! ### Segments -/

/-- The vowel of the given [back], [round] and [high] values. -/
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

/-- The eight vowels. -/
def vowels : List Segment := [a, e, ı, i, o, ö, u, ü]

/-- The vowel of A-type suffixes such as -lAr and -mA: unrounded and non-high, its
backness supplied by fronting harmony (§3.2.2). -/
def A : Segment :=
  Segment.ofSpecs [(.syllabic, true), (.dorsal, true), (.voice, true),
    (.high, false), (.round, false)]

/-- The vowel of I-type suffixes such as -(I)m and -mIş: high, its backness and rounding
supplied by the two harmonies (§3.2.1). -/
def I : Segment :=
  Segment.ofSpecs [(.syllabic, true), (.dorsal, true), (.voice, true), (.high, true)]

/-- A consonant of the given specifications. -/
private def consonant (specs : List (Phonology.Feature × Bool)) : Segment :=
  Segment.ofSpecs ((.syllabic, false) :: specs)

def b : Segment := consonant [(.consonantal, true), (.sonorant, false), (.continuant, false),
  (.labial, true), (.voice, true)]
def t : Segment := consonant [(.consonantal, true), (.sonorant, false), (.continuant, false),
  (.coronal, true), (.anterior, true), (.voice, false)]
def d : Segment := consonant [(.consonantal, true), (.sonorant, false), (.continuant, false),
  (.coronal, true), (.anterior, true), (.voice, true)]
/-- The suffix-initial D of -DI and -DA: `t` after a voiceless consonant, `d` otherwise
(§6.1.2). -/
def D : Segment := consonant [(.consonantal, true), (.sonorant, false), (.continuant, false),
  (.coronal, true), (.anterior, true)]
def k : Segment := consonant [(.consonantal, true), (.sonorant, false), (.continuant, false),
  (.dorsal, true), (.voice, false)]
def g : Segment := consonant [(.consonantal, true), (.sonorant, false), (.continuant, false),
  (.dorsal, true), (.voice, true)]
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
/-- The palatal l of loans such as *gol* and *hal*: [−back], so a trigger of fronting
harmony (§3.4 (iv), [clements-sezer-1982]). -/
def l' : Segment := consonant [(.consonantal, true), (.sonorant, true), (.lateral, true),
  (.coronal, true), (.voice, true), (.back, false)]
def r : Segment := consonant [(.consonantal, true), (.sonorant, true), (.tap, true),
  (.coronal, true), (.voice, true)]
def y : Segment := consonant [(.consonantal, false), (.sonorant, true), (.approximant, true),
  (.continuant, true), (.voice, true)]

/-! ### Suffixes

Citation forms after a consonant-final stem; the deletable vowels and buffer `y` of
§6.1.3 are not represented. -/

/-- -lAr, plural (§8.1.1). -/
def plural : List Segment := [l, A, r]
/-- -(I)m, first-person singular possessive (§8.1.2). -/
def possessive1sg : List Segment := [I, m]
/-- -(I)n, second-person singular possessive (§8.1.2). -/
def possessive2sg : List Segment := [I, n]
/-- -(I)mIz, first-person plural possessive (§8.1.2). -/
def possessive1pl : List Segment := [I, m, I, z]
/-- -(s)I, third-person singular possessive (§8.1.2). -/
def possessive3sg : List Segment := [I]
/-- -DA, locative (§8.1.3). -/
def locative : List Segment := [D, A]
/-- -Il, passive (§8.2.1.2). -/
def passive : List Segment := [I, l]
/-- -mA, negative (§8.2.2); before -(I)yor its vowel is raised to I (§8.2.2). -/
def negative : List Segment := [m, A]
/-- -DI, perfective (§8.2.3.3). -/
def perfective : List Segment := [D, I]
/-- -mIş, perfective/evidential (§8.2.3.3). -/
def evidential : List Segment := [m, I, ş]
/-- -(I)yor, imperfective; its `o` does not harmonize (§3.4 (vi)). -/
def imperfective : List Segment := [I, y, o, r]
/-- -(y)mIş, the evidential copula (§8.3.2). -/
def evidentialCopula : List Segment := [y, m, I, ş]
/-- -(y)ken, converb; invariable (§3.4 (vi)). -/
def ken : List Segment := [k, e, n]
/-- -(I)m, first-person singular of the group 2 person markers (§8.4). -/
def person1sg : List Segment := [I, m]
/-- -nIz, second-person plural of the group 1 person markers (§8.4). -/
def person2pl : List Segment := [n, I, z]

/-! ### Alternations -/

/-- Fronting harmony: a suffix vowel unspecified for [back] takes the value of the
preceding segment specified for it — a vowel, or a palatal `l'`; all other consonants are
off the tier (§3.1, §3.2). -/
def fronting : System Segment :=
  System.mk' (feature := .back)
    (isTrigger     := fun s => (s .back).isSome)
    (isTarget      := fun s => s.HasValue .syllabic true && (s .back).isNone)
    (isTransparent := fun s => (s .back).isNone && !s.HasValue .syllabic true)

/-- Rounding harmony: a high suffix vowel unspecified for [round] takes the value of the
preceding vowel; consonants are off the tier (§3.1, §3.2.1). -/
def rounding : System Segment :=
  System.mk' (feature := .round)
    (isTrigger     := fun s => (s .round).isSome)
    (isTarget      := fun s => s.HasValue .syllabic true && s.HasValue .high true
                                 && (s .round).isNone)
    (isTransparent := fun s => !s.HasValue .syllabic true)

/-- Voicing of a suffix-initial `D`: it takes the [voice] of the preceding segment
(§6.1.2). -/
def voicing : System Segment :=
  System.mk' (feature := .voice)
    (isTrigger     := fun s => (s .voice).isSome)
    (isTarget      := fun s => (s .voice).isNone)
    (isTransparent := fun _ => false)

/-- The surface form of a suffixed word: the three alternations applied in turn. -/
def surface (w : List Segment) : List Segment :=
  voicing.transduceWord (rounding.transduceWord (fronting.transduceWord w))

end Turkish.VowelHarmony
