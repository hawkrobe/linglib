import Linglib.Data.PHOIBLE.Inventories.Turkish
import Linglib.Phonology.Harmony.System
import Linglib.Phonology.Segmental.SegmentLike
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

The phonemes are a type of their own, read as segments, and their feature values come from
the PHOIBLE chart. A vowel keeps the chart's values for the features that distinguish the
eight vowels, together with [voice], which the voicing of D copies. Among consonants [back] is
contrastive only on the palatal lateral, so every other consonant keeps each chart value but
[back], as in Clements and Sezer's analysis, where plain consonants are unspecified for the
feature and the palatals are linked to [−back]. There are two departures from the chart. Its
`a` is central, and the grammar's `a` is a back vowel. The palatal l is the chart's l with
[−back]. The archiphonemes `A`, `I` and `D` are meets, the features their alternants share.

Before -(I)yor a stem-final `a` or `e` becomes high and then harmonizes, as in *anlıyor* from
*anla-* and the negative *-mIyor* from *-mA* (§8.2.2, §8.2.3.3). The surface form of a word
applies that raising and then the three alternations. The spelling is phonemic, each letter
writing one segment.

## Main definitions

* `Phoneme`: the phonemes, with `chart`, `departure` and `contrastive`, read as segments.
* `a`, `e`, …, `y`: the segment of each phoneme, under the phoneme's own name, so that
  underlying forms mix phonemes with archiphonemes, as in `[A, c, A, K]`.
* `A`, `I`, `D`, `K`: the suffix archiphonemes.
* `fronting`, `rounding`, `voicing`: the two vowel harmonies and D-voicing, as
  `Phonology.Harmony.System`s. The suffixes they apply to are the exponent forms of
  `Turkish.Morphotactics`.
* `raising`: the raising of a stem-final `a` or `e` before -(I)yor, as a
  `Subregular.LocalRewrite.Rule`.
* `surface`: the surface form of an underlying word.
* `ofChar`, `ofString?`: the segments that a spelled word writes.

## Main results

* `Phoneme.chart_mem_tur`: every phoneme but the two laterals is in PHOIBLE's Turkish
  inventory.
* `unspecified_back_iff`, `not_unspecified_voice`: a consonant lacks [back] unless it is the
  palatal lateral, and every phoneme has a value for [voice], which the tier tests of fronting
  and voicing rely on.
* `setFeature_back_A`, `setFeature_voice_D`: an archiphoneme with its feature filled in is one
  of its alternants.

## Implementation notes

The raised vowel harmonizes for rounding as well as backness, as in *okşuyor* from *okşa-*, so
raising replaces the stem vowel by the archiphoneme `I` instead of setting [high] alone. The
loss of the suffix's own `I` after a vowel is a matter of attachment, in
`Turkish.Morphotactics`. The letters *ç*, *f*, *ğ* and *j* write segments outside the
inventory and have no value under `ofChar`. The grammar's examples are derived in
`Studies/GokselKerslake2005.lean`.
The inventory is PHOIBLE 2217, whose glyphs the chart entries follow, the coronals being
dental there. `K` is `k` without a value for [continuant] and not a meet, since the meet of
`k` and `ğ` would lack [voice] and so be a target of voicing.

## References

* [A. Göksel and C. Kerslake, *Turkish: A Comprehensive Grammar* (2005)][goksel-kerslake-2005]
* [G. N. Clements and E. Sezer, *Vowel and consonant disharmony in Turkish*][clements-sezer-1982]
* [S. Moran and D. McCloy, *PHOIBLE 2.0*][moran-mccloy-2019]
-/

open Phonology Phonology.Harmony Subregular.LocalRewrite Data.PHOIBLE

namespace Turkish.Phonology

/-! ### Segments -/

/-- The phonemes, in Göksel and Kerslake's phonemic spelling, where `ı` is ɯ, `ö` is œ, `ü` is
y, `c` is dʒ, `ş` is ʃ, `y` is j and `r` is ɾ. The palatal l of loans such as *gol* and *hal*
is `l'`. -/
inductive Phoneme where
  | a | e | ı | i | o | ö | u | ü
  | p | b | t | d | k | g | c | s | z | ş | v | h | m | n | l | l' | r | y
  deriving DecidableEq, Fintype, Repr

namespace Phoneme

/-- The PHOIBLE chart entry of a phoneme, in the glyphs of the Turkish inventory. The palatal
l shares the entry of `l`. -/
def chart : Phoneme → FeatureMatrix
  | a => .«a» | e => .«e» | ı => .«ɯ» | i => .«i» | o => .«o» | ö => .«œ» | u => .«u»
  | ü => .«y» | p => .«p» | b => .«b» | t => .«t̪» | d => .«d̪» | k => .«k» | g => .«ɡ»
  | c => .«d̠ʒ» | s => .«s̪» | z => .«z̪» | ş => .«ʃ» | v => .«v» | h => .«h» | m => .«m»
  | n => .«n̪» | l | l' => .«l» | r => .«ɾ» | y => .«j»

/-- The vowels. -/
def vowels : Finset Phoneme := {a, e, ı, i, o, ö, u, ü}

/-- The grammar's `a` is a back vowel where the chart's is central, and the palatal l is
[−back] (§3.4 (iv)). -/
def departure : Phoneme → Segment
  | a => Segment.ofSpecs [(.back, true)]
  | l' => Segment.ofSpecs [(.back, false)]
  | _ => ⊥

/-- A vowel keeps the features that distinguish the eight vowels and [voice]. A consonant keeps
every feature but [back], which is contrastive among consonants on the palatal lateral
alone. -/
def contrastive (x : Phoneme) : Finset Phonology.Feature :=
  if x ∈ vowels then {.syllabic, .voice, .high, .back, .round}
  else if x = l' then Finset.univ else {.back}ᶜ

/-- Every phoneme but the two laterals is in PHOIBLE's Turkish inventory. -/
theorem chart_mem_tur (x : Phoneme) (hl : x ≠ l) (hl' : x ≠ l') :
    x.chart ∈ Inventories.Turkish.tur.phonemes.map (·.features) := by
  revert x; decide

end Phoneme

instance : SegmentLike Phoneme where
  coe x := .ofChart x.chart x.departure x.contrastive
  coe_injective' := by decide

segment_constants Phoneme

/-- `A` is the vowel of A-type suffixes such as -lAr and -mA. It is what `a` and `e` share,
unrounded and non-high, and fronting harmony supplies its backness (§3.2.2). -/
def A : Segment := a ⊓ e

/-- `I` is the vowel of I-type suffixes such as -(I)m and -mIş. It is what the four high
vowels share, and the two harmonies supply its backness and rounding (§3.2.1). -/
def I : Segment := ı ⊓ i ⊓ u ⊓ ü

/-- `D` is the suffix-initial stop of -DI and -DA, which is `t` after a voiceless consonant
and `d` otherwise (§6.1.2). It is what `t` and `d` share. -/
def D : Segment := t ⊓ d

/-- `K` is the final consonant of -(y)AcAK, which is `k`, or `ğ` before a vowel (Chapter 2). It
is `k` without a value for [continuant]. -/
def K : Segment := Bundle.restrict {.continuant}ᶜ k

/-- A consonant lacks a value for [back] unless it is the palatal lateral, which is what
fronting's tier test reads. -/
theorem unspecified_back_iff (x : Phoneme) (hx : x ∉ Phoneme.vowels) :
    (x : Segment).Unspecified .back ↔ x ≠ .l' := by
  revert x; decide

/-- Every phoneme has a value for [voice], so that only `D` is a target of voicing. -/
theorem not_unspecified_voice (x : Phoneme) : ¬ (x : Segment).Unspecified .voice := by
  revert x; decide

/-- `A` with [back] filled in is `a` or `e`. -/
theorem setFeature_back_A :
    A.setFeature .back true = a ∧ A.setFeature .back false = e := by
  decide

/-- `D` with [voice] filled in is `d` or `t`. -/
theorem setFeature_voice_D :
    D.setFeature .voice true = d ∧ D.setFeature .voice false = t := by
  decide

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

/-! ### Raising before -(I)yor -/

/-- A stem-final `a` or `e` becomes high before -(I)yor and then harmonizes, so that *anla-*
gives *anlıyor* and the negative -mA gives -mIyor (§8.2.2, §8.2.3.3). The raised vowel is the
archiphoneme `I`. -/
def raising : Rule where
  target := A
  effect := .replace I
  rightContext := [.seg y, .seg o, .seg r]

/-! ### Surface forms -/

/-- The surface form of an underlying word applies raising before -(I)yor and then the
search-and-copy runs of fronting, rounding and voicing in turn. -/
def surface (w : List Segment) : List Segment :=
  voicing.searchCopy.apply (rounding.searchCopy.apply (fronting.searchCopy.apply (raising.apply w)))

/-! ### Spelling -/

/-- `ofChar c` is the phoneme that the letter `c` writes. The palatal `l'` is spelled like
`l` and so is the value of no letter. -/
def ofChar : Char → Option Phoneme
  | 'a' => some .a | 'e' => some .e | 'ı' => some .ı | 'i' => some .i
  | 'o' => some .o | 'ö' => some .ö | 'u' => some .u | 'ü' => some .ü
  | 'p' => some .p | 'b' => some .b | 't' => some .t | 'd' => some .d | 'k' => some .k
  | 'g' => some .g | 'c' => some .c | 's' => some .s | 'z' => some .z | 'ş' => some .ş
  | 'v' => some .v | 'h' => some .h | 'm' => some .m | 'n' => some .n | 'l' => some .l
  | 'r' => some .r | 'y' => some .y
  | _ => none

/-- `ofString? s` is the string of segments that the spelled word `s` writes, if every letter
writes one. -/
def ofString? (s : String) : Option (List Segment) :=
  (s.toList.mapM ofChar).map fun w ↦ w.map SegmentLike.coe

end Turkish.Phonology
