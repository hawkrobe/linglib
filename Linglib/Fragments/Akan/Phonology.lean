/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Segmental.Basic
import Linglib.Phonology.Segmental.FeatureClass
import Linglib.Phonology.Subregular.LocalRewrite

/-!
# Akan segments

The nine-vowel ±ATR inventory of Akan (Kwa; Ghana), /i ɪ e ɛ a ɔ o ʊ u/
([stewart-1967]; [dolphyne-1988]): four [+ATR] vowels /i e o u/ paired with /ɪ ɛ ɔ ʊ/,
and the low vowel /a/ [−ATR] without a phonemic counterpart. Vowels in a word agree in
tongue-root position, the contrast Stewart first identified as tongue-root advancement.
With them, the consonants of the velar–palatal alternation that reduplication interacts
with ([mccarthy-prince-1995] §5.1): velars become corono-dorsal palatals before front
vowels, with the feature specifications of [hayes-2009] for manner and laryngeal
features and the corono-dorsal analysis of the palatals from McCarthy and Prince.

## Main definitions

* `Akan.Phonology.Vowel`, `Vowel.segment`, `Akan.Phonology.inventory`: the nine vowels,
  their segments, and the inventory; `Vowel.atr` is the ±ATR split.
* `Akan.Phonology.seg_k`, `Akan.Phonology.seg_tc`: the velar stop and its palatalized
  output.
-/

open Phonology

namespace Akan.Phonology

/-! ### Vowels -/

/-- The nine vowels. Constructor names ASCII-ize the IPA (capital = lax −ATR
    counterpart): `I` = ɪ, `E` = ɛ, `O` = ɔ, `U` = ʊ. -/
inductive Vowel where
  | i | e | o | u
  | I | E | a | O | U
  deriving DecidableEq, Repr, Fintype

/-- A vowel of the given height and backness, rounded or not, with its [ATR] value. -/
private def vowel (ht : Segment.Height) (bk : Segment.Backness) (round atr : Bool) :
    Segment :=
  ((Segment.vowel ht bk).setFeature .round round).setFeature .atr atr

/-- Each vowel's segment: the ±ATR pairs /i ɪ/, /e ɛ/, /o ɔ/, /u ʊ/ and unpaired /a/. -/
def Vowel.segment : Vowel → Segment
  | .i => vowel .high .front false true
  | .e => vowel .mid .front false true
  | .o => vowel .mid .back true true
  | .u => vowel .high .back true true
  | .I => vowel .high .front false false
  | .E => vowel .mid .front false false
  | .a => vowel .low .central false false
  | .O => vowel .mid .back true false
  | .U => vowel .high .back true false

/-- The vowel inventory. -/
def inventory : Finset Segment := Finset.univ.image Vowel.segment

/-- The ±ATR split, read off the segment. -/
def Vowel.atr (v : Vowel) : Bool := decide (v.segment.HasValue .atr true)

/-! ### The velar–palatal alternation -/

/-- /k/: voiceless velar stop, [+dorsal, −coronal], the underlying segment in stems like
    /ka/ 'bite'. -/
def seg_k : Segment := Segment.ofSpecs
  [(.syllabic, false), (.consonantal, true), (.sonorant, false), (.continuant, false),
   (.voice, false), (.delayedRelease, false), (.dorsal, true), (.coronal, false)]

/-- /tɕ/: voiceless palatal affricate, [+coronal, +dorsal, +del.rel.], the palatalized
    output of /k/ before front vowels: a corono-dorsal complex segment, palatalization
    spreading [+coronal, −anterior] from the front vowel while preserving [+dorsal]. -/
def seg_tc : Segment := Segment.ofSpecs
  [(.syllabic, false), (.consonantal, true), (.sonorant, false), (.continuant, false),
   (.voice, false), (.delayedRelease, true), (.dorsal, true), (.coronal, true),
   (.anterior, false), (.distributed, true)]

/-- Palatalization is a [coronal] feature change: /k/ is [−cor], /tɕ/ is [+cor], the
    difference IDENT-IO(−cor) and IDENT-BR(−cor) penalize. -/
theorem palatalization_is_coronal_change :
    seg_k.HasValue .coronal false ∧ seg_tc.HasValue .coronal true := by decide

/-- Both segments are [+dorsal]: the palatal is a corono-dorsal complex segment. -/
theorem seg_tc_isComplex : seg_k.HasValue .dorsal true ∧ seg_tc.IsComplex := by decide

/-- The front vowel /ɪ/ triggers palatalization; the low vowel /a/ does not. -/
theorem front_trigger :
    Vowel.I.segment.HasValue .front true ∧ Vowel.a.segment.HasValue .front false := by
  decide

end Akan.Phonology
