/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Segmental.Basic
import Linglib.Phonology.Segmental.FeatureClass

/-!
# Akan segments

This file lists the vowels of Akan as segments, together with the two consonants of its
velar–palatal alternation. Akan has nine vowels, /i ɪ e ɛ a ɔ o ʊ u/, which Dolphyne
groups into an advanced set /i e o u/ and an unadvanced set /ɪ ɛ a ɔ ʊ/ that do not mix
within a word, the tongue-root harmony Stewart identified; in Casali's typology the
inventory is a five-height system, with the low vowel the only one lacking a partner. In
Akuapem and Asante a tenth quality, the advanced variant of /a/ before syllables with
/i u/, joins the advanced set; it is not represented here. Velar stops become corono-dorsal
palatal affricates before front vowels, the alternation McCarthy and Prince's account of
Akan reduplication turns on; the consonants carry Hayes's manner and laryngeal
specifications and McCarthy and Prince's corono-dorsal analysis of the palatal.

## Main definitions

* `Akan.Phonology.Vowel`: the nine vowels.
* `Akan.Phonology.Vowel.segment`: the segment of each vowel.
* `Akan.Phonology.Vowel.atr`: the [ATR] value of each vowel.
* `Akan.Phonology.inventory`: the set of vowel segments.
* `Akan.Phonology.Consonant`: the velar stop and its palatalized output.
* `Akan.Phonology.Consonant.segment`: the segment of each consonant.

## References

* [dolphyne-1988]
* [stewart-1967]
* [casali-2003]
* [mccarthy-prince-1995]
* [hayes-2009]
-/

open Phonology

namespace Akan.Phonology

/-! ### Vowels -/

/-- The nine vowels of Akan. Constructor names ASCII-ize the IPA, a capital standing for the
unadvanced counterpart: `I` is ɪ, `E` is ɛ, `O` is ɔ, and `U` is ʊ. -/
inductive Vowel where
  | i | e | o | u
  | I | E | a | O | U
  deriving DecidableEq, Repr, Fintype

/-- The vowel of the given height and backness, rounded or not, with the given [ATR]
value. -/
private def vowel (ht : Segment.Height) (bk : Segment.Backness) (round atr : Bool) :
    Segment :=
  ((Segment.vowel ht bk).setFeature .round round).setFeature .atr atr

/-- The segment of each vowel. The pairs /i ɪ/, /e ɛ/, /o ɔ/ and /u ʊ/ differ only in
[ATR], and /a/ is the unadvanced low vowel. -/
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

/-- The set of vowel segments. -/
def inventory : Finset Segment := Finset.univ.image Vowel.segment

/-- The [ATR] value of a vowel is read off its segment. -/
def Vowel.atr (v : Vowel) : Bool := decide (v.segment.HasValue .atr true)

/-! ### The velar–palatal alternation -/

/-- The voiceless velar stop /k/ and the voiceless palatal affricate /tɕ/ it becomes before
a front vowel. -/
inductive Consonant where
  | k | tc
  deriving DecidableEq, Repr, Fintype

/-- The segment of each consonant. The stop is [+dorsal, −coronal]; the affricate keeps
[+dorsal] and adds [+coronal, −anterior, +distributed] with delayed release, so it is a
corono-dorsal complex segment. -/
def Consonant.segment : Consonant → Segment
  | .k => Segment.ofSpecs
      [(.syllabic, false), (.consonantal, true), (.sonorant, false), (.continuant, false),
       (.voice, false), (.delayedRelease, false), (.dorsal, true), (.coronal, false)]
  | .tc => Segment.ofSpecs
      [(.syllabic, false), (.consonantal, true), (.sonorant, false), (.continuant, false),
       (.voice, false), (.delayedRelease, true), (.dorsal, true), (.coronal, true),
       (.anterior, false), (.distributed, true)]

/-- Palatalization changes the value of [coronal]. -/
theorem k_tc_coronal :
    Consonant.k.segment.HasValue .coronal false ∧
      Consonant.tc.segment.HasValue .coronal true := by
  decide

/-- The palatal affricate has two designated articulators. -/
theorem tc_isComplex : Consonant.tc.segment.IsComplex := by decide

/-- The front vowel /ɪ/ triggers palatalization and the low vowel /a/ does not. -/
theorem I_front_a_not_front :
    Vowel.I.segment.HasValue .front true ∧ Vowel.a.segment.HasValue .front false := by
  decide

end Akan.Phonology
