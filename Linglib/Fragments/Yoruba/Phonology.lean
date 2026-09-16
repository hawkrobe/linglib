/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Segmental.Basic

/-!
# Yoruba vowels

The seven oral vowels of Standard Yoruba, /i e ɛ a ɔ o u/, the mid-only tongue-root system
of [casali-2003] analyzed in [archangeli-pulleyblank-1989]: the mid vowels pair, /e o/ [+ATR]
against /ɛ ɔ/ [−ATR], while the high vowels /i u/ are [+ATR] and the low vowel /a/
[−ATR] without counterparts. Non-high vowels in a word agree in ATR. The nasal vowels
are not represented.

## Main definitions

* `Yoruba.Vowel`, `Yoruba.Vowel.segment`, `Yoruba.inventory`: the seven vowels, their
  segments, and the inventory.
* `Yoruba.Vowel.atr`: the ±ATR split, read off the segment.
-/

namespace Yoruba

open Phonology

/-- The seven oral vowels. Constructor names ASCII-ize the IPA: `E` = ɛ, `O` = ɔ. -/
inductive Vowel where
  | i | e | E | a | O | o | u
  deriving DecidableEq, Repr, Fintype

/-- A vowel of the given height and backness, rounded or not, with its [ATR] value. -/
private def vowel (ht : Segment.Height) (bk : Segment.Backness) (round atr : Bool) :
    Segment :=
  ((Segment.vowel ht bk).setFeature .round round).setFeature .atr atr

/-- Each vowel's segment: the mid pairs /e ɛ/ and /o ɔ/, unpaired /i u/ and /a/. -/
def Vowel.segment : Vowel → Segment
  | .i => vowel .high .front false true
  | .e => vowel .mid .front false true
  | .E => vowel .mid .front false false
  | .a => vowel .low .central false false
  | .O => vowel .mid .back true false
  | .o => vowel .mid .back true true
  | .u => vowel .high .back true true

/-- The vowel inventory. -/
def inventory : Finset Segment := Finset.univ.image Vowel.segment

/-- The ±ATR split, read off the segment. -/
def Vowel.atr (v : Vowel) : Bool := decide (v.segment.HasValue .atr true)

end Yoruba
