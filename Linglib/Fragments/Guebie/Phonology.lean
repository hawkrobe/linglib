/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Segmental.Basic

/-!
# Guébie vowels

The ten-vowel ±ATR inventory of Guébie (Kru; Côte d'Ivoire), [sande-2022] §3.2: five
[+ATR] vowels /i e ə o u/ paired with five [−ATR] vowels /ɪ ɛ a ɔ ʊ/, the pairs
agreeing in height, backness and rounding. Vowels within a morpheme agree in ATR, and
affixes harmonize with roots.

## Main definitions

* `Guebie.Vowel`, `Guebie.Vowel.segment`, `Guebie.inventory`: the ten vowels, their
  segments, and the inventory.
* `Guebie.Vowel.atr`: the ±ATR split, read off the segment.
-/

namespace Guebie

open Phonology

/-- The ten Guébie vowels ([sande-2022] §3.2). Constructor names ASCII-ize the
    IPA (capital = lax −ATR counterpart): `schwa` = ə, `I` = ɪ, `E` = ɛ,
    `O` = ɔ, `U` = ʊ. -/
inductive Vowel where
  | i | e | schwa | o | u
  | I | E | a | O | U
  deriving DecidableEq, Repr, Fintype

/-- A vowel of the given height and backness, rounded or not, with its [ATR] value. -/
private def vowel (ht : Segment.Height) (bk : Segment.Backness) (round atr : Bool) :
    Segment :=
  ((Segment.vowel ht bk).setFeature .round round).setFeature .atr atr

/-- Each vowel's segment: the ±ATR pairs /i ɪ/, /e ɛ/, /o ɔ/, /u ʊ/ and /ə a/. -/
def Vowel.segment : Vowel → Segment
  | .i => vowel .high .front false true
  | .e => vowel .mid .front false true
  | .schwa => vowel .mid .central false true
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

end Guebie
