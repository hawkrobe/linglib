/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Segmental.Basic

/-!
# Guébie vowels

Guébie (Kru; Côte d'Ivoire) has ten vowels, five [+ATR] vowels /i e ə o u/ paired with five
[−ATR] vowels /ɪ ɛ a ɔ ʊ/ ([sande-2022] §3.2). The pairs agree in backness and rounding, and in
height except for /ə a/. Vowels within a morpheme agree in [ATR], and affixes harmonize with
roots.

## Main definitions

* `Guebie.Vowel`, `Guebie.Vowel.segment`, `Guebie.inventory`: the ten vowels, their
  segments, and the inventory.
* `Guebie.Vowel.atr`: the ±ATR split, read off the segment.
* `Guebie.Vowel.withATR`: the member of a vowel's pair with a given [ATR] value.

## References

* [sande-2022]
-/

@[expose] public section

namespace Guebie

open Phonology

/-- Guébie has ten vowels ([sande-2022] §3.2). Constructor names ASCII-ize the
    IPA (capital = lax −ATR counterpart): `schwa` = ə, `I` = ɪ, `E` = ɛ,
    `O` = ɔ, `U` = ʊ. -/
inductive Vowel where
  | i | e | schwa | o | u
  | I | E | a | O | U
  deriving DecidableEq, Repr, Fintype

/-- A vowel of the given height and backness, rounded or not, with its [ATR] value. -/
def vowel (ht : Segment.Height) (bk : Segment.Backness) (round atr : Bool) :
    Segment :=
  ((Segment.vowel ht bk).setFeature .round round).setFeature .atr atr

/-- Each vowel has its segment, the ±ATR pairs being /i ɪ/, /e ɛ/, /o ɔ/, /u ʊ/ and /ə a/. -/
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

/-- The member of a vowel's pair with the given [ATR] value. The pair /ə a/ differs in height
too, so this is not `Segment.setFeature .atr` on the segment. -/
def Vowel.withATR : Vowel → Bool → Vowel
  | .i, b | .I, b => if b then .i else .I
  | .e, b | .E, b => if b then .e else .E
  | .schwa, b | .a, b => if b then .schwa else .a
  | .o, b | .O, b => if b then .o else .O
  | .u, b | .U, b => if b then .u else .U

@[simp] theorem Vowel.atr_withATR (v : Vowel) (b : Bool) : (v.withATR b).atr = b := by
  cases v <;> cases b <;> decide

@[simp] theorem Vowel.withATR_atr (v : Vowel) : v.withATR v.atr = v := by
  cases v <;> decide

end Guebie
