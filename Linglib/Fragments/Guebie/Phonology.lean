/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Guébie vowels

Guébie (Kru; Côte d'Ivoire) has ten vowels, five [+ATR] vowels /i e ə o u/ paired with five
[−ATR] vowels /ɪ ɛ a ɔ ʊ/, as Sande describes them. The pairs agree in backness and rounding,
and in height except for /ə a/. Vowels within a morpheme agree in [ATR], and affixes harmonize
with roots.

The feature values come from the PHOIBLE chart, which codes the tongue-root contrast by
[tense], so a vowel is the segment of its chart entry's tongue-root reading. The chart's /ə/
is [−tense], and Guébie's /ə/ departs from it in being [+ATR].

## Main definitions

* `Guebie.Vowel`, `Guebie.Vowel.segment`, `Guebie.inventory`: the ten vowels, their
  segments from the chart, and the inventory.
* `Guebie.Vowel.atr`: the ±ATR split, read off the segment.
* `Guebie.Vowel.withATR`: the member of a vowel's pair with a given [ATR] value.

## References

* [sande-2022]
-/

@[expose] public section

namespace Guebie

open Phonology

/-- The ten Guébie vowels. Constructor names ASCII-ize the IPA, a capital being the [−ATR]
counterpart, so that `schwa` is ə, `I` is ɪ, `E` is ɛ, `O` is ɔ and `U` is ʊ. -/
inductive Vowel where
  | i | e | schwa | o | u
  | I | E | a | O | U
  deriving DecidableEq, Repr, Fintype

/-- A vowel is the segment of its chart entry's tongue-root reading, with its departure. -/
def vowel (m : Data.PHOIBLE.FeatureMatrix) (departure : Segment := ⊥) : Segment :=
  .ofChart m.tenseAsATR departure

/-- Each vowel has its segment, the ±ATR pairs being /i ɪ/, /e ɛ/, /o ɔ/, /u ʊ/ and /ə a/. -/
def Vowel.segment : Vowel → Segment
  | .i => vowel .«i»
  | .e => vowel .«e»
  | .schwa => vowel .«ə» (.ofSpecs [(.atr, true)])
  | .o => vowel .«o»
  | .u => vowel .«u»
  | .I => vowel .«ɪ»
  | .E => vowel .«ɛ»
  | .a => vowel .«a»
  | .O => vowel .«ɔ»
  | .U => vowel .«ʊ»

/-- The ten vowels have ten segments. -/
theorem Vowel.segment_injective : Function.Injective Vowel.segment := by decide

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
