import Linglib.Theories.Phonology.Featural.Features
import Linglib.Theories.Phonology.Prosodic.Syllable.Defs

/-!
# Natural Classes and the Parker Sonority Scale
@cite{parker-2002}

The 8-level Parker sonority scale refines @cite{clements-1990}'s 6-level
hierarchy by splitting obstruents into four classes based on [±continuant]
and [±voice]:

| Class              | son | cont | voice | Rank |
|--------------------|-----|------|-------|------|
| Voiceless stops    |  −  |  −   |  −    |  1   |
| Voiced stops       |  −  |  −   |  +    |  2   |
| Voiceless fric.    |  −  |  +   |  −    |  3   |
| Voiced fricatives  |  −  |  +   |  +    |  4   |
| Nasals             |  +  |  −   |  ±    |  5   |
| Liquids / Taps     |  +  |  +   |  ±    |  6   |
| Glides             |  +  |  +   |  ±    |  7   |
| Vowels             |  +  |  +   |  ±    |  8   |

Sonorants (ranks 5–8) are distinguished by [±approximant], [±consonantal],
and [±syllabic], exactly as in the Clements scale (`SonorityRank`). The
Parker refinement adds [±voice] only within obstruents.

This finer granularity is needed for sonority-conditioned gradient
phenomena such as intrusive vowel insertion in Tarifit Berber
(@cite{afkir-zellou-2025}).
-/

namespace Phonology.Syllable

open Phonology (Segment Feature)

-- ============================================================================
-- § 1: Natural Class Type
-- ============================================================================

/-- Natural-class partition for the 8-level Parker sonority scale.
    Refines the Clements 6-level hierarchy by splitting obstruents
    into four voicing × continuancy classes. -/
inductive NatClass where
  | vls    -- voiceless stops: [−son, −cont, −voice]
  | vds    -- voiced stops: [−son, −cont, +voice]
  | vlf    -- voiceless fricatives: [−son, +cont, −voice]
  | vdf    -- voiced fricatives: [−son, +cont, +voice]
  | nasal  -- nasals: [+son, −approx]
  | liquid -- liquids/taps: [+son, +approx, +cons]
  | glide  -- glides: [+son, +approx, −cons, −syll]
  | vowel  -- vowels: [+son, +approx, −cons, +syll]
  deriving DecidableEq, Repr

/-- Parker (2002) 8-level sonority ranking. -/
def NatClass.parkerSonority : NatClass → Nat
  | .vls => 1 | .vds => 2 | .vlf => 3 | .vdf => 4
  | .nasal => 5 | .liquid => 6 | .glide => 7 | .vowel => 8

-- ============================================================================
-- § 2: Segment Classification
-- ============================================================================

/-- Classify a segment into the Parker 8-level scale.
    Follows the feature decomposition of `SonorityRank` but additionally
    splits obstruents by [±voice] (@cite{parker-2002}). -/
def natClassOf (s : Segment) : NatClass :=
  if s.HasValue .sonorant false then
    -- Obstruent: split by [±continuant] then [±voice]
    if s.HasValue .continuant true then
      if s.HasValue .voice true then .vdf else .vlf
    else
      if s.HasValue .voice true then .vds else .vls
  else if s.HasValue .approximant false then .nasal
  else if s.HasValue .consonantal true then .liquid
  else if s.HasValue .syllabic true then .vowel
  else .glide

/-- Parker sonority of a segment (convenience). -/
def parkerSonorityOf (s : Segment) : Nat :=
  (natClassOf s).parkerSonority

-- ============================================================================
-- § 3: Verification
-- ============================================================================

/-- Map NatClass to the abstract `SonorityRank`. This collapses the Parker
    voicing distinction within obstruents (vls/vds → stop, vlf/vdf → fricative),
    connecting the fine-grained 8-level scale to the substance-free 6-level
    hierarchy that the grammar operates on. -/
def NatClass.toSonorityRank : NatClass → SonorityRank
  | .vls | .vds => .stop
  | .vlf | .vdf => .fricative
  | .nasal => .nasal
  | .liquid => .liquid
  | .glide => .glide
  | .vowel => .vowel

/-- Parker sonority is strictly monotone: the ranking is a total order. -/
theorem parker_strictly_monotone (a b : NatClass) (h : a ≠ b) :
    NatClass.parkerSonority a < NatClass.parkerSonority b ∨
    NatClass.parkerSonority a > NatClass.parkerSonority b := by
  cases a <;> cases b <;> simp_all [NatClass.parkerSonority]

end Phonology.Syllable
