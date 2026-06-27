import Linglib.Phonology.Segment
import Linglib.Phonology.Prosody.Syllable

/-!
# Natural Classes and the Parker Sonority Scale
[parker-2002]

The 8-level Parker sonority scale refines [clements-1990]'s 6-level
hierarchy by splitting obstruents into four classes based on [±continuant]
and [±voice]:

| Class              | son | cont | voice | Rank |
|--------------------|-----|------|-------|------|
| Voiceless stops    |  −  |  −   |  −    |  1   |
| Voiceless fric.    |  −  |  +   |  −    |  2   |
| Voiced stops       |  −  |  −   |  +    |  3   |
| Voiced fricatives  |  −  |  +   |  +    |  4   |
| Nasals             |  +  |  −   |  ±    |  5   |
| Liquids / Taps     |  +  |  +   |  ±    |  6   |
| Glides             |  +  |  +   |  ±    |  7   |
| Vowels             |  +  |  +   |  ±    |  8   |

Sonorants (ranks 5–8) are distinguished by [±approximant], [±consonantal],
and [±syllabic], exactly as in the Clements scale (`Sonority`). The
Parker refinement adds [±voice] only within obstruents.

Crucially, [parker-2002] ranks **voiced stops above voiceless fricatives**
(`vds > vlf`) — his intensity-based experimental result and the inverse of
the more common textbook ordering. Parker presents this as the *default
universal* ranking, which "in specific languages may be reversed" (e.g.
Imdlawn Tashlhiyt Berber ranks them the other way).

This finer granularity is needed for sonority-conditioned gradient
phenomena such as intrusive vowel insertion in Tarifit Berber
([afkir-zellou-2025]).
-/

namespace Prosody

open Phonology (Segment)

/-! ### Natural class -/

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

/-- Parker's default universal 8-level sonority ranking ([parker-2002]):
    voiced stops outrank voiceless fricatives (`vds = 3 > vlf = 2`), per
    Parker's intensity measurements. Reversible in particular languages. -/
def NatClass.parkerSonority : NatClass → Nat
  | .vls => 1 | .vlf => 2 | .vds => 3 | .vdf => 4
  | .nasal => 5 | .liquid => 6 | .glide => 7 | .vowel => 8

/-! ### Segment classification -/

/-- Classify a segment into the Parker 8-level scale.
    Follows the feature decomposition of `Sonority` but additionally
    splits obstruents by [±voice] ([parker-2002]). -/
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

/-! ### Bridge to the sonority hierarchy -/

/-- Map NatClass to the abstract `Sonority`. This collapses the Parker
    voicing distinction within obstruents (vls/vds → stop, vlf/vdf → fricative),
    connecting the fine-grained 8-level scale to the substance-free 6-level
    hierarchy that the grammar operates on. -/
def NatClass.toSonority : NatClass → Sonority
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

end Prosody
