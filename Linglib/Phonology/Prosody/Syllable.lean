import Mathlib.Order.Nat
import Linglib.Phonology.Segment

/-!
# Syllable structure

The syllable as a phonological object — sonority, constituency, and weight —
following the syllable chapter of *The Handbook of Phonological Theory*
([goldsmith-2011]) and [hayes-2009].

## Main definitions

* `Sonority` — the abstract sonority hierarchy (a `LinearOrder`);
  `Sonority.ofSegment` grounds a `Segment` in it via its features.
* `Syllable` — an onset–nucleus–coda triple, with `Syllable.moraCount`,
  `Syllable.weight`, and the nested weight object `Syllable.Weight`.
* `SyllabifiedForm` — a word parsed into syllables.

## Implementation notes

Following [berent-2026], sonority is an abstract ordered type rather than a
bundle of articulatory features: the grammar operates on the ordering alone,
and `Sonority.ofSegment` is the only place phonetic features ([±sonorant],
[±approximant], …) enter.
-/

namespace Prosody

open Phonology (Segment)

/-! ### Sonority -/

/-- The abstract sonority hierarchy: what the synchronic grammar operates on.

    | Rank | Class     |
    |------|-----------|
    |  0   | Stop      |
    |  1   | Fricative |
    |  2   | Nasal     |
    |  3   | Liquid    |
    |  4   | Glide     |
    |  5   | Vowel     |

    The six levels follow [clements-1990]'s refinement of the basic 5-class
    hierarchy (splitting obstruents by [±continuant]); see
    `NatClass.parkerSonority` for the finer 8-level Parker scale. -/
inductive Sonority where
  | stop
  | fricative
  | nasal
  | liquid
  | glide
  | vowel
  deriving DecidableEq, Repr

namespace Sonority

/-- Numeric rank (0 = least sonorous). -/
def rank : Sonority → Nat
  | .stop => 0 | .fricative => 1 | .nasal => 2
  | .liquid => 3 | .glide => 4 | .vowel => 5

instance : LinearOrder Sonority :=
  LinearOrder.lift' rank fun a b h => by cases a <;> cases b <;> simp_all [rank]

/-- The sonority of a segment, read off its phonetic features
    ([hayes-2009], [clements-1990]). -/
def ofSegment (s : Segment) : Sonority :=
  if s.HasValue .sonorant false then
    if s.HasValue .continuant true then .fricative else .stop
  else if s.HasValue .approximant false then .nasal
  else if s.HasValue .consonantal true then .liquid
  else if s.HasValue .syllabic true then .vowel
  else .glide

end Sonority

/-! ### Syllables -/

/-- A syllable: onset, nucleus, coda. -/
structure Syllable where
  onset   : List Segment
  nucleus : List Segment
  coda    : List Segment

namespace Syllable

/-- Syllable weight as a mora count. `Weight` wraps the actual count rather
    than a lossy 3-value enum, so the `MoraicSyllable → Syllable.Weight → PrWd`
    pipeline preserves exact mora counts. The names `.light` (1μ), `.heavy`
    (2μ), and `.superheavy` (3μ) abbreviate the common values. -/
structure Weight where
  /-- The mora count: 1μ = light (CV), 2μ = heavy (CVV, CVC),
      3μ = superheavy (CVVC, CVCC). -/
  morae : Nat
  deriving DecidableEq, Repr

namespace Weight
abbrev light : Weight := ⟨1⟩
abbrev heavy : Weight := ⟨2⟩
abbrev superheavy : Weight := ⟨3⟩
end Weight

/-- Mora count. `codaMoraic = true` means coda consonants contribute weight
    (the Weight-by-Position parameter of [hayes-1989]). -/
def moraCount (σ : Syllable) (codaMoraic : Bool := true) : Nat :=
  σ.nucleus.length + if codaMoraic then σ.coda.length else 0

/-- Weight from the mora count. -/
def weight (σ : Syllable) (codaMoraic : Bool := true) : Weight :=
  ⟨σ.moraCount codaMoraic⟩

end Syllable

/-! ### Syllabified forms -/

/-- A word parsed into syllables. -/
structure SyllabifiedForm where
  syllables : List Syllable

end Prosody
