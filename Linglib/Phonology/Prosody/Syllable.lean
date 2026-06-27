import Mathlib.Order.Nat
import Linglib.Phonology.Segment

/-!
# Syllable structure

Syllable constituency (onset–nucleus–coda), the sonority scale, and moraic
weight, following the syllable chapter of *The Handbook of Phonological Theory*
([goldsmith-2011]) and [hayes-2009].

## Main definitions

* `SonorityRank` — the abstract sonority hierarchy, ordered as a `LinearOrder`.
* `sonorityOf` — grounds a `Segment` in `SonorityRank` via its features.
* `Syllable` — an onset–nucleus–coda triple.
* `SyllWeight`, `Syllable.weight` — syllable weight as a mora count.

## Implementation notes

Following [berent-2026], the sonority hierarchy is an abstract ordered type
rather than a bundle of articulatory features: the synchronic grammar operates
on the ordering alone, and the correlation with phonetic features ([±sonorant],
[±approximant], …) is a diachronic fact. `sonorityOf` is the only place those
features enter.
-/

namespace Prosody

open Phonology (Segment)

/-! ### Sonority scale -/

/-- The abstract sonority hierarchy: what the synchronic grammar operates on.

    | Rank | Category  |
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
inductive SonorityRank where
  | stop
  | fricative
  | nasal
  | liquid
  | glide
  | vowel
  deriving DecidableEq, Repr

namespace SonorityRank

/-- Numeric rank (0 = least sonorous). -/
def rank : SonorityRank → Nat
  | .stop => 0 | .fricative => 1 | .nasal => 2
  | .liquid => 3 | .glide => 4 | .vowel => 5

/-- `SonorityRank.rank` is injective. -/
theorem rank_injective : Function.Injective SonorityRank.rank :=
  fun a b h => by cases a <;> cases b <;> simp_all [SonorityRank.rank]

/-- The linear order on sonority ranks, lifted from the numeric ranking. -/
instance : LinearOrder SonorityRank :=
  LinearOrder.lift' SonorityRank.rank rank_injective

end SonorityRank

/-- Ground a segment in the sonority hierarchy by its phonetic features.

    Following [hayes-2009], the hierarchy is decomposed by four features
    ([±sonorant] > [±approximant] > [±consonantal] > [±syllabic]), with
    [clements-1990]'s refinement splitting obstruents by [±continuant]. This is
    the only bridge from phonetic substance to the abstract `SonorityRank`. -/
def sonorityOf (s : Segment) : SonorityRank :=
  if s.HasValue .sonorant false then
    if s.HasValue .continuant true then .fricative else .stop
  else if s.HasValue .approximant false then .nasal
  else if s.HasValue .consonantal true then .liquid
  else if s.HasValue .syllabic true then .vowel
  else .glide

/-! ### Syllable constituents -/

/-- A syllable: onset, nucleus, coda. -/
structure Syllable where
  onset   : List Segment
  nucleus : List Segment
  coda    : List Segment

/-! ### Syllable weight -/

/-- Syllable weight as a mora count. `SyllWeight` wraps the actual count rather
    than a lossy 3-value enum, so the `MoraicSyllable → SyllWeight → PrWd`
    pipeline preserves exact mora counts. The names `.light` (1μ), `.heavy` (2μ),
    and `.superheavy` (3μ) abbreviate the common values. -/
structure SyllWeight where
  /-- The mora count: 1μ = light (CV), 2μ = heavy (CVV, CVC),
      3μ = superheavy (CVVC, CVCC). -/
  morae : Nat
  deriving DecidableEq, Repr

namespace SyllWeight
abbrev light : SyllWeight := ⟨1⟩
abbrev heavy : SyllWeight := ⟨2⟩
abbrev superheavy : SyllWeight := ⟨3⟩
end SyllWeight

/-- Mora count. `codaMoraic = true` means coda consonants contribute weight
    (the Weight-by-Position parameter of [hayes-1989]). -/
def Syllable.moraCount (σ : Syllable) (codaMoraic : Bool := true) : Nat :=
  σ.nucleus.length + if codaMoraic then σ.coda.length else 0

/-- Weight from the mora count. -/
def Syllable.weight (σ : Syllable) (codaMoraic : Bool := true) : SyllWeight :=
  ⟨σ.moraCount codaMoraic⟩

/-! ### Syllabified form -/

/-- A word parsed into syllables. -/
structure SyllabifiedForm where
  syllables : List Syllable

end Prosody
