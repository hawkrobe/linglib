import Mathlib.Order.Nat
import Linglib.Phonology.Prosody.Mora

/-!
# Syllables and sonority

The syllable (σ) — the second level of the prosodic hierarchy, a non-moraic
onset over a spine of `Mora`s. Weight is the number of morae, so there is no
separate weight type: `Syllable.Weight` is just `Nat`, and `Syllable.weight`
reads it off `morae.length`. Plus the sonority scale, on which segments are
ordered.

## Main definitions

* `Sonority` — the abstract sonority hierarchy (a `LinearOrder`);
  `Sonority.ofSegment` grounds a `Segment` in it via its features.
* `Syllable` — a `Mora`-spine syllable, with `Syllable.moraCount` / `weight`
  and the smart constructor `Syllable.ofCV` from a segmental string.
* `Syllable.Weight` — `Nat` (the mora count), with `.light`/`.heavy`/
  `.superheavy` for readable weight profiles.
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

/-- σ — a syllable: a non-moraic onset over a spine of morae. Weight is the
    number of morae (`moraCount`). -/
structure Syllable where
  onset : List Segment
  morae : List Mora

namespace Syllable

/-- Syllable weight is just the mora count — there is no separate weight type.
    `.light` (1μ), `.heavy` (2μ), `.superheavy` (3μ) name the common values for
    readable weight profiles in metrical and accentual computations. -/
abbrev Weight := Nat

namespace Weight
abbrev light : Weight := 1
abbrev heavy : Weight := 2
abbrev superheavy : Weight := 3
end Weight

/-- The number of morae — the syllable's weight. -/
def moraCount (σ : Syllable) : Nat := σ.morae.length

/-- The syllable's weight (= its mora count). -/
abbrev weight (σ : Syllable) : Weight := σ.moraCount

/-- Build a syllable from a segmental onset–nucleus–coda string. Each nucleus
    segment projects a mora; a coda segment projects a mora iff Weight-by-
    Position is active ([hayes-1989]), otherwise it rides on the last nucleus
    mora (a non-moraic coda). -/
def ofCV (onset nucleus coda : List Segment) (wbp : Bool := true) : Syllable :=
  let nuc := nucleus.map Mora.of
  if wbp then
    ⟨onset, nuc ++ coda.map Mora.of⟩
  else
    match nuc.reverse with
    | last :: rest => ⟨onset, rest.reverse ++ [last.attach coda]⟩
    | []           => ⟨onset, []⟩

end Syllable

end Prosody
