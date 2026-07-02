import Linglib.Phonology.Segmental.Basic

/-!
# Morae

The mora (μ) — the base node of the prosodic hierarchy and the unit of
syllable weight, following [hayes-1989]. A mora is an autosegmental node on
the prosodic tier that *dominates* melodic material (segments). Weight is the
number of morae; a syllable, foot, and word are each a structure dominating the
level below (`Syllable`, `Foot`, `Word`), so weight aggregates up one uniform
`moraCount` API.

A mora that dominates nothing (`dominates = []`) is **stranded**: the segment
it dominated was deleted but the μ node survives. This is the engine of
compensatory lengthening — the stranded μ is re-associated to an adjacent
segment rather than a count being shuffled on a side channel.

## Main definitions

* `Mora` — a prosodic-tier node dominating a (possibly empty) melody.
* `Mora.of`, `Mora.stranded` — the ordinary and floating morae.
* `Mora.IsStranded` — the mora dominates no melody.
-/

namespace Prosody

open Phonology (Segment)

/-- A mora (μ): a prosodic-tier node dominating the melody linked to it.
    `dominates = []` is a stranded/floating mora (its segment was deleted but
    the μ node survives). A long vowel is two morae dominating the same melody;
    a non-moraic coda rides on the preceding mora's `dominates`. -/
structure Mora where
  /-- The melody this μ node dominates; `[]` is a stranded/floating mora. -/
  dominates : List Segment
  deriving DecidableEq

namespace Mora

/-- The mora dominating a single segment. -/
def of (s : Segment) : Mora := ⟨[s]⟩

/-- A stranded (floating) mora, dominating no melody. -/
def stranded : Mora := ⟨[]⟩

/-- The mora is stranded — it dominates no melody. -/
abbrev IsStranded (μ : Mora) : Prop := μ.dominates = []

/-- Attach extra melody (e.g. a non-moraic coda) to a mora. -/
def attach (μ : Mora) (segs : List Segment) : Mora := ⟨μ.dominates ++ segs⟩

end Mora

end Prosody
