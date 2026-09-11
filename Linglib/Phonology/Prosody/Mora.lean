import Linglib.Phonology.Segmental.Basic

/-!
# Morae

The mora (μ) — the base node of the prosodic hierarchy and the unit of
syllable weight, following [hayes-1989]. A mora is an autosegmental node on
the prosodic tier that *dominates* melodic material (segments). Weight is the
number of morae; a syllable, foot, and word are each a structure dominating the
level below (`Syllable`, `Foot`, `Word`), so weight aggregates up one uniform
`moraCount` API.

A long vowel is two morae dominating the same melody; a non-moraic coda rides
on the preceding mora's `dominates`.

## Main definitions

* `Mora` — a prosodic-tier node dominating a melody.
* `Mora.of`, `Mora.attach` — the mora of one segment, and adjunction of further
  melody (a non-moraic coda) to a mora.
-/

namespace Prosody

open Phonology (Segment)

/-- A mora (μ): a prosodic-tier node dominating the melody linked to it. A long
    vowel is two morae dominating the same melody; a non-moraic coda rides on the
    preceding mora's `dominates`. -/
structure Mora where
  /-- The melody this μ node dominates. -/
  dominates : List Segment
  deriving DecidableEq

namespace Mora

/-- The mora dominating a single segment. -/
def of (s : Segment) : Mora := ⟨[s]⟩

/-- Attach extra melody (e.g. a non-moraic coda) to a mora. -/
def attach (μ : Mora) (segs : List Segment) : Mora := ⟨μ.dominates ++ segs⟩

end Mora

end Prosody
