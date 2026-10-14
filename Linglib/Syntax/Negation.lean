module

public import Linglib.Morphology.Morph

/-!
# Standard negation

A language negates a declarative verbal main clause with a marker: an affix on the verb, a free
particle, an inflecting negative verb, or two morphemes at once (French *ne … pas*). A negative
may differ from its affirmative only by the marker, or the clause may also change, taking a
nonfinite verb form or losing tense distinctions, the divide Miestamo calls symmetric and
asymmetric.

## Main declarations

* `Negation.Marker`: a standard negation marker, as the morphs exponing it.

## Implementation notes

A typology of markers or of negative constructions is one author's classification and lives in that
author's study, such as Miestamo's symmetry in `Studies/Miestamo2005.lean`, whose
affirmative–negative pairs are its example rows. An inflecting negative verb is cited by its stem,
and its endings form an `Agreement.Paradigm` in the language's fragment.

## References

* [miestamo-2005]
-/

@[expose] public section

namespace Negation

open Morphology (Morph)

/-- A standard sentential negation marker. -/
structure Marker where
  /-- The exponent as contiguous pieces in surface order; a bipartite
      marker has two (Burmese *ma-…-bu*). Affixal alternants are recorded by
      an abstract citation form (Turkish *-mA-* for *-ma-* ~ *-me-*). -/
  pieces : List (List Morph)
  deriving DecidableEq, Repr

/-- The surface form of a marker is its pieces in boundary notation, separated by `…`. -/
def Marker.form (m : Marker) : String := String.intercalate "…" (m.pieces.map Morph.surface)

/-- The morphs of a marker, across its pieces. -/
def Marker.morphs (m : Marker) : List Morph := m.pieces.flatten

end Negation
