import Linglib.Semantics.Quantification.Counting
import Linglib.Semantics.Composition.Ty

/-!
# Determiner readings as composition terminals

A reading of a quantificational determiner, a `Quantifier.GQ.Family`, is a composition
terminal on any finite entity domain: at the determiner type `Ty.det`, whose domain on `E` is
`GQ E` by definition, its value is the family at `E`. A fragment carrier therefore feeds
`Composition.Tree.interp` directly, its leaf interpretation choosing among the terminals of the
word's available readings, and the string lexicon shrinks to the words no carrier yet holds.

## Main declarations

* `Quantifier.GQ.Family.toDenotation` is a reading as a terminal on a domain.
* `Quantifier.GQ.terminals` is the set of terminals of a set of readings, the image of a word's
  `⟦w⟧`.

## References

* [heim-kratzer-1998]
* [barwise-cooper-1981]
-/

namespace Quantifier.GQ

open Semantics.Composition

/-- A reading as a composition terminal on the entity domain `E`, at the determiner type. -/
def Family.toDenotation (d : Family.{0}) (E W : Type) [Fintype E] : Denotation E W :=
  ⟨Ty.det, d E⟩

/-- The terminals of a set of readings on a domain. -/
def terminals (s : Set Family.{0}) (E W : Type) [Fintype E] : Set (Denotation E W) :=
  (Family.toDenotation · E W) '' s

theorem toDenotation_mem_terminals {s : Set Family.{0}} {d : Family.{0}} (h : d ∈ s)
    (E W : Type) [Fintype E] : d.toDenotation E W ∈ terminals s E W :=
  Set.mem_image_of_mem _ h

end Quantifier.GQ
