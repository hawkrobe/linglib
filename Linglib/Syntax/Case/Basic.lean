import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Case

The comparative case values: the labels under which the case systems of different languages are
compared. A language's own cases are its fragment's business, and a fragment maps them to these
labels. The hierarchies and orders the literature places on the labels are each stated where they
are used: the containment orders in `Syntax/Case/Order.lean` and Blake's hierarchy of case
systems in `Studies/Blake1994.lean`.

The Universal Dependencies case tags are the corpus vocabulary, reached through
`Morphology/Word/UD.lean`. The two inventories coincide cell for cell
([de-marneffe-zeman-2021]).

## Main declarations

* `Case`: the comparative case values.
* `Case.Marker`: a case marker, its form and the cases it realizes, with `Case.Marker.inventory`
  the cases a set of markers realizes.

## References

* [blake-1994]
* [de-marneffe-zeman-2021]
-/

/-- Grammatical case — the canonical analytical inventory. -/
inductive Case where
  /-- Nominative: citation/subject case. -/
  | nom
  /-- Accusative: direct object. -/
  | acc
  /-- Genitive: possessor, nominal dependent. -/
  | gen
  /-- Dative: indirect object, recipient. -/
  | dat
  /-- Instrumental: means, instrument. -/
  | inst
  /-- Locative: static location (general). -/
  | loc
  /-- Vocative: address form. -/
  | voc
  /-- Ablative: source, motion from (general). -/
  | abl
  /-- Ergative: transitive subject in ergative alignment. -/
  | erg
  /-- Absolutive: intransitive subject / transitive object in ergative
      alignment. -/
  | abs
  /-- Partitive: partial affectedness, indeterminate quantity
      (Finnic). -/
  | part
  /-- Essive: temporary state, capacity ("as an X"). -/
  | ess
  /-- Translative: change of state ("into an X"). -/
  | transl
  /-- Comitative: accompaniment ("with X"). -/
  | com
  /-- Adessive: at/near (exterior static). -/
  | ade
  /-- Inessive: in (interior static). -/
  | ine
  /-- Illative: into (interior goal). -/
  | ill
  /-- Elative: out of (interior source). -/
  | ela
  /-- Allative: onto/towards (exterior goal). -/
  | all
  /-- Sublative: onto (surface goal; Hungarian). -/
  | sub
  /-- Superessive: on (surface static; Hungarian). -/
  | sup
  /-- Delative: off of (surface source; Hungarian). -/
  | del
  /-- Terminative: up to a limit ("as far as X"). -/
  | ter
  /-- Temporal: at a time. -/
  | tem
  /-- Causative/causal: because of X. -/
  | caus
  /-- Benefactive: for the benefit of X. -/
  | ben
  /-- Perlative: path, motion through. -/
  | perl
  /-- Abessive/privative: without X. -/
  | abess
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace Case

/-! ### Markers -/

/-- A case marker, with its form and the cases it realizes, several for a polysemous marker. -/
structure Marker where
  /-- The form. -/
  form : String
  /-- The cases the marker realizes. -/
  cases : Finset Case
  deriving DecidableEq

/-- The cases a set of markers realizes. -/
def Marker.inventory (ms : Finset Marker) : Finset Case := ms.biUnion (·.cases)

end Case
