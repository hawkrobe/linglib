module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Order.Fin.Basic
public import Mathlib.Tactic.DeriveFintype

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
* `Case.Labelled`: a case of a language under its comparative label, with the case functions it
  expresses, for a language whose cases go by label rather than by form.

## References

* [blake-1994]
* [de-marneffe-zeman-2021]
-/

@[expose] public section

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

/-! ### Labelled cases -/

/-- A case of a language under its comparative label, with the case functions it expresses. The
label is one of the functions, by convention the highest, and a case of few functions and a case
of many may carry the same label. -/
structure Labelled where
  /-- The comparative label. -/
  label : Case
  /-- The case functions the case expresses. -/
  functions : Finset Case
  /-- The case expresses the function it is labelled for. -/
  label_mem : label ∈ functions
  deriving DecidableEq

namespace Labelled

/-- A case with the one function it is labelled for. -/
@[simps]
def single (c : Case) : Labelled := ⟨c, {c}, Finset.mem_singleton_self c⟩

/-- The labels of a set of cases are among the functions the cases express. -/
theorem image_label_subset_biUnion_functions (cs : Finset Labelled) :
    cs.image label ⊆ cs.biUnion functions :=
  Finset.image_subset_iff.2 fun c hc ↦ Finset.mem_biUnion.2 ⟨c, hc, c.label_mem⟩

end Labelled

end Case
