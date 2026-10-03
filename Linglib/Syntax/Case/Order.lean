module

public import Linglib.Core.Data.List.Sublist
public import Linglib.Syntax.Case.Basic
/-!
# The containment order on Case

Caha takes the representation of a case to be a stack of nested feature shells, so that each case
on his sequence contains the cases before it. Here the sequence is the list `containment` of the
nominative, accusative, genitive, dative and locative, and one case is below another when it comes
earlier in the list, `[c₁, c₂] <+ containment`. The cases off the list, such as the ergative, the
absolutive and the instrumental, are comparable only to themselves, and that silence is part of
the theory. The order is a scoped instance (`open scoped Case.Caha`), since a theoretical order is
an opt-in commitment and not an order on the inventory. McFadden's natural classes are read off
it: the nonnominative cases, whose shared accusative feature conditions the stem allomorphy that
sets the nominative apart, and the oblique cases beyond the structural nominative and accusative.
The *ABA syncretism law over the order is the framework-neutral `Morphology.IsContiguous`.

The directional containment of spatial cases, Place ⊂ Goal ⊂ Source ⊂ Route, is
`Spatial.PathDir`, and the decomposition of spatial cases into localization and direction is in
`Syntax/Case/Spatial.lean`.

## Main definitions

* `Case.containment`: the containment sequence.
* The scoped `PartialOrder Case` instance in `Case.Caha`: the containment order.
* `Case.IsNonnominative`, `Case.IsOblique`: the cases containing the accusative and the genitive.

## Main results

* `Case.IsOblique.isNonnominative`: every oblique case is nonnominative.
* `Case.IsNonnominative.mem_containment`: every nonnominative case is on the sequence.

## Implementation notes

The sequence matches neither of Caha's verbatim. His Universal Case sequence is nominative,
accusative, genitive, dative, instrumental, comitative, without the locative, and his Russian
sequence puts the prepositional between the genitive and the dative. The one here is closer to
Blake's typological hierarchy, which Caha argues should coincide with his sequence. Caha's own
sequences are stated in `Studies/Caha2009.lean`.

## References

* [caha-2009]
* [mcfadden-2018]
* [blake-1994]
-/

@[expose] public section

namespace Case

open List

/-- The containment sequence is the nominative, accusative, genitive, dative and locative, each
containing the cases before it. -/
def containment : List Case := [.nom, .acc, .gen, .dat, .loc]

theorem nodup_containment : containment.Nodup := by decide

namespace Caha

/-- In the containment order a case is below another when it comes earlier in `containment`, and
a case off the sequence is comparable only to itself. -/
scoped instance : PartialOrder Case :=
  haveI := nodup_containment.isStrictOrder_pair_sublist
  partialOrderOfSO fun c₁ c₂ ↦ [c₁, c₂] <+ containment

scoped instance : DecidableLE Case := fun c₁ c₂ ↦
  inferInstanceAs (Decidable (c₁ = c₂ ∨ [c₁, c₂] <+ containment))

scoped instance : DecidableLT Case := fun c₁ c₂ ↦
  inferInstanceAs (Decidable ([c₁, c₂] <+ containment))

end Caha

open scoped Caha

variable {c : Case}

/-- A case is nonnominative when its representation contains the accusative's, `.acc ≤ c` in the
containment order. -/
def IsNonnominative (c : Case) : Prop := (.acc : Case) ≤ c

instance (c : Case) : Decidable (IsNonnominative c) :=
  inferInstanceAs (Decidable ((.acc : Case) ≤ c))

/-- A case is oblique when its representation contains the genitive's, `.gen ≤ c` in the
containment order. -/
def IsOblique (c : Case) : Prop := (.gen : Case) ≤ c

instance (c : Case) : Decidable (IsOblique c) :=
  inferInstanceAs (Decidable ((.gen : Case) ≤ c))

theorem IsOblique.isNonnominative (h : IsOblique c) : IsNonnominative c :=
  le_trans (show (.acc : Case) ≤ .gen by decide) h

/-- A nonnominative case is on the containment sequence, so that the ergative, the absolutive and
the oblique of a direct–oblique system are neither nonnominative nor oblique. -/
theorem IsNonnominative.mem_containment (h : IsNonnominative c) : c ∈ containment := by
  rcases h with rfl | h
  · decide
  · exact h.subset (by simp)

end Case
