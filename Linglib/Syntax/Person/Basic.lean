/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Tactic.DeriveFintype

/-!
# Grammatical person

`Person` is the inventory of values that languages' person systems distinguish, clusivity among
them. Harbour's quadripartition, first exclusive, first inclusive, second and third, sits beside
the tripartition's `first`, the first person unmarked for clusivity (English *we*), to which
`coarsen` sends both clusivity values as coarsening sends `Number.dual` to `Number.plural`.
`zero` is the impersonal person, the Universal Dependencies tag `Person=0`; those tags have no
clusivity, so realization sends the quadripartition values to the first person
(`Morphology/Word/UD.lean`).

`Person.prominence` ranks the first person above the second and the second above the third. On
the referential values it is the size of the feature bundle (`Person.prominence_eq_card`) and the
order resolution induces up to clusivity (`Person.prominence_le_iff`), the hierarchy of reference
and coordination of Zwicky, Corbett, and Dalrymple and Kaplan. It is not the only person scale:
Zwicky distinguishes morphosyntactic hierarchies that order the participants otherwise, as
Algonquian ranks the second person above the first, and for argument coding splits Haspelmath's
person scale is the binary cut between participants and the rest (`Person.Class`).

## Main definitions

* `Person`: the inventory.
* `Person.coarsen`: the value without its clusivity.
* `Person.prominence`: the person hierarchy as a rank.
* `Person.System`: the values a language's paradigms distinguish.

## References

* [cysouw-2003]
* [harbour-2016]
* [siewierska-2004]
* [zwicky-1977b]
* [corbett-2006]
* [dalrymple-kaplan-2000]
* [haspelmath-2021]
-/

@[expose] public section

/-- Grammatical person, clusivity being a distinction among person values rather than an
orthogonal feature: `firstInclusive` and `firstExclusive` sit beside the tripartition's
`first`. -/
inductive Person where
  /-- `first` is the first person unmarked for clusivity, the tripartition's (English *we*). -/
  | first
  /-- `firstInclusive` is the first person including the addressee (Indonesian *kita*). -/
  | firstInclusive
  /-- `firstExclusive` is the first person excluding the addressee (Indonesian *kami*). -/
  | firstExclusive
  /-- `second` refers to the addressee and not the speaker. -/
  | second
  /-- `third` refers to neither the speaker nor the addressee. -/
  | third
  /-- `zero` is the impersonal or generic person (UD `Person=0`, Finnish-type impersonals). -/
  | zero
  deriving DecidableEq, Repr, Fintype

namespace Person

/-! ### Predicates -/

/-- The referent includes the speaker. -/
def IncludesSpeaker : Person → Prop
  | .first | .firstInclusive | .firstExclusive => True
  | _ => False

instance : DecidablePred IncludesSpeaker := fun p =>
  match p with
  | .first | .firstInclusive | .firstExclusive => isTrue trivial
  | .second | .third | .zero => isFalse fun h => h

/-- The value marks clusivity, a value of the quadripartition. -/
def MarksClusivity : Person → Prop
  | .firstInclusive | .firstExclusive => True
  | _ => False

instance : DecidablePred MarksClusivity := fun p =>
  match p with
  | .firstInclusive | .firstExclusive => isTrue trivial
  | .first | .second | .third | .zero => isFalse fun h => h

/-- A speech-act participant value includes the speaker or the addressee; `zero` is not one. -/
def IsSAP : Person → Prop
  | .third | .zero => False
  | _ => True

instance : DecidablePred IsSAP := fun p =>
  match p with
  | .first | .firstInclusive | .firstExclusive | .second => isTrue trivial
  | .third | .zero => isFalse fun h => h

/-! ### Coarsening

The clusivity values coarsen to the tripartition's `first`, as `Number.dual` coarsens to
`Number.plural`, so a system without clusivity realizes inclusive and exclusive referents
alike. -/

/-- `coarsen` collapses clusivity, sending each value to its tripartition value. -/
def coarsen : Person → Person
  | .firstInclusive | .firstExclusive => .first
  | p => p

@[simp] theorem coarsen_idempotent (p : Person) :
    p.coarsen.coarsen = p.coarsen := by cases p <;> rfl

/-- Coarsening erases exactly the clusivity marking. -/
theorem coarsen_eq_self_iff (p : Person) :
    p.coarsen = p ↔ ¬MarksClusivity p := by
  cases p <;> simp [coarsen, MarksClusivity]

/-! ### Prominence -/

/-- `prominence` ranks the first person (2) above the second (1) and the second above the third
(0); the clusivity values rank with `first` and the impersonal with the third person. -/
def prominence : Person → Nat
  | .first | .firstInclusive | .firstExclusive => 2
  | .second => 1
  | .third | .zero => 0

/-! ### Person systems -/

/-- A language's person system is the list of values its paradigms distinguish; the marking
types of the first person complex are `Person.Clusivity`. -/
structure System where
  /-- The person values the system distinguishes. -/
  values : List Person
  deriving DecidableEq, Repr

namespace System

/-- The system marks clusivity. -/
def HasClusivity (ns : System) : Prop :=
  .firstInclusive ∈ ns.values ∨ .firstExclusive ∈ ns.values

instance : DecidablePred HasClusivity := fun ns => by
  unfold HasClusivity; infer_instance

/-- The tripartition is the English-type system of first, second and third person. -/
def tripartition : System := ⟨[.first, .second, .third]⟩

/-- The quadripartition is the Indonesian- or Tagalog-type system with clusivity. -/
def quadripartition : System :=
  ⟨[.firstInclusive, .firstExclusive, .second, .third]⟩

theorem tripartition_no_clusivity : ¬tripartition.HasClusivity := by
  decide

theorem quadripartition_clusivity : quadripartition.HasClusivity := by
  decide

end System

end Person
