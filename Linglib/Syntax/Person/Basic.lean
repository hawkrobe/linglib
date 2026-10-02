/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Discourse.Role

/-!
# Grammatical person

`Person` is the inventory of values that languages' person systems distinguish, clusivity among
them. Harbour's quadripartition, first exclusive, first inclusive, second and third, sits beside
the tripartition's `first`, the first person unmarked for clusivity (English *we*), to which
`coarsen` sends both clusivity values as coarsening sends `Number.dual` to `Number.plural`.
`zero` is the impersonal person, the Universal Dependencies tag `Person=0`; those tags have no
clusivity, so realization sends the quadripartition values to the first person
(`Morphology/Word/UD.lean`). A value means the participant sets its referents can have
(`Person.participantSets`), and whether it includes the speaker, is a speech-act participant, or
marks clusivity is read off them.

`Person.prominence` ranks the first person above the second and the second above the third. On
the referential values it is the size of the feature bundle (`Person.prominence_eq_card`) and the
order resolution induces up to clusivity (`Person.prominence_le_iff`), the hierarchy of reference
and coordination of Zwicky, Corbett, and Dalrymple and Kaplan. It is not the only person scale:
Zwicky distinguishes morphosyntactic hierarchies that order the participants otherwise, as
Algonquian ranks the second person above the first, and for argument coding splits Haspelmath's
person scale is the binary cut between participants and the rest (`Person.Class`).

## Main definitions

* `Person`: the inventory.
* `Person.participantSets`: the participant sets a value covers.
* `Person.ofParticipants`: the value covering exactly one participant set.
* `Person.IncludesSpeaker`, `Person.IsSAP`, `Person.MarksClusivity`: predicates read off the
  participant sets.
* `Person.coarsen`: the value without its clusivity.
* `Person.prominence`: the person hierarchy as a rank.

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

/-! ### Participant sets

A person value covers the referents whose participants, the speaker and the addressee among them,
form one of its participant sets: `{speaker}` or `{speaker, addressee}` for the first person
unmarked for clusivity, a single set for each value of the quadripartition, and none for the
impersonal. The predicates on values read these sets off. -/

open Discourse

/-- `p.participantSets` is the family of participant sets of the referents `p` covers. -/
def participantSets : Person → Finset (Finset Role)
  | .first => {{.speaker}, {.speaker, .addressee}}
  | .firstInclusive => {{.speaker, .addressee}}
  | .firstExclusive => {{.speaker}}
  | .second => {{.addressee}}
  | .third => {∅}
  | .zero => ∅

theorem participantSets_injective : Function.Injective participantSets := by decide

@[simp] theorem participantSets_inj {p q : Person} :
    p.participantSets = q.participantSets ↔ p = q :=
  participantSets_injective.eq_iff

@[simp] theorem participantSets_eq_empty {p : Person} : p.participantSets = ∅ ↔ p = .zero := by
  cases p <;> decide

/-- The person of a referent whose participants are `s` is first inclusive with both, first
exclusive with the speaker alone, second with the addressee alone, and third with neither. -/
def ofParticipants (s : Finset Role) : Person :=
  if .speaker ∈ s then if .addressee ∈ s then .firstInclusive else .firstExclusive
  else if .addressee ∈ s then .second else .third

@[simp] theorem participantSets_ofParticipants (s : Finset Role) :
    (ofParticipants s).participantSets = {s} := by
  unfold ofParticipants
  split_ifs with hS hH hH <;> simp only [participantSets, Finset.singleton_inj] <;>
    ext r <;> cases r <;> simp_all

/-- The values of the quadripartition are exactly those covering a single participant set. -/
theorem participantSets_eq_singleton_iff {p : Person} {s : Finset Role} :
    p.participantSets = {s} ↔ p = ofParticipants s := by
  rw [← participantSets_inj, participantSets_ofParticipants]

theorem ofParticipants_injective : Function.Injective ofParticipants := fun s t h ↦ by
  simpa using congrArg participantSets h

/-! ### Predicates -/

/-- The value includes the speaker when it covers some participant set and each contains the
speaker. -/
def IncludesSpeaker (p : Person) : Prop :=
  p.participantSets.Nonempty ∧ ∀ s ∈ p.participantSets, .speaker ∈ s

instance : DecidablePred IncludesSpeaker := fun _ ↦ by unfold IncludesSpeaker; infer_instance

/-- A speech-act participant value covers some participant set, and each is nonempty. -/
def IsSAP (p : Person) : Prop :=
  p.participantSets.Nonempty ∧ ∀ s ∈ p.participantSets, s.Nonempty

instance : DecidablePred IsSAP := fun _ ↦ by unfold IsSAP; infer_instance

/-- The value marks clusivity when it includes the speaker and covers a single participant set,
fixing whether the addressee is included. -/
def MarksClusivity (p : Person) : Prop :=
  IncludesSpeaker p ∧ p.participantSets.card = 1

instance : DecidablePred MarksClusivity := fun _ ↦ by unfold MarksClusivity; infer_instance

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
  revert p; decide

/-! ### Prominence -/

/-- `prominence` ranks the first person (2) above the second (1) and the second above the third
(0); the clusivity values rank with `first` and the impersonal with the third person. -/
def prominence : Person → Nat
  | .first | .firstInclusive | .firstExclusive => 2
  | .second => 1
  | .third | .zero => 0

end Person
