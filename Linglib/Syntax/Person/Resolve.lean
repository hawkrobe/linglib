/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Finset.Sups
public import Mathlib.Data.Fintype.Powerset
public import Linglib.Discourse.Role
public import Linglib.Syntax.Person.Basic

/-!
# Person resolution

A person value covers the referents whose participants form one of its participant sets:
`{speaker}` or `{speaker, addressee}` for the first person unmarked for clusivity, a single set for
each value of the quadripartition, and none for the impersonal `zero`. As Zwicky proposes, a
coordination refers to the union of its conjuncts' referents, so its participant sets are the
pairwise unions `⊻` of theirs. Distinct values cover distinct participant sets, so this makes
`Person` a join-semilattice whose join `⊔` is person resolution, with third person at the bottom
and the impersonal at the top.

Dalrymple and Kaplan's marker sets are the participant sets of the quadripartition, and their union
is the join (`Person.ofParticipants_union`). A system without clusivity coarsens the join, and
resolution there follows the hierarchy 1 > 2 > 3 of Corbett's resolution rules.

## Main definitions

* `Person.participantSets`: the participant sets a person value covers.
* the `SemilatticeSup Person` instance: person resolution as the join.
* `Person.ofParticipants`: the value covering exactly one participant set.
* `Person.coarsenTo`, `Person.System.resolve`: resolution within a person system.

## Main results

* `Person.participantSets_sup`: the participant sets of a join are the pairwise unions.
* `Person.ofParticipants_union`: the person of a union of participant sets is the join of their
  persons.
* `Person.coarsen_eq_iff`: coarsening sends a value to the tripartition value covering it.
* `Person.System.tripartition_resolve`: in the tripartition, resolution selects the conjunct
  highest on the hierarchy.

## Implementation notes

The impersonal covers no participant set, so a coordination with an impersonal conjunct has no
referential person; making `zero` absorbing records this and keeps every law unconditional.

## References

* [zwicky-1977b]
* [dalrymple-kaplan-2000]
* [corbett-2006]
-/

@[expose] public section

open scoped FinsetFamily

namespace Person

open Finset Discourse

/-! ### Participant sets -/

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

/-- The participant sets of a value are closed under union. -/
theorem supClosed_participantSets (p : Person) :
    SupClosed (p.participantSets : Set (Finset Role)) := by
  rw [← sups_eq_self]; cases p <;> decide

/-! ### Resolution -/

/-- In person resolution the impersonal absorbs, third person is neutral, the first person
unmarked for clusivity absorbs the exclusive, and any other two distinct values together cover
both the speaker and the addressee. -/
instance : Max Person where
  max
    | .zero, _ | _, .zero => .zero
    | .third, p | p, .third => p
    | .first, .firstExclusive | .firstExclusive, .first => .first
    | p, q => if p = q then p else .firstInclusive

/-- The participant sets of a coordination are the unions of its conjuncts'. -/
@[simp] theorem participantSets_sup (p q : Person) :
    (p ⊔ q).participantSets = p.participantSets ⊻ q.participantSets := by
  revert p q; decide

instance : SemilatticeSup Person :=
  SemilatticeSup.mk'
    (fun _ _ ↦ participantSets_injective <| by simp only [participantSets_sup, sups_comm])
    (fun _ _ _ ↦ participantSets_injective <| by simp only [participantSets_sup, sups_assoc])
    (fun p ↦ participantSets_injective <| by
      rw [participantSets_sup, sups_eq_self]; exact supClosed_participantSets p)

instance : DecidableLE Person := fun p q ↦ inferInstanceAs (Decidable (p ⊔ q = q))

instance : BoundedOrder Person where
  bot := .third
  bot_le p := show .third ⊔ p = p by cases p <;> rfl
  top := .zero
  le_top p := show p ⊔ .zero = .zero by cases p <;> rfl

@[simp] theorem bot_eq_third : (⊥ : Person) = .third := rfl

@[simp] theorem top_eq_zero : (⊤ : Person) = .zero := rfl

/-! ### The person of a participant set -/

/-- The person of a referent whose participants are `s` is first inclusive with both, first
exclusive with the speaker alone, second with the addressee alone, and third with neither. -/
def ofParticipants (s : Finset Role) : Person :=
  if .speaker ∈ s then if .addressee ∈ s then .firstInclusive else .firstExclusive
  else if .addressee ∈ s then .second else .third

@[simp] theorem participantSets_ofParticipants (s : Finset Role) :
    (ofParticipants s).participantSets = {s} := by
  revert s; decide

/-- The values of the quadripartition are exactly those covering a single participant set. -/
theorem participantSets_eq_singleton_iff {p : Person} {s : Finset Role} :
    p.participantSets = {s} ↔ p = ofParticipants s := by
  rw [← participantSets_inj, participantSets_ofParticipants]

theorem ofParticipants_injective : Function.Injective ofParticipants := fun s t h ↦ by
  simpa using congrArg participantSets h

@[simp] theorem ofParticipants_empty : ofParticipants ∅ = ⊥ := rfl

/-- The person of a union of participant sets is the join of their persons. -/
theorem ofParticipants_union (s t : Finset Role) :
    ofParticipants (s ∪ t) = ofParticipants s ⊔ ofParticipants t :=
  participantSets_injective <| by simp

/-! ### Predicates read off the participant sets -/

theorem includesSpeaker_iff (p : Person) :
    IncludesSpeaker p ↔
      p.participantSets.Nonempty ∧ ∀ s ∈ p.participantSets, .speaker ∈ s := by
  cases p <;> decide

theorem isSAP_iff (p : Person) :
    IsSAP p ↔ p.participantSets.Nonempty ∧ ∀ s ∈ p.participantSets, s.Nonempty := by
  cases p <;> decide

/-! ### Coarsening -/

/-- Coarsening a value never loses a participant set. -/
theorem participantSets_subset_coarsen (p : Person) :
    p.participantSets ⊆ p.coarsen.participantSets := by
  cases p <;> decide

/-- Coarsening sends a referential value to the tripartition value covering its participant
sets. -/
theorem coarsen_eq_iff {p : Person} (hp : p ≠ .zero) (q : Person) :
    p.coarsen = q ↔
      q ∈ System.tripartition.values ∧ p.participantSets ⊆ q.participantSets := by
  revert p q; decide

/-- The tripartition value of a coordination depends only on the tripartition values of its
conjuncts. -/
theorem coarsen_sup (p q : Person) : (p ⊔ q).coarsen = (p.coarsen ⊔ q.coarsen).coarsen := by
  revert p q; decide

/-! ### Resolution in a person system -/

/-- Coarsening into a system keeps a value the system has and otherwise collapses clusivity. -/
def coarsenTo (sys : List Person) (p : Person) : Person :=
  if p ∈ sys then p
  else if p.coarsen ∈ sys then p.coarsen
  else p

/-- Resolution within a system is the join coarsened into the system. -/
def resolveIn (sys : List Person) (a b : Person) : Person :=
  coarsenTo sys (a ⊔ b)

theorem resolveIn_comm (sys : List Person) (a b : Person) :
    resolveIn sys a b = resolveIn sys b a := by
  rw [resolveIn, resolveIn, sup_comm]

/-- `ns.resolve` is resolution within the values of the person system `ns`. -/
def System.resolve (ns : System) (a b : Person) : Person :=
  resolveIn ns.values a b

/-- In the tripartition, resolution selects the conjunct highest on the hierarchy 1 > 2 > 3. -/
theorem System.tripartition_resolve :
    ∀ p ∈ tripartition.values, ∀ q ∈ tripartition.values,
      tripartition.resolve p q = if p.hierarchyRank ≤ q.hierarchyRank then p else q := by
  decide

end Person
