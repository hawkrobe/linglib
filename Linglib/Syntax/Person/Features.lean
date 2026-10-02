/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Person.Category
public import Linglib.Core.Order.UpperLower.Finset
public import Mathlib.Order.Concept

/-!
# Bivalent person features

Person decomposes into two features, [participant] and [author], the bivalent system Ackema and
Neeleman trace to Halle. Read on participant sets, [participant] holds of the nonempty ones and
[author] of those containing the speaker, so the participant sets and the features form a formal
context (`Person.Bears`). A value's bundle is the set of features holding of all its participant
sets, its intent in the context. Every set containing the speaker is nonempty, so the closed sets of
features are exactly the lower sets of the chain participant < author: the containment filter
that rules out an author who is no participant is the closure of the context. Harley and Ritter
caution that a geometry encodes morphological dependency, which need not follow logical
implication, so the chain stays a stipulated order, and its coincidence with the closure is a
theorem about person. Two features see the tripartition and not clusivity: a tripartition value
covers exactly the participant sets whose own features are its bundle.

## Main definitions

* `Person.Feature`: the two features, ordered participant < author.
* `Person.Bears`: the features a participant set bears.
* `Person.toFeatures`: the bundle of a person value, none for the impersonal.
* `Person.Features.WellFormed`: the containment filter.
* `Person.Category.toFeatures`: the bundle of a referential category.

## Main results

* `Person.wellFormed_iff_isIntent`: the well-formed bundles are the closed sets of the context.
* `Person.card_wellFormed`: there are three well-formed bundles, so no fourth person.
* `Person.mem_participantSets_iff`: a tripartition value covers the participant sets whose
  features are its bundle.
* `Person.toFeatures_sup`: the bundle of a coordination is the union of its conjuncts' bundles.
* `Person.Category.sharedPerson_isSome_iff`: a set of categories has a person iff they share a
  bundle.

## References

* [ackema-neeleman-2018]
* [harley-ritter-2002]
* [adger-harbour-2008]
* [harbour-2016]
* [cysouw-2003]
-/

@[expose] public section

open Finset Discourse Order

namespace Person

/-- Person has two features, the author feature depending on the participant feature. -/
inductive Feature where
  /-- [participant] holds of a referent including a speech-act participant. -/
  | participant
  /-- [author] holds of a referent including the speaker. -/
  | author
  deriving DecidableEq, Repr, Fintype

/-- `Feature.rank` places participant below author on the dependency chain. -/
def Feature.rank : Feature → Fin 2
  | .participant => 0
  | .author => 1

instance : LinearOrder Feature := LinearOrder.lift' Feature.rank (by decide)

/-- A person feature bundle is the set of its positive features. -/
abbrev Features := Finset Feature

/-! ### The context of participant sets and features -/

/-- A participant set bears [participant] when it is nonempty and [author] when it contains the
speaker. -/
def Bears (s : Finset Role) : Feature → Prop
  | .participant => s.Nonempty
  | .author => .speaker ∈ s

instance (s : Finset Role) : DecidablePred (Bears s) := fun f ↦ by
  cases f <;> unfold Bears <;> infer_instance

theorem Bears.participant {s : Finset Role} (h : Bears s .author) : Bears s .participant :=
  ⟨_, h⟩

/-- A bundle passes the containment filter when its features form a lower set of the chain, an
author being necessarily a participant. -/
abbrev Features.WellFormed (pf : Features) : Prop := IsLowerSet (↑pf : Set Feature)

private theorem mem_upperPolar_lowerPolar (t : Features) (f : Feature) :
    f ∈ upperPolar Bears (lowerPolar Bears (t : Set Feature)) ↔
      ∀ s : Finset Role, (∀ g ∈ t, Bears s g) → Bears s f := by
  simp [mem_upperPolar_iff, mem_lowerPolar_iff]

/-- The well-formed bundles are exactly the closed sets of features of the context. -/
theorem wellFormed_iff_isIntent (t : Features) :
    t.WellFormed ↔ IsIntent Bears (t : Set Feature) := by
  rw [isIntent_iff, Set.ext_iff]
  simp only [mem_upperPolar_lowerPolar, Finset.mem_coe]
  revert t; decide

/-- The author feature alone closes to both features. -/
theorem intentClosure_singleton_author :
    intentClosure Bears {Feature.author} = Set.univ := by
  ext f; cases f
  · simp [intentClosure, mem_upperPolar_iff, mem_lowerPolar_iff, Bears]
    exact fun _ h ↦ ⟨_, h⟩
  · simp [intentClosure, mem_upperPolar_iff, mem_lowerPolar_iff, Bears]

/-- The bundle with the author feature alone violates containment. -/
theorem not_wellFormed_singleton_author : ¬ ({.author} : Features).WellFormed := by decide

/-- Exactly three bundles are well-formed. -/
theorem card_wellFormed : Fintype.card {pf : Features // pf.WellFormed} = 3 := by decide

/-! ### The bundle of a person value -/

/-- The bundle of a person value is the set of features its participant sets all bear; the
impersonal, which covers no participant set, has none. -/
def toFeatures : Person → Option Features
  | .zero => none
  | p => some (univ.filter fun f ↦ ∀ s ∈ p.participantSets, Bears s f)

/-- A value's bundle is the intent of its participant sets. -/
theorem coe_toFeatures {p : Person} {t : Features} (h : p.toFeatures = some t) :
    (t : Set Feature) = upperPolar Bears (p.participantSets : Set (Finset Role)) := by
  cases p <;> simp only [toFeatures, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    ext f <;> simp [mem_upperPolar_iff]

@[simp] theorem toFeatures_first : toFeatures .first = some {.participant, .author} := by decide
@[simp] theorem toFeatures_firstInclusive :
    toFeatures .firstInclusive = some {.participant, .author} := by decide
@[simp] theorem toFeatures_firstExclusive :
    toFeatures .firstExclusive = some {.participant, .author} := by decide
@[simp] theorem toFeatures_second : toFeatures .second = some {.participant} := by decide
@[simp] theorem toFeatures_third : toFeatures .third = some ∅ := by decide
@[simp] theorem toFeatures_zero : toFeatures .zero = none := rfl

theorem toFeatures_eq_none_iff {p : Person} : p.toFeatures = none ↔ p.participantSets = ∅ := by
  cases p <;> decide

/-- Coarsening does not change a value's bundle, since the features do not see clusivity. -/
@[simp] theorem toFeatures_coarsen (p : Person) : p.coarsen.toFeatures = p.toFeatures := by
  cases p <;> decide

/-- The bundle of a coordination is the union of its conjuncts' bundles. -/
theorem toFeatures_sup {p q : Person} {s t : Features} (hp : p.toFeatures = some s)
    (hq : q.toFeatures = some t) : (p ⊔ q).toFeatures = some (s ∪ t) := by
  revert p q s t; decide

/-- Every bundle is well-formed. -/
theorem toFeatures_wellFormed {p : Person} {t : Features} (h : p.toFeatures = some t) :
    t.WellFormed := by
  revert p t; decide

/-- `IsSAP` is featural participanthood. -/
theorem isSAP_iff_participant {p : Person} {t : Features} (h : p.toFeatures = some t) :
    p.IsSAP ↔ .participant ∈ t := by
  revert p t; decide

/-- `IncludesSpeaker` is featural authorhood. -/
theorem includesSpeaker_iff_author {p : Person} {t : Features} (h : p.toFeatures = some t) :
    p.IncludesSpeaker ↔ .author ∈ t := by
  revert p t; decide

/-- A tripartition value covers exactly the participant sets whose features are its bundle, the
sets in the domain of its bundle and in no domain of a more specified one. -/
theorem mem_participantSets_iff {p : Person} (hp : p ∈ System.tripartition.values)
    {t : Features} (ht : p.toFeatures = some t) (s : Finset Role) :
    s ∈ p.participantSets ↔ univ.filter (Bears s) = t := by
  revert p t s; decide

/-- Two participant sets have the same tripartition person iff they bear the same features. -/
theorem coarsen_ofParticipants_eq_iff (s t : Finset Role) :
    (ofParticipants s).coarsen = (ofParticipants t).coarsen ↔
      univ.filter (Bears s) = univ.filter (Bears t) := by
  revert s t; decide

/-! ### The features of a referential category -/

namespace Category

variable {c : Category}

/-- The bundle of a category is the set of features its participants bear. The features
underdetermine the first person complex, whose three categories share a bundle; the
decomposition that distinguishes the exclusive is Harbour's (`Studies.Harbour2016.signOf`). -/
def toFeatures (c : Category) : Features := univ.filter (Bears c.participants)

@[simp] theorem mem_toFeatures {f : Feature} : f ∈ c.toFeatures ↔ Bears c.participants f := by
  simp [toFeatures]

@[simp] theorem author_mem_toFeatures : .author ∈ c.toFeatures ↔ c.IncludesSpeaker := by
  simp [Bears, IncludesSpeaker]

@[simp] theorem participant_mem_toFeatures :
    .participant ∈ c.toFeatures ↔ c.IncludesSpeaker ∨ c.IncludesAddressee := by
  cases c <;> decide +kernel

/-- The bundle of a category is the bundle of its person. -/
theorem toFeatures_person (c : Category) : c.person.toFeatures = some c.toFeatures := by
  cases c <;> decide

/-- Every category yields a well-formed bundle. -/
theorem toFeatures_wellFormed (c : Category) : c.toFeatures.WellFormed := by
  cases c <;> decide +kernel

/-- A set of categories has a person iff the categories share a bundle. -/
theorem sharedPerson_isSome_iff (s : Finset Category) :
    (sharedPerson s).isSome ↔ s.Nonempty ∧ ∀ c ∈ s, ∀ d ∈ s, c.toFeatures = d.toFeatures := by
  revert s; decide +kernel

end Category

end Person
