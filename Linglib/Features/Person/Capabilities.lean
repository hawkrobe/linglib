/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Order.Flat
import Linglib.Features.Agreement
import Linglib.Features.Person.Basic

/-!
# The person-bearing capability

`HasPerson` equips a carrier with the grammatical person it bears;
`HasPerson.Compatible` is the induced agreement relation, slot compatibility
in the flat information order. Carriers storing UD realization lift through
`Person.fromUD`; carriers storing a (UD person, clusivity) pair recover the
quadripartition cell ([cysouw-2009]) in
`Syntax/Category/Pronoun/Capabilities.lean`.
-/

/-- A carrier of grammatical person. `⊥` = the carrier does not mark
person. -/
class HasPerson (α : Type*) where
  /-- The person value the carrier bears, if marked. -/
  personOf : α → Flat Person

export HasPerson (personOf)

instance : HasPerson UD.MorphFeatures :=
  ⟨fun mf => mf.person.map Person.fromUD⟩

instance : HasPerson Person := ⟨(↑·)⟩

/-- Person compatibility: valued persons coincide, an unvalued carrier is a
wildcard. -/
abbrev HasPerson.Compatible {α β : Type*} [HasPerson α] [HasPerson β]
    (a : α) (b : β) : Prop :=
  Compat (personOf a) (personOf b)

/-- φ-compatibility of UD bundles entails person compatibility. -/
theorem UD.MorphFeatures.compatible_hasPerson {f1 f2 : UD.MorphFeatures}
    (h : f1.compatible f2 = true) :
    HasPerson.Compatible f1 f2 :=
  Features.compat_of_clause_map Person.fromUD (UD.MorphFeatures.compatible_person h)
