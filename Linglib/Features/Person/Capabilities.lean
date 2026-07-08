import Linglib.Core.Order.Flat
import Linglib.Features.Agreement
import Linglib.Features.Person.Basic

/-!
# Person — carrier capabilities
[cysouw-2009]

The typeclass mixin for carriers that bear grammatical person — the
person analogue of `HasNumber` (`Features/Number/Capabilities.lean`).
`personOf` extracts the carrier's analytical person value; `Compatible`
is the agreement-checking relation. Carriers that store UD realization
(`UD.MorphFeatures`) lift through `Person.fromUD`; carriers that store a
(UD person, clusivity) pair recover the quadripartition cell
(`Syntax/Category/Pronoun/Capabilities.lean`).
-/

set_option autoImplicit false

/-- A carrier of grammatical person. `none` = the carrier does not mark
    person. -/
class HasPerson (α : Type*) where
  /-- The analytical person value, if marked. -/
  personOf : α → Option Person

export HasPerson (personOf)

instance : HasPerson UD.MorphFeatures :=
  ⟨fun mf => mf.person.map Person.fromUD⟩

instance : HasPerson Person := ⟨some⟩

namespace HasPerson

variable {α β : Type*} [HasPerson α] [HasPerson β]

/-- Two carriers are person-compatible: the slot values are compatible in
    the flat information order (`Compat`) — if both mark person, the values
    agree; unmarked carriers are wildcards. -/
abbrev Compatible (a : α) (b : β) : Prop :=
  Compat (α := Flat Person) (personOf a) (personOf b)

end HasPerson

/-- φ-compatibility entails person compatibility: the `HasPerson` mixin
    never diverges from the unification-based agreement engine
    (`UD.MorphFeatures.compatible`) — the person analogue of
    `UD.MorphFeatures.compatible_hasNumber`. -/
theorem UD.MorphFeatures.compatible_hasPerson {f1 f2 : UD.MorphFeatures}
    (h : f1.compatible f2 = true) :
    HasPerson.Compatible f1 f2 :=
  Features.compat_of_clause_map Person.fromUD (UD.MorphFeatures.compatible_person h)
