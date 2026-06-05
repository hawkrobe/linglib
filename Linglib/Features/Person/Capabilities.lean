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
(`Syntax/Pronoun/Capabilities.lean`).
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

/-- Two carriers are person-compatible: if both mark person, the values
    agree. Unmarked carriers are compatible with everything. -/
def Compatible (a : α) (b : β) : Prop :=
  ∀ p q, personOf a = some p → personOf b = some q → p = q

instance (a : α) (b : β) : Decidable (Compatible a b) := by
  unfold Compatible
  infer_instance

theorem compatible_comm {a : α} {b : β} (h : Compatible a b) :
    Compatible b a := fun p q hp hq => (h q p hq hp).symm

theorem compatible_of_none {a : α} {b : β} (h : personOf a = none) :
    Compatible a b := fun p _ hp _ => by
  rw [h] at hp
  exact absurd hp (by simp)

end HasPerson
