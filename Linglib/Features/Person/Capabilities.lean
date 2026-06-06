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

/-- φ-compatibility entails person compatibility: the `HasPerson` mixin
    never diverges from the unification-based agreement engine
    (`UD.MorphFeatures.compatible`) — the person analogue of
    `UD.MorphFeatures.compatible_hasNumber`. -/
theorem UD.MorphFeatures.compatible_hasPerson {f1 f2 : UD.MorphFeatures}
    (h : f1.compatible f2 = true) :
    HasPerson.Compatible f1 f2 := by
  intro pa pb ha hb
  have hp : (f1.person.isNone || f2.person.isNone || f1.person == f2.person)
      = true := by
    unfold UD.MorphFeatures.compatible at h
    simp only [Bool.and_eq_true] at h
    tauto
  simp only [HasPerson.personOf] at ha hb
  rcases h1 : f1.person with _ | u1
  · rw [h1] at ha
    exact absurd ha (by simp)
  · rcases h2 : f2.person with _ | u2
    · rw [h2] at hb
      exact absurd hb (by simp)
    · rw [h1] at ha
      rw [h2] at hb
      rw [h1, h2] at hp
      simp only [Option.isNone_some, Bool.false_or, beq_iff_eq,
        Option.some.injEq] at hp
      simp only [Option.map_some, Option.some.injEq] at ha hb
      rw [← ha, ← hb, hp]
