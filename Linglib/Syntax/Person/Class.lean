module

public import Mathlib.Order.Atoms
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Person.Basic

/-!
# The binary person scale

The load-bearing cut of person prominence: speech-act participants, first and second
person, above the rest. It is the person scale of [haspelmath-2021]'s (8a), locuphoric
above aliophoric in his terms, the cut the person-case constraint's strong variety draws
([bonet-1991]), and the coarsening of `Person.prominence` at the participant level.

## Main declarations

* `Person.Class`: `nonParticipant < participant`, a two-element bounded linear order.
* `Person.toClass`: the class of a person, `participant` exactly when it `IsSAP`, and
  `toClass_mono` for its agreement with `prominence`.

## References

* [haspelmath-2021]
* [bonet-1991]
-/

@[expose] public section

namespace Person

/-- The binary person scale: speech-act participants above non-participants. -/
inductive Class where
  | nonParticipant
  | participant
  deriving DecidableEq, Repr, Fintype

namespace Class

/-- Rank on the binary person scale. -/
def rank : Class → ℕ
  | .nonParticipant => 0
  | .participant => 1

/-- `nonParticipant < participant`. -/
instance : LinearOrder Class := LinearOrder.lift' rank (by decide)

/-- `⊥ = nonParticipant`, `⊤ = participant`. -/
instance : BoundedOrder Class where
  top := .participant
  le_top := by decide
  bot := .nonParticipant
  bot_le := by decide

instance : IsSimpleOrder Class where
  exists_pair_ne := ⟨.nonParticipant, .participant, by decide⟩
  eq_bot_or_eq_top := by decide

end Class

/-- The class of a person: `participant` exactly when it is a speech-act participant. -/
def toClass (p : Person) : Class := if p.IsSAP then .participant else .nonParticipant

@[simp] theorem toClass_eq_participant_iff {p : Person} : p.toClass = .participant ↔ p.IsSAP := by
  cases p <;> simp [toClass, IsSAP]

@[simp] theorem toClass_eq_nonParticipant_iff {p : Person} :
    p.toClass = .nonParticipant ↔ ¬ p.IsSAP := by
  cases p <;> simp [toClass, IsSAP]

/-- The class is the coarsening of prominence at the participant level. -/
theorem toClass_mono {p q : Person} (h : p.prominence ≤ q.prominence) :
    p.toClass ≤ q.toClass := by
  revert h; cases p <;> cases q <;> decide

end Person
