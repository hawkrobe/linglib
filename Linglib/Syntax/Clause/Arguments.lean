import Linglib.Semantics.ArgumentStructure.Valency
import Linglib.Syntax.Clause.ArgumentRole

/-!
# Core arguments of a clause token

What each core-argument position of a clause (`ArgumentStructure.ArgPosition`)
bears — a DP, its φ-features, its number — with `none` at an unfilled
position. The filled positions are the clause's valency.

## Main definitions

* `Clause.Arguments α` — the assignment of an `α` to each filled position.
* `Clause.Arguments.unaccusative`, `unergative`, `transitive`, `empty` — the
  clause shapes by which positions are filled.
* `Clause.Arguments.valency` — the filled positions.
* `Clause.Arguments.codingRole` — the comparative S/A/P classification of
  a filled position; the clause, not the predicate, takes the
  classification.

## Main results

* `Clause.Arguments.unaccusative_isRootValency`,
  `transitive_isTransitive` — the shapes land in the valency classes of
  [coon-2019]'s division of labor.
-/

namespace Clause

open ArgumentStructure

/-- What each core-argument position of a clause token bears, `none` where the
position is unfilled. -/
abbrev Arguments (α : Type*) := ArgPosition → Option α

namespace Arguments

variable {α : Type*} (x obj subj : α)

/-- An intransitive clause whose sole argument is internal. -/
def unaccusative : Arguments α
  | .internal => some x
  | .external => none

/-- An intransitive clause whose sole argument is external. -/
def unergative : Arguments α
  | .internal => none
  | .external => some x

/-- A transitive clause: an internal argument `obj` and an external one
`subj`. -/
def transitive : Arguments α
  | .internal => some obj
  | .external => some subj

/-- A clause with no core argument filled. -/
def empty : Arguments α := fun _ => none

/-- The filled positions. -/
def valency (c : Arguments α) : Valency := Finset.univ.filter fun p => (c p).isSome

/-- The comparative classification of a filled position — the *clause*
    takes the classification: the sole argument of a one-place clause is S;
    in a two-place clause the external argument is A and the internal P.
    `Verb.codingRoles` is the special case classifying a verb entry's
    citation clause. -/
def codingRole (c : Arguments α) : ArgPosition → Option ArgumentRole
  | .external => (c .external).map fun _ => if (c .internal).isSome then .A else .S
  | .internal => (c .internal).map fun _ => if (c .external).isSome then .P else .S

@[simp] theorem codingRole_unaccusative :
    (unaccusative x).codingRole .internal = some .S := rfl

@[simp] theorem codingRole_unergative :
    (unergative x).codingRole .external = some .S := rfl

@[simp] theorem codingRole_transitive :
    (transitive obj subj).codingRole .external = some .A ∧
    (transitive obj subj).codingRole .internal = some .P := ⟨rfl, rfl⟩

@[simp] theorem valency_unaccusative : (unaccusative x).valency = {.internal} := by
  ext p; cases p <;> simp [valency, unaccusative]

@[simp] theorem valency_unergative : (unergative x).valency = {.external} := by
  ext p; cases p <;> simp [valency, unergative]

@[simp] theorem valency_transitive : (transitive obj subj).valency = {.internal, .external} := by
  ext p; cases p <;> simp [valency, transitive]

@[simp] theorem valency_empty : (empty : Arguments α).valency = ∅ := by
  ext p; simp [valency, empty]

/-- An unaccusative clause's sole argument occupies the root's valency. -/
theorem unaccusative_isRootValency : (unaccusative x).valency.IsRootValency := by
  rw [valency_unaccusative]; exact le_rfl

/-- An unergative clause's sole argument occupies Voice's valency. -/
theorem unergative_isVoiceValency : (unergative x).valency.IsVoiceValency := by
  rw [valency_unergative]; exact le_rfl

theorem transitive_isTransitive : (transitive obj subj).valency.IsTransitive :=
  valency_transitive obj subj

end Arguments

end Clause
