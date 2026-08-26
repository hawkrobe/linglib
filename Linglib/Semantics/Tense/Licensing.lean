import Linglib.Semantics.Tense.Embedding

/-!
# Tense licensing by transmitted temporal relations

This file defines the semantics of tense in intensional contexts on which sequence of tense rests.
Every temporal argument carries a relation variable relating its time to its local evaluation
time; an intensional operator transmits its temporal argument's relation to its complement, so an
embedded tense has access to a set of relations; and a tense constrains that whole set — past
tense requires some accessible relation to be temporal precedence, present tense requires every
accessible relation to exclude it. A past tense is *locally* licensed when its own relation is
precedence and *non-locally* licensed when a transmitted one is; the upper limit constraint bounds
every temporal argument by its local evaluation time.

## Main definitions

* `Tense.TemporalArgument`: a temporal argument with its relation variable, time index, and local
  evaluation index; `TemporalArgument.Con` is its relational constraint and
  `TemporalArgument.UpperLimit` the upper limit constraint on it.
* `Tense.PastConstraint`, `Tense.PresentConstraint`: the tense constraints on an accessible set
  of relation variables.
* `Tense.TemporalArgument.LocallyLicensed`, `Tense.TemporalArgument.NonLocallyLicensed`.

## Main statements

* `Tense.TemporalArgument.not_locallyLicensed_of_coindexed`,
  `Tense.PastConstraint.nonLocallyLicensed_of_coindexed`: a past tense coindexed with its
  evaluation time is licensed only non-locally.
* `Tense.PresentConstraint.ne_lt`: a present-constrained relation that holds somewhere is not
  precedence, so a past tense transmitted only such relations is licensed locally.
* `Tense.PastConstraint.false_of_presentConstraint`: no relation both licenses a past tense and
  satisfies a present constraint at an instantiated argument.

## References

* [abusch-1997]
-/

namespace Tense

variable {ι Time : Type*}

/-- A temporal argument: its relation variable, the index of its time, and the index of its local
evaluation time. -/
structure TemporalArgument (ι : Type*) where
  /-- The relation variable. -/
  rel : ι
  /-- The index of the argument's time. -/
  index : ℕ
  /-- The index of the local evaluation time. -/
  evalIndex : ℕ

/-- An assignment of temporal relations to relation variables. -/
abbrev RelationAssignment (ι Time : Type*) := ι → Time → Time → Prop

namespace TemporalArgument

variable (a : TemporalArgument ι) (ρ : RelationAssignment ι Time) (g : ℕ → Time)

/-- The constraint `con`: the argument's relation holds between its time and its local
evaluation time. -/
def Con : Prop := ρ a.rel (g a.index) (g a.evalIndex)

/-- The upper limit constraint: the argument's time does not follow its local evaluation time. -/
def UpperLimit [LE Time] : Prop := upperLimitConstraint (g a.index) (g a.evalIndex)

/-- Locally licensed: the argument's own relation is temporal precedence. -/
def LocallyLicensed [LT Time] : Prop := ρ a.rel = (· < ·)

/-- Non-locally licensed: a transmitted relation other than the argument's own is precedence. -/
def NonLocallyLicensed [LT Time] (acc : Finset ι) : Prop :=
  ∃ r ∈ acc, r ≠ a.rel ∧ ρ r = (· < ·)

end TemporalArgument

/-- The past tense constraint on the relations a tense has access to: at least one is temporal
precedence. -/
def PastConstraint [LT Time] (ρ : RelationAssignment ι Time) (acc : Finset ι) : Prop :=
  ∃ r ∈ acc, ρ r = (· < ·)

/-- The present tense constraint: every accessible relation entails the negation of temporal
precedence. -/
def PresentConstraint [LT Time] (ρ : RelationAssignment ι Time) (acc : Finset ι) : Prop :=
  ∀ r ∈ acc, ∀ a b, ρ r a b → ¬ a < b

variable {ρ : RelationAssignment ι Time} {acc : Finset ι} {r : ι}

section LT

variable [LT Time]

theorem pastConstraint_singleton : PastConstraint ρ {r} ↔ ρ r = (· < ·) := by
  simp [PastConstraint]

theorem PastConstraint.of_mem (hr : r ∈ acc) (h : ρ r = (· < ·)) : PastConstraint ρ acc :=
  ⟨r, hr, h⟩

/-- A present-constrained relation that holds somewhere is not temporal precedence. -/
theorem PresentConstraint.ne_lt (hq : PresentConstraint ρ acc) (hr : r ∈ acc) {a b : Time}
    (hab : ρ r a b) : ρ r ≠ (· < ·) := fun h =>
  hq r hr a b hab ((congrFun (congrFun h a) b).mp hab)

/-- No relation both licenses a past tense and satisfies a present constraint at an instantiated
argument. -/
theorem PastConstraint.false_of_presentConstraint (hp : PastConstraint ρ {r}) {acc : Finset ι}
    (hq : PresentConstraint ρ acc) (hr : r ∈ acc) {a b : Time} (hab : ρ r a b) : False :=
  hq.ne_lt hr hab (pastConstraint_singleton.1 hp)

end LT

section Preorder

variable [Preorder Time] {a : TemporalArgument ι} {g : ℕ → Time}

theorem TemporalArgument.not_locallyLicensed_of_coindexed (hcon : a.Con ρ g)
    (h : a.index = a.evalIndex) : ¬ a.LocallyLicensed ρ := fun hl => by
  rw [TemporalArgument.LocallyLicensed] at hl
  rw [TemporalArgument.Con, hl, h] at hcon
  exact lt_irrefl _ hcon

/-- A past tense coindexed with its local evaluation time is licensed non-locally. -/
theorem PastConstraint.nonLocallyLicensed_of_coindexed (hp : PastConstraint ρ acc)
    (hcon : a.Con ρ g) (h : a.index = a.evalIndex) : a.NonLocallyLicensed ρ acc :=
  let ⟨r, hr, hρ⟩ := hp
  ⟨r, hr, fun hra => a.not_locallyLicensed_of_coindexed hcon h
    (by rw [TemporalArgument.LocallyLicensed, ← hra]; exact hρ), hρ⟩

end Preorder

end Tense
