import Mathlib.Data.Set.Basic

/-!
# Order Theory

Satisfaction-based orderings: ordering elements by how many criteria they satisfy.
Used by Kratzer modal semantics (worlds by propositions) and Phillips-Brown
desire semantics (propositions by desires).
-/

namespace Core.OrderTheory

/-- Satisfaction-based ordering on type α by subset inclusion of satisfied criteria. -/
structure SatisfactionOrdering (α : Type*) (Criterion : Type*) where
  satisfies : α → Criterion → Bool
  criteria : List Criterion

namespace SatisfactionOrdering

variable {α Criterion : Type*}

def satisfiedBy (o : SatisfactionOrdering α Criterion) (a : α) : List Criterion :=
  o.criteria.filter (o.satisfies a)

/-- Weak ordering: a ≥ a' iff a satisfies everything a' satisfies. -/
def atLeastAsGood (o : SatisfactionOrdering α Criterion) (a a' : α) : Bool :=
  (o.satisfiedBy a').all (o.satisfies a)

/-- Strict ordering: a > a' iff a ≥ a' but not a' ≥ a. -/
def strictlyBetter (o : SatisfactionOrdering α Criterion) (a a' : α) : Bool :=
  o.atLeastAsGood a a' && !o.atLeastAsGood a' a

/-- Equivalence: a and a' satisfy the same criteria. -/
def equivalent (o : SatisfactionOrdering α Criterion) (a a' : α) : Bool :=
  o.atLeastAsGood a a' && o.atLeastAsGood a' a

/-- Best elements: those at least as good as all others. -/
def best (o : SatisfactionOrdering α Criterion) (candidates : List α) : List α :=
  candidates.filter λ a => candidates.all λ a' => o.atLeastAsGood a a'

theorem atLeastAsGood_refl (o : SatisfactionOrdering α Criterion) (a : α) :
    o.atLeastAsGood a a = true := by
  unfold atLeastAsGood satisfiedBy
  simp only [List.all_eq_true, List.mem_filter, and_imp]
  intro p _ hp; exact hp

theorem atLeastAsGood_trans (o : SatisfactionOrdering α Criterion) (a b c : α)
    (hab : o.atLeastAsGood a b = true) (hbc : o.atLeastAsGood b c = true) :
    o.atLeastAsGood a c = true := by
  unfold atLeastAsGood at *
  simp only [List.all_eq_true, satisfiedBy, List.mem_filter] at *
  intro p ⟨hp_in, hp_c⟩
  have hp_b : o.satisfies b p = true := hbc p ⟨hp_in, hp_c⟩
  exact hab p ⟨hp_in, hp_b⟩

theorem empty_criteria_all_equivalent (o : SatisfactionOrdering α Criterion)
    (h : o.criteria = []) (a a' : α) : o.equivalent a a' = true := by
  unfold equivalent atLeastAsGood satisfiedBy
  simp only [h, List.filter_nil, List.all_nil, Bool.and_self]

theorem empty_criteria_all_best (o : SatisfactionOrdering α Criterion)
    (h : o.criteria = []) (candidates : List α) : o.best candidates = candidates := by
  unfold best
  simp only [List.filter_eq_self]
  intro a _
  simp only [List.all_eq_true]
  intro a' _
  unfold atLeastAsGood satisfiedBy
  simp only [h, List.filter_nil, List.all_nil]

/-- Prop-valued ordering for mathlib. -/
def le (o : SatisfactionOrdering α Criterion) (a a' : α) : Prop :=
  o.atLeastAsGood a a' = true

def toPreorder (o : SatisfactionOrdering α Criterion) : Preorder α where
  le := o.le
  le_refl a := atLeastAsGood_refl o a
  le_trans a b c := atLeastAsGood_trans o a b c

def equiv (o : SatisfactionOrdering α Criterion) (a a' : α) : Prop :=
  o.le a a' ∧ o.le a' a

theorem equiv_refl (o : SatisfactionOrdering α Criterion) (a : α) : o.equiv a a :=
  ⟨atLeastAsGood_refl o a, atLeastAsGood_refl o a⟩

theorem equiv_symm (o : SatisfactionOrdering α Criterion) (a a' : α)
    (h : o.equiv a a') : o.equiv a' a := ⟨h.2, h.1⟩

theorem equiv_trans (o : SatisfactionOrdering α Criterion) (a b c : α)
    (hab : o.equiv a b) (hbc : o.equiv b c) : o.equiv a c :=
  ⟨atLeastAsGood_trans o a b c hab.1 hbc.1, atLeastAsGood_trans o c b a hbc.2 hab.2⟩

end SatisfactionOrdering

end Core.OrderTheory
