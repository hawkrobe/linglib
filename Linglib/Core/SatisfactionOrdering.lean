import Mathlib.Data.Set.Basic

/-!
# Satisfaction Ordering

Generic ordering framework for Kratzer-style semantics: ordering elements
by how many "ideals" they satisfy.
-/

namespace Core.SatisfactionOrdering

/-- A satisfaction-based ordering on type α by subset inclusion of satisfied ideals. -/
structure SatisfactionOrdering (α : Type*) (Ideal : Type*) where
  /-- Which ideals does α satisfy? -/
  satisfies : α → Ideal → Bool
  /-- The domain of ideals (for enumeration) -/
  ideals : List Ideal

namespace SatisfactionOrdering

variable {α Ideal : Type*}

/-- The set of ideals satisfied by element a -/
def satisfiedBy (o : SatisfactionOrdering α Ideal) (a : α) : List Ideal :=
  o.ideals.filter (o.satisfies a)

/-- Weak ordering: a ≥ a' iff a satisfies everything a' satisfies. -/
def atLeastAsGood (o : SatisfactionOrdering α Ideal) (a a' : α) : Bool :=
  (o.satisfiedBy a').all (o.satisfies a)

/-- Strict ordering: a > a' iff a ≥ a' but not a' ≥ a. -/
def strictlyBetter (o : SatisfactionOrdering α Ideal) (a a' : α) : Bool :=
  o.atLeastAsGood a a' && !o.atLeastAsGood a' a

/-- Equivalence: a and a' satisfy the same ideals. -/
def equivalent (o : SatisfactionOrdering α Ideal) (a a' : α) : Bool :=
  o.atLeastAsGood a a' && o.atLeastAsGood a' a

/-- Best elements: those at least as good as all others. -/
def best (o : SatisfactionOrdering α Ideal) (candidates : List α) : List α :=
  candidates.filter fun a =>
    candidates.all fun a' => o.atLeastAsGood a a'

/-- The ordering is reflexive. -/
theorem atLeastAsGood_refl (o : SatisfactionOrdering α Ideal) (a : α) :
    o.atLeastAsGood a a = true := by
  unfold atLeastAsGood satisfiedBy
  simp only [List.all_eq_true, List.mem_filter, and_imp]
  intro p _ hp
  exact hp

/-- The ordering is transitive. -/
theorem atLeastAsGood_trans (o : SatisfactionOrdering α Ideal) (a b c : α)
    (hab : o.atLeastAsGood a b = true)
    (hbc : o.atLeastAsGood b c = true) :
    o.atLeastAsGood a c = true := by
  unfold atLeastAsGood at *
  simp only [List.all_eq_true, satisfiedBy, List.mem_filter] at *
  intro p ⟨hp_in, hp_c⟩
  -- c satisfies p, so b satisfies p (by hbc)
  have hp_b : o.satisfies b p = true := hbc p ⟨hp_in, hp_c⟩
  -- b satisfies p, so a satisfies p (by hab)
  exact hab p ⟨hp_in, hp_b⟩

/-- With empty ideals, all elements are equivalent. -/
theorem empty_ideals_all_equivalent (o : SatisfactionOrdering α Ideal)
    (h : o.ideals = []) (a a' : α) :
    o.equivalent a a' = true := by
  unfold equivalent atLeastAsGood satisfiedBy
  simp only [h, List.filter_nil, List.all_nil, Bool.and_self]

/-- With empty ideals, all candidates are "best". -/
theorem empty_ideals_all_best (o : SatisfactionOrdering α Ideal)
    (h : o.ideals = []) (candidates : List α) :
    o.best candidates = candidates := by
  unfold best
  simp only [List.filter_eq_self]
  intro a _
  simp only [List.all_eq_true]
  intro a' _
  unfold atLeastAsGood satisfiedBy
  simp only [h, List.filter_nil, List.all_nil]

/-- Convert Boolean ordering to Prop for mathlib compatibility. -/
def le (o : SatisfactionOrdering α Ideal) (a a' : α) : Prop :=
  o.atLeastAsGood a a' = true

/-- Mathlib Preorder instance for SatisfactionOrdering. -/
def toPreorder (o : SatisfactionOrdering α Ideal) : Preorder α where
  le := o.le
  le_refl a := atLeastAsGood_refl o a
  le_trans a b c := atLeastAsGood_trans o a b c

/-- Equivalence relation induced by the preorder. -/
def equiv (o : SatisfactionOrdering α Ideal) (a a' : α) : Prop :=
  o.le a a' ∧ o.le a' a

theorem equiv_refl (o : SatisfactionOrdering α Ideal) (a : α) :
    o.equiv a a :=
  ⟨atLeastAsGood_refl o a, atLeastAsGood_refl o a⟩

theorem equiv_symm (o : SatisfactionOrdering α Ideal) (a a' : α)
    (h : o.equiv a a') : o.equiv a' a :=
  ⟨h.2, h.1⟩

theorem equiv_trans (o : SatisfactionOrdering α Ideal) (a b c : α)
    (hab : o.equiv a b) (hbc : o.equiv b c) : o.equiv a c :=
  ⟨atLeastAsGood_trans o a b c hab.1 hbc.1, atLeastAsGood_trans o c b a hbc.2 hab.2⟩

end SatisfactionOrdering

/-- Kratzer's world ordering: w satisfies p iff p(w) = true. -/
def worldOrdering (World : Type*) (props : List (World → Bool)) :
    SatisfactionOrdering World (World → Bool) where
  satisfies := fun w p => p w
  ideals := props

/-- Phillips-Brown's proposition ordering: a satisfies p iff a entails p. -/
def propositionOrdering (World : Type*) [BEq World] (worlds : List World)
    (desires : List (World → Bool)) :
    SatisfactionOrdering (World → Bool) (World → Bool) where
  satisfies := fun a p => worlds.all fun w => !a w || p w  -- a entails p
  ideals := desires

/-- Proposition entailment: a entails p iff every a-world is a p-world. -/
def propEntails {World : Type*} (worlds : List World) (a p : World → Bool) : Bool :=
  worlds.all fun w => !a w || p w

end Core.SatisfactionOrdering
