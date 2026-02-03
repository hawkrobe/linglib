/-
# Generic Ordering Framework for Kratzer-Style Semantics

Abstracts the common pattern in Kratzer modal semantics and Phillips-Brown
desire semantics: ordering elements by how many "ideals" they satisfy.

## The Pattern

Both Kratzer (1981) on worlds and Phillips-Brown (2025) on propositions use:

1. **Satisfaction**: Which ideals does element α satisfy?
   - Kratzer: `{p ∈ A : w ∈ p}` — propositions in A satisfied by world w
   - Phillips-Brown: `{p ∈ G_S : a ⊆ p}` — desires entailed by answer a

2. **Ordering**: α ≥ α' iff α satisfies everything α' satisfies
   - Kratzer: `w ≤_A z` iff `{p ∈ A : z ∈ p} ⊆ {p ∈ A : w ∈ p}`
   - Phillips-Brown: prefer a to a' iff `{p : a' ⊆ p} ⊂ {p : a ⊆ p}`

3. **Selection**: The "best" elements are maximal under the ordering

This module extracts the common structure, enabling code reuse and
making the parallel explicit.

## References

- Kratzer, A. (1981). The Notional Category of Modality.
- Phillips-Brown, M. (2025). Some-things-considered desire.
-/

import Mathlib.Data.Set.Basic

namespace Core.Ordering

-- ============================================================================
-- Generic Kratzer-Style Ordering
-- ============================================================================

/--
A satisfaction-based ordering on type α.

Given a list of "ideals" (propositions to satisfy), we can order elements
by subset inclusion of satisfied ideals.

This abstracts the common structure in:
- Kratzer: ordering worlds by satisfied propositions
- Phillips-Brown: ordering propositions by entailed desires
-/
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

/--
Element a is at least as good as a' iff a satisfies everything a' satisfies.

This is the weak ordering: a ≥ a'.
-/
def atLeastAsGood (o : SatisfactionOrdering α Ideal) (a a' : α) : Bool :=
  (o.satisfiedBy a').all (o.satisfies a)

/--
Element a is strictly better than a' iff a ≥ a' but not a' ≥ a.

This means a satisfies strictly more ideals than a'.
-/
def strictlyBetter (o : SatisfactionOrdering α Ideal) (a a' : α) : Bool :=
  o.atLeastAsGood a a' && !o.atLeastAsGood a' a

/--
Elements a and a' are equivalent iff they satisfy the same ideals.
-/
def equivalent (o : SatisfactionOrdering α Ideal) (a a' : α) : Bool :=
  o.atLeastAsGood a a' && o.atLeastAsGood a' a

/--
The best elements among a list: those that are at least as good as all others.
-/
def best (o : SatisfactionOrdering α Ideal) (candidates : List α) : List α :=
  candidates.filter fun a =>
    candidates.all fun a' => o.atLeastAsGood a a'

-- ============================================================================
-- Theorems
-- ============================================================================

/--
The ordering is reflexive: every element is at least as good as itself.
-/
theorem atLeastAsGood_refl (o : SatisfactionOrdering α Ideal) (a : α) :
    o.atLeastAsGood a a = true := by
  unfold atLeastAsGood satisfiedBy
  simp only [List.all_eq_true, List.mem_filter, and_imp]
  intro p _ hp
  exact hp

/--
The ordering is transitive.
-/
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

/--
With empty ideals, all elements are equivalent.
-/
theorem empty_ideals_all_equivalent (o : SatisfactionOrdering α Ideal)
    (h : o.ideals = []) (a a' : α) :
    o.equivalent a a' = true := by
  unfold equivalent atLeastAsGood satisfiedBy
  simp only [h, List.filter_nil, List.all_nil, Bool.and_self]

/--
With empty ideals, all candidates are "best".
-/
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

-- ============================================================================
-- Mathlib Preorder Instance
-- ============================================================================

/-- Convert Boolean ordering to Prop for mathlib compatibility. -/
def le (o : SatisfactionOrdering α Ideal) (a a' : α) : Prop :=
  o.atLeastAsGood a a' = true

/--
**Mathlib Preorder instance for SatisfactionOrdering.**

This gives access to all mathlib preorder lemmas (le_refl, le_trans, etc.)
for any satisfaction-based ordering.
-/
def toPreorder (o : SatisfactionOrdering α Ideal) : Preorder α where
  le := o.le
  le_refl a := atLeastAsGood_refl o a
  le_trans a b c := atLeastAsGood_trans o a b c

/--
**Equivalence relation induced by the preorder.**

Two elements are equivalent iff they satisfy the same ideals.
This is mathlib's `AntisymmRel` specialized to our ordering.
-/
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

-- ============================================================================
-- Convenience Constructors
-- ============================================================================

/--
Create a satisfaction ordering for worlds given propositions.

This is Kratzer's ordering: a world w satisfies proposition p iff p(w) = true.
-/
def worldOrdering (World : Type*) (props : List (World → Bool)) :
    SatisfactionOrdering World (World → Bool) where
  satisfies := fun w p => p w
  ideals := props

/--
Create a satisfaction ordering for propositions given desires.

This is Phillips-Brown's ordering: proposition a satisfies desire p iff a entails p.
-/
def propositionOrdering (World : Type*) [BEq World] (worlds : List World)
    (desires : List (World → Bool)) :
    SatisfactionOrdering (World → Bool) (World → Bool) where
  satisfies := fun a p => worlds.all fun w => !a w || p w  -- a entails p
  ideals := desires

/-- Proposition entailment: a entails p iff every a-world is a p-world. -/
def propEntails {World : Type*} (worlds : List World) (a p : World → Bool) : Bool :=
  worlds.all fun w => !a w || p w

-- ============================================================================
-- Summary
-- ============================================================================

/-!
## What This Module Provides

### Core Structure
- `SatisfactionOrdering α Ideal`: Generic ordering on α by ideal satisfaction

### Operations
- `satisfiedBy`: Ideals satisfied by an element
- `atLeastAsGood`: Weak ordering (≥)
- `strictlyBetter`: Strict ordering (>)
- `equivalent`: Equivalence under ordering
- `best`: Select maximal elements

### Theorems
- `atLeastAsGood_refl`: Reflexivity
- `atLeastAsGood_trans`: Transitivity
- `empty_ideals_all_equivalent`: Empty ideals → universal equivalence
- `empty_ideals_all_best`: Empty ideals → all elements are best

### Constructors
- `worldOrdering`: For Kratzer-style world ordering
- `propositionOrdering`: For Phillips-Brown-style proposition ordering

## Usage

```lean
-- Kratzer: order worlds by desires
let kratzerOrd := worldOrdering World desires
let bestWorlds := kratzerOrd.best accessibleWorlds

-- Phillips-Brown: order propositions by desires
let pbOrd := propositionOrdering World allWorlds desires
let bestAnswers := pbOrd.best liveAnswers
```
-/

end Core.Ordering
