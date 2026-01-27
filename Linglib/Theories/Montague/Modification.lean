/-
# Montague Semantics: Predicate Modification

The Predicate Modification composition rule from Heim & Kratzer (1998) Ch. 4.

## The Rule

When two expressions of type ⟨e,t⟩ combine, their denotations are intersected:

  ⟦α β⟧ = λx. ⟦α⟧(x) ∧ ⟦β⟧(x)

## Linguistic Motivation

This handles cases like:
- "gray cat" = λx. gray(x) ∧ cat(x)
- "big gray cat" = λx. big(x) ∧ gray(x) ∧ cat(x)

This is the standard treatment of **intersective adjectives**. Non-intersective
adjectives (subsective like "skillful", intensional like "alleged") require
different treatments and may override this rule.

## References

- Heim & Kratzer (1998) "Semantics in Generative Grammar", Ch. 4
-/

import Linglib.Theories.Montague.Basic
import Mathlib.Data.Set.Basic

namespace Montague.Modification

open Montague

-- ============================================================================
-- Predicate Modification (H&K §4.2)
-- ============================================================================

/--
Predicate Modification: intersect two ⟨e,t⟩ predicates.

If α and β are both of type ⟨e,t⟩, then:
  ⟦α β⟧ = λx. ⟦α⟧(x) ∧ ⟦β⟧(x)

This handles cases like "happy dog" where both predicates are intersected.
-/
def predicateModification {m : Model}
    (p₁ p₂ : m.interpTy (.e ⇒ .t)) : m.interpTy (.e ⇒ .t) :=
  fun x => p₁ x && p₂ x

/-- Infix notation for predicate modification -/
infixl:70 " ⊓ₚ " => predicateModification

-- ============================================================================
-- Algebraic Properties
-- ============================================================================

/-- Predicate Modification is commutative -/
theorem predicateModification_comm {m : Model} (p₁ p₂ : m.interpTy (.e ⇒ .t))
    : p₁ ⊓ₚ p₂ = p₂ ⊓ₚ p₁ := by
  funext x
  simp only [predicateModification, Bool.and_comm]

/-- Predicate Modification is associative -/
theorem predicateModification_assoc {m : Model}
    (p₁ p₂ p₃ : m.interpTy (.e ⇒ .t))
    : (p₁ ⊓ₚ p₂) ⊓ₚ p₃ = p₁ ⊓ₚ (p₂ ⊓ₚ p₃) := by
  funext x
  simp only [predicateModification, Bool.and_assoc]

/-- Predicate Modification is idempotent -/
theorem predicateModification_idem {m : Model} (p : m.interpTy (.e ⇒ .t))
    : p ⊓ₚ p = p := by
  funext x
  simp only [predicateModification, Bool.and_self]

/-- The tautological predicate (λx. true) is a right identity -/
theorem predicateModification_true_right {m : Model} (p : m.interpTy (.e ⇒ .t))
    : p ⊓ₚ (fun _ => true) = p := by
  funext x
  simp only [predicateModification, Bool.and_true]

/-- The tautological predicate (λx. true) is a left identity -/
theorem predicateModification_true_left {m : Model} (p : m.interpTy (.e ⇒ .t))
    : (fun _ => true) ⊓ₚ p = p := by
  funext x
  simp only [predicateModification, Bool.true_and]

/-- The contradictory predicate (λx. false) is a right annihilator -/
theorem predicateModification_false_right {m : Model} (p : m.interpTy (.e ⇒ .t))
    : p ⊓ₚ (fun _ => false) = (fun _ => false) := by
  funext x
  simp only [predicateModification, Bool.and_false]

/-- The contradictory predicate (λx. false) is a left annihilator -/
theorem predicateModification_false_left {m : Model} (p : m.interpTy (.e ⇒ .t))
    : (fun _ => false) ⊓ₚ p = (fun _ => false) := by
  funext x
  simp only [predicateModification, Bool.false_and]

-- ============================================================================
-- Connection to Set Theory
-- ============================================================================

/-- The extension of a modified predicate is the intersection of extensions -/
theorem predicateModification_extension {m : Model}
    (p₁ p₂ : m.interpTy (.e ⇒ .t))
    : predicateToSet (p₁ ⊓ₚ p₂) = predicateToSet p₁ ∩ predicateToSet p₂ := by
  ext x
  simp only [predicateToSet, predicateModification, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · intro h; exact ⟨Bool.and_elim_left h, Bool.and_elim_right h⟩
  · intro ⟨h1, h2⟩; exact Bool.and_intro h1 h2

/-- PM preserves subset relations: if P ⊆ Q then (P ⊓ R) ⊆ (Q ⊓ R) -/
theorem predicateModification_subset_left {m : Model}
    (p q r : m.interpTy (.e ⇒ .t))
    (h : predicateToSet p ⊆ predicateToSet q)
    : predicateToSet (p ⊓ₚ r) ⊆ predicateToSet (q ⊓ₚ r) := by
  simp only [predicateModification_extension]
  exact Set.inter_subset_inter_left _ h

/-- PM preserves subset relations: if P ⊆ Q then (R ⊓ P) ⊆ (R ⊓ Q) -/
theorem predicateModification_subset_right {m : Model}
    (p q r : m.interpTy (.e ⇒ .t))
    (h : predicateToSet p ⊆ predicateToSet q)
    : predicateToSet (r ⊓ₚ p) ⊆ predicateToSet (r ⊓ₚ q) := by
  simp only [predicateModification_extension]
  exact Set.inter_subset_inter_right _ h

-- ============================================================================
-- Examples with Toy Model
-- ============================================================================

section Examples

open ToyEntity ToyLexicon

/-- "gray" as a predicate (John and Mary are gray for this example) -/
def gray_sem : toyModel.interpTy (.e ⇒ .t) :=
  fun x => match x with
    | .john => true
    | .mary => true
    | _ => false

/-- "cat" as a predicate (pizza is our "cat" in this toy model) -/
def cat_sem : toyModel.interpTy (.e ⇒ .t) :=
  fun x => match x with
    | .pizza => true
    | _ => false

/-- "big" as a predicate (only book is big) -/
def big_sem : toyModel.interpTy (.e ⇒ .t) :=
  fun x => match x with
    | .book => true
    | _ => false

/-- "gray cat" via Predicate Modification -/
def grayCat_sem : toyModel.interpTy (.e ⇒ .t) :=
  gray_sem ⊓ₚ cat_sem

/-- The extension of "gray cat" is the intersection of "gray" and "cat" -/
example : predicateToSet grayCat_sem = predicateToSet gray_sem ∩ predicateToSet cat_sem :=
  predicateModification_extension gray_sem cat_sem

/-- No entity is both gray and a cat in our toy model -/
theorem grayCat_empty : predicateToSet grayCat_sem = ∅ := by
  ext x
  simp only [predicateToSet, grayCat_sem, predicateModification,
             Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  cases x <;> simp [gray_sem, cat_sem]

/-- "big gray cat" = "big" ⊓ ("gray" ⊓ "cat") -/
def bigGrayCat_sem : toyModel.interpTy (.e ⇒ .t) :=
  big_sem ⊓ₚ (gray_sem ⊓ₚ cat_sem)

/-- Associativity: "big gray cat" = ("big" ⊓ "gray") ⊓ "cat" -/
theorem bigGrayCat_assoc :
    big_sem ⊓ₚ (gray_sem ⊓ₚ cat_sem) = (big_sem ⊓ₚ gray_sem) ⊓ₚ cat_sem :=
  (predicateModification_assoc big_sem gray_sem cat_sem).symm

/-- Order doesn't matter: "gray big cat" = "big gray cat" -/
theorem grayCat_order :
    gray_sem ⊓ₚ (big_sem ⊓ₚ cat_sem) = big_sem ⊓ₚ (gray_sem ⊓ₚ cat_sem) := by
  conv_lhs => rw [← predicateModification_assoc]
  conv_rhs => rw [← predicateModification_assoc]
  rw [predicateModification_comm gray_sem big_sem]

end Examples

-- ============================================================================
-- Type-Driven Composition
-- ============================================================================

/--
Check if two semantic types can compose via Predicate Modification.
Both must be ⟨e,t⟩.
-/
def canPM (ty₁ ty₂ : Ty) : Bool :=
  decide (ty₁ = Ty.fn Ty.e Ty.t) && decide (ty₂ = Ty.fn Ty.e Ty.t)

/-- PM is only possible when both types are ⟨e,t⟩ -/
theorem canPM_spec (ty₁ ty₂ : Ty) :
    canPM ty₁ ty₂ = true ↔ ty₁ = Ty.fn Ty.e Ty.t ∧ ty₂ = Ty.fn Ty.e Ty.t := by
  simp only [canPM, Bool.and_eq_true, decide_eq_true_eq]

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This Module Provides

### Core Definition
- `predicateModification p₁ p₂`: intersect two ⟨e,t⟩ predicates
- Notation: `p₁ ⊓ₚ p₂`

### Algebraic Properties
- Commutativity: `predicateModification_comm`
- Associativity: `predicateModification_assoc`
- Idempotence: `predicateModification_idem`
- Identity: `predicateModification_true_right/left`
- Annihilator: `predicateModification_false_right/left`

### Set-Theoretic Connection
- `predicateModification_extension`: PM = set intersection

### Linguistic Application
- Intersective adjectives: "gray cat", "big gray cat"
- The order of modifiers doesn't affect truth conditions (for intersective adjectives)

### Limitations
This module handles **intersective** adjectives only. For other adjective types:
- **Subsective** ("skillful surgeon"): not every skillful surgeon is skillful
- **Non-subsective** ("alleged criminal"): alleged criminals may not be criminals
- **Privative** ("fake diamond"): fake diamonds are definitely not diamonds

These require more sophisticated treatments beyond simple PM.
-/

end Montague.Modification
