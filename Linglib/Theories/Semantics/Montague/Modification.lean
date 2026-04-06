/-
# Predicate Modification
@cite{kamp-1975} @cite{kamp-partee-1995} @cite{parsons-1970}

Predicate modification (@cite{heim-kratzer-1998} Ch. 4):
`⟦α β⟧ = λx. ⟦α⟧(x) ∧ ⟦β⟧(x)`, valid for intersective adjectives only.

The adjective classification hierarchy (intersective, subsective,
privative, extensional) is in
`Theories/Semantics/Lexical/Adjective/Classification.lean`.
-/

import Linglib.Theories.Semantics.Montague.Types
import Mathlib.Data.Set.Basic

namespace Semantics.Montague.Modification

open Semantics.Montague

section Generic

/-- Predicate modification: `⟦α β⟧ = λx. ⟦α⟧(x) ∧ ⟦β⟧(x)` -/
def predMod {E : Type*} (p q : E → Bool) : E → Bool :=
  λ x => p x && q x

def truePred {E : Type*} : E → Bool := λ _ => true

theorem predMod_comm {E : Type*} (p q : E → Bool) : predMod p q = predMod q p := by
  funext x; simp only [predMod, Bool.and_comm]

theorem predMod_assoc {E : Type*} (p q r : E → Bool) :
    predMod (predMod p q) r = predMod p (predMod q r) := by
  funext x; simp only [predMod, Bool.and_assoc]

theorem predMod_true_right {E : Type*} (p : E → Bool) : predMod p truePred = p := by
  funext x; simp only [predMod, truePred, Bool.and_true]

theorem predMod_true_left {E : Type*} (p : E → Bool) : predMod truePred p = p := by
  funext x; simp only [predMod, truePred, Bool.true_and]

end Generic

/-! The adjective classification hierarchy (intersective, subsective,
    privative, extensional) is in `Lexical/Adjective/Classification.lean`.
    This file provides the composition operation (Predicate Modification)
    that implements the intersective case. -/

section PredicateModification

def predicateModification {m : Model}
    (p₁ p₂ : m.interpTy (.e ⇒ .t)) : m.interpTy (.e ⇒ .t) :=
  λ x => p₁ x ∧ p₂ x

infixl:70 " ⊓ₚ " => predicateModification

theorem predicateModification_comm {m : Model} (p₁ p₂ : m.interpTy (.e ⇒ .t))
    : p₁ ⊓ₚ p₂ = p₂ ⊓ₚ p₁ := by
  funext x
  simp only [predicateModification, And.comm]

theorem predicateModification_assoc {m : Model}
    (p₁ p₂ p₃ : m.interpTy (.e ⇒ .t))
    : (p₁ ⊓ₚ p₂) ⊓ₚ p₃ = p₁ ⊓ₚ (p₂ ⊓ₚ p₃) := by
  funext x
  exact propext and_assoc

theorem predicateModification_idem {m : Model} (p : m.interpTy (.e ⇒ .t))
    : p ⊓ₚ p = p := by
  funext x
  exact propext ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, h⟩⟩

theorem predicateModification_true_right {m : Model} (p : m.interpTy (.e ⇒ .t))
    : p ⊓ₚ (λ _ => True) = p := by
  funext x
  exact propext ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, trivial⟩⟩

theorem predicateModification_true_left {m : Model} (p : m.interpTy (.e ⇒ .t))
    : (λ _ => True) ⊓ₚ p = p := by
  funext x
  exact propext ⟨fun ⟨_, h⟩ => h, fun h => ⟨trivial, h⟩⟩

theorem predicateModification_false_right {m : Model} (p : m.interpTy (.e ⇒ .t))
    : p ⊓ₚ (λ _ => False) = (λ _ => False) := by
  funext x
  exact propext ⟨fun ⟨_, h⟩ => h, fun h => h.elim⟩

theorem predicateModification_false_left {m : Model} (p : m.interpTy (.e ⇒ .t))
    : (λ _ => False) ⊓ₚ p = (λ _ => False) := by
  funext x
  exact propext ⟨fun ⟨h, _⟩ => h, fun h => h.elim⟩

theorem predicateModification_extension {m : Model}
    (p₁ p₂ : m.interpTy (.e ⇒ .t))
    : predicateToSet (p₁ ⊓ₚ p₂) = predicateToSet p₁ ∩ predicateToSet p₂ := by
  ext x
  simp only [predicateToSet, predicateModification, Set.mem_setOf_eq, Set.mem_inter_iff]

theorem predicateModification_subset_left {m : Model}
    (p q r : m.interpTy (.e ⇒ .t))
    (h : predicateToSet p ⊆ predicateToSet q)
    : predicateToSet (p ⊓ₚ r) ⊆ predicateToSet (q ⊓ₚ r) := by
  simp only [predicateModification_extension]
  exact Set.inter_subset_inter_left _ h

theorem predicateModification_subset_right {m : Model}
    (p q r : m.interpTy (.e ⇒ .t))
    (h : predicateToSet p ⊆ predicateToSet q)
    : predicateToSet (r ⊓ₚ p) ⊆ predicateToSet (r ⊓ₚ q) := by
  simp only [predicateModification_extension]
  exact Set.inter_subset_inter_right _ h

/-- `(P ⊓ₚ Q)(x) ↔ P(x) ∧ Q(x)` -/
theorem intersective_equivalence {m : Model}
    (p q : m.interpTy (.e ⇒ .t)) (x : m.Entity)
    : (p ⊓ₚ q) x ↔ p x ∧ q x := by
  exact Iff.rfl

theorem intersective_equivalence_set {m : Model}
    (p q : m.interpTy (.e ⇒ .t)) (x : m.Entity)
    : x ∈ predicateToSet (p ⊓ₚ q) ↔ x ∈ predicateToSet p ∧ x ∈ predicateToSet q := by
  simp only [predicateToSet, Set.mem_setOf_eq, predicateModification]

theorem pm_entails_left {m : Model}
    (p q : m.interpTy (.e ⇒ .t)) (x : m.Entity)
    (h : (p ⊓ₚ q) x) : p x := h.1

theorem pm_entails_right {m : Model}
    (p q : m.interpTy (.e ⇒ .t)) (x : m.Entity)
    (h : (p ⊓ₚ q) x) : q x := h.2

theorem pm_intro {m : Model}
    (p q : m.interpTy (.e ⇒ .t)) (x : m.Entity)
    (hp : p x) (hq : q x) : (p ⊓ₚ q) x := ⟨hp, hq⟩

end PredicateModification

section Examples

open ToyEntity ToyLexicon

def gray_sem : toyModel.interpTy (.e ⇒ .t) :=
  λ x => match x with
    | .john => True
    | .mary => True
    | _ => False

def cat_sem : toyModel.interpTy (.e ⇒ .t) :=
  λ x => match x with
    | .pizza => True
    | _ => False

def big_sem : toyModel.interpTy (.e ⇒ .t) :=
  λ x => match x with
    | .book => True
    | _ => False

def grayCat_sem : toyModel.interpTy (.e ⇒ .t) :=
  gray_sem ⊓ₚ cat_sem

example : predicateToSet grayCat_sem = predicateToSet gray_sem ∩ predicateToSet cat_sem :=
  predicateModification_extension gray_sem cat_sem

theorem grayCat_empty : predicateToSet grayCat_sem = ∅ := by
  ext x
  show grayCat_sem x ↔ x ∈ (∅ : Set _)
  simp only [Set.mem_empty_iff_false, iff_false]
  cases x <;> simp [grayCat_sem, predicateModification, gray_sem, cat_sem]

def bigGrayCat_sem : toyModel.interpTy (.e ⇒ .t) :=
  big_sem ⊓ₚ (gray_sem ⊓ₚ cat_sem)

theorem bigGrayCat_assoc :
    big_sem ⊓ₚ (gray_sem ⊓ₚ cat_sem) = (big_sem ⊓ₚ gray_sem) ⊓ₚ cat_sem :=
  (predicateModification_assoc big_sem gray_sem cat_sem).symm

theorem grayCat_order :
    gray_sem ⊓ₚ (big_sem ⊓ₚ cat_sem) = big_sem ⊓ₚ (gray_sem ⊓ₚ cat_sem) := by
  conv_lhs => rw [← predicateModification_assoc]
  conv_rhs => rw [← predicateModification_assoc]
  rw [predicateModification_comm gray_sem big_sem]

end Examples

end Semantics.Montague.Modification
