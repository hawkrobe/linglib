/-
# Adjective Semantics and Predicate Modification

The adjective hierarchy (Kamp 1975, Parsons 1970, Kamp & Partee 1995):
1. Intersective: `⟦gray cat⟧ = ⟦gray⟧ ∩ ⟦cat⟧`
2. Subsective: `⟦skillful surgeon⟧ ⊆ ⟦surgeon⟧`
3. Non-subsective/modal: no entailment ("alleged")

General adjective type: `⟨⟨e,t⟩, ⟨e,t⟩⟩`. Meaning postulates constrain subclasses.

Predicate modification (H&K Ch. 4): `⟦α β⟧ = λx. ⟦α⟧(x) ∧ ⟦β⟧(x)`,
valid for intersective adjectives only.

## References

- Kamp (1975). Two theories about adjectives.
- Kamp & Partee (1995). Prototype theory and compositionality.
- Partee (2001). Privative Adjectives: Subsective plus Coercion.
- Heim & Kratzer (1998). Semantics in Generative Grammar, Ch. 4.
-/

import Linglib.Theories.Semantics.Compositional.Basic
import Mathlib.Data.Set.Basic

namespace Semantics.Compositional.Modification

open Semantics.Compositional

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

section AdjClasses

abbrev AdjMeaning (m : Model) := m.interpTy (.e ⇒ .t) → m.interpTy (.e ⇒ .t)

/-- `ADJ(N) ⊆ N` for all nouns `N`. -/
def isSubsective {m : Model} (adj : AdjMeaning m) : Prop :=
  ∀ (noun : m.interpTy (.e ⇒ .t)),
    predicateToSet (adj noun) ⊆ predicateToSet noun

/-- `ADJ(N)(x) ↔ P(x) ∧ N(x)` for some fixed predicate `P`. -/
def isIntersective {m : Model} (adj : AdjMeaning m) : Prop :=
  ∃ (adjPred : m.interpTy (.e ⇒ .t)),
    ∀ (noun : m.interpTy (.e ⇒ .t)),
      ∀ (x : m.Entity), adj noun x = (adjPred x && noun x)

theorem intersective_implies_subsective {m : Model} (adj : AdjMeaning m)
    (h : isIntersective adj) : isSubsective adj := by
  intro noun x hx
  obtain ⟨adjPred, hAdj⟩ := h
  simp only [predicateToSet, Set.mem_setOf_eq] at hx ⊢
  rw [hAdj] at hx
  exact Bool.and_elim_right hx

end AdjClasses

section PredicateModification

def predicateModification {m : Model}
    (p₁ p₂ : m.interpTy (.e ⇒ .t)) : m.interpTy (.e ⇒ .t) :=
  λ x => p₁ x && p₂ x

infixl:70 " ⊓ₚ " => predicateModification

def intersectiveAdj {m : Model} (adjPred : m.interpTy (.e ⇒ .t)) : AdjMeaning m :=
  λ noun => adjPred ⊓ₚ noun

theorem intersectiveAdj_is_intersective {m : Model} (adjPred : m.interpTy (.e ⇒ .t))
    : isIntersective (intersectiveAdj adjPred) := by
  use adjPred
  intro noun x
  rfl

theorem predicateModification_comm {m : Model} (p₁ p₂ : m.interpTy (.e ⇒ .t))
    : p₁ ⊓ₚ p₂ = p₂ ⊓ₚ p₁ := by
  funext x
  simp only [predicateModification, Bool.and_comm]

theorem predicateModification_assoc {m : Model}
    (p₁ p₂ p₃ : m.interpTy (.e ⇒ .t))
    : (p₁ ⊓ₚ p₂) ⊓ₚ p₃ = p₁ ⊓ₚ (p₂ ⊓ₚ p₃) := by
  funext x
  simp only [predicateModification, Bool.and_assoc]

theorem predicateModification_idem {m : Model} (p : m.interpTy (.e ⇒ .t))
    : p ⊓ₚ p = p := by
  funext x
  simp only [predicateModification, Bool.and_self]

theorem predicateModification_true_right {m : Model} (p : m.interpTy (.e ⇒ .t))
    : p ⊓ₚ (λ _ => true) = p := by
  funext x
  simp only [predicateModification, Bool.and_true]

theorem predicateModification_true_left {m : Model} (p : m.interpTy (.e ⇒ .t))
    : (λ _ => true) ⊓ₚ p = p := by
  funext x
  simp only [predicateModification, Bool.true_and]

theorem predicateModification_false_right {m : Model} (p : m.interpTy (.e ⇒ .t))
    : p ⊓ₚ (λ _ => false) = (λ _ => false) := by
  funext x
  simp only [predicateModification, Bool.and_false]

theorem predicateModification_false_left {m : Model} (p : m.interpTy (.e ⇒ .t))
    : (λ _ => false) ⊓ₚ p = (λ _ => false) := by
  funext x
  simp only [predicateModification, Bool.false_and]

theorem predicateModification_extension {m : Model}
    (p₁ p₂ : m.interpTy (.e ⇒ .t))
    : predicateToSet (p₁ ⊓ₚ p₂) = predicateToSet p₁ ∩ predicateToSet p₂ := by
  ext x
  simp only [predicateToSet, predicateModification, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · intro h; exact ⟨Bool.and_elim_left h, Bool.and_elim_right h⟩
  · intro ⟨h1, h2⟩; exact Bool.and_intro h1 h2

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

/-- `(P ⊓ₚ Q)(x) = true ↔ P(x) = true ∧ Q(x) = true` -/
theorem intersective_equivalence {m : Model}
    (p q : m.interpTy (.e ⇒ .t)) (x : m.Entity)
    : (p ⊓ₚ q) x = true ↔ p x = true ∧ q x = true := by
  simp only [predicateModification]
  constructor
  · intro h; exact ⟨Bool.and_elim_left h, Bool.and_elim_right h⟩
  · intro ⟨h1, h2⟩; exact Bool.and_intro h1 h2

theorem intersective_equivalence_set {m : Model}
    (p q : m.interpTy (.e ⇒ .t)) (x : m.Entity)
    : x ∈ predicateToSet (p ⊓ₚ q) ↔ x ∈ predicateToSet p ∧ x ∈ predicateToSet q := by
  simp only [predicateToSet, Set.mem_setOf_eq, predicateModification]
  constructor
  · intro h; exact ⟨Bool.and_elim_left h, Bool.and_elim_right h⟩
  · intro ⟨h1, h2⟩; exact Bool.and_intro h1 h2

theorem pm_entails_left {m : Model}
    (p q : m.interpTy (.e ⇒ .t)) (x : m.Entity)
    (h : (p ⊓ₚ q) x = true) : p x = true := by
  simp only [predicateModification] at h
  exact Bool.and_elim_left h

theorem pm_entails_right {m : Model}
    (p q : m.interpTy (.e ⇒ .t)) (x : m.Entity)
    (h : (p ⊓ₚ q) x = true) : q x = true := by
  simp only [predicateModification] at h
  exact Bool.and_elim_right h

theorem pm_intro {m : Model}
    (p q : m.interpTy (.e ⇒ .t)) (x : m.Entity)
    (hp : p x = true) (hq : q x = true) : (p ⊓ₚ q) x = true := by
  simp only [predicateModification]
  exact Bool.and_intro hp hq

end PredicateModification

section Examples

open ToyEntity ToyLexicon

def gray_sem : toyModel.interpTy (.e ⇒ .t) :=
  λ x => match x with
    | .john => true
    | .mary => true
    | _ => false

def cat_sem : toyModel.interpTy (.e ⇒ .t) :=
  λ x => match x with
    | .pizza => true
    | _ => false

def big_sem : toyModel.interpTy (.e ⇒ .t) :=
  λ x => match x with
    | .book => true
    | _ => false

def grayCat_sem : toyModel.interpTy (.e ⇒ .t) :=
  gray_sem ⊓ₚ cat_sem

example : predicateToSet grayCat_sem = predicateToSet gray_sem ∩ predicateToSet cat_sem :=
  predicateModification_extension gray_sem cat_sem

theorem grayCat_empty : predicateToSet grayCat_sem = ∅ := by
  ext x
  simp only [predicateToSet, grayCat_sem, predicateModification,
             Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  cases x <;> simp [gray_sem, cat_sem]

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

section TypeDriven

def canPM (ty₁ ty₂ : Ty) : Bool :=
  decide (ty₁ = Ty.fn Ty.e Ty.t) && decide (ty₂ = Ty.fn Ty.e Ty.t)

theorem canPM_spec (ty₁ ty₂ : Ty) :
    canPM ty₁ ty₂ = true ↔ ty₁ = Ty.fn Ty.e Ty.t ∧ ty₂ = Ty.fn Ty.e Ty.t := by
  simp only [canPM, Bool.and_eq_true, decide_eq_true_eq]

end TypeDriven

end Semantics.Compositional.Modification
