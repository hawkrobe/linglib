/-
# Adjective Semantics and Predicate Modification

This module formalizes the semantics of adjectives following Kamp (1975),
Parsons (1970), and the synthesis in Kamp & Partee (1995).

## The Adjective Hierarchy

Adjectives form a hierarchy based on their semantic properties:

1. **Intersective** ("gray", "French", "carnivorous"):
   ⟦gray cat⟧ = ⟦gray⟧ ∩ ⟦cat⟧

2. **Subsective** ("skillful", "good", "typical"):
   ⟦skillful surgeon⟧ ⊆ ⟦surgeon⟧  (but NOT intersection!)
   A skillful surgeon + violinist ≠ skillful violinist

3. **Non-subsective/Modal** ("alleged", "potential", "putative"):
   No entailment either way. An alleged murderer may or may not be a murderer.

4. **"Privative"** ("fake", "counterfeit", "fictitious"):
   Traditionally: ⟦fake gun⟧ ∩ ⟦gun⟧ = ∅
   But Partee (2001) argues these are actually subsective + noun coercion!

## The General Type for Adjectives

Following Montague (1970), the most general type for adjectives is:
  ⟨⟨s,⟨e,t⟩⟩, ⟨e,t⟩⟩  (functions from properties to properties)

Meaning postulates constrain subclasses:
- Intersective: ∃P. ∀Q,x. ADJ(Q)(x) ↔ P(x) ∧ Q(x)
- Subsective: ∀Q,x. ADJ(Q)(x) → Q(x)
- (No constraint for modal adjectives)

## Predicate Modification (H&K Ch. 4)

PM is a **special composition rule** for intersective adjectives only:
  ⟦α β⟧ = λx. ⟦α⟧(x) ∧ ⟦β⟧(x)

This handles: "gray cat" = λx. gray(x) ∧ cat(x)

**Important**: PM should NOT be applied blindly to all adjective-noun
combinations. The inference "Francis is a skillful surgeon and a violinist,
therefore Francis is a skillful violinist" is INVALID.

## Partee's Insight: No Privatives

Partee (2001) "Privative Adjectives: Subsective plus Coercion" argues that
"fake gun" involves coerced expansion of "gun" to include fake-guns, making
"fake" subsective within this expanded domain. Evidence:
- "Is that gun real or fake?" (the noun must include both!)
- Polish NP-splitting: privative adjectives pattern with subsective, not modal

## References

- Kamp (1975) "Two theories about adjectives"
- Parsons (1970) "Some problems concerning the logic of grammatical modifiers"
- Kamp & Partee (1995) "Prototype theory and compositionality"
- Partee (2001) "Privative Adjectives: Subsective plus Coercion"
- Heim & Kratzer (1998) "Semantics in Generative Grammar", Ch. 4
-/

import Linglib.Theories.Montague.Basic
import Mathlib.Data.Set.Basic

namespace Montague.Modification

open Montague

-- ============================================================================
-- Generic Predicate Modification (for any entity type)
-- ============================================================================

/-!
## Generic Predicate Modification

These definitions work for any entity type `E`, making them usable in
RSA implementations without requiring full Montague model infrastructure.

**Key function**: `predMod` implements the H&K predicate modification rule:
  ⟦α β⟧ = λx. ⟦α⟧(x) ∧ ⟦β⟧(x)
-/

/-- Predicate modification for arbitrary entity types.

Implements H&K Ch. 4 predicate modification:
  ⟦α β⟧ = λx. ⟦α⟧(x) ∧ ⟦β⟧(x)

This is the semantic operation underlying intersective adjective composition.
-/
def predMod {E : Type*} (p q : E → Bool) : E → Bool :=
  fun x => p x && q x

/-- The tautological predicate (λx. true) is the identity for predMod -/
def truePred {E : Type*} : E → Bool := fun _ => true

/-- Predicate modification is commutative -/
theorem predMod_comm {E : Type*} (p q : E → Bool) : predMod p q = predMod q p := by
  funext x; simp only [predMod, Bool.and_comm]

/-- Predicate modification is associative -/
theorem predMod_assoc {E : Type*} (p q r : E → Bool) :
    predMod (predMod p q) r = predMod p (predMod q r) := by
  funext x; simp only [predMod, Bool.and_assoc]

/-- The tautological predicate is a right identity -/
theorem predMod_true_right {E : Type*} (p : E → Bool) : predMod p truePred = p := by
  funext x; simp only [predMod, truePred, Bool.and_true]

/-- The tautological predicate is a left identity -/
theorem predMod_true_left {E : Type*} (p : E → Bool) : predMod truePred p = p := by
  funext x; simp only [predMod, truePred, Bool.true_and]

-- ============================================================================
-- General Adjective Semantics (Kamp 1975, Parsons 1970)
-- ============================================================================

/--
The general type for adjectives: functions from properties to properties.

Following Montague (1970): adjective meanings map the property denoted by
the noun onto the property denoted by the adjective-noun combination.

In extensional terms: ⟨⟨e,t⟩, ⟨e,t⟩⟩
-/
abbrev AdjMeaning (m : Model) := m.interpTy (.e ⇒ .t) → m.interpTy (.e ⇒ .t)

/--
An adjective is **subsective** if ADJ(N) ⊆ N for all nouns N.

This captures: "skillful surgeon" ⊆ "surgeon", "fake gun" ⊆ "gun*" (coerced)

Subsectivity is the WEAKEST constraint on "normal" adjectives.
Only modal adjectives (alleged, potential) escape it.
-/
def isSubsective {m : Model} (adj : AdjMeaning m) : Prop :=
  ∀ (noun : m.interpTy (.e ⇒ .t)),
    predicateToSet (adj noun) ⊆ predicateToSet noun

/--
An adjective is **intersective** if ADJ(N) = ADJ ∩ N for some fixed predicate ADJ.

This is STRONGER than subsectivity: the adjective has a context-independent
extension that simply intersects with the noun.
-/
def isIntersective {m : Model} (adj : AdjMeaning m) : Prop :=
  ∃ (adjPred : m.interpTy (.e ⇒ .t)),
    ∀ (noun : m.interpTy (.e ⇒ .t)),
      ∀ (x : m.Entity), adj noun x = (adjPred x && noun x)

/-- Every intersective adjective is subsective -/
theorem intersective_implies_subsective {m : Model} (adj : AdjMeaning m)
    (h : isIntersective adj) : isSubsective adj := by
  intro noun x hx
  obtain ⟨adjPred, hAdj⟩ := h
  simp only [predicateToSet, Set.mem_setOf_eq] at hx ⊢
  rw [hAdj] at hx
  exact Bool.and_elim_right hx

-- ============================================================================
-- Predicate Modification (H&K §4.2) - For Intersective Adjectives Only!
-- ============================================================================

/--
Predicate Modification: intersect two ⟨e,t⟩ predicates.

**IMPORTANT**: This rule is valid ONLY for intersective adjectives!

If α and β are both of type ⟨e,t⟩ AND the adjective is intersective, then:
  ⟦α β⟧ = λx. ⟦α⟧(x) ∧ ⟦β⟧(x)

For non-intersective adjectives (skillful, alleged, fake), applying PM
blindly leads to invalid inferences.
-/
def predicateModification {m : Model}
    (p₁ p₂ : m.interpTy (.e ⇒ .t)) : m.interpTy (.e ⇒ .t) :=
  fun x => p₁ x && p₂ x

/-- Infix notation for predicate modification -/
infixl:70 " ⊓ₚ " => predicateModification

/--
PM as an adjective meaning: given an adjective predicate, return the
adjective function that intersects with any noun.

This shows how intersective adjectives can be "lowered" from the general
⟨⟨e,t⟩,⟨e,t⟩⟩ type to a simple ⟨e,t⟩ predicate.
-/
def intersectiveAdj {m : Model} (adjPred : m.interpTy (.e ⇒ .t)) : AdjMeaning m :=
  fun noun => adjPred ⊓ₚ noun

/-- An intersective adjective defined via PM is indeed intersective -/
theorem intersectiveAdj_is_intersective {m : Model} (adjPred : m.interpTy (.e ⇒ .t))
    : isIntersective (intersectiveAdj adjPred) := by
  use adjPred
  intro noun x
  rfl

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
-- The Intersective Adjective Equivalence (H&K §4.3.3)
-- ============================================================================

/-
H&K Chapter 4, section 4.3.3:

Both analyses of adjectives that we have entertained so far predict that the
following pair of sentences are logically equivalent:

  (12) (a) Julius is a gray cat.
       (b) Julius is gray and Julius is a cat.

In the analysis that uses PM, the equivalence follows directly from the content
of the rule. **We can prove it without using any specific information about the
meanings of the lexical items, except the information about their semantic type.**

This is the key theorem: PM ensures intersective adjective equivalence purely
from the composition rule itself.
-/

/--
**Intersective Adjective Equivalence (pointwise)**

For any entity x and predicates P, Q of type ⟨e,t⟩:
  (P ⊓ₚ Q)(x) = true  ↔  P(x) = true ∧ Q(x) = true

H&K (12): "Julius is a gray cat" ≡ "Julius is gray ∧ Julius is a cat"

This equivalence follows purely from the PM rule without any lexical knowledge.
-/
theorem intersective_equivalence {m : Model}
    (p q : m.interpTy (.e ⇒ .t)) (x : m.Entity)
    : (p ⊓ₚ q) x = true ↔ p x = true ∧ q x = true := by
  simp only [predicateModification]
  constructor
  · intro h; exact ⟨Bool.and_elim_left h, Bool.and_elim_right h⟩
  · intro ⟨h1, h2⟩; exact Bool.and_intro h1 h2

/--
**Intersective Adjective Equivalence (membership form)**

x ∈ ⟦A N⟧ ↔ x ∈ ⟦A⟧ ∧ x ∈ ⟦N⟧

An entity satisfies "gray cat" iff it satisfies both "gray" and "cat".
-/
theorem intersective_equivalence_set {m : Model}
    (p q : m.interpTy (.e ⇒ .t)) (x : m.Entity)
    : x ∈ predicateToSet (p ⊓ₚ q) ↔ x ∈ predicateToSet p ∧ x ∈ predicateToSet q := by
  simp only [predicateToSet, Set.mem_setOf_eq, predicateModification]
  constructor
  · intro h; exact ⟨Bool.and_elim_left h, Bool.and_elim_right h⟩
  · intro ⟨h1, h2⟩; exact Bool.and_intro h1 h2

/--
**Downward Entailment for PM**

If x satisfies (P ⊓ₚ Q), then x satisfies P.

This captures: "Julius is a gray cat" entails "Julius is a cat"
-/
theorem pm_entails_left {m : Model}
    (p q : m.interpTy (.e ⇒ .t)) (x : m.Entity)
    (h : (p ⊓ₚ q) x = true) : p x = true := by
  simp only [predicateModification] at h
  exact Bool.and_elim_left h

/--
**Downward Entailment for PM (right)**

If x satisfies (P ⊓ₚ Q), then x satisfies Q.

This captures: "Julius is a gray cat" entails "Julius is gray"
-/
theorem pm_entails_right {m : Model}
    (p q : m.interpTy (.e ⇒ .t)) (x : m.Entity)
    (h : (p ⊓ₚ q) x = true) : q x = true := by
  simp only [predicateModification] at h
  exact Bool.and_elim_right h

/--
**Conjunction Introduction for PM**

If x satisfies P and x satisfies Q, then x satisfies (P ⊓ₚ Q).

This is the converse direction: from "Julius is gray" and "Julius is a cat",
we can conclude "Julius is a gray cat".
-/
theorem pm_intro {m : Model}
    (p q : m.interpTy (.e ⇒ .t)) (x : m.Entity)
    (hp : p x = true) (hq : q x = true) : (p ⊓ₚ q) x = true := by
  simp only [predicateModification]
  exact Bool.and_intro hp hq

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

### The Adjective Hierarchy (Kamp 1975, Parsons 1970, Partee 2001)

1. **General type**: `AdjMeaning m` = ⟨⟨e,t⟩, ⟨e,t⟩⟩ (property → property)

2. **Subsectivity**: `isSubsective adj` - ADJ(N) ⊆ N
   - The weakest constraint on "normal" adjectives
   - "skillful surgeon" ⊆ "surgeon"

3. **Intersectivity**: `isIntersective adj` - ADJ(N) = ADJ ∩ N
   - Stronger: adjective has context-independent extension
   - "gray cat" = "gray" ∩ "cat"

4. **Key theorem**: `intersective_implies_subsective`
   - Every intersective adjective is subsective

### Predicate Modification (for Intersective Adjectives)

- `predicateModification p₁ p₂`: intersect two ⟨e,t⟩ predicates
- Notation: `p₁ ⊓ₚ p₂`
- `intersectiveAdj adjPred`: lift ⟨e,t⟩ to intersective ⟨⟨e,t⟩,⟨e,t⟩⟩

**WARNING**: PM should ONLY be used for intersective adjectives!

### Algebraic Properties of PM
- Commutativity, Associativity, Idempotence
- Identity (λx.true), Annihilator (λx.false)

### The H&K §4.3.3 Theorem (Intersective Case Only)
- `intersective_equivalence`: (P ⊓ₚ Q)(x) ↔ P(x) ∧ Q(x)
- `pm_entails_left/right`: downward entailment
- `pm_intro`: conjunction introduction

### What This Module Does NOT Handle

- **Subsective non-intersective** ("skillful"): Francis is a skillful surgeon
  and a violinist, but NOT a skillful violinist. Requires relative interpretation.

- **Modal/Non-subsective** ("alleged"): No entailment. Needs intensional types.

- **"Privative"** ("fake"): Partee argues these are subsective + coercion.
  "fake gun" = subsective within coerced "gun*" (= guns ∪ fake-guns).
  This requires formalizing noun coercion, not currently implemented.

## References

- Kamp (1975) "Two theories about adjectives"
- Kamp & Partee (1995) "Prototype theory and compositionality"
- Partee (2001) "Privative Adjectives: Subsective plus Coercion"
- Heim & Kratzer (1998) Ch. 4
-/

end Montague.Modification
