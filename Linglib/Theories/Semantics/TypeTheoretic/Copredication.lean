import Linglib.Theories.Semantics.TypeTheoretic.Core

/-!
# Copredication and Complex Types @cite{chatzikyriakidis-etal-2025}

Polysemous nouns like "book" denote objects with multiple aspects
(physical object AND informational content). Copredication applies
predicates selecting different aspects to the same noun phrase:
  "The book is heavy and interesting"
  — heavy selects PhysObj, interesting selects Info.

We model complex types as TTR meet types (T₁ × T₂), copredication
as subtype projection, and individuation criteria as equivalence
relations that determine counting under each aspect.

## Key idea

A dot type (Pustejovsky 1995, Asher 2011) is just a TTR meet type:
  Book = PhysObj ⊓ Info = PhysObj × Info

Copredication works because MeetType projects to each component
via the existing SubtypeOf instances (meetSubtypeLeft/Right).

The non-trivial contribution is *individuation*: when we count
"three books were mastered and burned," do we count physical
volumes or informational contents? This requires an individuation
criterion — an equivalence relation determining what counts as "one."

## References

- Chatzikyriakidis, S., Cooper, R., Gregoromichelaki, E. & Sutton, P. (2025).
  Types and the Structure of Meaning. Cambridge Elements in Semantics.
- Pustejovsky, J. (1995). The Generative Lexicon. MIT Press.
- Asher, N. (2011). Lexical Meaning in Context. CUP.
- Cooper, R. (2023). From Perception to Communication. OUP.
-/

namespace Semantics.TypeTheoretic

/-! ## Complex types (dot types)

A complex type pairs two aspects of a polysemous noun.
This is TTR's `MeetType` (= Lean `Prod`), re-exported with
linguistic terminology for the polysemy domain. -/

/-- A complex (dot) type: an entity with two semantic aspects.
Pustejovsky's `PhysObj • Info` is `ComplexType PhysObj Info`.
Equivalent to `MeetType` but named for the polysemy domain. -/
abbrev ComplexType (Aspect₁ Aspect₂ : Type) := MeetType Aspect₁ Aspect₂

/-- Project to the first aspect (e.g., PhysObj from a book). -/
abbrev ComplexType.aspect₁ {A₁ A₂ : Type} (x : ComplexType A₁ A₂) : A₁ := x.1

/-- Project to the second aspect (e.g., Info from a book). -/
abbrev ComplexType.aspect₂ {A₁ A₂ : Type} (x : ComplexType A₁ A₂) : A₂ := x.2

/-- Complex types are subtypes of each aspect via meet projection. -/
example (A₁ A₂ : Type) : SubtypeOf (ComplexType A₁ A₂) A₁ := inferInstance
example (A₁ A₂ : Type) : SubtypeOf (ComplexType A₁ A₂) A₂ := inferInstance

/-! ## Copredication

Copredication applies predicates selecting different aspects to the
same complex-typed argument. The projections are the existing
`meetSubtypeLeft`/`meetSubtypeRight` instances. -/

/-- Apply a predicate selecting aspect₁ to a complex-typed argument. -/
def copred₁ {A₁ A₂ : Type} (P : A₁ → Prop) (x : ComplexType A₁ A₂) : Prop :=
  P x.aspect₁

/-- Apply a predicate selecting aspect₂ to a complex-typed argument. -/
def copred₂ {A₁ A₂ : Type} (P : A₂ → Prop) (x : ComplexType A₁ A₂) : Prop :=
  P x.aspect₂

/-- Copredication: conjunction of predicates on different aspects.
"The book is heavy and interesting" = heavy(book.phys) ∧ interesting(book.info). -/
def copredicate {A₁ A₂ : Type}
    (P : A₁ → Prop) (Q : A₂ → Prop) (x : ComplexType A₁ A₂) : Prop :=
  P x.aspect₁ ∧ Q x.aspect₂

/-- Copredication is well-typed: each predicate sees only its aspect. -/
theorem copredicate_factors {A₁ A₂ : Type}
    (P : A₁ → Prop) (Q : A₂ → Prop) (x : ComplexType A₁ A₂) :
    copredicate P Q x ↔ copred₁ P x ∧ copred₂ Q x :=
  Iff.rfl

/-! ## Individuation criteria

An individuation criterion determines when two complex-typed objects
count as "the same" for purposes of counting. Different criteria
yield different counts for the same collection.

Chatzikyriakidis et al. (2025) §3: "Three books were mastered and burned"
— under physical individuation, we count physical volumes;
under informational individuation, we count informational contents. -/

/-- An individuation criterion for a type: an equivalence relation
determining what counts as "one" object. -/
structure IndividuationCriterion (α : Type) where
  /-- When two objects count as the same individual -/
  sameIndividual : α → α → Prop
  /-- Reflexivity -/
  refl : ∀ x, sameIndividual x x
  /-- Symmetry -/
  symm : ∀ x y, sameIndividual x y → sameIndividual y x
  /-- Transitivity -/
  trans : ∀ x y z, sameIndividual x y → sameIndividual y z → sameIndividual x z

/-- Individuate a complex type by its first aspect.
Two book-objects are the same physical individual iff their PhysObj aspects match. -/
def individuateBy₁ {A₁ A₂ : Type} [DecidableEq A₁] :
    IndividuationCriterion (ComplexType A₁ A₂) where
  sameIndividual x y := x.aspect₁ = y.aspect₁
  refl _ := rfl
  symm _ _ h := h.symm
  trans _ _ _ h₁ h₂ := h₁.trans h₂

/-- Individuate a complex type by its second aspect. -/
def individuateBy₂ {A₁ A₂ : Type} [DecidableEq A₂] :
    IndividuationCriterion (ComplexType A₁ A₂) where
  sameIndividual x y := x.aspect₂ = y.aspect₂
  refl _ := rfl
  symm _ _ h := h.symm
  trans _ _ _ h₁ h₂ := h₁.trans h₂

/-- Count distinct individuals in a list under a criterion.
Uses a simple quadratic distinctness check (fine for finite linguistic examples). -/
def countDistinct {α : Type} (ic : IndividuationCriterion α)
    [∀ x y, Decidable (ic.sameIndividual x y)]
    (xs : List α) : Nat :=
  xs.foldl (λ (seen : List α) x =>
    if seen.any (λ s => decide (ic.sameIndividual s x)) then seen else x :: seen
  ) [] |>.length

/-- Different individuation criteria can yield different counts
for the same collection. This is the formal content of
Chatzikyriakidis et al. (2025) §3's counting puzzle. -/
theorem individuation_can_diverge :
    ∃ (A₁ A₂ : Type) (_ : DecidableEq A₁) (_ : DecidableEq A₂)
      (xs : List (ComplexType A₁ A₂))
      (_ : ∀ x y, Decidable ((@individuateBy₁ A₁ A₂ _).sameIndividual x y))
      (_ : ∀ x y, Decidable ((@individuateBy₂ A₁ A₂ _).sameIndividual x y)),
      countDistinct (@individuateBy₁ A₁ A₂ _) xs ≠
      countDistinct (@individuateBy₂ A₁ A₂ _) xs := by
  -- Two physical volumes, one informational content
  -- (e.g., two copies of the same novel)
  refine ⟨Bool, Bool, inferInstance, inferInstance,
    [(true, true), (false, true)],
    λ x y => inferInstanceAs (Decidable (x.1 = y.1)),
    λ x y => inferInstanceAs (Decidable (x.2 = y.2)), ?_⟩
  native_decide

end Semantics.TypeTheoretic
