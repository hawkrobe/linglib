import Linglib.Theories.Semantics.TypeTheoretic.Core

/-!
# Copredication and Dot Types @cite{chatzikyriakidis-etal-2025}

Polysemous nouns like "book" denote objects with multiple aspects
(physical object AND informational content). Copredication applies
predicates selecting different aspects to the same noun phrase:
  "The book is heavy and interesting"
  — heavy selects PhysObj, interesting selects Info.

Values of a dot type are TTR meet types (A₁ × A₂). Copredication
works via projection (Prod.fst / Prod.snd = meetSubtypeLeft/Right).

The non-trivial contribution is *individuation*: when we count
"three books were mastered and burned," do we count physical
volumes or informational contents? A `DotType` bundles two aspect
types with a `Setoid` — an equivalence relation determining what
counts as "one."

We use `Setoid` directly (passed as a value, not via instance
resolution) since a single type may need multiple individuation
criteria (physical vs. informational individuation of books).

## References

- Chatzikyriakidis, S., Cooper, R., Gregoromichelaki, E. & Sutton, P. (2025).
  Types and the Structure of Meaning. Cambridge Elements in Semantics.
- Pustejovsky, J. (1995). The Generative Lexicon. MIT Press.
- Asher, N. (2011). Lexical Meaning in Context. CUP.
- Gotham, M. (2017). Composing Criteria of Individuation in Copredication.
  Journal of Semantics 34(2): 331–371.
- Cooper, R. (2023). From Perception to Communication. OUP.
-/

namespace Semantics.TypeTheoretic

/-! ## Copredication

Copredication applies predicates selecting different aspects to the
same pair-typed argument. The projections are the existing
`meetSubtypeLeft`/`meetSubtypeRight` instances on `MeetType = Prod`. -/

/-- Apply a predicate selecting the first aspect. -/
def copred₁ {A₁ A₂ : Type} (P : A₁ → Prop) (x : A₁ × A₂) : Prop := P x.1

/-- Apply a predicate selecting the second aspect. -/
def copred₂ {A₁ A₂ : Type} (P : A₂ → Prop) (x : A₁ × A₂) : Prop := P x.2

/-- Copredication: conjunction of predicates on different aspects.
"The book is heavy and interesting" = heavy(book.phys) ∧ interesting(book.info). -/
def copredicate {A₁ A₂ : Type}
    (P : A₁ → Prop) (Q : A₂ → Prop) (x : A₁ × A₂) : Prop :=
  P x.1 ∧ Q x.2

/-- Copredication factors into independent aspect predicates. -/
theorem copredicate_factors {A₁ A₂ : Type}
    (P : A₁ → Prop) (Q : A₂ → Prop) (x : A₁ × A₂) :
    copredicate P Q x ↔ copred₁ P x ∧ copred₂ Q x :=
  Iff.rfl

/-! ## Dot types

A dot type bundles two aspect types with a `Setoid` for individuation.
The individuation is part of the lexical specification — "book" =
⟨PhysObj, Info, individuate by volume⟩ — not just the raw product type.

Values of a dot type are pairs `A₁ × A₂` (= `MeetType A₁ A₂`). -/

/-- A dot type: a polysemous type with two aspects and an individuation
criterion (a `Setoid`). The individuation determines counting under
copredication. Chatzikyriakidis et al. (2025) §3. -/
structure DotType (A₁ A₂ : Type) where
  /-- How to individuate objects of this complex type -/
  individuation : Setoid (A₁ × A₂)

/-- Individuate by the first aspect.
"book" individuated physically: two copies of Hamlet count as two. -/
def DotType.byAspect₁ {A₁ A₂ : Type} [DecidableEq A₁] : DotType A₁ A₂ where
  individuation :=
    { r := λ x y => x.1 = y.1
      iseqv := ⟨λ _ => rfl, λ h => h.symm, λ h₁ h₂ => h₁.trans h₂⟩ }

/-- Individuate by the second aspect.
"book" individuated informationally: two copies of Hamlet count as one. -/
def DotType.byAspect₂ {A₁ A₂ : Type} [DecidableEq A₂] : DotType A₁ A₂ where
  individuation :=
    { r := λ x y => x.2 = y.2
      iseqv := ⟨λ _ => rfl, λ h => h.symm, λ h₁ h₂ => h₁.trans h₂⟩ }

/-- Count distinct individuals in a list under a `Setoid`.
Uses a simple quadratic distinctness check (fine for finite linguistic examples). -/
def countDistinct {α : Type} (s : Setoid α)
    [∀ x y, Decidable (s.r x y)]
    (xs : List α) : Nat :=
  xs.foldl (λ (seen : List α) x =>
    if seen.any (λ e => decide (s.r e x)) then seen else x :: seen
  ) [] |>.length

/-- Different individuation criteria can yield different counts
for the same collection. This is the formal content of
Chatzikyriakidis et al. (2025) §3's counting puzzle. -/
theorem individuation_can_diverge :
    ∃ (A₁ A₂ : Type) (_ : DecidableEq A₁) (_ : DecidableEq A₂)
      (xs : List (A₁ × A₂))
      (_ : ∀ x y, Decidable ((@DotType.byAspect₁ A₁ A₂ _).individuation.r x y))
      (_ : ∀ x y, Decidable ((@DotType.byAspect₂ A₁ A₂ _).individuation.r x y)),
      countDistinct (@DotType.byAspect₁ A₁ A₂ _).individuation xs ≠
      countDistinct (@DotType.byAspect₂ A₁ A₂ _).individuation xs := by
  refine ⟨Bool, Bool, inferInstance, inferInstance,
    [(true, true), (false, true)],
    λ (x : Bool × Bool) (y : Bool × Bool) => inferInstanceAs (Decidable (x.1 = y.1)),
    λ (x : Bool × Bool) (y : Bool × Bool) => inferInstanceAs (Decidable (x.2 = y.2)), ?_⟩
  native_decide

end Semantics.TypeTheoretic
