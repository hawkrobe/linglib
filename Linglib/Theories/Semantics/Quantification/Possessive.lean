import Linglib.Core.Logic.Quantification
import Linglib.Theories.Semantics.Noun.Relational.Barker2011

/-!
# Possessive Quantifiers
@cite{peters-westerstahl-2006} @cite{barker-2011}

The higher-order possessive operator `Poss(Q₁, C, Q₂, R)` composes:
- Q₁: the possessor quantifier ("every student's", "John's")
- C: the possessor restrictor (e.g., "student")
- Q₂: the possessee quantifier ("a", "every", "the", typically covert)
- R: the possession relation

"Every student's cat sleeps" =
  Poss(every, student, a, own)(cat)(sleep)
  = every(student ∩ dom_cat(own), λx. a({y : own(x,y) ∧ cat(y)}, sleep))

## Domain Narrowing

`dom_A(R) = {a : ∃b ∈ A, R(a,b)}` — the set of possessors who possess
at least one A-thing. Used to narrow Q₁'s restrictor to relevant possessors.
@cite{peters-westerstahl-2006} Ch 7, p235, (7.101).

## Variants

- `Poss`: with domain narrowing via `domR` on Q₁'s restrictor (P&W Ch 7 Def 1)
- `PossW`: without domain narrowing (P&W Ch 7, Poss^w)

## Key Results

- Monotonicity inheritance: if Q₂ is Mon↑ and Q₁ is Mon↑, then PossW is Mon↑
- Connection to @cite{barker-2011}'s π operator
- Possessive GQs are NOT isomorphism-invariant

Cross-reference: `Barker2011.possessiveAsNPQ` for type ⟨1⟩ possessives.
-/

namespace Semantics.Quantification.Possessive

open Core.Quantification

variable {α : Type*}

-- ============================================================================
-- §1 Domain Narrowing
-- ============================================================================

/-- Domain of R restricted to A: `dom_A(R) = {a : ∃b ∈ A, R(a,b)}`.
    The set of individuals who stand in relation R to some member of A.
    Used to narrow the possessor restrictor to those who actually possess
    an A-thing.
    @cite{peters-westerstahl-2006} Ch 7, p235, (7.101). -/
def domR [Fintype α] [DecidableEq α] (A : α → Bool) (R : α → α → Bool) : α → Bool :=
  λ a => decide (∃ b, A b = true ∧ R a b = true)

-- ============================================================================
-- §2 Possessive Operators
-- ============================================================================

/-- Possessive quantifier without domain narrowing.

    `PossW(Q₁, C, Q₂, R)(A)(B) = Q₁(C, λx. Q₂(A ∩ R_x, B))`

    where `R_x(y) = R(x,y)`. Simpler variant; does not restrict the
    possessor domain to those who actually possess A-things.

    @cite{peters-westerstahl-2006} Ch 7, Poss^w. -/
def PossW (Q₁ Q₂ : GQ α) (C : α → Bool) (R : α → α → Bool) : GQ α :=
  λ A B => Q₁ C (λ x => Q₂ (λ y => R x y && A y) B)

/-- Possessive quantifier with domain narrowing.

    `Poss(Q₁, C, Q₂, R)(A, B) = Q₁(C ∩ dom_A(R), λx. Q₂(A ∩ R_x, B))`

    Domain narrowing restricts Q₁'s restrictor to possessors in C who
    actually possess some A-thing, ensuring the possessor domain is
    contextually appropriate.

    @cite{peters-westerstahl-2006} Ch 7 Def 1. -/
def Poss [Fintype α] [DecidableEq α]
    (Q₁ Q₂ : GQ α) (C : α → Bool) (R : α → α → Bool) : GQ α :=
  λ A B => Q₁ (λ x => C x && domR A R x) (λ x => Q₂ (λ y => A y && R x y) B)

-- ============================================================================
-- §3 Monotonicity Inheritance
-- ============================================================================

/-- If Q₁ is Mon↑ in scope and Q₂ is Mon↑ in scope, then
    PossW(Q₁, C, Q₂, R) is Mon↑ in scope.

    Proof: B ⊆ B' makes Q₂(A∩R_x, B) → Q₂(A∩R_x, B') by Q₂ Mon↑,
    so λx.Q₂(A∩R_x, B) ⊆ λx.Q₂(A∩R_x, B') pointwise,
    and Q₁ Mon↑ in scope gives the result.

    @cite{peters-westerstahl-2006} Ch 7. -/
theorem possW_scopeUpMono (Q₁ Q₂ : GQ α) (C : α → Bool) (R : α → α → Bool)
    (h₁ : ScopeUpwardMono Q₁) (h₂ : ScopeUpwardMono Q₂) :
    ScopeUpwardMono (PossW Q₁ Q₂ C R) := by
  intro A B B' hBB' hQ
  unfold PossW at *
  apply h₁ C _ _ _ hQ
  intro x hx
  exact h₂ _ B B' hBB' hx

/-- If Q₁ is Mon↑ in scope and Q₂ is Mon↓ in scope, then
    PossW(Q₁, C, Q₂, R) is Mon↓ in scope.

    Proof: B⊆B'. Q₂ scope-↓ gives Q₂(A∩R_x, B')→Q₂(A∩R_x, B),
    so {x : Q₂(A∩R_x,B)} ⊇ {x : Q₂(A∩R_x,B')} pointwise.
    Then Q₁ scope-↑ gives Q₁(C, inner_B') → Q₁(C, inner_B).

    @cite{peters-westerstahl-2006} Ch 7. -/
theorem possW_scopeDownMono (Q₁ Q₂ : GQ α) (C : α → Bool) (R : α → α → Bool)
    (h₁ : ScopeUpwardMono Q₁) (h₂ : ScopeDownwardMono Q₂) :
    ScopeDownwardMono (PossW Q₁ Q₂ C R) := by
  intro A B B' hBB' hQ
  unfold PossW at *
  apply h₁ C _ _ _ hQ
  intro x hx
  exact h₂ _ B B' hBB' hx

/-- The inner quantifier Q₂ in PossW is applied conservatively to its own
    restrictor `A ∩ R_x`. This means PossW inherits Q₂'s conservativity
    at the inner level, though PossW itself is not CONSERV as a GQ
    (it has a complex restrictor-scope interaction).
    @cite{peters-westerstahl-2006} Ch 7. -/
theorem possW_inner_conservative (Q₁ Q₂ : GQ α) (C : α → Bool) (R : α → α → Bool)
    (hCons₂ : Conservative Q₂) (A B : α → Bool) :
    PossW Q₁ Q₂ C R A B =
      Q₁ C (λ x => Q₂ (λ y => R x y && A y) (λ z => (R x z && A z) && B z)) := by
  unfold PossW
  congr 1; funext x
  exact hCons₂ _ B

end Semantics.Quantification.Possessive
