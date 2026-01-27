/-
# Montague Semantics: Variable Binding and Assignment Functions

General infrastructure for interpreting expressions with free variables.
This is framework-neutral — pronouns and variable binding exist in every
syntactic theory, not just Minimalism.

## Key Concepts

Following Heim & Kratzer (1998) Ch. 5:

- **Assignment functions** map variable indices to entities
- **Modified assignments** g[n↦x] update a single index
- **Pronouns** are interpreted relative to an assignment

## Usage

This module provides the foundation for:
- Pronoun interpretation in any framework
- Lambda abstraction in compositional semantics
- Trace interpretation (in Minimalism/Semantics/Interface.lean)

## References

- Heim & Kratzer (1998) "Semantics in Generative Grammar", Ch. 5
-/

import Linglib.Theories.Montague.Basic

namespace Montague.Variables

open Montague

-- ============================================================================
-- Assignment Functions (H&K §5.1)
-- ============================================================================

/--
An assignment function maps variable indices to entities.

Following H&K §5.1: "An assignment is a (possibly partial) function from
the set of natural numbers to the domain of individuals D."

We use total functions for simplicity; partial assignments can be modeled
by using Option or a distinguished "undefined" entity.
-/
@[ext]
structure Assignment (m : Model) where
  /-- The function mapping indices to entities -/
  val : ℕ → m.Entity

instance {m : Model} : CoeFun (Assignment m) (λ _ => ℕ → m.Entity) where
  coe g := g.val

/--
Modified assignment: g[n↦x] is like g except it maps n to x.

H&K §5.1.4: "g[α/n] is just like g except that it assigns α to n"
-/
def Assignment.update {m : Model} (g : Assignment m) (n : ℕ) (x : m.Entity)
    : Assignment m :=
  ⟨fun i => if i = n then x else g i⟩

/-- Notation for assignment modification: g[n ↦ x] -/
notation:max g "[" n " ↦ " x "]" => Assignment.update g n x

-- ============================================================================
-- Assignment Update Lemmas
-- ============================================================================

/-- Modified assignment maps the modified index to the new value -/
@[simp]
theorem update_same {m : Model} (g : Assignment m) (n : ℕ) (x : m.Entity)
    : g[n ↦ x] n = x := by
  simp only [Assignment.update, ite_true]

/-- Modified assignment agrees with original on other indices -/
@[simp]
theorem update_other {m : Model} (g : Assignment m) (n i : ℕ) (x : m.Entity)
    (h : i ≠ n) : g[n ↦ x] i = g i := by
  simp only [Assignment.update, h, ite_false]

/-- Double modification at the same index: later modification wins -/
theorem update_update_same {m : Model} (g : Assignment m) (n : ℕ) (x y : m.Entity)
    : g[n ↦ x][n ↦ y] = g[n ↦ y] := by
  ext i
  simp only [Assignment.update]
  split_ifs <;> rfl

/-- Modification of different indices commutes -/
theorem update_update_comm {m : Model} (g : Assignment m) (n₁ n₂ : ℕ)
    (x₁ x₂ : m.Entity) (h : n₁ ≠ n₂)
    : g[n₁ ↦ x₁][n₂ ↦ x₂] = g[n₂ ↦ x₂][n₁ ↦ x₁] := by
  ext i
  simp only [Assignment.update]
  split_ifs with h1 h2 h3
  · exact absurd (h1.symm.trans h2) h.symm
  · rfl
  · rfl
  · rfl

/-- Updating with the same value is idempotent -/
theorem update_self {m : Model} (g : Assignment m) (n : ℕ)
    : g[n ↦ g n] = g := by
  ext i
  simp only [Assignment.update]
  split_ifs with h
  · simp only [h]
  · rfl

-- ============================================================================
-- Assignment-Relative Denotations
-- ============================================================================

/--
A denotation that depends on an assignment function.

This is needed for expressions containing free variables. The type
`DenotG m ty` represents meanings that vary with the assignment.
-/
def DenotG (m : Model) (ty : Ty) := Assignment m → m.interpTy ty

/--
Pronoun/variable denotation: ⟦xₙ⟧^g = g(n)

H&K §5.1.3: "For any assignment g: ⟦xₙ⟧^g = g(n)"

This is how indexed pronouns (he₁, she₂, etc.) are interpreted.
-/
def interpPronoun {m : Model} (n : ℕ) : DenotG m .e :=
  fun g => g n

/--
Lift a constant denotation to assignment-relative form.
Constants don't depend on the assignment.
-/
def constDenot {m : Model} {ty : Ty} (d : m.interpTy ty) : DenotG m ty :=
  fun _ => d

/-- Constants are assignment-independent -/
theorem constDenot_independent {m : Model} {ty : Ty} (d : m.interpTy ty)
    (g₁ g₂ : Assignment m) : constDenot d g₁ = constDenot d g₂ := rfl

-- ============================================================================
-- Composition with Assignments
-- ============================================================================

/--
Function application with assignments.

⟦α β⟧^g = ⟦α⟧^g(⟦β⟧^g)

Both function and argument are evaluated relative to the same assignment.
-/
def applyG {m : Model} {σ τ : Ty}
    (f : DenotG m (σ ⇒ τ)) (x : DenotG m σ) : DenotG m τ :=
  fun g => f g (x g)

/--
Lambda abstraction with variable binding.

⟦λn. α⟧^g = λx. ⟦α⟧^{g[n↦x]}

This creates a function that binds variable n. When applied to an
argument x, the body α is evaluated with n bound to x.

This is the key rule for interpreting structures where a binder
(quantifier, λ-operator, relative pronoun) binds a variable/trace.
-/
def lambdaAbsG {m : Model} {τ : Ty} (n : ℕ) (body : DenotG m τ)
    : DenotG m (.e ⇒ τ) :=
  fun g => fun x => body (g[n ↦ x])

-- ============================================================================
-- Theorems about Lambda Abstraction
-- ============================================================================

/-- Beta reduction: applying a lambda abstraction substitutes the argument -/
theorem lambdaAbsG_apply {m : Model} {τ : Ty} (n : ℕ) (body : DenotG m τ)
    (arg : m.Entity) (g : Assignment m)
    : (lambdaAbsG n body g) arg = body (g[n ↦ arg]) := rfl

/-- Alpha equivalence: bound variable names don't matter (when fresh) -/
theorem lambdaAbsG_alpha {m : Model} {τ : Ty} (n₁ n₂ : ℕ) (body : DenotG m τ)
    (g : Assignment m)
    (h_fresh : ∀ g' : Assignment m, ∀ x : m.Entity,
      body (g'[n₁ ↦ x]) = body (g'[n₂ ↦ x]))
    : lambdaAbsG n₁ body g = lambdaAbsG n₂ body g := by
  funext x
  exact h_fresh g x

-- ============================================================================
-- Examples with Toy Model
-- ============================================================================

section Examples

open ToyEntity ToyLexicon

/-- A default assignment for the toy model -/
def g₀ : Assignment toyModel := ⟨fun _ => .john⟩

/-- Variable x₀ denotes john under g₀ -/
example : interpPronoun 0 g₀ = ToyEntity.john := rfl

/-- Modified assignment g₀[0↦mary] maps 0 to mary -/
example : (g₀[0 ↦ ToyEntity.mary]) 0 = ToyEntity.mary := update_same g₀ 0 ToyEntity.mary

/-- Modified assignment preserves other indices -/
example : (g₀[0 ↦ ToyEntity.mary]) 1 = ToyEntity.john := by
  simp only [update_other g₀ 0 1 ToyEntity.mary (by decide)]
  rfl

/-- Lambda abstraction: λx₀. sleeps(x₀) -/
def sleeps_lambda : DenotG toyModel (.e ⇒ .t) :=
  lambdaAbsG 0 (applyG (constDenot sleeps_sem) (interpPronoun 0))

/-- The lambda abstraction evaluates to the sleeps predicate -/
theorem sleeps_lambda_eq : sleeps_lambda g₀ = sleeps_sem := by
  funext x
  simp only [sleeps_lambda, lambdaAbsG, applyG, constDenot, interpPronoun, update_same]

end Examples

-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This Module Provides

### Core Types
- `Assignment m`: assignment functions mapping indices to entities
- `DenotG m ty`: assignment-relative denotations

### Assignment Operations
- `Assignment.update` (notation: `g[n ↦ x]`): modify assignment at index n
- Update lemmas: `update_same`, `update_other`, `update_update_same`, `update_update_comm`

### Interpretation Functions
- `interpPronoun n`: interpret pronoun with index n
- `constDenot d`: lift constant to assignment-relative form
- `applyG f x`: function application preserving assignments
- `lambdaAbsG n body`: λ-abstraction binding variable n

### Key Insight

The assignment function machinery is framework-neutral. It provides the
semantic foundation for:
- Pronouns ("he₁ saw her₂")
- Bound variables in quantification ("every x ... x ...")
- Traces in movement (see Minimalism/Semantics/Interface.lean)

The specific syntactic mechanism that creates binding configurations
varies by theory, but the semantic interpretation is uniform.
-/

end Montague.Variables
