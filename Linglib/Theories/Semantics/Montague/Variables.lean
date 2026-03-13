/-
# Variable Binding and Assignment Functions

Framework-neutral infrastructure for interpreting expressions with free variables.
Provides assignment functions, modified assignments, pronoun interpretation, and lambda abstraction.

## Main definitions

`Assignment`, `Assignment.update`, `DenotG`, `interpPronoun`, `applyG`, `lambdaAbsG`

## Unification with Core.Assignment

`Assignment m` is an abbreviation for `Core.Assignment m.Entity` (i.e., `Nat → m.Entity`).
This makes it the same type used across the library:
- Static binding (@cite{heim-kratzer-1998} Ch. 5): `Assignment m = Nat → m.Entity`
- Dynamic semantics (DRT, DPL, CDRT): `Core.Assignment E`
- Cylindric algebra (@cite{henkin-monk-tarski-1971}): `Core.Assignment D`

For heterogeneous assignments mapping indices to entities, concepts, and
world-time indices (@cite{krifka-2026}), instantiate `Core.Assignment (DRefVal W E)`.

-/

import Linglib.Theories.Semantics.Montague.Basic
import Linglib.Core.Assignment

namespace Semantics.Montague.Variables

open Semantics.Montague

/-- Assignment function: maps variable indices to entities.

Unified with `Core.Assignment` — this is `Nat → m.Entity`. All variable-binding
frameworks in the library (Montague, DRT, DPL, CDRT, cylindric algebra) share
this canonical type, differing only in the entity parameter. -/
abbrev Assignment (m : Model) := Core.Assignment m.Entity

namespace Assignment

/-- Modified assignment g[n↦x]. Delegates to `Core.Assignment.update`. -/
def update {m : Model} (g : Assignment m) (n : ℕ) (x : m.Entity)
    : Assignment m :=
  Core.Assignment.update g n x

end Assignment

scoped notation:max g "[" n " ↦ " x "]" => Assignment.update g n x

@[simp]
theorem update_same {m : Model} (g : Assignment m) (n : ℕ) (x : m.Entity)
    : g[n ↦ x] n = x :=
  Core.Assignment.update_at g n x

@[simp]
theorem update_other {m : Model} (g : Assignment m) (n i : ℕ) (x : m.Entity)
    (h : i ≠ n) : g[n ↦ x] i = g i :=
  Core.Assignment.update_ne g x h

theorem update_update_same {m : Model} (g : Assignment m) (n : ℕ) (x y : m.Entity)
    : g[n ↦ x][n ↦ y] = g[n ↦ y] :=
  Core.Assignment.update_overwrite g n x y

theorem update_update_comm {m : Model} (g : Assignment m) (n₁ n₂ : ℕ)
    (x₁ x₂ : m.Entity) (h : n₁ ≠ n₂)
    : g[n₁ ↦ x₁][n₂ ↦ x₂] = g[n₂ ↦ x₂][n₁ ↦ x₁] :=
  Core.Assignment.update_comm g x₁ x₂ h

theorem update_self {m : Model} (g : Assignment m) (n : ℕ)
    : g[n ↦ g n] = g :=
  Core.Assignment.update_self g n

/-- Denotation depending on assignment function. -/
def DenotG (m : Model) (ty : Ty) := Assignment m → m.interpTy ty

/-- Pronoun/variable denotation: ⟦xₙ⟧^g = g(n). -/
def interpPronoun {m : Model} (n : ℕ) : DenotG m .e :=
  λ g => g n

/-- Lift constant denotation to assignment-relative form. -/
def constDenot {m : Model} {ty : Ty} (d : m.interpTy ty) : DenotG m ty :=
  λ _ => d

theorem constDenot_independent {m : Model} {ty : Ty} (d : m.interpTy ty)
    (g₁ g₂ : Assignment m) : constDenot d g₁ = constDenot d g₂ := rfl

/-- Function application with assignments. -/
def applyG {m : Model} {σ τ : Ty}
    (f : DenotG m (σ ⇒ τ)) (x : DenotG m σ) : DenotG m τ :=
  λ g => f g (x g)

/-- Lambda abstraction with variable binding. -/
def lambdaAbsG {m : Model} {τ : Ty} (n : ℕ) (body : DenotG m τ)
    : DenotG m (.e ⇒ τ) :=
  λ g => λ x => body (g[n ↦ x])

theorem lambdaAbsG_apply {m : Model} {τ : Ty} (n : ℕ) (body : DenotG m τ)
    (arg : m.Entity) (g : Assignment m)
    : (lambdaAbsG n body g) arg = body (g[n ↦ arg]) := rfl

theorem lambdaAbsG_alpha {m : Model} {τ : Ty} (n₁ n₂ : ℕ) (body : DenotG m τ)
    (g : Assignment m)
    (h_fresh : ∀ g' : Assignment m, ∀ x : m.Entity,
      body (g'[n₁ ↦ x]) = body (g'[n₂ ↦ x]))
    : lambdaAbsG n₁ body g = lambdaAbsG n₂ body g := by
  funext x
  exact h_fresh g x

section Examples

open ToyEntity ToyLexicon

def g₀ : Assignment toyModel := λ _ => .john

example : interpPronoun 0 g₀ = ToyEntity.john := rfl
example : (g₀[0 ↦ ToyEntity.mary]) 0 = ToyEntity.mary := rfl
example : (g₀[0 ↦ ToyEntity.mary]) 1 = ToyEntity.john := rfl

def sleeps_lambda : DenotG toyModel (.e ⇒ .t) :=
  lambdaAbsG 0 (applyG (constDenot sleeps_sem) (interpPronoun 0))

theorem sleeps_lambda_eq : sleeps_lambda g₀ = sleeps_sem := by
  funext x
  simp only [sleeps_lambda, lambdaAbsG, applyG, constDenot, interpPronoun, update_same]

end Examples

-- ════════════════════════════════════════════════════════════════
-- § Cylindric Algebra Structure
-- ════════════════════════════════════════════════════════════════

/-! ### Assignments as a cylindric set algebra

Heim & Kratzer's assignment functions satisfy the same algebraic axioms
as DRT's dynamic assignments: predicates on assignments form a cylindric
set algebra (@cite{henkin-monk-tarski-1971}). The operations:

- **Existential closure** `∃n.φ(g) = ∃x.φ(g[n↦x])` = cylindrification
- **Identity** `g(n) = g(m)` = diagonal element
- **Lambda abstraction** `λn.φ = fun x => φ(g[n↦x])` = the integrand
  of cylindrification
- **Pronoun resolution** (binding n to m) = cylindric substitution

This section develops these correspondences purely within the Montague
`Assignment` type, without importing the dynamic semantics stack. -/

section CylindricStructure

variable {m : Model}

/-- Existential closure at variable `n`:
`(∃n.φ)(g) = ∃x. φ(g[n↦x])`.

This is cylindrification on Montague assignments
(@cite{henkin-monk-tarski-1971}, @cite{heim-kratzer-1998} Ch. 5). -/
def existsClosure (n : Nat) (φ : Assignment m → Prop) : Assignment m → Prop :=
  fun g => ∃ x : m.Entity, φ (g[n ↦ x])

/-- Diagonal element: assignments where variables n and k agree.
`Dnk = {g : g(n) = g(k)}`. -/
def diag (n k : Nat) : Assignment m → Prop :=
  fun g => g n = g k

/-- **C₁**: Existential closure of False is False. -/
theorem existsClosure_bot (n : Nat) :
    existsClosure n (fun _ : Assignment m => False) = fun _ => False := by
  ext g; simp [existsClosure]

/-- **C₂**: φ implies its existential closure. -/
theorem le_existsClosure (n : Nat) (φ : Assignment m → Prop) (g : Assignment m) :
    φ g → existsClosure n φ g :=
  fun h => ⟨g n, by rw [update_self]; exact h⟩

/-- **C₅**: `Dnn = ⊤` (reflexivity of equality). -/
theorem diag_refl (n : Nat) :
    @diag m n n = (fun _ => True) := by
  ext; simp [diag]

/-- Pronoun resolution: setting variable κ to read from variable l.

When pronoun κ is bound by a binder at index l, the semantic effect
is `φ(g[κ↦g(l)])`. This is the cylindric algebra's direct
substitution `σ^κ_l`. -/
def resolve (κ l : Nat) (φ : Assignment m → Prop) : Assignment m → Prop :=
  fun g => φ (g[κ ↦ g l])

/-- **Substitution = resolution.**

Algebraic substitution `cκ(Dκl · φ)` — cylindrification after
constraining κ to equal l via the diagonal — computes the same
predicate as direct pronoun resolution `φ(g[κ↦g(l)])`. -/
theorem resolve_eq_existsClosure_diag (κ l : Nat) (φ : Assignment m → Prop)
    (h : κ ≠ l) (g : Assignment m) :
    resolve κ l φ g ↔ existsClosure κ (fun g' => diag κ l g' ∧ φ g') g := by
  simp only [resolve, existsClosure, diag]; constructor
  · intro hφ
    exact ⟨g l, by simp [update_other g κ l (g l) (Ne.symm h)], hφ⟩
  · rintro ⟨x, hd, hφ⟩
    have : x = g l := by
      rw [update_same, update_other g κ l x (Ne.symm h)] at hd; exact hd
    subst this; exact hφ

/-- Lambda abstraction at n is the "integrand" of existential closure:
`∃n.φ = ∃x. (λn.φ)(g)(x)`. -/
theorem existsClosure_eq_exists_lambda (n : Nat) (body : DenotG m .t) (g : Assignment m) :
    existsClosure n (fun g' => body g' = true) g ↔
    ∃ x : m.Entity, lambdaAbsG n body g x = true := by
  simp [existsClosure, lambdaAbsG]

end CylindricStructure

end Semantics.Montague.Variables
