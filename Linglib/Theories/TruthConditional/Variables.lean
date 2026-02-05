/-
# Variable Binding and Assignment Functions

Framework-neutral infrastructure for interpreting expressions with free variables.
Provides assignment functions, modified assignments, pronoun interpretation, and lambda abstraction.

## Main definitions

`Assignment`, `Assignment.update`, `DenotG`, `interpPronoun`, `applyG`, `lambdaAbsG`

## References

Heim & Kratzer (1998). Semantics in Generative Grammar, Ch. 5.
-/

import Linglib.Theories.TruthConditional.Basic

namespace TruthConditional.Variables

open TruthConditional

/-- Assignment function: maps variable indices to entities. -/
@[ext]
structure Assignment (m : Model) where
  /-- Function mapping indices to entities. -/
  val : ℕ → m.Entity

instance {m : Model} : CoeFun (Assignment m) (λ _ => ℕ → m.Entity) where
  coe g := g.val

/-- Modified assignment g[n↦x]. -/
def Assignment.update {m : Model} (g : Assignment m) (n : ℕ) (x : m.Entity)
    : Assignment m :=
  ⟨λ i => if i = n then x else g i⟩

notation:max g "[" n " ↦ " x "]" => Assignment.update g n x

@[simp]
theorem update_same {m : Model} (g : Assignment m) (n : ℕ) (x : m.Entity)
    : g[n ↦ x] n = x := by
  simp only [Assignment.update, ite_true]

@[simp]
theorem update_other {m : Model} (g : Assignment m) (n i : ℕ) (x : m.Entity)
    (h : i ≠ n) : g[n ↦ x] i = g i := by
  simp only [Assignment.update, h, ite_false]

theorem update_update_same {m : Model} (g : Assignment m) (n : ℕ) (x y : m.Entity)
    : g[n ↦ x][n ↦ y] = g[n ↦ y] := by
  ext i
  simp only [Assignment.update]
  split_ifs <;> rfl

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

theorem update_self {m : Model} (g : Assignment m) (n : ℕ)
    : g[n ↦ g n] = g := by
  ext i
  simp only [Assignment.update]
  split_ifs with h
  · simp only [h]
  · rfl

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

def g₀ : Assignment toyModel := ⟨λ _ => .john⟩

example : interpPronoun 0 g₀ = ToyEntity.john := rfl

example : (g₀[0 ↦ ToyEntity.mary]) 0 = ToyEntity.mary := update_same g₀ 0 ToyEntity.mary

example : (g₀[0 ↦ ToyEntity.mary]) 1 = ToyEntity.john := by
  simp only [update_other g₀ 0 1 ToyEntity.mary (by decide)]
  rfl

def sleeps_lambda : DenotG toyModel (.e ⇒ .t) :=
  lambdaAbsG 0 (applyG (constDenot sleeps_sem) (interpPronoun 0))

theorem sleeps_lambda_eq : sleeps_lambda g₀ = sleeps_sem := by
  funext x
  simp only [sleeps_lambda, lambdaAbsG, applyG, constDenot, interpPronoun, update_same]

end Examples

end TruthConditional.Variables
