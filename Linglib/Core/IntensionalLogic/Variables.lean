import Linglib.Core.IntensionalLogic.Frame
import Linglib.Core.Assignment
import Linglib.Core.CylindricAlgebra

/-!
# Variable Binding and Assignment Functions

@cite{heim-kratzer-1998} @cite{charlow-2018}

Framework-neutral infrastructure for interpreting expressions with free variables,
built on `Core.IntensionalLogic.Frame`.

## Main definitions

- `Assignment` — maps variable indices to entities
- `DenotG` — assignment-relative denotations
- `applyG`, `lambdaAbsG`, `constDenot` — composition with assignments
- Applicative functor laws (@cite{charlow-2018})
- Cylindric algebra bridge (@cite{henkin-monk-tarski-1971})
-/

namespace Core.IntensionalLogic.Variables

open Core.IntensionalLogic

/-- Assignment function: maps variable indices to entities.

Unified with `Core.Assignment` — this is `Nat → F.Entity`. All variable-binding
frameworks in the library (Montague, DRT, DPL, CDRT, cylindric algebra) share
this canonical type, differing only in the entity parameter. -/
abbrev Assignment (F : Frame) := Core.Assignment F.Entity

namespace Assignment

/-- Modified assignment g[n↦x]. Delegates to `Core.Assignment.update`. -/
def update {F : Frame} (g : Assignment F) (n : ℕ) (x : F.Entity)
    : Assignment F :=
  Core.Assignment.update g n x

end Assignment

scoped notation:max g "[" n " ↦ " x "]" => Assignment.update g n x

@[simp]
theorem update_same {F : Frame} (g : Assignment F) (n : ℕ) (x : F.Entity)
    : g[n ↦ x] n = x :=
  Core.Assignment.update_at g n x

@[simp]
theorem update_other {F : Frame} (g : Assignment F) (n i : ℕ) (x : F.Entity)
    (h : i ≠ n) : g[n ↦ x] i = g i :=
  Core.Assignment.update_ne g x h

theorem update_update_same {F : Frame} (g : Assignment F) (n : ℕ) (x y : F.Entity)
    : g[n ↦ x][n ↦ y] = g[n ↦ y] :=
  Core.Assignment.update_overwrite g n x y

theorem update_update_comm {F : Frame} (g : Assignment F) (n₁ n₂ : ℕ)
    (x₁ x₂ : F.Entity) (h : n₁ ≠ n₂)
    : g[n₁ ↦ x₁][n₂ ↦ x₂] = g[n₂ ↦ x₂][n₁ ↦ x₁] :=
  Core.Assignment.update_comm g x₁ x₂ h

theorem update_self {F : Frame} (g : Assignment F) (n : ℕ)
    : g[n ↦ g n] = g :=
  Core.Assignment.update_self g n

/-- Denotation depending on assignment function. -/
def DenotG (F : Frame) (ty : Ty) := Assignment F → F.Denot ty

/-- Pronoun/variable denotation: ⟦xₙ⟧^g = g(n). -/
def interpPronoun {F : Frame} (n : ℕ) : DenotG F .e :=
  λ g => g n

/-- Lift constant denotation to assignment-relative form. -/
def constDenot {F : Frame} {ty : Ty} (d : F.Denot ty) : DenotG F ty :=
  λ _ => d

theorem constDenot_independent {F : Frame} {ty : Ty} (d : F.Denot ty)
    (g₁ g₂ : Assignment F) : constDenot d g₁ = constDenot d g₂ := rfl

/-- Function application with assignments. -/
def applyG {F : Frame} {σ τ : Ty}
    (f : DenotG F (σ ⇒ τ)) (x : DenotG F σ) : DenotG F τ :=
  λ g => f g (x g)

/-- Lambda abstraction with variable binding. -/
def lambdaAbsG {F : Frame} {τ : Ty} (n : ℕ) (body : DenotG F τ)
    : DenotG F (.e ⇒ τ) :=
  λ g => λ x => body (g[n ↦ x])

theorem lambdaAbsG_apply {F : Frame} {τ : Ty} (n : ℕ) (body : DenotG F τ)
    (arg : F.Entity) (g : Assignment F)
    : (lambdaAbsG n body g) arg = body (g[n ↦ arg]) := rfl

theorem lambdaAbsG_alpha {F : Frame} {τ : Ty} (n₁ n₂ : ℕ) (body : DenotG F τ)
    (g : Assignment F)
    (h_fresh : ∀ g' : Assignment F, ∀ x : F.Entity,
      body (g'[n₁ ↦ x]) = body (g'[n₂ ↦ x]))
    : lambdaAbsG n₁ body g = lambdaAbsG n₂ body g := by
  funext x
  exact h_fresh g x

-- ════════════════════════════════════════════════════════════════
-- § Applicative Functor Structure
-- ════════════════════════════════════════════════════════════════

/-! ### Assignment-sensitive composition as an applicative functor

@cite{charlow-2018} observes that `constDenot` (ρ) and `applyG` (⊛)
form an applicative functor for the Reader type constructor `G a := g → a`
(@cite{mcbride-paterson-2008}). The four applicative functor laws hold
definitionally. -/

section ApplicativeFunctor

variable {F : Frame} {σ τ υ : Ty}

/-- **Homomorphism**: `ρ f ⊛ ρ x = ρ (f x)`. -/
theorem constDenot_applyG (f : F.Denot (σ ⇒ τ)) (x : F.Denot σ) :
    applyG (constDenot f) (constDenot x) = constDenot (f x) := rfl

/-- **Identity**: `ρ id ⊛ v = v`. -/
theorem applyG_constDenot_id (v : DenotG F σ) :
    applyG (constDenot id) v = v := rfl

/-- **Interchange**: `u ⊛ ρ y = ρ (· y) ⊛ u`. -/
theorem applyG_constDenot_interchange
    (u : DenotG F (σ ⇒ τ)) (y : F.Denot σ) :
    applyG u (constDenot y) =
    applyG (constDenot (ty := (σ ⇒ τ) ⇒ τ) (fun f => f y)) u := rfl

/-- **Composition**: `ρ comp ⊛ u ⊛ v ⊛ w = u ⊛ (v ⊛ w)`. -/
theorem applyG_composition
    (u : DenotG F (τ ⇒ υ)) (v : DenotG F (σ ⇒ τ)) (w : DenotG F σ) :
    applyG (applyG (applyG (constDenot
      (ty := (τ ⇒ υ) ⇒ (σ ⇒ τ) ⇒ σ ⇒ υ)
      (fun f g x => f (g x))) u) v) w =
    applyG u (applyG v w) := rfl

end ApplicativeFunctor

-- ════════════════════════════════════════════════════════════════
-- § Monadic Join for Higher-Order Variables
-- ════════════════════════════════════════════════════════════════

section MonadicJoin

variable {F : Frame}

/-- **Join** (μ): flatten a doubly assignment-dependent meaning.

@cite{charlow-2018} §4.2: `μ m := λg. m g g`.

Enables higher-order variables: a pronoun anaphoric to an *intension*
(type `g → g → a`) is flattened to a standard denotation (type `g → a`)
by evaluating the retrieved intension at the current assignment. -/
def denotGJoin {A : Type} (ho : Assignment F → Assignment F → A) :
    Assignment F → A :=
  fun g => ho g g

/-- **Left identity**: `μ (ρ d) = d`. -/
theorem denotGJoin_const {A : Type} (d : Assignment F → A) :
    denotGJoin (fun _ => d) = d := rfl

/-- **Right identity**: `μ (λg. ρ(d g)) = d`. -/
theorem denotGJoin_inner_const {A : Type} (d : Assignment F → A) :
    denotGJoin (fun g _ => d g) = d := rfl

/-- **Associativity**: `μ ∘ μ = μ ∘ fmap μ`. -/
theorem denotGJoin_assoc {A : Type}
    (hho : Assignment F → Assignment F → Assignment F → A) :
    denotGJoin (denotGJoin hho) =
    denotGJoin (fun g => denotGJoin (hho g)) := rfl

end MonadicJoin

-- ════════════════════════════════════════════════════════════════
-- § Cylindric Algebra Structure
-- ════════════════════════════════════════════════════════════════

/-! ### Assignments as a cylindric set algebra

@cite{heim-kratzer-1998} assignment functions satisfy the same algebraic axioms
as DRT's dynamic assignments: predicates on assignments form a cylindric
set algebra (@cite{henkin-monk-tarski-1971}). -/

section CylindricStructure

variable {F : Frame}

/-- Existential closure at variable `n`:
    `(∃n.φ)(g) = ∃x. φ(g[n↦x])`. -/
def existsClosure (n : Nat) (φ : Assignment F → Prop) : Assignment F → Prop :=
  fun g => ∃ x : F.Entity, φ (g[n ↦ x])

/-- Diagonal element: assignments where variables n and k agree. -/
def diag (n k : Nat) : Assignment F → Prop :=
  fun g => g n = g k

/-- **C₁**: Existential closure of False is False. -/
theorem existsClosure_bot (n : Nat) :
    existsClosure n (fun _ : Assignment F => False) = fun _ => False := by
  ext g; simp [existsClosure]

/-- **C₂**: φ implies its existential closure. -/
theorem le_existsClosure (n : Nat) (φ : Assignment F → Prop) (g : Assignment F) :
    φ g → existsClosure n φ g :=
  fun h => ⟨g n, by rw [update_self]; exact h⟩

/-- **C₅**: `Dnn = ⊤` (reflexivity of equality). -/
theorem diag_refl (n : Nat) :
    @diag F n n = (fun _ => True) := by
  ext; simp [diag]

/-- Pronoun resolution: setting variable κ to read from variable l. -/
def resolve (κ l : Nat) (φ : Assignment F → Prop) : Assignment F → Prop :=
  fun g => φ (g[κ ↦ g l])

/-- **Substitution = resolution.** -/
theorem resolve_eq_existsClosure_diag (κ l : Nat) (φ : Assignment F → Prop)
    (h : κ ≠ l) (g : Assignment F) :
    resolve κ l φ g ↔ existsClosure κ (fun g' => diag κ l g' ∧ φ g') g := by
  simp only [resolve, existsClosure, diag]; constructor
  · intro hφ
    exact ⟨g l, by simp [update_other g κ l (g l) (Ne.symm h)], hφ⟩
  · rintro ⟨x, hd, hφ⟩
    have : x = g l := by
      rw [update_same, update_other g κ l x (Ne.symm h)] at hd; exact hd
    subst this; exact hφ

/-- Lambda abstraction at n is the "integrand" of existential closure. -/
theorem existsClosure_eq_exists_lambda (n : Nat) (body : DenotG F .t) (g : Assignment F) :
    existsClosure n (fun g' => body g') g ↔
    ∃ x : F.Entity, lambdaAbsG n body g x := by
  simp [existsClosure, lambdaAbsG]

-- Bridge to Core.CylindricAlgebra

open Core.CylindricAlgebra

theorem existsClosure_eq_cylindrify (n : Nat) (φ : Assignment F → Prop) :
    existsClosure n φ = cylindrify n φ := rfl

theorem diag_eq_diagonal (n k : Nat) :
    @diag F n k = @diagonal F.Entity n k := rfl

theorem resolve_eq_directSubst (κ l : Nat) (φ : Assignment F → Prop) :
    resolve κ l φ = @directSubst F.Entity κ l φ := rfl

end CylindricStructure

end Core.IntensionalLogic.Variables
