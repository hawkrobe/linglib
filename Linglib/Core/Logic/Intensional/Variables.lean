import Linglib.Core.Logic.Intensional.Frame
import Linglib.Core.Logic.Assignment
import Linglib.Core.CylindricAlgebra

/-!
# Variable Binding and Assignment Functions

[heim-kratzer-1998] [charlow-2018]

Framework-neutral infrastructure for interpreting expressions with free variables,
built on `Core.Logic.Intensional.Frame`.

## Main definitions

- `Assignment` (from `Core/Logic/Assignment.lean`) instantiated at
  `F.Entity` for entity pronouns and `F.Index` for situation pronouns;
  the `g[n ↦ x]` notation for `Function.update` is declared here
- `DenotG` — assignment-relative denotations
- `applyG`, `lambdaAbsG`, `constDenot` — composition with assignments
- Applicative functor laws ([charlow-2018])
- Cylindric algebra bridge ([henkin-monk-tarski-1971])
-/

namespace Core.Logic.Intensional.Variables

open Core.Logic.Intensional

/-- Heim-Kratzer assignment-modification notation: `g[n ↦ x]` is
`Function.update g n x`. The `Function.update_*` lemmas (`update_self`,
`update_of_ne`, `update_idem`, `update_comm`, `update_eq_self`) are the
update laws. -/
scoped notation:max g "[" n " ↦ " x "]" => Function.update g n x

/-- Denotation depending on assignment function. -/
def DenotG (F : Frame) (ty : Ty) := Assignment F.Entity → F.Denot ty

/-- Pronoun/variable denotation: ⟦xₙ⟧^g = g(n). -/
def interpPronoun {F : Frame} (n : ℕ) : DenotG F .e :=
  λ g => g n

/-- Lift constant denotation to assignment-relative form. -/
def constDenot {F : Frame} {ty : Ty} (d : F.Denot ty) : DenotG F ty :=
  λ _ => d

theorem constDenot_independent {F : Frame} {ty : Ty} (d : F.Denot ty)
    (g₁ g₂ : Assignment F.Entity) : constDenot d g₁ = constDenot d g₂ := rfl

/-- Function application with assignments. -/
def applyG {F : Frame} {σ τ : Ty}
    (f : DenotG F (σ ⇒ τ)) (x : DenotG F σ) : DenotG F τ :=
  λ g => f g (x g)

/-- Lambda abstraction with variable binding. -/
def lambdaAbsG {F : Frame} {τ : Ty} (n : ℕ) (body : DenotG F τ)
    : DenotG F (.e ⇒ τ) :=
  λ g => λ x => body (g[n ↦ x])

theorem lambdaAbsG_apply {F : Frame} {τ : Ty} (n : ℕ) (body : DenotG F τ)
    (arg : F.Entity) (g : Assignment F.Entity)
    : (lambdaAbsG n body g) arg = body (g[n ↦ arg]) := rfl

theorem lambdaAbsG_alpha {F : Frame} {τ : Ty} (n₁ n₂ : ℕ) (body : DenotG F τ)
    (g : Assignment F.Entity)
    (h_fresh : ∀ g' : Assignment F.Entity, ∀ x : F.Entity,
      body (g'[n₁ ↦ x]) = body (g'[n₂ ↦ x]))
    : lambdaAbsG n₁ body g = lambdaAbsG n₂ body g := by
  funext x
  exact h_fresh g x

-- ════════════════════════════════════════════════════════════════
-- § Applicative Functor Structure
-- ════════════════════════════════════════════════════════════════

/-! ### Assignment-sensitive composition as an applicative functor

[charlow-2018] observes that `constDenot` (ρ) and `applyG` (⊛)
form an applicative functor for the Reader type constructor `G a := g → a`
([mcbride-paterson-2008]). The four applicative functor laws hold
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

[charlow-2018] §4.2: `μ m := λg. m g g`.

Enables higher-order variables: a pronoun anaphoric to an *intension*
(type `g → g → a`) is flattened to a standard denotation (type `g → a`)
by evaluating the retrieved intension at the current assignment. -/
def denotGJoin {A : Type} (ho : Assignment F.Entity → Assignment F.Entity → A) :
    Assignment F.Entity → A :=
  fun g => ho g g

/-- **Left identity**: `μ (ρ d) = d`. -/
theorem denotGJoin_const {A : Type} (d : Assignment F.Entity → A) :
    denotGJoin (fun _ => d) = d := rfl

/-- **Right identity**: `μ (λg. ρ(d g)) = d`. -/
theorem denotGJoin_inner_const {A : Type} (d : Assignment F.Entity → A) :
    denotGJoin (fun g _ => d g) = d := rfl

/-- **Associativity**: `μ ∘ μ = μ ∘ fmap μ`. -/
theorem denotGJoin_assoc {A : Type}
    (hho : Assignment F.Entity → Assignment F.Entity → Assignment F.Entity → A) :
    denotGJoin (denotGJoin hho) =
    denotGJoin (fun g => denotGJoin (hho g)) := rfl

end MonadicJoin

-- ════════════════════════════════════════════════════════════════
-- § Cylindric Algebra Structure
-- ════════════════════════════════════════════════════════════════

/-! ### Assignments as a cylindric set algebra

[heim-kratzer-1998] assignment functions satisfy the same algebraic axioms
as DRT's dynamic assignments: predicates on assignments form a cylindric
set algebra ([henkin-monk-tarski-1971]). -/

section CylindricStructure

variable {F : Frame}

/-- Existential closure at variable `n`:
    `(∃n.φ)(g) = ∃x. φ(g[n↦x])`. -/
def existsClosure (n : Nat) (φ : Assignment F.Entity → Prop) : Assignment F.Entity → Prop :=
  fun g => ∃ x : F.Entity, φ (g[n ↦ x])

/-- Diagonal element: assignments where variables n and k agree. -/
def diag (n k : Nat) : Assignment F.Entity → Prop :=
  fun g => g n = g k

/-- **C₁**: Existential closure of False is False. -/
theorem existsClosure_bot (n : Nat) :
    existsClosure n (fun _ : Assignment F.Entity => False) = fun _ => False := by
  ext g; simp [existsClosure]

/-- **C₂**: φ implies its existential closure. -/
theorem le_existsClosure (n : Nat) (φ : Assignment F.Entity → Prop) (g : Assignment F.Entity) :
    φ g → existsClosure n φ g :=
  fun h => ⟨g n, by rw [Function.update_eq_self]; exact h⟩

/-- **C₅**: `Dnn = ⊤` (reflexivity of equality). -/
theorem diag_refl (n : Nat) :
    @diag F n n = (fun _ => True) := by
  ext; simp [diag]

/-- Pronoun resolution: setting variable κ to read from variable l. -/
def resolve (κ l : Nat) (φ : Assignment F.Entity → Prop) : Assignment F.Entity → Prop :=
  fun g => φ (g[κ ↦ g l])

/-- **Substitution = resolution.** -/
theorem resolve_eq_existsClosure_diag (κ l : Nat) (φ : Assignment F.Entity → Prop)
    (h : κ ≠ l) (g : Assignment F.Entity) :
    resolve κ l φ g ↔ existsClosure κ (fun g' => diag κ l g' ∧ φ g') g := by
  simp only [resolve, existsClosure, diag]; constructor
  · intro hφ
    exact ⟨g l, by simp [Function.update_of_ne (Ne.symm h) (g l) g], hφ⟩
  · rintro ⟨x, hd, hφ⟩
    have : x = g l := by
      rw [Function.update_self, Function.update_of_ne (Ne.symm h) x g] at hd; exact hd
    subst this; exact hφ

/-- Lambda abstraction at n is the "integrand" of existential closure. -/
theorem existsClosure_eq_exists_lambda (n : Nat) (body : DenotG F .t) (g : Assignment F.Entity) :
    existsClosure n (fun g' => body g') g ↔
    ∃ x : F.Entity, lambdaAbsG n body g x := by
  simp [existsClosure, lambdaAbsG]

-- Bridge to Core.CylindricAlgebra

open Core.CylindricAlgebra

theorem existsClosure_eq_cylindrify (n : Nat) (φ : Assignment F.Entity → Prop) :
    existsClosure n φ = cylindrify n φ := rfl

theorem diag_eq_diagonal (n k : Nat) :
    @diag F n k = @diagonal F.Entity n k := rfl

theorem resolve_eq_directSubst (κ l : Nat) (φ : Assignment F.Entity → Prop) :
    resolve κ l φ = @directSubst F.Entity κ l φ := rfl

end CylindricStructure

-- ════════════════════════════════════════════════════════════════
-- § Situation Assignment (Hanink-style situation-pronoun binding)
-- ════════════════════════════════════════════════════════════════

/-! ### Situation pronouns as the type-level dual of entity pronouns

Hanink (2018, 2021), Bondarenko (2022, 2023) and the broader post-Schwarz
literature on situational vs anaphoric definites argue that a situation
argument can be a *bound variable* (a "situation pronoun"), not just a free
parameter handed to an interpretation function.

Type-theoretically this is the dual of entity binding under `Ty.intens`:
where entity pronouns are interpreted relative to `Assignment F.Entity := ℕ → F.Entity`,
situation pronouns are interpreted relative to `SitAssignment F := ℕ → F.Index`.
Both reuse `Core.Assignment` at different instantiations, so mathlib's
`Function.update` lemmas apply to both. -/

/-- Situation assignment: maps situation-pronoun indices to frame indices.
    Reuses `Assignment` at type `F.Index`. -/
abbrev SitAssignment (F : Frame) := Assignment F.Index

/-- Situation-pronoun denotation: ⟦sₙ⟧^{gs} = gs(n). Parallels `interpPronoun`. -/
def interpSitPronoun {F : Frame} (n : Nat) : SitAssignment F → F.Index :=
  fun gs => gs n

/-- Bi-assignment-relative denotation: depends on both an entity assignment
    and a situation assignment. Used by any module that interprets expressions
    containing both entity pronouns and situation pronouns (definites,
    attitude reports, modal scope, world-variable binding). -/
def DenotGS (F : Frame) (ty : Ty) :=
  Assignment F.Entity → SitAssignment F → F.Denot ty

/-- Lift a pure entity-assignment-relative denotation to bi-assignment form
    (ignores the situation assignment). -/
def DenotGS.ofDenotG {F : Frame} {ty : Ty} (d : DenotG F ty) : DenotGS F ty :=
  fun g _ => d g

/-- Lift a constant denotation to bi-assignment form (ignores both
    assignments). -/
def DenotGS.const {F : Frame} {ty : Ty} (d : F.Denot ty) : DenotGS F ty :=
  fun _ _ => d

/-- Bi-assignment lift of a pure constant is the same as DenotG-lift of a
    constant — the two `const` paths agree. -/
theorem DenotGS.ofDenotG_const {F : Frame} {ty : Ty} (d : F.Denot ty) :
    DenotGS.ofDenotG (constDenot d) = DenotGS.const d := rfl

end Core.Logic.Intensional.Variables
