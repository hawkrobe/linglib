import Linglib.Semantics.Intensional.Defs
import Linglib.Logic.Assignment

/-!
# Assignment-relative denotations

Denotations of expressions with free variables, relative to an assignment `g : ℕ → E` of
entities to indices ([heim-kratzer-1998]): a pronoun with index `n` denotes `g n`, a binder
at `n` abstracts over the value of `n` by updating `g`, and composition threads the assignment
through — the Reader applicative of [charlow-2018], whose laws hold definitionally. Situation
pronouns are the same construction at an assignment of indices, and `DenotGS` carries both.

## Main definitions

* `DenotG E W ty`: denotations relative to an entity assignment; `constDenot`, `applyG`,
  `lambdaAbsG`, `interpPronoun`, `denotGJoin`.
* `DenotGS E W ty`: denotations relative to an entity and a situation assignment;
  `interpSitPronoun`, `DenotGS.const`.
* `g[n ↦ x]`: [heim-kratzer-1998]'s assignment update, `Function.update g n x`.

## References

* [I. Heim, A. Kratzer, *Semantics in Generative Grammar* (1998)][heim-kratzer-1998]
* [S. Charlow, *A modular theory of pronouns and binding* (2018)][charlow-2018]
-/

namespace Intensional.Variables

open Intensional

/-- Heim-Kratzer assignment-modification notation: `g[n ↦ x]` is
`Function.update g n x`. The `Function.update_*` lemmas (`update_self`,
`update_of_ne`, `update_idem`, `update_comm`, `update_eq_self`) are the
update laws. -/
scoped notation:max g "[" n " ↦ " x "]" => Function.update g n x

/-- A denotation relative to an entity assignment. -/
abbrev DenotG (E W : Type) (ty : Ty) := Assignment E → Denot E W ty

/-- Pronoun/variable denotation: ⟦xₙ⟧^g = g(n). -/
def interpPronoun {E W : Type} (n : ℕ) : DenotG E W .e :=
  λ g => g n

/-- Lift constant denotation to assignment-relative form. -/
def constDenot {E W : Type} {ty : Ty} (d : Denot E W ty) : DenotG E W ty :=
  λ _ => d

/-- Function application with assignments. -/
def applyG {E W : Type} {σ τ : Ty}
    (f : DenotG E W (σ ⇒ τ)) (x : DenotG E W σ) : DenotG E W τ :=
  λ g => f g (x g)

/-- Lambda abstraction with variable binding. -/
def lambdaAbsG {E W : Type} {τ : Ty} (n : ℕ) (body : DenotG E W τ)
    : DenotG E W (.e ⇒ τ) :=
  λ g => λ x => body (g[n ↦ x])

theorem lambdaAbsG_apply {E W : Type} {τ : Ty} (n : ℕ) (body : DenotG E W τ)
    (arg : E) (g : Assignment E)
    : (lambdaAbsG n body g) arg = body (g[n ↦ arg]) := rfl

/-! ### Assignment-sensitive composition as an applicative functor

[charlow-2018] observes that `constDenot` (ρ) and `applyG` (⊛)
form an applicative functor for the Reader type constructor `G a := g → a`
([mcbride-paterson-2008]). The four applicative functor laws hold
definitionally. -/

section ApplicativeFunctor

variable {E W : Type} {σ τ υ : Ty}

/-- **Homomorphism**: `ρ f ⊛ ρ x = ρ (f x)`. -/
theorem constDenot_applyG (f : Denot E W (σ ⇒ τ)) (x : Denot E W σ) :
    applyG (constDenot f) (constDenot x) = constDenot (f x) := rfl

/-- **Identity**: `ρ id ⊛ v = v`. -/
theorem applyG_constDenot_id (v : DenotG E W σ) :
    applyG (constDenot id) v = v := rfl

/-- **Interchange**: `u ⊛ ρ y = ρ (· y) ⊛ u`. -/
theorem applyG_constDenot_interchange
    (u : DenotG E W (σ ⇒ τ)) (y : Denot E W σ) :
    applyG u (constDenot y) =
    applyG (constDenot (ty := (σ ⇒ τ) ⇒ τ) (fun f => f y)) u := rfl

/-- **Composition**: `ρ comp ⊛ u ⊛ v ⊛ w = u ⊛ (v ⊛ w)`. -/
theorem applyG_composition
    (u : DenotG E W (τ ⇒ υ)) (v : DenotG E W (σ ⇒ τ)) (w : DenotG E W σ) :
    applyG (applyG (applyG (constDenot
      (ty := (τ ⇒ υ) ⇒ (σ ⇒ τ) ⇒ σ ⇒ υ)
      (fun f g x => f (g x))) u) v) w =
    applyG u (applyG v w) := rfl

end ApplicativeFunctor

/-! ### Monadic join for higher-order variables -/

section MonadicJoin

variable {E W : Type}

/-- **Join** (μ): flatten a doubly assignment-dependent meaning.

[charlow-2018] §4.2: `μ m := λg. m g g`.

Enables higher-order variables: a pronoun anaphoric to an *intension*
(type `g → g → a`) is flattened to a standard denotation (type `g → a`)
by evaluating the retrieved intension at the current assignment. -/
def denotGJoin {A : Type} (ho : Assignment E → Assignment E → A) :
    Assignment E → A :=
  fun g => ho g g

/-- **Left identity**: `μ (ρ d) = d`. -/
theorem denotGJoin_const {A : Type} (d : Assignment E → A) :
    denotGJoin (fun _ => d) = d := rfl

/-- **Right identity**: `μ (λg. ρ(d g)) = d`. -/
theorem denotGJoin_inner_const {A : Type} (d : Assignment E → A) :
    denotGJoin (fun g _ => d g) = d := rfl

/-- **Associativity**: `μ ∘ μ = μ ∘ fmap μ`. -/
theorem denotGJoin_assoc {A : Type}
    (hho : Assignment E → Assignment E → Assignment E → A) :
    denotGJoin (denotGJoin hho) =
    denotGJoin (fun g => denotGJoin (hho g)) := rfl

end MonadicJoin

/-! ### Situation pronouns as the type-level dual of entity pronouns

Hanink (2018, 2021), Bondarenko (2022, 2023) and the broader post-Schwarz
literature on situational vs anaphoric definites argue that a situation
argument can be a *bound variable* (a "situation pronoun"), not just a free
parameter handed to an interpretation function.

Type-theoretically this is the dual of entity binding under `Ty.intens`:
where entity pronouns are interpreted relative to `Assignment E := ℕ → E`,
situation pronouns are interpreted relative to `SitAssignment W := ℕ → W`.
Both reuse `Assignment` at different instantiations, so mathlib's
`Function.update` lemmas apply to both. -/

/-- Situation assignment: maps situation-pronoun indices to frame indices.
    Reuses `Assignment` at type `W`. -/
abbrev SitAssignment (W : Type) := Assignment W

/-- Situation-pronoun denotation: ⟦sₙ⟧^{gs} = gs(n). Parallels `interpPronoun`. -/
def interpSitPronoun {W : Type} (n : Nat) : SitAssignment W → W :=
  fun gs => gs n

/-- A denotation relative to an entity assignment and a situation assignment, for
expressions containing both entity and situation pronouns (definites, attitude reports,
world-variable binding). -/
abbrev DenotGS (E W : Type) (ty : Ty) :=
  Assignment E → SitAssignment W → Denot E W ty

/-- A constant denotation as a bi-assignment-relative one. -/
def DenotGS.const {E W : Type} {ty : Ty} (d : Denot E W ty) : DenotGS E W ty :=
  fun _ _ => d

end Intensional.Variables
