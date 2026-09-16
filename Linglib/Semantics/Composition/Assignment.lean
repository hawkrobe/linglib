import Linglib.Logic.Assignment

/-!
# Assignment-relative denotations

Denotations of expressions with free variables, relative to an assignment `g : ℕ → E` of
entities to indices ([heim-kratzer-1998]): a pronoun with index `n` denotes `g n`, a binder
at `n` abstracts over the value of `n` by updating `g`, and composition threads the assignment
through. An assignment-relative denotation in `α` is a function `Assignment E → α`, the Reader
applicative of [charlow-2018], whose laws hold definitionally. Situation pronouns are the same
construction at an assignment of indices.

## Main definitions

* `interpPronoun`, `constDenot`, `applyG`, `lambdaAbsG`, `denotGJoin`: the pronoun, the
  constant lift, application, abstraction, and join of assignment-relative denotations.
* `SitAssignment`, `interpSitPronoun`: situation assignments and situation pronouns.

## References

* [I. Heim, A. Kratzer, *Semantics in Generative Grammar* (1998)][heim-kratzer-1998]
* [S. Charlow, *A modular theory of pronouns and binding* (2018)][charlow-2018]
-/

namespace Semantics.Composition

open scoped Assignment

variable {E α β γ : Type*}

/-- Pronoun/variable denotation: ⟦xₙ⟧^g = g(n). -/
def interpPronoun (n : ℕ) : Assignment E → E := fun g ↦ g n

/-- Lift a constant denotation to assignment-relative form. -/
def constDenot (d : α) : Assignment E → α := fun _ ↦ d

/-- Function application with assignments. -/
def applyG (f : Assignment E → α → β) (x : Assignment E → α) : Assignment E → β :=
  fun g ↦ f g (x g)

/-- Lambda abstraction with variable binding. -/
def lambdaAbsG (n : ℕ) (body : Assignment E → α) : Assignment E → E → α :=
  fun g x ↦ body (g[n ↦ x])

theorem lambdaAbsG_apply (n : ℕ) (body : Assignment E → α) (arg : E) (g : Assignment E) :
    lambdaAbsG n body g arg = body (g[n ↦ arg]) := rfl

/-! ### Assignment-sensitive composition as an applicative functor

[charlow-2018] observes that `constDenot` (ρ) and `applyG` (⊛)
form an applicative functor for the Reader type constructor `G a := g → a`
([mcbride-paterson-2008]). The four applicative functor laws hold
definitionally. -/

section ApplicativeFunctor

/-- **Homomorphism**: `ρ f ⊛ ρ x = ρ (f x)`. -/
theorem constDenot_applyG (f : α → β) (x : α) :
    applyG (constDenot (E := E) f) (constDenot x) = constDenot (f x) := rfl

/-- **Identity**: `ρ id ⊛ v = v`. -/
theorem applyG_constDenot_id (v : Assignment E → α) : applyG (constDenot id) v = v := rfl

/-- **Interchange**: `u ⊛ ρ y = ρ (· y) ⊛ u`. -/
theorem applyG_constDenot_interchange (u : Assignment E → α → β) (y : α) :
    applyG u (constDenot y) = applyG (constDenot fun f : α → β ↦ f y) u := rfl

/-- **Composition**: `ρ comp ⊛ u ⊛ v ⊛ w = u ⊛ (v ⊛ w)`. -/
theorem applyG_composition
    (u : Assignment E → β → γ) (v : Assignment E → α → β) (w : Assignment E → α) :
    applyG (applyG (applyG (constDenot fun (f : β → γ) (g : α → β) x ↦ f (g x)) u) v) w =
      applyG u (applyG v w) := rfl

end ApplicativeFunctor

/-! ### Monadic join for higher-order variables -/

section MonadicJoin

/-- **Join** (μ): flatten a doubly assignment-dependent meaning.

[charlow-2018] §4.2: `μ m := λg. m g g`.

Enables higher-order variables: a pronoun anaphoric to an *intension*
(type `g → g → a`) is flattened to a standard denotation (type `g → a`)
by evaluating the retrieved intension at the current assignment. -/
def denotGJoin (ho : Assignment E → Assignment E → α) : Assignment E → α :=
  fun g ↦ ho g g

/-- **Left identity**: `μ (ρ d) = d`. -/
theorem denotGJoin_const (d : Assignment E → α) : denotGJoin (fun _ ↦ d) = d := rfl

/-- **Right identity**: `μ (λg. ρ(d g)) = d`. -/
theorem denotGJoin_inner_const (d : Assignment E → α) : denotGJoin (fun g _ ↦ d g) = d := rfl

/-- **Associativity**: `μ ∘ μ = μ ∘ fmap μ`. -/
theorem denotGJoin_assoc (hho : Assignment E → Assignment E → Assignment E → α) :
    denotGJoin (denotGJoin hho) = denotGJoin (fun g ↦ denotGJoin (hho g)) := rfl

end MonadicJoin

/-! ### Situation pronouns as the type-level dual of entity pronouns

Hanink (2018, 2021), Bondarenko (2022, 2023) and the broader post-Schwarz
literature on situational vs anaphoric definites argue that a situation
argument can be a *bound variable* (a "situation pronoun"), not just a free
parameter handed to an interpretation function.

Where entity pronouns are interpreted relative to `Assignment E := ℕ → E`,
situation pronouns are interpreted relative to `SitAssignment W := ℕ → W`.
Both reuse `Assignment` at different instantiations, so mathlib's
`Function.update` lemmas apply to both. -/

/-- Situation assignment: maps situation-pronoun indices to frame indices.
    Reuses `Assignment` at type `W`. -/
abbrev SitAssignment (W : Type*) := Assignment W

/-- Situation-pronoun denotation: ⟦sₙ⟧^{gs} = gs(n). Parallels `interpPronoun`. -/
def interpSitPronoun {W : Type*} (n : ℕ) : SitAssignment W → W :=
  fun gs ↦ gs n

end Semantics.Composition
