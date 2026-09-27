module

public import Linglib.Logic.Assignment

/-!
# Assignment-relative denotations

Denotations of expressions with free variables, relative to an assignment `g : ℕ → E` of
entities to indices ([heim-kratzer-1998]): a pronoun with index `n` denotes `g n`, a binder
at `n` abstracts over the value of `n` by updating `g`, and composition threads the assignment
through. An assignment-relative denotation in `α` is a function `Assignment E → α`, a
computation of Lean's reader monad `ReaderM (Assignment E)`, whose `pure`, `<*>` and `joinM` are
the lift, application and flattener of [charlow-2018]. Situation pronouns are the same
construction at an assignment of indices.

## Main definitions

* `interpPronoun`, `lambdaAbsG`: the pronoun and abstraction of assignment-relative
  denotations.
* `SitAssignment`, `interpSitPronoun`: situation assignments and situation pronouns.

## References

* [I. Heim, A. Kratzer, *Semantics in Generative Grammar* (1998)][heim-kratzer-1998]
* [S. Charlow, *A modular theory of pronouns and binding* (2018)][charlow-2018]
-/

@[expose] public section

namespace Semantics.Composition

open scoped Assignment

variable {E α : Type*}

/-- Pronoun/variable denotation: ⟦xₙ⟧^g = g(n). -/
def interpPronoun (n : ℕ) : Assignment E → E := fun g ↦ g n

/-- Lambda abstraction with variable binding. -/
def lambdaAbsG (n : ℕ) (body : Assignment E → α) : Assignment E → E → α :=
  fun g x ↦ body (g[n ↦ x])

theorem lambdaAbsG_apply (n : ℕ) (body : Assignment E → α) (arg : E) (g : Assignment E) :
    lambdaAbsG n body g arg = body (g[n ↦ arg]) := rfl

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
