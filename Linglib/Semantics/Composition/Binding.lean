/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Composition.Assignment
import Linglib.Logic.CylindricAlgebra

/-!
# Binding

Two renderings of binding and their agreement. In assignment-based binding
([heim-kratzer-1998]) a binder at index `n` updates the assignment and the bound pronoun reads
it back (`hkBinding`); in the continuation rendering of [barker-shan-2014] binding is the
duplicator `W κ x = κ x x` applied to the body (`bsBinding`), and the two agree on reflexive
binding (`hk_bs_reflexive_equiv`). Assignment-indexed meanings are the reader monad `Reader E`,
whose `pure` and `<*>` are the constant and pointwise application; and binding a pronoun at
`κ` to a binder at `l` is the cylindric substitution of [henkin-monk-tarski-1971]
(`binding_eq_directSubst`), after which the two coordinates satisfy the diagonal
(`binding_establishes_diagonal`).

## References

* [heim-kratzer-1998]
* [barker-shan-2014]
* [henkin-monk-tarski-1971]
-/

namespace Semantics.Composition

open scoped Assignment
open CylindricAlgebra

variable {E A B : Type}

/-- The duplicator combinator `W κ x = κ x x`. -/
def W (κ : A → A → B) (x : A) : B := κ x x

/-- Assignment-based binding: the body is read at the assignment updated at `n`. -/
def hkBinding (n : ℕ) (body : E → Prop) (binder : E) (g : Assignment E) : Prop :=
  body (g[n ↦ binder] n)

/-- Continuation-based binding: the duplicator applied to the body. -/
def bsBinding (body : E → E → Prop) (binder : E) : Prop := W body binder

/-- The two renderings agree on reflexive binding. -/
theorem hk_bs_reflexive_equiv (n : ℕ) (body : E → E → Prop) (binder : E) (g : Assignment E) :
    body (g[n ↦ binder] n) (g[n ↦ binder] n) = bsBinding body binder := by
  simp only [bsBinding, W, Function.update_self]

/-- Assignment-indexed meanings: the reader monad. -/
abbrev Reader (E A : Type) := E → A

instance : Monad (Reader E) where
  pure a := λ _ => a
  bind m f := λ e => f (m e) e

/-- Binding the pronoun at `κ` to the binder at `l` is cylindric substitution. -/
theorem binding_eq_directSubst (κ l : ℕ) (φ : Assignment E → Prop) (g : Assignment E) :
    φ (g[κ ↦ g l]) = directSubst κ l φ g :=
  rfl

/-- After binding, the pronoun and its binder agree: the diagonal. -/
theorem binding_establishes_diagonal (κ l : ℕ) (g : Assignment E) (h : κ ≠ l) :
    diagonal κ l (g[κ ↦ g l]) := by
  simp [diagonal, Function.update_of_ne (Ne.symm h) (g l) g]

end Semantics.Composition
