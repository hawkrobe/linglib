/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Computability.TransitionMonoid`.
-/
import Linglib.Core.Algebra.Group.End
import Linglib.Core.Algebra.Opposites
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Computability.DFA
import Mathlib.GroupTheory.Congruence.Basic
import Mathlib.GroupTheory.Congruence.Hom

/-!
# The transition monoid of a DFA

Each word induces a transformation of the states of a DFA, and reading one word after another
composes these transformations. The monoid they generate is the *transition monoid*, the basic
algebraic invariant of an automaton [pin-mfa].

## Main definitions

- `DFA.transitionHom`: the monoid homomorphism sending a word to the transformation it induces
- `DFA.transitionMonoid`: the transition monoid, the range of `DFA.transitionHom`
- `DFA.transitionMonoidEquiv`: the transition monoid as a quotient of `FreeMonoid α`

## Implementation notes

A word `w` acts on a state `s` by `s ↦ M.evalFrom s w`, and `evalFrom_of_append` makes this a
*right* action, written `q · u` in the literature. Since `Function.End` composes on the left, that
is an anti-homomorphism, so the target of `DFA.transitionHom` is the opposite monoid
`(Function.End σ)ᵐᵒᵖ`.

[pin-mfa] takes automata to be partial, so its transition monoid sits in the monoid of *partial*
transformations. `DFA` has a total `step`, so the transformations here are total and the target is
`Function.End σ`.
-/

universe u v

namespace DFA

variable {α : Type u} {σ : Type v} (M : DFA α σ)

/-- `M.transitionHom w` is the transformation of states induced by the word `w`. -/
def transitionHom : FreeMonoid α →* (Function.End σ)ᵐᵒᵖ where
  toFun w := MulOpposite.op fun s => M.evalFrom s w.toList
  map_one' := rfl
  map_mul' u v := MulOpposite.unop_injective <|
    funext fun s => M.evalFrom_of_append s u.toList v.toList

@[simp]
theorem unop_transitionHom_apply (w : FreeMonoid α) (s : σ) :
    (M.transitionHom w).unop s = M.evalFrom s w.toList := rfl

theorem transitionHom_eq_iff {u v : FreeMonoid α} : M.transitionHom u = M.transitionHom v ↔
    ∀ s : σ, M.evalFrom s u.toList = M.evalFrom s v.toList :=
  MulOpposite.unop_inj.symm.trans funext_iff

/-- `M.transitionMonoid` is the monoid of transformations of the states of `M` induced by words. -/
def transitionMonoid : Submonoid (Function.End σ)ᵐᵒᵖ := MonoidHom.mrange M.transitionHom

/-- `M.transitionMonoidEquiv` presents the transition monoid as a quotient of `FreeMonoid α`, by
the first isomorphism theorem. -/
noncomputable def transitionMonoidEquiv :
    (Con.ker M.transitionHom).Quotient ≃* M.transitionMonoid :=
  Con.quotientKerEquivRange _

instance instFiniteTransitionMonoid [Finite σ] : Finite M.transitionMonoid :=
  inferInstanceAs (Finite (MonoidHom.mrange M.transitionHom))

end DFA
