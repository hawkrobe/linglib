/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Computability.DFA
import Mathlib.Computability.MyhillNerode
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Range
import Mathlib.GroupTheory.Congruence.Basic
import Mathlib.GroupTheory.Congruence.Hom

/-!
# The transition monoid of a DFA

The *transition monoid* of an automaton is the monoid of state-transformations induced by input
words — foundational algebraic automata theory (syntactic monoid, Schützenberger's theorem,
Eilenberg variety theory), currently absent from mathlib.

A word `w` acts on a state `s` of `M : DFA α σ` by `s ↦ M.evalFrom s w`. Reading `u` then `v`
(`evalFrom_of_append`) makes this a *right* action — an anti-homomorphism into `Function.End σ` — so
as a `MonoidHom` its target is the opposite monoid `(Function.End σ)ᵐᵒᵖ`.

* `DFA.transitionHom M : FreeMonoid α →* (Function.End σ)ᵐᵒᵖ` — the transition action.
* `DFA.transitionMonoid M : Submonoid (Function.End σ)ᵐᵒᵖ` — its range, the transition monoid.
* `DFA.transitionMonoidEquiv M` — the first iso theorem: `(Con.ker M.transitionHom).Quotient ≃*`
  the transition monoid.
* `Finite (Function.End σ)` / `Finite M.transitionMonoid` instances (these do not auto-synthesize
  from `Finite σ`, so we register them here once).
-/

noncomputable section

universe u v

namespace DFA

variable {α : Type u} {σ : Type v} (M : DFA α σ)

/-- The transition action of `M`: word `w` sends state `s` to `M.evalFrom s w`. -/
def transitionHom : FreeMonoid α →* (Function.End σ)ᵐᵒᵖ where
  toFun w := MulOpposite.op fun s => M.evalFrom s w.toList
  map_one' := rfl
  map_mul' u v := MulOpposite.unop_injective <| funext fun s => M.evalFrom_of_append s u.toList v.toList

@[simp]
theorem unop_transitionHom_apply (w : FreeMonoid α) (s : σ) :
    (M.transitionHom w).unop s = M.evalFrom s w.toList := rfl

/-- Two words induce the same transition iff `evalFrom` agrees from every state. -/
theorem transitionHom_eq_iff {u v : FreeMonoid α} : M.transitionHom u = M.transitionHom v ↔
    ∀ s : σ, M.evalFrom s u.toList = M.evalFrom s v.toList :=
  MulOpposite.unop_inj.symm.trans funext_iff

/-- The transition monoid of `M`: the range of its transition action. -/
def transitionMonoid : Submonoid (Function.End σ)ᵐᵒᵖ := MonoidHom.mrange M.transitionHom

/-- First isomorphism theorem: the transition monoid as a quotient of `FreeMonoid α`. -/
def transitionMonoidEquiv : (Con.ker M.transitionHom).Quotient ≃* M.transitionMonoid :=
  Con.quotientKerEquivRange _

/-- `Function.End σ` is finite when `σ` is (not found automatically through the `def`). -/
instance Function.End.instFinite [Finite σ] : Finite (Function.End σ) :=
  Finite.of_equiv (σ → σ) (Equiv.refl _)

/-- `(Function.End σ)ᵐᵒᵖ` is finite when `σ` is (likewise not found automatically). -/
instance instFiniteEndMop [Finite σ] : Finite (Function.End σ)ᵐᵒᵖ :=
  Finite.of_equiv (Function.End σ) MulOpposite.opEquiv

instance transitionMonoid.instFinite [Finite σ] : Finite (transitionMonoid M) :=
  inferInstanceAs (Finite (MonoidHom.mrange M.transitionHom))

end DFA

end
