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

The **transition monoid** of an automaton is the monoid of state-transformations induced by input
words. It is foundational algebraic automata theory (syntactic monoid, Schützenberger's theorem,
Eilenberg variety theory) and is currently **absent from mathlib**. This file prototypes it.

A word `w` acts on a state `s` of `M : DFA α σ` by `s ↦ M.evalFrom s w`. Because reading `u` then
`v` is `evalFrom_of_append`, this is a *right* action: `act (u * v) = act v ∘ act u`, i.e. an
*anti*-homomorphism into `Function.End σ`. Packaged as a genuine `MonoidHom`, the target is the
opposite monoid `(Function.End σ)ᵐᵒᵖ`.

* `DFA.transitionHom M : FreeMonoid α →* (Function.End σ)ᵐᵒᵖ` — the transition action.
* `DFA.transitionMonoid M : Submonoid (Function.End σ)ᵐᵒᵖ` — its range, the transition monoid.
* `DFA.transitionMonoidEquiv M` — the first iso theorem: `(Con.ker M.transitionHom).Quotient ≃*`
  the transition monoid.
* `Finite (Function.End σ)` / `Finite M.transitionMonoid` instances (these do **not**
  auto-synthesize from `Finite σ`, so we register them here once).

The syntactic monoid of a `Language α` is built as a consumer of this layer in
`Linglib.Core.Computability.SyntacticMonoid`.
-/

noncomputable section

universe u v

namespace DFA

variable {α : Type u} {σ : Type v} (M : DFA α σ)

/-- The transition action of words on the states of `M`, packaged as a monoid hom into the opposite
of `Function.End σ`. A word `w` sends the state `s` to `M.evalFrom s w`. The action is on the
*right* (reading `u` then `v`), hence the `ᵐᵒᵖ`. -/
def transitionHom : FreeMonoid α →* (Function.End σ)ᵐᵒᵖ where
  toFun w := MulOpposite.op fun s => M.evalFrom s w.toList
  map_one' := by
    refine congrArg MulOpposite.op (funext fun s => ?_)
    rw [FreeMonoid.toList_one, M.evalFrom_nil]
    rfl
  map_mul' u v := by
    apply MulOpposite.unop_injective
    funext s
    show M.evalFrom s (u * v).toList = M.evalFrom (M.evalFrom s u.toList) v.toList
    rw [FreeMonoid.toList_mul, M.evalFrom_of_append]

@[simp]
theorem unop_transitionHom_apply (w : FreeMonoid α) (s : σ) :
    (M.transitionHom w).unop s = M.evalFrom s w.toList := rfl

/-- Two words induce the same transition iff they are indistinguishable by `evalFrom` from every
state. -/
theorem transitionHom_eq_iff {u v : FreeMonoid α} :
    M.transitionHom u = M.transitionHom v ↔
      ∀ s : σ, M.evalFrom s u.toList = M.evalFrom s v.toList := by
  rw [← MulOpposite.unop_inj]
  exact funext_iff

/-- The transition monoid of `M`: the submonoid of `(Function.End σ)ᵐᵒᵖ` of all
state-transformations induced by words. -/
def transitionMonoid : Submonoid (Function.End σ)ᵐᵒᵖ := MonoidHom.mrange M.transitionHom

/-- The first isomorphism theorem: the transition monoid is the quotient of the free monoid by the
kernel of the transition action. -/
def transitionMonoidEquiv : (Con.ker M.transitionHom).Quotient ≃* M.transitionMonoid :=
  Con.quotientKerEquivRange _

/-- `Function.End σ` is finite when `σ` is. This does **not** synthesize automatically (the
definitional unfolding of `Function.End` is not reducible enough for the instance search), so we
register it here. -/
instance Function.End.instFinite [Finite σ] : Finite (Function.End σ) :=
  Finite.of_equiv (σ → σ) (Equiv.refl _)

/-- `(Function.End σ)ᵐᵒᵖ` is finite when `σ` is. Like `Function.End.instFinite`, this does not
synthesize automatically, so we register it for the transition-monoid finiteness instance. -/
instance instFiniteEndMop [Finite σ] : Finite (Function.End σ)ᵐᵒᵖ :=
  Finite.of_equiv (Function.End σ) MulOpposite.opEquiv

instance transitionMonoid.instFinite [Finite σ] : Finite (transitionMonoid M) :=
  inferInstanceAs (Finite (MonoidHom.mrange M.transitionHom))

end DFA

end
