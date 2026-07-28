/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Computability.Variety.SemigroupLangs`.
-/
import Linglib.Core.Algebra.Semigroup.Pseudovariety
import Linglib.Core.Computability.SyntacticSemigroup

/-!
# The language-side operator of a semigroup pseudovariety

For a pseudovariety `V` of finite semigroups, `V.langs` collects the regular languages whose
syntactic *semigroup* lies in `V`. This is the `+`-variety half of the Eilenberg correspondence
([eilenberg-1976] Ch. VII), the counterpart of `Monoid.Pseudovariety.langs`.

The semigroup half is what the classes `D`, `K`, `LI` require: they are not monoid varieties, so
they have no image under the monoid-side operator.

## Main definitions

* `Semigroup.Pseudovariety.langs`: the languages whose syntactic semigroup lies in `V`.

## Main results

* `Semigroup.Pseudovariety.langs_compl`: closure under complement, from complement-invariance of
  the syntactic congruence.
-/

universe u

namespace Semigroup.Pseudovariety

open Language

variable (V : Pseudovariety.{u}) {α : Type u} {L : Language α}

/-- The languages over `α` whose (necessarily finite) syntactic semigroup lies in `V` — the
`+`-variety side of the Eilenberg correspondence. -/
def langs (L : Language α) : Prop := L.IsRegular ∧ V.mem L.syntacticSemigroup

theorem langs_def : V.langs L ↔ L.IsRegular ∧ V.mem L.syntacticSemigroup := Iff.rfl

/-- **Closure under complement** — immediate from complement-invariance of the syntactic
congruence (`Language.syntacticSemigroupCon_compl`). -/
theorem langs_compl (h : V.langs L) : V.langs Lᶜ := by
  refine ⟨h.1.compl, ?_⟩
  show V.mem (syntacticSemigroupCon Lᶜ).Quotient
  rw [syntacticSemigroupCon_compl]
  exact h.2

end Semigroup.Pseudovariety
