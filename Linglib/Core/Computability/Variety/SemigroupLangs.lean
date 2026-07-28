/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Computability.Variety.SemigroupLangs`.
-/
import Linglib.Core.Algebra.Semigroup.Pseudovariety
import Linglib.Core.Computability.SyntacticSemigroup
import Linglib.Core.Computability.Variety.Langs
import Linglib.Core.GroupTheory.Congruence.Hom

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

/-- **Closure under complement** — immediate from complement-invariance of the syntactic
congruence (`Language.syntacticSemigroupCon_compl`). -/
theorem langs_compl (h : V.langs L) : V.langs Lᶜ := by
  refine ⟨h.1.compl, ?_⟩
  show V.mem (syntacticSemigroupCon Lᶜ).Quotient
  rw [syntacticSemigroupCon_compl]
  exact h.2

/-! ### Closure under quotients

Eilenberg's axiom VII.3.3, on the `+` side. The argument is the monoid one: a quotient's syntactic
congruence is coarser, so its syntactic semigroup is a quotient of the original's. -/

theorem _root_.Language.syntacticSemigroupCon_le_leftQuotient (L : Language α) (u : List α) :
    L.syntacticSemigroupCon ≤ (L.leftQuotient u).syntacticSemigroupCon := fun {p q} h x y => by
  have := h (u ++ x) y
  simpa [Language.mem_leftQuotient, List.append_assoc] using this

theorem _root_.Language.syntacticSemigroupCon_le_rightQuotient (L : Language α) (u : List α) :
    L.syntacticSemigroupCon ≤ (L.rightQuotient u).syntacticSemigroupCon := fun {p q} h x y => by
  have := h x (y ++ u)
  simpa [Language.mem_rightQuotient, List.append_assoc] using this

variable {V}

/-- A coarser syntactic congruence keeps the language in `V.langs`. -/
private theorem langs_of_syntacticSemigroupCon_le {M : Language α} (h : V.langs L)
    (hle : L.syntacticSemigroupCon ≤ M.syntacticSemigroupCon) : V.langs M := by
  haveI : Finite L.syntacticMonoid := finite_syntacticMonoid h.1
  haveI : Finite L.syntacticSemigroupCon.Quotient :=
    inferInstanceAs (Finite L.syntacticSemigroup)
  have hsurj : Function.Surjective
      (Con.mapMulHom L.syntacticSemigroupCon M.syntacticSemigroupCon hle) :=
    Con.mapMulHom_surjective _ _ hle
  haveI : Finite M.syntacticSemigroup := .of_surjective _ hsurj
  haveI : Finite M.syntacticSemigroupCon.Quotient :=
    inferInstanceAs (Finite M.syntacticSemigroup)
  exact ⟨M.isRegular_of_finite_syntacticSemigroup ‹Finite M.syntacticSemigroup›,
    V.quot hsurj h.2⟩

/-- **Closure under left quotient** — Eilenberg's axiom VII.3.3. -/
theorem langs_leftQuotient (h : V.langs L) (u : List α) : V.langs (L.leftQuotient u) :=
  langs_of_syntacticSemigroupCon_le h (L.syntacticSemigroupCon_le_leftQuotient u)

/-- **Closure under right quotient** — Eilenberg's axiom VII.3.3. -/
theorem langs_rightQuotient (h : V.langs L) (u : List α) : V.langs (L.rightQuotient u) :=
  langs_of_syntacticSemigroupCon_le h (L.syntacticSemigroupCon_le_rightQuotient u)
/-- **Closure under intersection** — the syntactic semigroup of `L ⊓ M` is a quotient of a
subsemigroup of `L.syntacticSemigroup × M.syntacticSemigroup`, which is in `V` by
`prod`/`sub`/`quot`. -/
theorem langs_inf {M : Language α} (hL : V.langs L) (hM : V.langs M) : V.langs (L ⊓ M) := by
  refine ⟨hL.1.inf hM.1, ?_⟩
  haveI : Finite L.syntacticMonoid := finite_syntacticMonoid hL.1
  haveI : Finite M.syntacticMonoid := finite_syntacticMonoid hM.1
  haveI : Finite (L ⊓ M).syntacticMonoid := finite_syntacticMonoid (hL.1.inf hM.1)
  set φ := L.toSyntacticSemigroup.prod M.toSyntacticSemigroup with hφ
  haveI : Finite (Con.ker φ).Quotient := .of_injective _ (Con.kerLiftMulHom_injective φ)
  have hker : V.mem (Con.ker φ).Quotient :=
    V.sub (Con.kerLiftMulHom_injective φ) (V.prod hL.2 hM.2)
  have hle : Con.ker φ ≤ (L ⊓ M).syntacticSemigroupCon := by
    rw [hφ, ker_prod_toSyntacticSemigroup]
    exact inf_syntacticSemigroupCon_le_syntacticSemigroupCon_inf L M
  haveI : Finite (L ⊓ M).syntacticSemigroupCon.Quotient :=
    inferInstanceAs (Finite (L ⊓ M).syntacticSemigroup)
  exact V.quot (Con.mapMulHom_surjective _ _ hle) hker

/-- **Closure under union** — by De Morgan, `L ⊔ M = (Lᶜ ⊓ Mᶜ)ᶜ`. -/
theorem langs_sup {M : Language α} (hL : V.langs L) (hM : V.langs M) : V.langs (L ⊔ M) := by
  rw [show L ⊔ M = (Lᶜ ⊓ Mᶜ)ᶜ by rw [compl_inf, compl_compl, compl_compl]]
  exact V.langs_compl (V.langs_inf (V.langs_compl hL) (V.langs_compl hM))

end Semigroup.Pseudovariety
