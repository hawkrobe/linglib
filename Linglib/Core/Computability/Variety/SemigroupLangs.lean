/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Computability.Variety.SemigroupLangs`.
-/
import Linglib.Core.Algebra.Semigroup.Pseudovariety
import Linglib.Core.Computability.SyntacticSemigroup
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

* `Semigroup.Pseudovariety.langs_compl` / `langs_inf` / `langs_sup`: boolean closure.
* `Semigroup.Pseudovariety.langs_leftQuotient` / `langs_rightQuotient`: closure under quotients.
* `Semigroup.Pseudovariety.langs_comap`: closure under inverse homomorphism of free semigroups.
* `Semigroup.Pseudovariety.langs_of_recognizes`: a language recognized by a finite semigroup in
  `V` lies in `V.langs` — the engine behind `langs_univ` and `langs_bot`.

Together these are the four conditions of [eilenberg-1976] VII, Theorem 3.2.
-/

universe u

namespace Semigroup.Pseudovariety

open Language FreeSemigroup

variable (V : Pseudovariety.{u}) {α : Type u} {L : Language α}

/-- The languages over `α` whose (necessarily finite) syntactic semigroup lies in `V` — the
`+`-variety side of the Eilenberg correspondence. -/
def langs (L : Language α) : Prop := L.IsRegular ∧ V.mem L.SyntacticSemigroup

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

section Quotients

variable {V}

/-- A coarser syntactic congruence keeps the language in `V.langs`. -/
private theorem langs_of_syntacticSemigroupCon_le {M : Language α} (h : V.langs L)
    (hle : L.syntacticSemigroupCon ≤ M.syntacticSemigroupCon) : V.langs M := by
  haveI : Finite L.SyntacticMonoid := IsRegular.finite_syntacticMonoid h.1
  have hsurj : Function.Surjective
      (Con.mapMulHom L.syntacticSemigroupCon M.syntacticSemigroupCon hle) :=
    Con.mapMulHom_surjective _ _ hle
  haveI : Finite M.SyntacticSemigroup := .of_surjective _ hsurj
  exact ⟨IsRegular.of_finite_syntacticSemigroup ‹Finite M.SyntacticSemigroup›,
    V.quot hsurj h.2⟩

/-- **Closure under left quotient** — Eilenberg's axiom VII.3.3. -/
theorem langs_leftQuotient (h : V.langs L) (u : List α) : V.langs (L.leftQuotient u) :=
  langs_of_syntacticSemigroupCon_le h (L.syntacticSemigroupCon_le_leftQuotient u)

/-- **Closure under right quotient** — Eilenberg's axiom VII.3.3. -/
theorem langs_rightQuotient (h : V.langs L) (u : List α) : V.langs (L.rightQuotient u) :=
  langs_of_syntacticSemigroupCon_le h (L.syntacticSemigroupCon_le_rightQuotient u)

end Quotients

/-- **Closure under intersection** — the syntactic semigroup of `L ⊓ M` is a quotient of a
subsemigroup of `L.SyntacticSemigroup × M.SyntacticSemigroup`, which is in `V` by
`prod`/`sub`/`quot`. -/
theorem langs_inf {M : Language α} (hL : V.langs L) (hM : V.langs M) : V.langs (L ⊓ M) := by
  refine ⟨hL.1.inf hM.1, ?_⟩
  haveI : Finite L.SyntacticMonoid := IsRegular.finite_syntacticMonoid hL.1
  haveI : Finite M.SyntacticMonoid := IsRegular.finite_syntacticMonoid hM.1
  haveI : Finite (L ⊓ M).SyntacticMonoid := IsRegular.finite_syntacticMonoid (hL.1.inf hM.1)
  set φ := L.toSyntacticSemigroup.prod M.toSyntacticSemigroup with hφ
  haveI : Finite (Con.ker φ).Quotient := .of_injective _ (Con.kerLiftMulHom_injective φ)
  have hker : V.mem (Con.ker φ).Quotient :=
    V.sub (Con.kerLiftMulHom_injective φ) (V.prod hL.2 hM.2)
  have hle : Con.ker φ ≤ (L ⊓ M).syntacticSemigroupCon := by
    rw [hφ, ker_prod_toSyntacticSemigroup]
    exact inf_syntacticSemigroupCon_le_syntacticSemigroupCon_inf
  haveI : Finite (L ⊓ M).syntacticSemigroupCon.Quotient :=
    inferInstanceAs (Finite (L ⊓ M).SyntacticSemigroup)
  exact V.quot (Con.mapMulHom_surjective _ _ hle) hker

/-- **Closure under union** — by De Morgan, `L ⊔ M = (Lᶜ ⊓ Mᶜ)ᶜ`. -/
theorem langs_sup {M : Language α} (hL : V.langs L) (hM : V.langs M) : V.langs (L ⊔ M) := by
  rw [show L ⊔ M = (Lᶜ ⊓ Mᶜ)ᶜ by rw [compl_inf, compl_compl, compl_compl]]
  exact V.langs_compl (V.langs_inf (V.langs_compl hL) (V.langs_compl hM))

/-- **Engine.** A language recognized by a finite semigroup in `V` lies in `V.langs`: the
syntactic semigroup is a quotient of a subsemigroup of the recognizer. -/
theorem langs_of_recognizes {T : Type u} [Semigroup T] [Finite T] (hT : V.mem T)
    (η : FreeSemigroup α →ₙ* T) (P : Set T)
    (hL : ∀ w : FreeSemigroup α, w.toFreeMonoid.toList ∈ L ↔ η w ∈ P) : V.langs L := by
  have hle : Con.ker η ≤ L.syntacticSemigroupCon :=
    ker_le_syntacticSemigroupCon_of_recognizes (recognizesSemigroup_iff.mpr ⟨P, hL⟩)
  haveI : Finite (Con.ker η).Quotient := .of_injective _ (Con.kerLiftMulHom_injective η)
  have hkerMem : V.mem (Con.ker η).Quotient := V.sub (Con.kerLiftMulHom_injective η) hT
  have hsurj := Con.mapMulHom_surjective (Con.ker η) L.syntacticSemigroupCon hle
  haveI : Finite L.SyntacticSemigroup := .of_surjective _ hsurj
  exact ⟨IsRegular.of_finite_syntacticSemigroup ‹_›, V.quot hsurj hkerMem⟩

/-- **The full language** — recognized by the trivial semigroup, which is in every
pseudovariety. -/
theorem langs_univ : V.langs (⊤ : Language α) := by
  refine V.langs_of_recognizes V.memUnit (1 : FreeSemigroup α →ₙ* PUnit.{u + 1}) Set.univ ?_
  intro _
  exact iff_of_true trivial (Set.mem_univ _)

/-- **The empty language** — `⊥ = ⊤ᶜ`. -/
theorem langs_bot : V.langs (⊥ : Language α) := by
  simpa using V.langs_compl V.langs_univ

/-- **Closure under inverse homomorphism** — Eilenberg's fourth axiom, on the `+` side. The
morphism is between free *semigroups*: [eilenberg-1976] VII, Exercise 3.7 shows that the
`*`-variety form of this axiom decomposes into a non-erasing morphism condition, and a free
semigroup has no erasing morphisms. -/
theorem langs_comap {β : Type u} {Lb : Language β} (h : V.langs Lb)
    (φ : FreeSemigroup α →ₙ* FreeSemigroup β) :
    V.langs {w : List α | ∃ u : FreeSemigroup α,
      u.toFreeMonoid.toList = w ∧ (φ u).toFreeMonoid.toList ∈ Lb} := by
  haveI : Finite Lb.SyntacticMonoid := IsRegular.finite_syntacticMonoid h.1
  refine V.langs_of_recognizes h.2 (Lb.toSyntacticSemigroup.comp φ)
    {m | ∃ u : FreeSemigroup β, Lb.toSyntacticSemigroup u = m ∧ u.toFreeMonoid.toList ∈ Lb} ?_
  intro w
  constructor
  · rintro ⟨u, hu, hmem⟩
    obtain rfl : u = w := toFreeMonoid_injective (FreeMonoid.toList.injective hu)
    exact ⟨φ u, rfl, hmem⟩
  · rintro ⟨v, hv, hmem⟩
    exact ⟨w, rfl, (SyntacticEquiv.mem_iff (toSyntacticSemigroup_eq_iff.mp hv)).mp hmem⟩

end Semigroup.Pseudovariety
