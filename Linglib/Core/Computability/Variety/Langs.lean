/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.SyntacticMonoid
import Linglib.Core.Algebra.Group.Pseudovariety

/-!
# The language-side operator of a pseudovariety

The forward half of the Eilenberg correspondence: for a pseudovariety `V` of finite monoids,
`V.langs` collects the regular languages whose syntactic monoid lies in `V`. The **keystone** is
that `V.langs` is a *variety of languages* — closed under the boolean operations and inverse
homomorphism — for *any* `V`. Each closure proof is the syntactic-monoid argument already used for
star-free languages (`Language.IsStarFree`, the `V = aperiodicVariety` instance), generalized by
replacing `Monoid.IsAperiodic` with `V.mem` and the aperiodic closure lemmas with the closure
fields of `V`.

## Main definitions

* `Monoid.Pseudovariety.langs` — the languages whose syntactic monoid lies in `V`.

## Main results

* `Monoid.Pseudovariety.langs_of_recognizes` — a language recognized by a finite monoid in `V` is in
  `V.langs` (the engine).
* `langs_compl` / `langs_inf` / `langs_sup` / `langs_univ` / `langs_bot` — boolean closure.
* `langs_comap` — closure under inverse homomorphism.
-/

universe u

namespace Monoid.Pseudovariety

open Language

variable (V : Pseudovariety.{u}) {α : Type u} {L : Language α}

/-- The languages over `α` whose (necessarily finite) syntactic monoid lies in `V` — the
language-side operator of the Eilenberg correspondence. -/
def langs (L : Language α) : Prop := L.IsRegular ∧ V.mem L.syntacticMonoid

theorem langs_def : V.langs L ↔ L.IsRegular ∧ V.mem L.syntacticMonoid := Iff.rfl

/-- **Engine.** A language recognized by a finite monoid in `V` lies in `V.langs`: the syntactic
monoid is a quotient of a submonoid of the recognizer, hence in `V`. Generalizes
`Language.IsStarFree.of_recognizes`. -/
theorem langs_of_recognizes {N : Type u} [Monoid N] [Finite N] (hN : V.mem N)
    (η : FreeMonoid α →* N) (P : Set N)
    (hL : ∀ w : List α, w ∈ L ↔ η (FreeMonoid.ofList w) ∈ P) : V.langs L := by
  have hle : Con.ker η ≤ L.syntacticCon := ker_le_syntacticCon_of_recognizes ⟨P, Set.ext hL⟩
  haveI : Finite (Con.ker η).Quotient :=
    Finite.of_equiv _ (Con.quotientKerEquivRange η).symm.toEquiv
  have hkerMem : V.mem (Con.ker η).Quotient :=
    V.mem_of_mulEquiv (Con.quotientKerEquivRange η).symm
      (V.sub (MonoidHom.mrange η).subtype_injective hN)
  have hsurj : Function.Surjective (Con.map (Con.ker η) L.syntacticCon hle) :=
    Con.lift_surjective_of_surjective _ Con.mk'_surjective
  haveI : Finite L.syntacticMonoid := Finite.of_surjective _ hsurj
  exact ⟨isRegular_of_finite_syntacticMonoid ‹_›, V.quot hsurj hkerMem⟩

/-- **Closure under complement** — immediate from complement-invariance of the syntactic monoid. -/
theorem langs_compl (h : V.langs L) : V.langs Lᶜ := by
  refine ⟨h.1.compl, ?_⟩
  show V.mem (syntacticCon Lᶜ).Quotient
  rw [syntacticCon_compl]
  exact h.2

/-- **Closure under intersection** — the syntactic monoid of `L ⊓ M` is a quotient of a submonoid
of `L.syntacticMonoid × M.syntacticMonoid`, which is in `V` by `prod`/`sub`/`quot`. -/
theorem langs_inf {M : Language α} (hL : V.langs L) (hM : V.langs M) : V.langs (L ⊓ M) := by
  refine ⟨hL.1.inf hM.1, ?_⟩
  set φ := L.toSyntacticMonoid.prod M.toSyntacticMonoid with hφ
  haveI : Finite L.syntacticMonoid := finite_syntacticMonoid hL.1
  haveI : Finite M.syntacticMonoid := finite_syntacticMonoid hM.1
  have hprod : V.mem (L.syntacticMonoid × M.syntacticMonoid) := V.prod hL.2 hM.2
  have hrange : V.mem (MonoidHom.mrange φ) := V.sub (MonoidHom.mrange φ).subtype_injective hprod
  haveI : Finite (Con.ker φ).Quotient :=
    Finite.of_equiv _ (Con.quotientKerEquivRange φ).symm.toEquiv
  have hker : V.mem (Con.ker φ).Quotient :=
    V.mem_of_mulEquiv (Con.quotientKerEquivRange φ).symm hrange
  have hle : Con.ker φ ≤ (L ⊓ M).syntacticCon := by
    rw [hφ, ker_prod_toSyntacticMonoid]; exact inf_syntacticCon_le_syntacticCon_inf L M
  haveI : Finite (L ⊓ M).syntacticMonoid := finite_syntacticMonoid (hL.1.inf hM.1)
  exact V.quot (f := Con.map (Con.ker φ) _ hle)
    (Con.lift_surjective_of_surjective _ Con.mk'_surjective) hker

/-- **Closure under union** — by De Morgan, `L ⊔ M = (Lᶜ ⊓ Mᶜ)ᶜ`. -/
theorem langs_sup {M : Language α} (hL : V.langs L) (hM : V.langs M) : V.langs (L ⊔ M) := by
  rw [show L ⊔ M = (Lᶜ ⊓ Mᶜ)ᶜ by rw [compl_inf, compl_compl, compl_compl]]
  exact V.langs_compl (V.langs_inf (V.langs_compl hL) (V.langs_compl hM))

/-- **The full language** is in `V.langs` — recognized by the trivial monoid, which is in every
pseudovariety (`memUnit`). -/
theorem langs_univ : V.langs (⊤ : Language α) :=
  V.langs_of_recognizes V.memUnit (1 : FreeMonoid α →* PUnit.{u + 1}) Set.univ
    (fun _ => iff_of_true (Set.mem_univ _) (Set.mem_univ _))

/-- **The empty language** is in `V.langs` — `⊥ = ⊤ᶜ`. -/
theorem langs_bot : V.langs (⊥ : Language α) := by
  simpa using V.langs_compl V.langs_univ

/-- **Closure under inverse homomorphism.** If `Lb` over `β` is in `V.langs` and
`φ : FreeMonoid α →* FreeMonoid β` is any monoid hom, the preimage language is in `V.langs`. The
recognizer is `Lb.toSyntacticMonoid.comp φ` into the finite `Lb.syntacticMonoid ∈ V`. Generalizes
`Language.IsStarFree.comap`. -/
theorem langs_comap {β : Type u} {Lb : Language β} (h : V.langs Lb)
    (φ : FreeMonoid α →* FreeMonoid β) :
    V.langs {w : List α | φ (FreeMonoid.ofList w) ∈ Lb} := by
  haveI : Finite Lb.syntacticMonoid := finite_syntacticMonoid h.1
  refine V.langs_of_recognizes h.2 (Lb.toSyntacticMonoid.comp φ)
    {m | ∃ u : FreeMonoid β, Lb.toSyntacticMonoid u = m ∧ u ∈ Lb} fun w => ?_
  refine ⟨fun hw => ⟨φ (FreeMonoid.ofList w), rfl, hw⟩, fun ⟨u, hu, hmem⟩ => ?_⟩
  exact (mem_iff_of_syntacticCon ((toSyntacticMonoid_eq_iff (L := Lb)).mp hu)).mp hmem

end Monoid.Pseudovariety
