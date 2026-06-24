/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.SyntacticMonoid
import Linglib.Core.Algebra.Group.Aperiodic

/-!
# Star-free languages

A language is **star-free** when it is regular with an aperiodic syntactic monoid
([schutzenberger-1965]) — the algebraic characterization of the star-free regular
expressions (built from finite sets by `∪`, `·`, complement, *no* Kleene star),
equivalently the counter-free / `FO[<]`-definable stringsets ([mcnaughton-papert-1971]).
Taking the syntactic-monoid characterization as the definition mirrors the project's
treatment of regularity (`Language.isRegular_iff_finite_syntacticMonoid`).

## Main definitions

* `Language.IsStarFree` — regular with an aperiodic syntactic monoid.

## Main results

* `Language.IsStarFree.compl` — star-free languages are closed under complement.
* `Language.IsStarFree.inter` — star-free languages are closed under intersection (`⊓`).
* `Language.IsStarFree.union` — star-free languages are closed under union (`⊔`, via De Morgan).
-/

namespace Language

variable {α : Type*} {L : Language α}

/-- A language is **star-free** when it is regular and its syntactic monoid is aperiodic
([schutzenberger-1965]). Star-free = `FO[<]`-definable = counter-free
([mcnaughton-papert-1971]). -/
def IsStarFree (L : Language α) : Prop :=
  L.IsRegular ∧ Monoid.IsAperiodic L.syntacticMonoid

theorem IsStarFree.isRegular (h : L.IsStarFree) : L.IsRegular := h.1

theorem IsStarFree.isAperiodic (h : L.IsStarFree) :
    Monoid.IsAperiodic L.syntacticMonoid := h.2

/-- The syntactic congruence is complement-invariant: a two-sided context distinguishes
`u` from `v` for `L` exactly when it does for `Lᶜ`. -/
theorem syntacticCon_compl (L : Language α) : Lᶜ.syntacticCon = L.syntacticCon :=
  Con.ext fun u v => by
    rw [syntacticCon_iff, syntacticCon_iff]
    exact forall_congr' fun _ => forall_congr' fun _ => not_iff_not

/-- The syntactic monoid is complement-invariant. -/
theorem syntacticMonoid_compl (L : Language α) : Lᶜ.syntacticMonoid = L.syntacticMonoid := by
  unfold syntacticMonoid; rw [syntacticCon_compl]

/-- **Star-free languages are closed under complement** — immediate from the
complement-invariance of the syntactic monoid (`syntacticMonoid_compl`) and of regularity
(`Language.IsRegular.compl`). -/
theorem IsStarFree.compl (h : L.IsStarFree) : Lᶜ.IsStarFree := by
  refine ⟨h.1.compl, ?_⟩
  show Monoid.IsAperiodic (syntacticCon Lᶜ).Quotient
  rw [syntacticCon_compl]
  exact h.2

/-! ### Closure under intersection and union

`Language α` carries its `BooleanAlgebra`, so intersection/union are the lattice meet/join
`⊓`/`⊔` (defeq to set intersection/union); these are the forms `Language.IsRegular.inf` uses. -/

variable (L) in
/-- The meet of the two syntactic congruences refines that of the intersection: if no `L`-context
and no `M`-context distinguishes `u` from `v`, then no `(L ⊓ M)`-context does either. -/
theorem inf_syntacticCon_le_syntacticCon_inf (M : Language α) :
    L.syntacticCon ⊓ M.syntacticCon ≤ (L ⊓ M).syntacticCon := by
  rw [Con.le_def]
  intro u v huv x y
  rw [Con.inf_iff_and, syntacticCon_iff, syntacticCon_iff] at huv
  exact and_congr (huv.1 x y) (huv.2 x y)

variable (L) in
/-- The kernel of the pairing of the two syntactic morphisms is exactly the meet of the two
syntactic congruences (a word's class in the product is the pair of its classes). -/
theorem ker_prod_toSyntacticMonoid (M : Language α) :
    Con.ker ((L.toSyntacticMonoid).prod M.toSyntacticMonoid) =
      L.syntacticCon ⊓ M.syntacticCon :=
  Con.ext fun u v => by
    rw [Con.ker_apply, MonoidHom.prod_apply, MonoidHom.prod_apply, Prod.ext_iff,
      toSyntacticMonoid_eq_iff, toSyntacticMonoid_eq_iff, Con.inf_iff_and]

/-- **Star-free languages are closed under intersection.** The syntactic monoid of `L ⊓ M`
is a quotient of a submonoid of `L.syntacticMonoid × M.syntacticMonoid`, which is aperiodic
(`Monoid.IsAperiodic.prod`); regularity is `Language.IsRegular.inf`. -/
theorem IsStarFree.inter {M : Language α} (hL : L.IsStarFree) (hM : M.IsStarFree) :
    (L ⊓ M).IsStarFree := by
  refine ⟨hL.1.inf hM.1, ?_⟩
  set φ := (L.toSyntacticMonoid).prod M.toSyntacticMonoid with hφ
  -- The product is aperiodic, hence so is its range submonoid, hence `(Con.ker φ).Quotient`.
  have hprod : Monoid.IsAperiodic (L.syntacticMonoid × M.syntacticMonoid) := hL.2.prod hM.2
  have hrange : Monoid.IsAperiodic (MonoidHom.mrange φ) :=
    hprod.of_injective (MonoidHom.mrange φ).subtype_injective
  have hker : Monoid.IsAperiodic (Con.ker φ).Quotient :=
    hrange.of_mulEquiv (Con.quotientKerEquivRange φ).symm
  -- The quotient map for `Con.ker φ ≤ (L ⊓ M).syntacticCon` is surjective.
  have hle : Con.ker φ ≤ (L ⊓ M).syntacticCon := by
    rw [hφ, ker_prod_toSyntacticMonoid]; exact inf_syntacticCon_le_syntacticCon_inf L M
  exact hker.of_surjective (f := Con.map (Con.ker φ) _ hle)
    (Con.lift_surjective_of_surjective _ Con.mk'_surjective)

/-- **Star-free languages are closed under union** — by De Morgan, `L ⊔ M = (Lᶜ ⊓ Mᶜ)ᶜ`. -/
theorem IsStarFree.union {M : Language α} (hL : L.IsStarFree) (hM : M.IsStarFree) :
    (L ⊔ M).IsStarFree := by
  rw [show L ⊔ M = (Lᶜ ⊓ Mᶜ)ᶜ by rw [compl_inf, compl_compl, compl_compl]]
  exact (hL.compl.inter hM.compl).compl

/-! ### Recognition by a finite aperiodic monoid -/

/-- **A language recognized by a finite aperiodic monoid is star-free** — the algebraic
characterization of star-free ([schutzenberger-1965]). When `η : FreeMonoid α →* M` with `M`
finite and aperiodic and `L = η ⁻¹' P`, the syntactic congruence is coarser than `ker η`
(`η`-equal words share every context), so `L.syntacticMonoid` is a quotient of a submonoid of
`M` — hence finite and aperiodic. This is the engine for placing a constraint class inside
`SF`: exhibit a finite aperiodic recognizer. -/
theorem IsStarFree.of_recognizes {M : Type*} [Monoid M] [Finite M]
    (hM : Monoid.IsAperiodic M) (η : FreeMonoid α →* M) (P : Set M)
    (hL : ∀ w : List α, w ∈ L ↔ η (FreeMonoid.ofList w) ∈ P) : L.IsStarFree := by
  have hle : Con.ker η ≤ L.syntacticCon :=
    ker_le_syntacticCon_of_recognizes ⟨P, Set.ext hL⟩
  have hker : Monoid.IsAperiodic (Con.ker η).Quotient :=
    (hM.of_injective (MonoidHom.mrange η).subtype_injective).of_mulEquiv
      (Con.quotientKerEquivRange η).symm
  have hfin : Finite (Con.ker η).Quotient :=
    Finite.of_equiv _ (Con.quotientKerEquivRange η).symm.toEquiv
  have hsurj : Function.Surjective (Con.map (Con.ker η) L.syntacticCon hle) :=
    Con.lift_surjective_of_surjective _ Con.mk'_surjective
  exact ⟨isRegular_of_finite_syntacticMonoid (Finite.of_surjective _ hsurj),
    hker.of_surjective hsurj⟩

end Language
