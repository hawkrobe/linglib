import Linglib.Core.Algebra.RootedTree.Coproduct
import Linglib.Core.Combinatorics.RootedTree.Nonplanar

set_option autoImplicit false

/-!
# Δ^p on `ConnesKreimer R (Nonplanar α)` via projection from `Planar`
@cite{marcolli-chomsky-berwick-2025} @cite{foissy-introduction-hopf-algebras-trees}

Phase A.7 substrate. The Nonplanar Δ^p is obtained by descending the
planar Δ^p (`Coproduct.lean`) through the projection
`mk : Planar α → Nonplanar α`. Foissy's clean proof of coassociativity
(via the Hochschild 1-cocycle property of `B+_a = Nonplanar.node a`) then
gives a sorry-free `Bialgebra` instance.

## Status

`[UPSTREAM]` candidate. Phase A.7-α (this file's first section): the
projection algebra hom + API. Δ^p, cocycle, coassoc, Bialgebra instance
land in subsequent sub-phases (A.7-β / γ / δ).

## Architecture

The projection algebra hom is built directly on top of mathlib's
`AddMonoidAlgebra.mapDomainAlgHom`, applied to the additive monoid hom
`Multiset.mapAddMonoidHom Nonplanar.mk`. No bespoke construction —
the universal property of `AddMonoidAlgebra` does the heavy lifting.
-/

namespace RootedTree

namespace ConnesKreimer

variable {R : Type*} [CommSemiring R] {α : Type*}

/-! ## §1: Projection algebra hom `Planar → Nonplanar`

`Nonplanar.mk : Planar α → Nonplanar α` extends to an algebra hom on
`ConnesKreimer R` via `AddMonoidAlgebra.mapDomainAlgHom`. Surjective at
the carrier level; the kernel encodes PlanarEquiv-equivalence of forests
of trees, which is what subsequent sub-phases will need to factor through. -/

/-- The additive monoid hom from forests of planar trees to forests of
    nonplanar trees, given by mapping `Nonplanar.mk` componentwise. -/
noncomputable def forestProjAddHom :
    Forest (Planar α) →+ Forest (Nonplanar α) :=
  Multiset.mapAddMonoidHom Nonplanar.mk

/-- The **projection algebra hom** `ConnesKreimer R (Planar α) →ₐ[R]
    ConnesKreimer R (Nonplanar α)` induced by `Nonplanar.mk`. -/
noncomputable def planarToNonplanarAlg :
    ConnesKreimer R (Planar α) →ₐ[R] ConnesKreimer R (Nonplanar α) :=
  AddMonoidAlgebra.mapDomainAlgHom R R (forestProjAddHom (α := α))

/-! ## §2: API lemmas — action on `of'` and `ofTree` -/

@[simp] theorem planarToNonplanarAlg_of' (F : Forest (Planar α)) :
    planarToNonplanarAlg (R := R) (of' F) =
      of' (R := R) (F.map Nonplanar.mk) := by
  show Finsupp.mapDomain (forestProjAddHom (α := α)) (Finsupp.single F 1) =
       Finsupp.single (F.map Nonplanar.mk) 1
  rw [Finsupp.mapDomain_single]
  rfl

@[simp] theorem planarToNonplanarAlg_ofTree (t : Planar α) :
    planarToNonplanarAlg (R := R) (ofTree t) =
      ofTree (Nonplanar.mk t) := by
  unfold ofTree
  rw [planarToNonplanarAlg_of', Multiset.map_singleton]

@[simp] theorem planarToNonplanarAlg_one :
    planarToNonplanarAlg (R := R) (1 : ConnesKreimer R (Planar α)) = 1 :=
  map_one _

@[simp] theorem planarToNonplanarAlg_mul
    (x y : ConnesKreimer R (Planar α)) :
    planarToNonplanarAlg (R := R) (x * y) =
      planarToNonplanarAlg x * planarToNonplanarAlg y :=
  map_mul _ _ _

end ConnesKreimer

end RootedTree
