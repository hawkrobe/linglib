import Mathlib.Order.Hom.CompleteLattice

/-!
# Injectivity of `CompleteLatticeHom.setPreimage`

`Mathlib.Order.Hom.CompleteLattice` packages set-preimage `f⁻¹` of a
function `f : Y → X` as a `CompleteLatticeHom (Set X) (Set Y)` via
`CompleteLatticeHom.setPreimage`. This file establishes that the
packaging is injective in `f`: distinct functions induce distinct
set-preimage operators.

The proof probes the operator at the singleton `{f y}` to extract
`g y = f y` pointwise — the same atom-decomposition technique that
underlies @cite{hoeksema-1983} Fact 1 (uniqueness of NP-comparative GQ
homomorphisms from their threshold functions).

Candidate for upstreaming to mathlib.
-/

namespace Core.Order

/-- `CompleteLatticeHom.setPreimage` is injective in its function argument. -/
theorem setPreimage_injective {X Y : Type*} :
    Function.Injective
      (CompleteLatticeHom.setPreimage : (Y → X) → CompleteLatticeHom (Set X) (Set Y)) := by
  intro f g h
  funext y
  have key := congrArg (fun (φ : CompleteLatticeHom (Set X) (Set Y)) => φ {f y}) h
  simp only [CompleteLatticeHom.coe_setPreimage] at key
  have hmem := Set.ext_iff.mp key y
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hmem
  exact (hmem.mp trivial).symm

end Core.Order
