/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.Coproduct.Pruning
public import Linglib.Core.Combinatorics.RootedTree.Conservation
public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# The Connes–Kreimer Hopf algebra of nonplanar rooted trees

The pruning bialgebra on `ConnesKreimer R (UnorderedTree α)` (`Coproduct/Pruning.lean`) is a Hopf
algebra over any commutative ring: the Connes–Kreimer Hopf algebra of nonplanar, not necessarily
binary, rooted trees.

The antipode is the inductive formula `S(x) = −x − Σ S(x′) · x″` of a graded connected bialgebra
(Foissy's notes, §1.3, Lemma 2). As the algebra is commutative, the antipode is an algebra map,
so it is determined by its values on trees. Summing over every admissible cut `(F, T')` of a tree
`T` (crown forest `F`, trunk `T'`), including the empty cut `(0, T)` that supplies the `−T` term,

  `S(T) = −Σ_{(F, T')} (Π_{t ∈ F} S(t)) · T'`.

## Main definitions

* `ConnesKreimer.antipodeTreeN`: the antipode on a tree.
* `ConnesKreimer.antipodeAlgHomN`: its multiplicative extension to forests.

## Main results

* `ConnesKreimer.antipodeAlgHomN_convMul_id`, `ConnesKreimer.id_convMul_antipodeAlgHomN`:
  `S ⋆ id = 1 = id ⋆ S` in the convolution monoid of algebra endomorphisms.
* The `HopfAlgebra R (ConnesKreimer R (UnorderedTree α))` instance, over any commutative ring.
* `ConnesKreimer.antipode_ofTree`: the antipode on a tree is `antipodeTreeN`.

## Implementation notes

The construction needs only a commutative ring (for the negation), and the bialgebra only a
commutative semiring.

The recursion descends on `UnorderedTree.numNodes`, the grading by weight: every crown tree has
fewer vertices than `T` (`cutSummandsN_crown_numNodes_lt`). The recursion makes `S` a left
convolution inverse of the identity. Foissy's proof also takes a right antipode, realized here by
the recursion `R(T) = −T − Σ_{F ≠ 0} F · R(T')` on the trunk; the two agree by
`left_inv_eq_right_inv` in the convolution monoid `WithConv (H →ₐ[R] H)`.

## TODO

* Derive the antipode from a general construction for connected graded bialgebras once one is
  in mathlib (mathlib4#39849).
* Foissy's closed form `S(t) = Σ (−1)^(n_c + 1) W^c(t)` over the non-total cuts `c` of `t`
  ([foissy-introduction-hopf-algebras-trees] §1.3, Theorem 2).

## References

* [connes-kreimer-1998]
* [foissy-introduction-hopf-algebras-trees]
-/

@[expose] public section

open UnorderedTree WithConv

namespace ConnesKreimer

variable {R : Type*} [CommRing R] {α : Type*}

/-- The antipode on a tree, summed over all cuts,
`S(T) = −Σ_{(F, T') ∈ cutSummandsN T} (Π_{t ∈ F} S(t)) · T'`. -/
noncomputable def antipodeTreeN (T : UnorderedTree α) : ConnesKreimer R (UnorderedTree α) :=
  -((cutSummandsN T).attach.map fun p ↦
    (p.1.1.attach.map fun t ↦ antipodeTreeN t.1).prod * ofTree p.1.2).sum
termination_by T.numNodes
decreasing_by exact cutSummandsN_crown_numNodes_lt p.2 t.2

theorem antipodeTreeN_unfold (T : UnorderedTree α) :
    antipodeTreeN (R := R) T =
      -((cutSummandsN T).map fun p ↦ (p.1.map antipodeTreeN).prod * ofTree p.2).sum := by
  rw [antipodeTreeN]
  simp only [Multiset.attach_map_val' _ (antipodeTreeN (R := R))]
  exact congrArg (fun s ↦ -s.sum) (Multiset.attach_map_val' _
    fun p : Forest (UnorderedTree α) × UnorderedTree α ↦
      (p.1.map (antipodeTreeN (R := R))).prod * ofTree p.2)

/-- The antipode as an algebra map extends `antipodeTreeN` multiplicatively to forests. -/
noncomputable def antipodeAlgHomN :
    ConnesKreimer R (UnorderedTree α) →ₐ[R] ConnesKreimer R (UnorderedTree α) :=
  aeval antipodeTreeN

@[simp] theorem antipodeAlgHomN_apply_of' (F : Forest (UnorderedTree α)) :
    antipodeAlgHomN (R := R) (of' F) = (F.map antipodeTreeN).prod :=
  aeval_of' _ F

@[simp] theorem antipodeAlgHomN_apply_ofTree (T : UnorderedTree α) :
    antipodeAlgHomN (R := R) (ofTree T) = antipodeTreeN T :=
  aeval_ofTree _ T

/-- The right antipode on a tree, recursing on the trunk of the nonempty cuts:
`R(T) = −T − Σ_{(F, T'), F ≠ 0} F · R(T')`. -/
private noncomputable def antipodeRightTreeN (T : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) :=
  -ofTree T - (((cutSummandsN T).filter (¬ ·.1.card = 0)).attach.map fun p ↦
    of' p.1.1 * antipodeRightTreeN p.1.2).sum
termination_by T.numNodes
decreasing_by
  obtain ⟨hp, h⟩ := Multiset.mem_filter.1 p.2
  exact cutSummandsN_trunk_numNodes_lt hp (Multiset.card_eq_zero.not.1 h)

private theorem antipodeRightTreeN_unfold (T : UnorderedTree α) :
    antipodeRightTreeN (R := R) T = -ofTree T -
      (((cutSummandsN T).filter (¬ ·.1.card = 0)).map fun p ↦
        of' p.1 * antipodeRightTreeN p.2).sum := by
  rw [antipodeRightTreeN]
  exact congrArg (fun s ↦ -ofTree T - s.sum) (Multiset.attach_map_val' _
    fun p : Forest (UnorderedTree α) × UnorderedTree α ↦ of' p.1 * antipodeRightTreeN (R := R) p.2)

/-- `S ⋆ id = 1`, since on a tree the summands of `(S ⊗ id) Δ T` are those of `−S(T)`. An input to
the instance; afterwards this is `AlgHom.antipode_id_cancel`. -/
theorem antipodeAlgHomN_convMul_id :
    toConv (antipodeAlgHomN (R := R) (α := α)) * toConv (AlgHom.id R _) = 1 := by
  refine ofConv_injective (algHom_ext_ofTree fun T ↦ ?_)
  simp [AlgHom.convMul_apply, coalgebra_comul_apply, coalgebra_counit_apply, comulTreeN,
    comulTreeNG, map_multiset_sum, Multiset.map_map, antipodeTreeN_unfold T]

/-- `id ⋆ R = 1`, since the empty cut contributes `R(T)`, which cancels the rest. -/
private theorem id_convMul_aeval_antipodeRightTreeN :
    toConv (AlgHom.id R _) * toConv (aeval (antipodeRightTreeN (R := R) (α := α))) = 1 := by
  refine ofConv_injective (algHom_ext_ofTree fun T ↦ ?_)
  simp only [AlgHom.convMul_apply, coalgebra_comul_apply, comulAlgHomN_apply_ofTree, comulTreeN,
    comulTreeNG, map_add, map_multiset_sum, Multiset.map_map, Function.comp_def,
    Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, map_one, mul_one, aeval_ofTree]
  rw [← Multiset.filter_add_not (·.1.card = 0) (cutSummandsN T), Multiset.map_add,
    Multiset.sum_add, cutSummandsN_filter_empty, Multiset.map_singleton, Multiset.sum_singleton,
    of'_zero, one_mul, antipodeRightTreeN_unfold T, AlgHom.convOne_apply, coalgebra_counit_apply,
    counit_ofTree, map_zero]
  abel

/-- `id ⋆ S = 1`, since `S` equals the right antipode. An input to
the instance; afterwards this is `LinearMap.id_mul_antipode`. -/
theorem id_convMul_antipodeAlgHomN :
    toConv (AlgHom.id R _) * toConv (antipodeAlgHomN (R := R) (α := α)) = 1 :=
  left_inv_eq_right_inv antipodeAlgHomN_convMul_id (id_convMul_aeval_antipodeRightTreeN (R := R))
    ▸ id_convMul_aeval_antipodeRightTreeN

noncomputable instance : HopfAlgebra R (ConnesKreimer R (UnorderedTree α)) :=
  .ofConvInverse antipodeAlgHomN.toLinearMap
    congr(toConv ($(antipodeAlgHomN_convMul_id (R := R) (α := α))).ofConv.toLinearMap)
    congr(toConv ($(id_convMul_antipodeAlgHomN (R := R) (α := α))).ofConv.toLinearMap)

@[simp] theorem antipode_ofTree (T : UnorderedTree α) :
    HopfAlgebra.antipode R (ofTree T) = antipodeTreeN (R := R) T :=
  antipodeAlgHomN_apply_ofTree T

theorem antipodeAlgHom_eq_antipodeAlgHomN :
    HopfAlgebra.antipodeAlgHom R (ConnesKreimer R (UnorderedTree α)) = antipodeAlgHomN :=
  rfl

end ConnesKreimer
