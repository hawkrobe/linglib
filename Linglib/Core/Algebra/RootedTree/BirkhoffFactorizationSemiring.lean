/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.Coproduct.Pruning
public import Linglib.Core.Combinatorics.RootedTree.Conservation
public import Linglib.Core.Algebra.RotaBaxter

@[expose] public section

open RoseTree UnorderedTree

/-!
# Semiring Birkhoff factorization on the Connes–Kreimer Hopf algebra

The Bogolyubov recursion for a linear map `φ : H → ℛ` into a commutative semiring `ℛ`, whose
addition is not invertible (tropical, Viterbi and Boolean semirings), with a Rota–Baxter operator
`R` of weight `+1`:

  `φ̃(x) = φ(x) ⊡ Σ φ₋(x′) ⊙ φ(x″)`,    `φ₋(x) = R(φ̃(x))`,    `φ₊(x) = φ₋(x) ⊡ φ̃(x)`,

with `⊡, ⊙` the semiring addition and multiplication. The Hopf algebra `H` needs only a semiring
of coefficients, so `ℕ` serves for a Boolean target. A semiring has no antipode, so only the form
`φ₊ = φ₋ ⋆ φ` of the factorization is available.

## Main definitions

* `ConnesKreimer.SemiringRenorm.birkhoffMinusTree`, `birkhoffMinus`: the negative part
  `φ₋ = R(φ̃)`, on a tree and as an algebra homomorphism.
* `ConnesKreimer.SemiringRenorm.birkhoffPrepTree`: the Bogolyubov preparation `φ̃`.
* `ConnesKreimer.SemiringRenorm.birkhoffPlusTree`: the renormalized part `φ₊ = φ̃ + φ₋`.

## Main results

* `ConnesKreimer.SemiringRenorm.birkhoffFactorization_ofTree`: `φ₊ = φ₋ ⋆ φ` on generators.

## References

* [marcolli-tedeschi-2015]
-/

namespace ConnesKreimer.SemiringRenorm

open scoped TensorProduct

variable {R ℛ : Type*} [CommSemiring R] [CommSemiring ℛ] [Algebra R ℛ] {α : Type*}
  (φ : ConnesKreimer R (UnorderedTree α) →ₗ[R] ℛ) (RB : RotaBaxterSemiring ℛ)

/-- The Bogolyubov negative part on a tree, for a weight-`+1` operator,
    `φ₋(T) = R(Σ_{(cf,rem) ∈ cutSummandsN T} (Π_{Tᵢ ∈ cf} φ₋(Tᵢ)) · φ(ofTree rem))`. The semiring
    analogue of the ring `birkhoffMinusTree`, with the *positive* projection `R` in place of `−R`;
    well-founded on `T.numNodes`. -/
noncomputable def birkhoffMinusTree (T : UnorderedTree α) : ℛ :=
  RB.op ((cutSummandsN T).attach.map fun p ↦
    (p.1.1.attach.map fun t ↦ birkhoffMinusTree t.1).prod * φ (ofTree p.1.2)).sum
termination_by T.numNodes
decreasing_by exact cutSummandsN_crown_numNodes_lt p.2 t.2

/-- The negative part `φ₋` as an algebra homomorphism, `birkhoffMinusTree` extended
    multiplicatively to forests. -/
noncomputable def birkhoffMinus : ConnesKreimer R (UnorderedTree α) →ₐ[R] ℛ :=
  aeval (birkhoffMinusTree φ RB)

@[simp] theorem birkhoffMinus_apply_of' (F : Forest (UnorderedTree α)) :
    birkhoffMinus φ RB (of' F) = (F.map (birkhoffMinusTree φ RB)).prod :=
  aeval_of' _ F

@[simp] theorem birkhoffMinus_apply_ofTree (T : UnorderedTree α) :
    birkhoffMinus φ RB (ofTree T) = birkhoffMinusTree φ RB T :=
  aeval_ofTree _ T

/-- The Bogolyubov preparation
    `φ̃(T) = Σ_{(cf,rem) ∈ cutSummandsN T} (Π_{Tᵢ ∈ cf} φ₋(Tᵢ)) · φ(ofTree rem)`, of which the
    negative part is `φ₋(T) = R(φ̃(T))` and the renormalized part is `φ₊(T) = φ̃(T) + φ₋(T)`. -/
noncomputable def birkhoffPrepTree (T : UnorderedTree α) : ℛ :=
  ((cutSummandsN T).map fun p ↦ (p.1.map (birkhoffMinusTree φ RB)).prod * φ (ofTree p.2)).sum

/-- The negative part is the projection `R` of the preparation, `φ₋(T) = R(φ̃(T))`. -/
theorem birkhoffMinusTree_eq_op_prep (T : UnorderedTree α) :
    birkhoffMinusTree φ RB T = RB.op (birkhoffPrepTree φ RB T) := by
  rw [birkhoffMinusTree]
  simp only [Multiset.attach_map_val' _ (birkhoffMinusTree φ RB)]
  exact congrArg (fun s ↦ RB.op s.sum) (Multiset.attach_map_val' _
    fun p : Forest (UnorderedTree α) × UnorderedTree α ↦
      (p.1.map (birkhoffMinusTree φ RB)).prod * φ (ofTree p.2))

/-- The renormalized part on a tree, `φ₊(T) = φ̃(T) + φ₋(T)` (the semiring `φ₋ ⊡ φ̃`). -/
noncomputable def birkhoffPlusTree (T : UnorderedTree α) : ℛ :=
  birkhoffPrepTree φ RB T + birkhoffMinusTree φ RB T

/-- The semiring Birkhoff factorization `φ₊ = φ₋ ⋆ φ` on generators. On each tree the
    convolution `φ₋ ⋆ φ`, that is `mul' ∘ (φ₋ ⊗ φ) ∘ comul`, recovers the renormalized part `φ₊`.
    Needs `φ` unital (`φ 1 = 1`). Same proof as the ring keystone, the identity being pure
    coproduct bookkeeping. -/
theorem birkhoffFactorization_ofTree (hφ : φ 1 = 1) (T : UnorderedTree α) :
    LinearMap.mul' R ℛ
        ((TensorProduct.map (birkhoffMinus φ RB).toLinearMap φ) (comulAlgHomN (ofTree T)))
      = birkhoffPlusTree φ RB T := by
  rw [comulAlgHomN_apply_ofTree, comulTreeN, comulTreeNG]
  simp only [map_add, map_multiset_sum, Multiset.map_map, Function.comp_def,
    TensorProduct.map_tmul, LinearMap.mul'_apply, AlgHom.toLinearMap_apply,
    birkhoffMinus_apply_ofTree, birkhoffMinus_apply_of', hφ, mul_one]
  rw [← birkhoffPrepTree, birkhoffPlusTree]
  exact add_comm _ _

end ConnesKreimer.SemiringRenorm
