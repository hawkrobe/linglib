/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.HopfAlgebra
public import Linglib.Core.Algebra.RotaBaxter
public import Mathlib.RingTheory.Coalgebra.Convolution
public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.Convolution

@[expose] public section

open RoseTree UnorderedTree

/-!
# Birkhoff factorization on the Connes–Kreimer Hopf algebra

Given a linear map `φ : H → ℛ` from the Connes–Kreimer Hopf algebra `H` into a commutative algebra
`ℛ` with a Rota–Baxter operator `R` of weight `-1`, the Bogolyubov recursion splits `φ` into a
negative part `φ₋` and a renormalized part `φ₊`. For a character `φ` they satisfy the algebraic
Birkhoff factorization `φ = (φ₋ ∘ S) ⋆ φ₊`, with `S` the antipode and `⋆` the convolution.

The negative part is built by the same recursion over cuts as the antipode `antipodeTreeN`, with
the character value `φ (ofTree rem)` in place of `ofTree rem` and `−R` in place of negation; at
`R = id` and `φ = id` it is the antipode (`birkhoffMinusTree_id_eq_antipodeTreeN`).

## Main definitions

* `ConnesKreimer.birkhoffMinusTree`, `ConnesKreimer.birkhoffMinus`: the negative part `φ₋`, on a
  tree and as an algebra homomorphism.
* `ConnesKreimer.birkhoffPlusTree`, `ConnesKreimer.birkhoffPlus`: the renormalized part
  `φ₊ = (1 − R)(φ̃)`, on a tree and as an algebra homomorphism.

## Main results

* `ConnesKreimer.birkhoffFactorization_ofTree`: `φ₊ = φ₋ ⋆ φ` on generators, for any linear `φ`.
* `ConnesKreimer.birkhoffPlus_eq_convMul`: `φ₊ = φ₋ ⋆ φ` on all of `H`, for a character `φ`.
* `ConnesKreimer.birkhoffFactorization`: `φ = (φ₋ ∘ S) ⋆ φ₊` for a character `φ`.
* `ConnesKreimer.birkhoffMinusTree_id_eq_antipodeTreeN`: at `R = id` the negative part is the
  antipode.

## Implementation notes

The factorization is stated in the convolution monoid of characters `WithConv (H →ₐ[R] ℛ)`. The
target carries no coproduct, so this is not mathlib's `AlgHom.convGroup`; the convolution inverse
`φ₋ ∘ S` of `φ₋` comes from the antipode law (`antipodeComp_convMul_self`).

## References

* [connes-kreimer-2000]
* [ebrahimi-fard-guo-kreimer-2004]
-/

namespace ConnesKreimer

open scoped TensorProduct

variable {R ℛ : Type*} [CommRing R] [CommRing ℛ] [Algebra R ℛ] {α : Type*}
  (φ : ConnesKreimer R (UnorderedTree α) →ₗ[R] ℛ) (RB : RotaBaxter R ℛ (-1))

/-- The Bogolyubov negative part on a tree,
    `φ₋(T) = −R(Σ_{(cf,rem) ∈ cutSummandsN T} (Π_{Tᵢ ∈ cf} φ₋(Tᵢ)) · φ(ofTree rem))`.
    Models `antipodeTreeN` with the character value `φ(ofTree rem)` in place of `ofTree rem` and
    the Rota–Baxter `−R` in place of bare negation; well-founded on `T.numNodes`. -/
noncomputable def birkhoffMinusTree (T : UnorderedTree α) : ℛ :=
  -RB.op ((cutSummandsN T).attach.map fun p ↦
    (p.1.1.attach.map fun t ↦ birkhoffMinusTree t.1).prod * φ (ofTree p.1.2)).sum
termination_by T.numNodes
decreasing_by exact cutSummandsN_crown_numNodes_lt p.2 t.2

/-- The negative part `φ₋` as an algebra homomorphism, `birkhoffMinusTree` extended
    multiplicatively to forests. -/
noncomputable def birkhoffMinus : ConnesKreimer R (UnorderedTree α) →ₐ[R] ℛ :=
  aeval (birkhoffMinusTree φ RB)

/-- `φ₋` on a forest basis element is the product of `φ₋` over its trees. -/
@[simp] theorem birkhoffMinus_apply_of' (F : Forest (UnorderedTree α)) :
    birkhoffMinus φ RB (of' F) = (F.map (birkhoffMinusTree φ RB)).prod :=
  aeval_of' _ F

/-- `φ₋` on a single tree generator agrees with `birkhoffMinusTree`. -/
@[simp] theorem birkhoffMinus_apply_ofTree (T : UnorderedTree α) :
    birkhoffMinus φ RB (ofTree T) = birkhoffMinusTree φ RB T :=
  aeval_ofTree _ T

/-! ### The Bogolyubov preparation and the renormalized part -/

/-- The Bogolyubov preparation
    `φ̃(T) = Σ_{(cf,rem) ∈ cutSummandsN T} (Π_{Tᵢ ∈ cf} φ₋(Tᵢ)) · φ(ofTree rem)`, of which the
    negative part is `φ₋(T) = −R(φ̃(T))` and the renormalized part is `φ₊(T) = (1−R)(φ̃(T))`. -/
noncomputable def birkhoffPrepTree (T : UnorderedTree α) : ℛ :=
  ((cutSummandsN T).map fun p ↦ (p.1.map (birkhoffMinusTree φ RB)).prod * φ (ofTree p.2)).sum

/-- The negative part is `−R` applied to the Bogolyubov preparation, `φ₋(T) = −R(φ̃(T))`. -/
theorem birkhoffMinusTree_eq_neg_op_prep (T : UnorderedTree α) :
    birkhoffMinusTree φ RB T = -RB.op (birkhoffPrepTree φ RB T) := by
  rw [birkhoffMinusTree]
  simp only [Multiset.attach_map_val' _ (birkhoffMinusTree φ RB)]
  exact congrArg (fun s ↦ -RB.op s.sum) (Multiset.attach_map_val' _
    fun p : Forest (UnorderedTree α) × UnorderedTree α ↦
      (p.1.map (birkhoffMinusTree φ RB)).prod * φ (ofTree p.2))

/-- The renormalized part on a tree, `φ₊(T) = (1−R)(φ̃(T)) = φ̃(T) − R(φ̃(T))`. -/
noncomputable def birkhoffPlusTree (T : UnorderedTree α) : ℛ :=
  birkhoffPrepTree φ RB T - RB.op (birkhoffPrepTree φ RB T)

/-- The renormalized and negative parts recover the preparation, `φ₊(T) = φ̃(T) + φ₋(T)`. -/
theorem birkhoffPlusTree_eq_prep_add_minus (T : UnorderedTree α) :
    birkhoffPlusTree φ RB T = birkhoffPrepTree φ RB T + birkhoffMinusTree φ RB T := by
  rw [birkhoffPlusTree, birkhoffMinusTree_eq_neg_op_prep]; ring

/-! ### `φ₊` as an algebra hom (the renormalized character) -/

/-- The renormalized character `φ₊`, `birkhoffPlusTree` extended multiplicatively to forests,
    an algebra homomorphism into `range (1 − R)`. -/
noncomputable def birkhoffPlus : ConnesKreimer R (UnorderedTree α) →ₐ[R] ℛ :=
  aeval (birkhoffPlusTree φ RB)

/-- `φ₊` on a forest basis element is the product of `φ₊` over its trees. -/
@[simp] theorem birkhoffPlus_apply_of' (F : Forest (UnorderedTree α)) :
    birkhoffPlus φ RB (of' F) = (F.map (birkhoffPlusTree φ RB)).prod :=
  aeval_of' _ F

/-- `φ₊` on a single tree generator agrees with `birkhoffPlusTree`. -/
@[simp] theorem birkhoffPlus_apply_ofTree (T : UnorderedTree α) :
    birkhoffPlus φ RB (ofTree T) = birkhoffPlusTree φ RB T :=
  aeval_ofTree _ T

/-! ### The Birkhoff factorization `φ₊ = φ₋ ⋆ φ` -/

/-- The Birkhoff factorization `φ₊ = φ₋ ⋆ φ` on generators. On each tree the convolution
    `φ₋ ⋆ φ`, written as `mul' ∘ (φ₋ ⊗ φ) ∘ comul` (`LinearMap.convMul_apply`), recovers the
    renormalized part `φ₊`.
    Needs `φ` unital (`φ 1 = 1`), as characters are.

    Proof route: `comulAlgHomN (ofTree T) = comulTreeN T = ofTree T ⊗ 1 + Σ_{(cf,rem) ∈
    cutSummandsN T} of' cf ⊗ ofTree rem`. Pushing `mul' ∘ map φ₋ φ` through that sum (via
    `map_multiset_sum` / `TensorProduct.map_tmul` / `LinearMap.mul'_apply`, with `birkhoffMinus`
    on `ofTree`/`of'` from the `AddMonoidAlgebra.lift`) gives `φ₋(ofTree T)·φ(1) + Σ φ₋(of' cf)·
    φ(ofTree rem) = birkhoffMinusTree T + birkhoffPrepTree T`, which is `birkhoffPlusTree T` by
    `birkhoffPlusTree_eq_prep_add_minus`. -/
theorem birkhoffFactorization_ofTree (hφ : φ 1 = 1) (T : UnorderedTree α) :
    LinearMap.mul' R ℛ
        ((TensorProduct.map (birkhoffMinus φ RB).toLinearMap φ) (comulAlgHomN (ofTree T)))
      = birkhoffPlusTree φ RB T := by
  rw [comulAlgHomN_apply_ofTree, comulTreeN, comulTreeNG]
  simp only [map_add, map_multiset_sum, Multiset.map_map, Function.comp_def,
    TensorProduct.map_tmul, LinearMap.mul'_apply, AlgHom.toLinearMap_apply,
    birkhoffMinus_apply_ofTree, birkhoffMinus_apply_of', hφ, mul_one]
  rw [← birkhoffPrepTree, birkhoffPlusTree_eq_prep_add_minus]
  exact add_comm _ _

/-! ### The `R = id` specialization recovers the Hopf antipode

The Bogolyubov recursion builds `φ₋` by the *same* `cutSummandsN`/weight
recursion as the Hopf antipode `antipodeTreeN`, with two
substitutions: the character value `φ (ofTree rem)` in place of the canonical embedding
`ofTree rem`, and the Rota–Baxter `−R` in place of bare negation. Taking the trivial
regularization `R = id` (`RotaBaxter.id`, weight `-1`) together with the canonical character
`φ = id` (the identity `H →ₗ[R] H`, which fixes `ofTree rem`) collapses *both* substitutions, so
the Bogolyubov negative part of the identity character is exactly the antipode, the convolution
inverse `S = id⁻¹`. -/

/-- At `R = id` and `φ = id`, the negative part on a tree is the antipode. The Bogolyubov
    negative part `φ₋` of the identity character `id : H →ₗ[R] H` under the trivial weight-`-1`
    Rota–Baxter operator `RotaBaxter.id` coincides with the Hopf antipode `antipodeTreeN`. -/
theorem birkhoffMinusTree_id_eq_antipodeTreeN (T : UnorderedTree α) :
    birkhoffMinusTree (LinearMap.id : ConnesKreimer R (UnorderedTree α) →ₗ[R] _)
      RotaBaxter.id T = antipodeTreeN T := by
  rw [birkhoffMinusTree_eq_neg_op_prep, birkhoffPrepTree, antipodeTreeN_unfold, neg_inj,
    show (RotaBaxter.id (k := R) (A := ConnesKreimer R (UnorderedTree α))).op
      = LinearMap.id from rfl,
    LinearMap.id_coe, id_eq]
  -- The outer `R = id` is gone; match the two sums summand-by-summand.
  refine congrArg Multiset.sum (Multiset.map_congr rfl (fun p hp => ?_))
  -- `φ = id` fixes `ofTree p.2`; the inner products agree by the recursive call on subtrees.
  rw [id_eq]
  exact congrArg (· * ofTree p.2) (congrArg Multiset.prod (Multiset.map_congr rfl
    (fun T_i hT_i => birkhoffMinusTree_id_eq_antipodeTreeN T_i)))
termination_by T.numNodes
decreasing_by exact cutSummandsN_crown_numNodes_lt hp hT_i

/-- At `R = id` and `φ = id`, the negative part is the antipode. The forest-level Bogolyubov
    negative part `φ₋` of the identity character under `RotaBaxter.id` is the Hopf antipode
    `antipodeAlgHomN`. Lifts `birkhoffMinusTree_id_eq_antipodeTreeN` through the shared
    `ConnesKreimer.lift`. -/
theorem birkhoffMinus_id_eq_antipodeAlgHomN :
    birkhoffMinus (LinearMap.id : ConnesKreimer R (UnorderedTree α) →ₗ[R] _) RotaBaxter.id
      = antipodeAlgHomN := by
  refine ConnesKreimer.algHom_ext (fun F => ?_)
  show birkhoffMinus _ _ (of' F) = antipodeAlgHomN (of' F)
  rw [birkhoffMinus_apply_of', antipodeAlgHomN_apply_of']
  exact congrArg Multiset.prod (Multiset.map_congr rfl
    (fun T _ => birkhoffMinusTree_id_eq_antipodeTreeN T))

/-! ### The full Birkhoff factorization `φ = (φ₋ ∘ S) ⋆ φ₊`

The Birkhoff factorization of a character `φ : H → R` is `φ = (φ₋ ∘ S) ⋆ φ₊` (`S` the antipode,
`⋆` the convolution). The keystone above proves the form `φ₊ = φ₋ ⋆ φ` on generators, which also
makes sense over a semiring; over a ring the two forms are equivalent,
because the antipode-composite `φ₋ ∘ S` is the convolution inverse of the character `φ₋`. We work in
the convolution monoid `WithConv (H →ₐ[R] R)` of characters. The target `R` carries
no coproduct, so this is *not* mathlib's `AlgHom.convGroup` (which requires the target to be a
bialgebra) — the inverse of a single character is read off directly from the antipode law. -/

section Factorization

/-- The convolution inverse of a character `ψ` is `ψ ∘ S`. For a character
    `ψ : H →ₐ[R] R`, the antipode-composite `ψ ∘ S` is its left convolution inverse in the
    character monoid `WithConv (H →ₐ[R] R)`. The one-character specialization of the antipode law
    (`AlgHom.antipode_id_cancel`), transported along `ψ` by `comp_convMul_distrib`. It needs only
    `H` Hopf and `R` a commutative algebra; `R` carries no coproduct. -/
theorem antipodeComp_convMul_self (ψ : ConnesKreimer R (UnorderedTree α) →ₐ[R] ℛ) :
    WithConv.toConv (ψ.comp (HopfAlgebra.antipodeAlgHom R (ConnesKreimer R (UnorderedTree α))))
        * WithConv.toConv ψ
      = (1 : WithConv (ConnesKreimer R (UnorderedTree α) →ₐ[R] ℛ)) := by
  have h := AlgHom.comp_convMul_distrib ψ
    (WithConv.toConv (HopfAlgebra.antipodeAlgHom R (ConnesKreimer R (UnorderedTree α))))
    (WithConv.toConv (AlgHom.id R (ConnesKreimer R (UnorderedTree α))))
  rw [AlgHom.antipode_id_cancel, AlgHom.comp_id] at h
  apply WithConv.ofConv_injective
  rw [← h]
  simp only [AlgHom.convOne_def, WithConv.ofConv_toConv, ← AlgHom.comp_assoc,
    Subsingleton.elim (ψ.comp (Algebra.ofId R (ConnesKreimer R (UnorderedTree α))))
      (Algebra.ofId R ℛ)]

/-- The convolution `φ₋ ⋆ φ` on a tree generator is the renormalized value `φ₊(T)`. Restates
    the keystone `birkhoffFactorization_ofTree` as a value in the character monoid, for a character
    `φ : H →ₐ[R] R` (unital via `map_one`). -/
theorem convMul_birkhoffMinus_apply_ofTree (φ : ConnesKreimer R (UnorderedTree α) →ₐ[R] ℛ)
    (T : UnorderedTree α) :
    (WithConv.toConv (birkhoffMinus φ.toLinearMap RB) * WithConv.toConv φ) (ofTree T)
      = birkhoffPlusTree φ.toLinearMap RB T := by
  exact birkhoffFactorization_ofTree φ.toLinearMap RB (map_one φ) T

/-- For a character `φ : H →ₐ[R] R`, the renormalized character `φ₊`, the multiplicative
    `(1 − R)(φ̃)`, is the convolution `φ₋ ⋆ φ` on all of `H`. Lifts the keystone (which holds on
    generators for any linear `φ`) to all forests via the multiplicativity of a character. -/
theorem birkhoffPlus_eq_convMul (φ : ConnesKreimer R (UnorderedTree α) →ₐ[R] ℛ) :
    WithConv.toConv (birkhoffMinus φ.toLinearMap RB) * WithConv.toConv φ
      = WithConv.toConv (birkhoffPlus φ.toLinearMap RB) := by
  apply WithConv.ofConv_injective
  refine ConnesKreimer.algHom_ext (fun F => ?_)
  show (WithConv.toConv (birkhoffMinus φ.toLinearMap RB) * WithConv.toConv φ).ofConv (of' F)
     = birkhoffPlus φ.toLinearMap RB (of' F)
  induction F using Multiset.induction with
  | empty => rw [of'_zero, map_one, map_one]
  | cons T F' ih =>
    have hcons : (of' (T ::ₘ F') : ConnesKreimer R (UnorderedTree α)) = ofTree T * of' F' := by
      rw [← Multiset.singleton_add, of'_add]; rfl
    rw [hcons, map_mul, map_mul, ih, birkhoffPlus_apply_ofTree]
    exact congrArg (· * birkhoffPlus φ.toLinearMap RB (of' F'))
      (convMul_birkhoffMinus_apply_ofTree RB φ T)

/-- The Birkhoff factorization `φ = (φ₋ ∘ S) ⋆ φ₊`. Every character `φ : H →ₐ[R] R` factors
    through its Bogolyubov counterterm `φ₋` (via the antipode `S`) and its renormalized part
    `φ₊ = birkhoffPlus`. Derived from `birkhoffPlus_eq_convMul` and the character-inverse law
    `antipodeComp_convMul_self`, by associativity in the character monoid. -/
theorem birkhoffFactorization (φ : ConnesKreimer R (UnorderedTree α) →ₐ[R] ℛ) :
    WithConv.toConv φ
      = WithConv.toConv ((birkhoffMinus φ.toLinearMap RB).comp
            (HopfAlgebra.antipodeAlgHom R (ConnesKreimer R (UnorderedTree α))))
          * WithConv.toConv (birkhoffPlus φ.toLinearMap RB) := by
  rw [← birkhoffPlus_eq_convMul, ← mul_assoc, antipodeComp_convMul_self, one_mul]

end Factorization

end ConnesKreimer
