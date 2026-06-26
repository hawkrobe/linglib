/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.HopfAlgebraNonplanar
import Linglib.Core.Algebra.RotaBaxter

/-!
# Semiring Birkhoff factorization on the Connes–Kreimer Hopf algebra  `[UPSTREAM]`

The **semiring** form of [marcolli-chomsky-berwick-2025]'s renormalization (Def. 3.1.2, Prop. 3.1.9):
the linguistically operative case, where the target `ℛ` is a commutative *semiring* whose addition
is not invertible — tropical `(ℝ ∪ {−∞}, max, +)`, Viterbi, and Boolean parsing semirings (§3.5,
"Birkhoff Factorization and (Semi)ring Parsing"; §3.5.2, "Minimal Yield as Birkhoff Factorization").

The Hopf algebra `H = ConnesKreimer R (Nonplanar α)` of nonplanar rooted forests is unchanged (base
`R` only a commutative *semiring* — the antipode-free factorization needs no negation, so this works
over `R = ℕ`, the base for a Boolean-semiring target), so the entire coproduct/cut infrastructure is
reused. Only the *character target* `ℛ` is a semiring, with a weight-`+1` `RotaBaxterSemiring`
operator `R`. The
Bogolyubov recursion (Prop. 3.1.9, eq. (3.1.7)) reads

  `φ̃(x) = φ(x) ⊡ Σ φ₋(x′) ⊙ φ(x″)`,    `φ₋(x) = R(φ̃(x))`,    `φ₊(x) = φ₋(x) ⊡ φ̃(x)`,

with `⊡, ⊙` the semiring addition/multiplication and `R` the *positive* projection (contrast the
ring case `φ₋ = −R(φ̃)`, `φ₊ = (1−R)(φ̃)`). Because a semiring has no antipode, only the form
`φ₊ = φ₋ ⋆ φ` (Def. 3.1.6) is available — there is no `φ = (φ₋ ∘ S) ⋆ φ₊` (Def. 3.1.5).

## Main definitions

- `birkhoffMinusTree φ R T` / `birkhoffMinus φ R`: the Bogolyubov negative part `φ₋ = R(φ̃)` on a
  tree, and as an algebra hom `H →ₐ[R] ℛ`.
- `birkhoffPrepTree φ R T`: the Bogolyubov preparation `φ̃`.
- `birkhoffPlusTree φ R T`: the renormalized part `φ₊ = φ̃ + φ₋`.

## Main results

- `birkhoffFactorization_ofTree`: `φ₊ = φ₋ ⋆ φ` on generators (Def. 3.1.6, Prop. 3.1.9 eq. (3.1.7)).

## References

[marcolli-chomsky-berwick-2025] (Def. 3.1.2, Def. 3.1.6, Prop. 3.1.9, Rem. 3.1.10)
-/

namespace RootedTree.ConnesKreimer.SemiringRenorm

open scoped TensorProduct

variable {R ℛ : Type*} [CommSemiring R] [CommSemiring ℛ] [Algebra R ℛ] {α : Type*}
  (φ : ConnesKreimer R (Nonplanar α) →ₗ[R] ℛ) (RB : RotaBaxterSemiring ℛ)

set_option linter.unusedVariables false in
/-- **The Bogolyubov negative part `φ₋` on a single tree** (semiring, weight `+1`;
    [marcolli-chomsky-berwick-2025] Prop. 3.1.9):
    `φ₋(T) = R(Σ_{(cf,rem) ∈ cutSummandsN T} (Π_{Tᵢ ∈ cf} φ₋(Tᵢ)) · φ(ofTree rem))`. The semiring
    analogue of the ring `birkhoffMinusTree`, with the *positive* projection `R` in place of `−R`;
    well-founded on `T.depth`. -/
noncomputable def birkhoffMinusTree (T : Nonplanar α) : ℛ :=
  RB.op ((cutSummandsN T).attach.map (fun ⟨pf, h_mem⟩ =>
      (pf.1.attach.map (fun ⟨T_i, h_T_i⟩ => birkhoffMinusTree T_i)).prod * φ (ofTree pf.2))).sum
termination_by T.depth
decreasing_by exact cutSummandsN_subtree_depth_lt T pf.1 pf.2 h_mem T_i h_T_i

/-- **`φ₋` extended multiplicatively to forests**, as a `MonoidHom`. Mirrors the ring
    `birkhoffMinusMonoidHom`. -/
noncomputable def birkhoffMinusMonoidHom :
    Multiplicative (Forest (Nonplanar α)) →* ℛ where
  toFun F := (F.toAdd.map (birkhoffMinusTree φ RB)).prod
  map_one' := by
    show ((0 : Forest (Nonplanar α)).map _).prod = 1
    rw [Multiset.map_zero, Multiset.prod_zero]
  map_mul' F G := by
    show ((F.toAdd + G.toAdd).map (birkhoffMinusTree φ RB)).prod =
         (F.toAdd.map _).prod * (G.toAdd.map _).prod
    rw [Multiset.map_add, Multiset.prod_add]

/-- **`φ₋` as an algebra hom** `H →ₐ[R] ℛ`, lifting `birkhoffMinusMonoidHom`. Mirrors the ring
    `birkhoffMinus`. -/
noncomputable def birkhoffMinus : ConnesKreimer R (Nonplanar α) →ₐ[R] ℛ :=
  AddMonoidAlgebra.lift R ℛ (Forest (Nonplanar α)) (birkhoffMinusMonoidHom φ RB)

@[simp] theorem birkhoffMinus_apply_of' (F : Forest (Nonplanar α)) :
    birkhoffMinus φ RB (of' F) = (F.map (birkhoffMinusTree φ RB)).prod := by
  show AddMonoidAlgebra.lift R _ _ (birkhoffMinusMonoidHom φ RB) (Finsupp.single F 1) = _
  rw [AddMonoidAlgebra.lift_single, one_smul]
  rfl

@[simp] theorem birkhoffMinus_apply_ofTree (T : Nonplanar α) :
    birkhoffMinus φ RB (ofTree T) = birkhoffMinusTree φ RB T := by
  unfold ofTree
  rw [birkhoffMinus_apply_of', Multiset.map_singleton, Multiset.prod_singleton]

/-- **The Bogolyubov preparation `φ̃`** ([marcolli-chomsky-berwick-2025] Prop. 3.1.9):
    `φ̃(T) = Σ_{(cf,rem) ∈ cutSummandsN T} (Π_{Tᵢ ∈ cf} φ₋(Tᵢ)) · φ(ofTree rem)`, of which the
    negative part is `φ₋(T) = R(φ̃(T))` and the renormalized part is `φ₊(T) = φ̃(T) + φ₋(T)`. -/
noncomputable def birkhoffPrepTree (T : Nonplanar α) : ℛ :=
  ((cutSummandsN T).attach.map (fun ⟨pf, _⟩ =>
      (pf.1.attach.map (fun ⟨T_i, _⟩ => birkhoffMinusTree φ RB T_i)).prod * φ (ofTree pf.2))).sum

/-- The Bogolyubov preparation in non-`attach`-decorated form. Mirrors the ring
    `birkhoffPrepTree_unfold`. -/
theorem birkhoffPrepTree_unfold (T : Nonplanar α) :
    birkhoffPrepTree φ RB T = ((cutSummandsN T).map
      (fun p => (p.1.map (birkhoffMinusTree φ RB)).prod * φ (ofTree p.2))).sum := by
  rw [birkhoffPrepTree]
  rw [show (cutSummandsN T).attach.map (fun (pf : { x // x ∈ cutSummandsN T }) =>
            (pf.val.1.attach.map (fun (T_i : { x // x ∈ pf.val.1 }) =>
              birkhoffMinusTree φ RB T_i.val)).prod * φ (ofTree pf.val.2)) =
          (cutSummandsN T).attach.map (fun (pf : { x // x ∈ cutSummandsN T }) =>
            (pf.val.1.map (birkhoffMinusTree φ RB)).prod * φ (ofTree pf.val.2)) from by
    refine Multiset.map_congr rfl (fun ⟨pf, _⟩ _ => ?_)
    show (pf.1.attach.map (fun T_i => birkhoffMinusTree φ RB T_i.val)).prod * _ =
         (pf.1.map (birkhoffMinusTree φ RB)).prod * _
    congr 1
    exact congrArg Multiset.prod (Multiset.attach_map_val' _ _)]
  exact congrArg Multiset.sum (@Multiset.attach_map_val'
    (Forest (Nonplanar α) × Nonplanar α) _ (cutSummandsN T)
    (fun p => (p.1.map (birkhoffMinusTree φ RB)).prod * φ (ofTree p.2)))

/-- `φ₋(T) = R(φ̃(T))`: the negative part is the positive projection `R` of the preparation. -/
theorem birkhoffMinusTree_eq_op_prep (T : Nonplanar α) :
    birkhoffMinusTree φ RB T = RB.op (birkhoffPrepTree φ RB T) := by
  rw [birkhoffMinusTree, birkhoffPrepTree]

/-- **The renormalized part `φ₊` on a single tree** ([marcolli-chomsky-berwick-2025] Prop. 3.1.9):
    `φ₊(T) = φ̃(T) + φ₋(T)` (the semiring `φ₋ ⊡ φ̃`) — the consistency-checked value. -/
noncomputable def birkhoffPlusTree (T : Nonplanar α) : ℛ :=
  birkhoffPrepTree φ RB T + birkhoffMinusTree φ RB T

/-- **Semiring Birkhoff factorization on generators** ([marcolli-chomsky-berwick-2025] Def. 3.1.6,
    Prop. 3.1.9 eq. (3.1.7), `φ₊ = φ₋ ⋆ φ`): on each tree generator the convolution `φ₋ ⋆ φ` —
    `mul' ∘ (φ₋ ⊗ φ) ∘ comul` — recovers the renormalized part `φ₊`. Needs `φ` unital (`φ 1 = 1`).
    Same proof as the ring keystone (the identity is pure coproduct bookkeeping, sign-agnostic). -/
theorem birkhoffFactorization_ofTree (hφ : φ 1 = 1) (T : Nonplanar α) :
    LinearMap.mul' R ℛ
        ((TensorProduct.map (birkhoffMinus φ RB).toLinearMap φ) (comulAlgHomN (ofTree T)))
      = birkhoffPlusTree φ RB T := by
  rw [comulAlgHomN_apply_ofTree, comulTreeN]
  simp only [map_add, map_multiset_sum, Multiset.map_map, Function.comp_def,
    TensorProduct.map_tmul, LinearMap.mul'_apply, AlgHom.toLinearMap_apply,
    birkhoffMinus_apply_ofTree, birkhoffMinus_apply_of', hφ, mul_one]
  rw [← birkhoffPrepTree_unfold, birkhoffPlusTree]
  exact add_comm _ _

end RootedTree.ConnesKreimer.SemiringRenorm
