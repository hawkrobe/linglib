/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.HopfAlgebraNonplanar
import Linglib.Core.Algebra.RotaBaxter
import Mathlib.RingTheory.Coalgebra.Convolution

/-!
# Birkhoff factorization on the Connes–Kreimer Hopf algebra  `[UPSTREAM]`

[marcolli-chomsky-berwick-2025]'s renormalization of a character (Prop. 3.1.7): given a character
`φ : H → ℛ` from the Hopf algebra `H` of nonplanar rooted trees into a commutative algebra `ℛ`
carrying a weight-`-1` Rota–Baxter operator `R`, the **Bogolyubov recursion** splits `φ` into a
"meaningless part" `φ₋` and a renormalized, consistency-checked part `φ₊`. This is the algebraic
core of the "single map that recursively modifies an assignment of semantic values so as to
incorporate the consistency checking over all substructures."

The negative part `φ₋` is built by the *same* `cutSummandsN`/depth recursion as the Hopf antipode
`antipodeTreeN`, with two substitutions: the canonical embedding `ofTree rem` becomes the character
value `φ (ofTree rem) ∈ ℛ`, and the bare negation becomes `−R`. Indeed `antipodeTreeN` is the
`R = id`, canonical-character specialization of this recursion (`S(x) = −x − Σ S(x′)·x″`).

## Main definitions

- `birkhoffMinusTree φ R T`: the Bogolyubov negative part `φ₋` on a single tree.
- `birkhoffMinusMonoidHom φ R`: `φ₋` extended multiplicatively to forests.
- `birkhoffMinus φ R`: `φ₋` as an algebra hom `H →ₐ[R] ℛ` ([marcolli-chomsky-berwick-2025]:
  `φ₋` is an algebra hom into `range R = ℛ₋`).

## References

[marcolli-chomsky-berwick-2025] (Prop. 3.1.7, Def. 3.1.1)
-/

namespace RootedTree.ConnesKreimer

variable {R ℛ : Type*} [CommRing R] [CommRing ℛ] [Algebra R ℛ] {α : Type*}
  (φ : ConnesKreimer R (Nonplanar α) →ₗ[R] ℛ) (RB : RotaBaxter R ℛ (-1))

/-- **The Bogolyubov negative part `φ₋` on a single tree** ([marcolli-chomsky-berwick-2025]
    Prop. 3.1.7): `φ₋(T) = −R(Σ_{(cf,rem) ∈ cutSummandsN T} (Π_{Tᵢ ∈ cf} φ₋(Tᵢ)) · φ(ofTree rem))`.
    Models `antipodeTreeN` with the character value `φ(ofTree rem)` in place of `ofTree rem` and
    the Rota–Baxter `−R` in place of bare negation; well-founded on `T.depth`. -/
noncomputable def birkhoffMinusTree (T : Nonplanar α) : ℛ :=
  - RB.op ((cutSummandsN T).attach.map (fun ⟨pf, h_mem⟩ =>
      (pf.1.attach.map (fun ⟨T_i, h_T_i⟩ => birkhoffMinusTree T_i)).prod * φ (ofTree pf.2))).sum
termination_by T.depth
decreasing_by exact cutSummandsN_subtree_depth_lt T pf.1 pf.2 h_mem T_i h_T_i

/-- **`φ₋` extended multiplicatively to forests**, as a `MonoidHom` on `Multiplicative (Forest …)`.
    Mirrors `antipodeMonoidHomN`. -/
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

/-- **`φ₋` as an algebra hom** `H →ₐ[R] ℛ`, lifting `birkhoffMinusMonoidHom` via
    `AddMonoidAlgebra.lift`. Mirrors `antipodeAlgHomN`. -/
noncomputable def birkhoffMinus : ConnesKreimer R (Nonplanar α) →ₐ[R] ℛ :=
  AddMonoidAlgebra.lift R ℛ (Forest (Nonplanar α)) (birkhoffMinusMonoidHom φ RB)

/-- `φ₋` on a forest basis element is the product of `φ₋` over its trees. Mirrors
    `antipodeAlgHomN_apply_of'`. -/
@[simp] theorem birkhoffMinus_apply_of' (F : Forest (Nonplanar α)) :
    birkhoffMinus φ RB (of' F) = (F.map (birkhoffMinusTree φ RB)).prod := by
  show AddMonoidAlgebra.lift R _ _ (birkhoffMinusMonoidHom φ RB) (Finsupp.single F 1) = _
  rw [AddMonoidAlgebra.lift_single, one_smul]
  rfl

/-- `φ₋` on a single tree generator agrees with `birkhoffMinusTree`. Mirrors
    `antipodeAlgHomN_apply_ofTree`. -/
@[simp] theorem birkhoffMinus_apply_ofTree (T : Nonplanar α) :
    birkhoffMinus φ RB (ofTree T) = birkhoffMinusTree φ RB T := by
  unfold ofTree
  rw [birkhoffMinus_apply_of', Multiset.map_singleton, Multiset.prod_singleton]

/-! ### The Bogolyubov preparation and the renormalized part -/

/-- **The Bogolyubov preparation `φ̃`** ([marcolli-chomsky-berwick-2025] Rem. 3.1.8):
    `φ̃(T) = Σ_{(cf,rem) ∈ cutSummandsN T} (Π_{Tᵢ ∈ cf} φ₋(Tᵢ)) · φ(ofTree rem)`, of which the
    negative part is `φ₋(T) = −R(φ̃(T))` and the renormalized part is `φ₊(T) = (1−R)(φ̃(T))`. -/
noncomputable def birkhoffPrepTree (T : Nonplanar α) : ℛ :=
  ((cutSummandsN T).attach.map (fun ⟨pf, _⟩ =>
      (pf.1.attach.map (fun ⟨T_i, _⟩ => birkhoffMinusTree φ RB T_i)).prod * φ (ofTree pf.2))).sum

/-- The Bogolyubov preparation in non-`attach`-decorated form: the `attach` def keeps the
    membership info for well-foundedness, this strips it for downstream proofs. Mirrors
    `antipodeTreeN_unfold`. -/
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

/-- `φ₋(T) = −R(φ̃(T))`: the negative part is `−R` applied to the Bogolyubov preparation. -/
theorem birkhoffMinusTree_eq_neg_op_prep (T : Nonplanar α) :
    birkhoffMinusTree φ RB T = - RB.op (birkhoffPrepTree φ RB T) := by
  rw [birkhoffMinusTree, birkhoffPrepTree]

/-- **The renormalized part `φ₊` on a single tree** ([marcolli-chomsky-berwick-2025] Prop. 3.1.7):
    `φ₊(T) = (1−R)(φ̃(T)) = φ̃(T) − R(φ̃(T))` — the consistency-checked value. -/
noncomputable def birkhoffPlusTree (T : Nonplanar α) : ℛ :=
  birkhoffPrepTree φ RB T - RB.op (birkhoffPrepTree φ RB T)

/-- `φ₊(T) = φ̃(T) + φ₋(T)`: the renormalized and negative parts recover the preparation. -/
theorem birkhoffPlusTree_eq_prep_add_minus (T : Nonplanar α) :
    birkhoffPlusTree φ RB T = birkhoffPrepTree φ RB T + birkhoffMinusTree φ RB T := by
  rw [birkhoffPlusTree, birkhoffMinusTree_eq_neg_op_prep]; ring

/-! ### The Birkhoff factorization `φ₊ = φ₋ ⋆ φ` -/

/-- **Birkhoff factorization on generators** ([marcolli-chomsky-berwick-2025] Def. 3.1.6,
    `φ₊ = φ₋ ⋆ φ`): on each tree generator the convolution `φ₋ ⋆ φ` — written explicitly as
    `mul' ∘ (φ₋ ⊗ φ) ∘ comul` (`LinearMap.convMul_apply`) — recovers the renormalized part `φ₊`.
    Needs `φ` unital (`φ 1 = 1`), as characters are.

    Proof route: `comulAlgHomN (ofTree T) = comulTreeN T = ofTree T ⊗ 1 + Σ_{(cf,rem) ∈
    cutSummandsN T} of' cf ⊗ ofTree rem`. Pushing `mul' ∘ map φ₋ φ` through that sum (via
    `map_multiset_sum` / `TensorProduct.map_tmul` / `LinearMap.mul'_apply`, with `birkhoffMinus`
    on `ofTree`/`of'` from the `AddMonoidAlgebra.lift`) gives `φ₋(ofTree T)·φ(1) + Σ φ₋(of' cf)·
    φ(ofTree rem) = birkhoffMinusTree T + birkhoffPrepTree T`, which is `birkhoffPlusTree T` by
    `birkhoffPlusTree_eq_prep_add_minus`. -/
theorem birkhoffFactorization_ofTree (hφ : φ 1 = 1) (T : Nonplanar α) :
    LinearMap.mul' R ℛ
        ((TensorProduct.map (birkhoffMinus φ RB).toLinearMap φ) (comulAlgHomN (ofTree T)))
      = birkhoffPlusTree φ RB T := by
  rw [comulAlgHomN_apply_ofTree, comulTreeN]
  simp only [map_add, map_multiset_sum, Multiset.map_map, Function.comp_def,
    TensorProduct.map_tmul, LinearMap.mul'_apply, AlgHom.toLinearMap_apply,
    birkhoffMinus_apply_ofTree, birkhoffMinus_apply_of', hφ, mul_one]
  rw [← birkhoffPrepTree_unfold, birkhoffPlusTree_eq_prep_add_minus]
  exact add_comm _ _

end RootedTree.ConnesKreimer
