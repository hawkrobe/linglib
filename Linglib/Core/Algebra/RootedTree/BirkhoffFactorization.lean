/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.HopfAlgebraNonplanar
import Linglib.Core.Algebra.RotaBaxter
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.RingTheory.HopfAlgebra.Convolution

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
`R = id`, canonical-character specialization of this recursion (`S(x) = −x − Σ S(x′)·x″`),
proved here as `birkhoffMinusTree_id_eq_antipodeTreeN`.

For a genuine character `φ : H →ₐ[R] ℛ` (a *multiplicative* assignment, Def. 3.1.3) the two parts
satisfy the full factorization `φ = (φ₋ ∘ S) ⋆ φ₊` (Def. 3.1.5), proved in `birkhoffFactorization`.
We work in the character convolution monoid `WithConv (H →ₐ[R] ℛ)`; per Rem. 3.1.4 the target `ℛ`
carries no coproduct, so this is *not* mathlib's `AlgHom.convGroup` (target-bialgebra) — the
convolution inverse `φ₋ ∘ S` of the character `φ₋` is read off directly from the antipode law
(`antipodeComp_convMul_self`).

## Main definitions

- `birkhoffMinusTree φ R T` / `birkhoffMinus φ R`: the Bogolyubov negative part `φ₋` on a tree, and
  as an algebra hom `H →ₐ[R] ℛ` into `range R = ℛ₋`.
- `birkhoffPlusTree φ R T` / `birkhoffPlus φ R`: the renormalized part `φ₊ = (1 − R)(φ̃)` on a tree,
  and as an algebra hom `H →ₐ[R] ℛ` into `range (1 − R) = ℛ₊`.

## Main results

- `birkhoffFactorization_ofTree`: `φ₊ = φ₋ ⋆ φ` on generators (Def. 3.1.6), for any linear `φ`.
- `birkhoffPlus_eq_convMul`: `φ₊ = φ₋ ⋆ φ` on *all* of `H`, for a character `φ` (Def. 3.1.6).
- `birkhoffFactorization`: `φ = (φ₋ ∘ S) ⋆ φ₊` for a character `φ` (Def. 3.1.5, eq. (3.1.4)).
- `birkhoffMinusTree_id_eq_antipodeTreeN`: the `R = id` counterterm is the Hopf antipode.

## References

[marcolli-chomsky-berwick-2025] (Def. 3.1.1, Def. 3.1.3, Rem. 3.1.4, Def. 3.1.5, Def. 3.1.6,
Prop. 3.1.7, Rem. 3.1.8)
-/

namespace RootedTree.ConnesKreimer

open scoped TensorProduct

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
    `ConnesKreimer.lift`. Mirrors `antipodeAlgHomN`. -/
noncomputable def birkhoffMinus : ConnesKreimer R (Nonplanar α) →ₐ[R] ℛ :=
  ConnesKreimer.lift (birkhoffMinusMonoidHom φ RB)

/-- `φ₋` on a forest basis element is the product of `φ₋` over its trees. Mirrors
    `antipodeAlgHomN_apply_of'`. -/
@[simp] theorem birkhoffMinus_apply_of' (F : Forest (Nonplanar α)) :
    birkhoffMinus φ RB (of' F) = (F.map (birkhoffMinusTree φ RB)).prod := by
  rw [birkhoffMinus, ConnesKreimer.lift_of']
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

/-! ### `φ₊` as an algebra hom (the renormalized character) -/

/-- **`φ₊` extended multiplicatively to forests**, as a `MonoidHom`. Mirrors
    `birkhoffMinusMonoidHom`; the renormalized character `φ₊ : H → R₊` of
    [marcolli-chomsky-berwick-2025] Prop. 3.1.7 is an algebra hom into `range (1 − R)`. -/
noncomputable def birkhoffPlusMonoidHom :
    Multiplicative (Forest (Nonplanar α)) →* ℛ where
  toFun F := (F.toAdd.map (birkhoffPlusTree φ RB)).prod
  map_one' := by
    show ((0 : Forest (Nonplanar α)).map _).prod = 1
    rw [Multiset.map_zero, Multiset.prod_zero]
  map_mul' F G := by
    show ((F.toAdd + G.toAdd).map (birkhoffPlusTree φ RB)).prod =
         (F.toAdd.map _).prod * (G.toAdd.map _).prod
    rw [Multiset.map_add, Multiset.prod_add]

/-- **`φ₊` as an algebra hom** `H →ₐ[R] ℛ`, lifting `birkhoffPlusMonoidHom`. Mirrors
    `birkhoffMinus`; the multiplicative extension of `birkhoffPlusTree` is automatically an
    algebra hom, so this is the renormalized character `φ₊`. -/
noncomputable def birkhoffPlus : ConnesKreimer R (Nonplanar α) →ₐ[R] ℛ :=
  ConnesKreimer.lift (birkhoffPlusMonoidHom φ RB)

/-- `φ₊` on a forest basis element is the product of `φ₊` over its trees. Mirrors
    `birkhoffMinus_apply_of'`. -/
@[simp] theorem birkhoffPlus_apply_of' (F : Forest (Nonplanar α)) :
    birkhoffPlus φ RB (of' F) = (F.map (birkhoffPlusTree φ RB)).prod := by
  rw [birkhoffPlus, ConnesKreimer.lift_of']
  rfl

/-- `φ₊` on a single tree generator agrees with `birkhoffPlusTree`. Mirrors
    `birkhoffMinus_apply_ofTree`. -/
@[simp] theorem birkhoffPlus_apply_ofTree (T : Nonplanar α) :
    birkhoffPlus φ RB (ofTree T) = birkhoffPlusTree φ RB T := by
  unfold ofTree
  rw [birkhoffPlus_apply_of', Multiset.map_singleton, Multiset.prod_singleton]

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

/-! ### The `R = id` specialization recovers the Hopf antipode

[marcolli-chomsky-berwick-2025] Prop. 3.1.7 builds `φ₋` by the *same* `cutSummandsN`/depth
recursion as the Hopf antipode `antipodeTreeN` (the inductive antipode of §1.2), with two
substitutions: the character value `φ (ofTree rem)` in place of the canonical embedding
`ofTree rem`, and the Rota–Baxter `−R` in place of bare negation. Taking the trivial
regularization `R = id` (`RotaBaxter.id`, weight `-1`) together with the canonical character
`φ = id` (the identity `H →ₗ[R] H`, which fixes `ofTree rem`) collapses *both* substitutions, so
the Bogolyubov negative part of the identity character is exactly the antipode. This is the
algebraic content of the book's remark that the antipode "is like a group inverse": `S = id⁻¹`
in the convolution group, recovered here as the `R = id` Birkhoff counterterm. -/

/-- **`R = id`, `φ = id` recovers the antipode on a tree.** The Bogolyubov negative part `φ₋`
    (Prop. 3.1.7) of the identity character `id : H →ₗ[R] H` under the trivial weight-`-1`
    Rota–Baxter operator `RotaBaxter.id` coincides with the Hopf antipode `antipodeTreeN`. -/
theorem birkhoffMinusTree_id_eq_antipodeTreeN (T : Nonplanar α) :
    birkhoffMinusTree (LinearMap.id : ConnesKreimer R (Nonplanar α) →ₗ[R] _)
      RotaBaxter.id T = antipodeTreeN T := by
  rw [birkhoffMinusTree_eq_neg_op_prep, birkhoffPrepTree_unfold, antipodeTreeN_unfold, neg_inj,
    show (RotaBaxter.id (k := R) (A := ConnesKreimer R (Nonplanar α))).op = LinearMap.id from rfl,
    LinearMap.id_coe, id_eq]
  -- The outer `R = id` is gone; match the two sums summand-by-summand.
  refine congrArg Multiset.sum (Multiset.map_congr rfl (fun p hp => ?_))
  -- `φ = id` fixes `ofTree p.2`; the inner products agree by the recursive call on subtrees.
  rw [id_eq]
  exact congrArg (· * ofTree p.2) (congrArg Multiset.prod (Multiset.map_congr rfl
    (fun T_i hT_i => birkhoffMinusTree_id_eq_antipodeTreeN T_i)))
termination_by T.depth
decreasing_by exact cutSummandsN_subtree_depth_lt T p.1 p.2 hp T_i hT_i

/-- **`R = id`, `φ = id` recovers the antipode as an algebra hom.** The forest-level Bogolyubov
    negative part `φ₋` of the identity character under `RotaBaxter.id` is the Hopf antipode
    `antipodeAlgHomN`. Lifts `birkhoffMinusTree_id_eq_antipodeTreeN` through the shared
    `ConnesKreimer.lift`. -/
theorem birkhoffMinus_id_eq_antipodeAlgHomN :
    birkhoffMinus (LinearMap.id : ConnesKreimer R (Nonplanar α) →ₗ[R] _) RotaBaxter.id
      = antipodeAlgHomN := by
  refine ConnesKreimer.algHom_ext (fun F => ?_)
  show birkhoffMinus _ _ (of' F) = antipodeAlgHomN (of' F)
  rw [birkhoffMinus_apply_of', antipodeAlgHomN_apply_of']
  exact congrArg Multiset.prod (Multiset.map_congr rfl
    (fun T _ => birkhoffMinusTree_id_eq_antipodeTreeN T))

/-! ### The full Birkhoff factorization `φ = (φ₋ ∘ S) ⋆ φ₊`  (MCB Def. 3.1.5)

[marcolli-chomsky-berwick-2025] Def. 3.1.5 calls `φ = (φ₋ ∘ S) ⋆ φ₊` *the* Birkhoff factorization
of a character `φ : H → R` (`S` the antipode, `⋆` the convolution). The keystone above proves the
*semiring-form* `φ₊ = φ₋ ⋆ φ` (Def. 3.1.6) on generators; over a ring the two forms are equivalent,
because the antipode-composite `φ₋ ∘ S` is the convolution inverse of the character `φ₋`. We work in
the convolution monoid `WithConv (H →ₐ[R] R)` of characters. Per Rem. 3.1.4 the target `R` carries
no coproduct, so this is *not* mathlib's `AlgHom.convGroup` (which requires the target to be a
bialgebra) — the inverse of a single character is read off directly from the antipode law. The
factorization needs `H` to be a Hopf algebra, hence `CharZero R` and `NoZeroDivisors R`. -/

section Factorization

variable [CharZero R] [NoZeroDivisors R]

/-- **The convolution inverse of a character is `character ∘ S`.** For a character
    `ψ : H →ₐ[R] R`, the antipode-composite `ψ ∘ S` is its left convolution inverse in the
    character monoid `WithConv (H →ₐ[R] R)`. The one-character specialization of the antipode law
    (`AlgHom.antipode_id_cancel`), transported along `ψ` by `comp_convMul_distrib`. Per Rem. 3.1.4
    it needs only `H` Hopf and `R` a commutative algebra — `R` carries no coproduct. -/
theorem antipodeComp_convMul_self (ψ : ConnesKreimer R (Nonplanar α) →ₐ[R] ℛ) :
    WithConv.toConv (ψ.comp (HopfAlgebra.antipodeAlgHom R (ConnesKreimer R (Nonplanar α))))
        * WithConv.toConv ψ
      = (1 : WithConv (ConnesKreimer R (Nonplanar α) →ₐ[R] ℛ)) := by
  have h := AlgHom.comp_convMul_distrib ψ
    (WithConv.toConv (HopfAlgebra.antipodeAlgHom R (ConnesKreimer R (Nonplanar α))))
    (WithConv.toConv (AlgHom.id R (ConnesKreimer R (Nonplanar α))))
  rw [AlgHom.antipode_id_cancel, AlgHom.comp_id] at h
  apply WithConv.ofConv_injective
  rw [← h]
  simp only [AlgHom.convOne_def, WithConv.ofConv_toConv, ← AlgHom.comp_assoc,
    Subsingleton.elim (ψ.comp (Algebra.ofId R (ConnesKreimer R (Nonplanar α))))
      (Algebra.ofId R ℛ)]

omit [CharZero R] [NoZeroDivisors R] in
/-- `Algebra.TensorProduct.lift` of two characters agrees with `mul' ∘ map` on every tensor: the
    bridge between the character convolution (`AlgHom.convMul_apply`, `lift` form) and the keystone
    (`mul' ∘ map` form). -/
private theorem lift_eq_mulPrime_map (f g : ConnesKreimer R (Nonplanar α) →ₐ[R] ℛ)
    (z : ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) :
    Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) z =
      LinearMap.mul' R ℛ (TensorProduct.map f.toLinearMap g.toLinearMap z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [Algebra.TensorProduct.lift_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply]; rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- **The convolution `φ₋ ⋆ φ` on a tree generator is the renormalized value `φ₊(T)`.** Restates
    the keystone `birkhoffFactorization_ofTree` as a value in the character monoid, for a character
    `φ : H →ₐ[R] R` (unital via `map_one`). -/
theorem convMul_birkhoffMinus_apply_ofTree (φ : ConnesKreimer R (Nonplanar α) →ₐ[R] ℛ)
    (T : Nonplanar α) :
    (WithConv.toConv (birkhoffMinus φ.toLinearMap RB) * WithConv.toConv φ) (ofTree T)
      = birkhoffPlusTree φ.toLinearMap RB T := by
  rw [AlgHom.convMul_apply, lift_eq_mulPrime_map]
  exact birkhoffFactorization_ofTree φ.toLinearMap RB (map_one φ) T

/-- **The full Birkhoff factorization `φ₊ = φ₋ ⋆ φ`** ([marcolli-chomsky-berwick-2025] Def. 3.1.6)
    on *all* of `H` for a character `φ : H →ₐ[R] R`: the renormalized character `φ₊` (the
    multiplicative `(1 − R)(φ̃)`) is the convolution `φ₋ ⋆ φ`. Lifts the keystone (which holds on
    generators for any linear `φ`) to all forests via the multiplicativity of a character. -/
theorem birkhoffPlus_eq_convMul (φ : ConnesKreimer R (Nonplanar α) →ₐ[R] ℛ) :
    WithConv.toConv (birkhoffMinus φ.toLinearMap RB) * WithConv.toConv φ
      = WithConv.toConv (birkhoffPlus φ.toLinearMap RB) := by
  apply WithConv.ofConv_injective
  refine ConnesKreimer.algHom_ext (fun F => ?_)
  show (WithConv.toConv (birkhoffMinus φ.toLinearMap RB) * WithConv.toConv φ).ofConv (of' F)
     = birkhoffPlus φ.toLinearMap RB (of' F)
  induction F using Multiset.induction with
  | empty => rw [of'_zero, map_one, map_one]
  | cons T F' ih =>
    have hcons : (of' (T ::ₘ F') : ConnesKreimer R (Nonplanar α)) = ofTree T * of' F' := by
      rw [← Multiset.singleton_add, of'_add]; rfl
    rw [hcons, map_mul, map_mul, ih, birkhoffPlus_apply_ofTree]
    exact congrArg (· * birkhoffPlus φ.toLinearMap RB (of' F'))
      (convMul_birkhoffMinus_apply_ofTree RB φ T)

/-- **The Birkhoff factorization `φ = (φ₋ ∘ S) ⋆ φ₊`** ([marcolli-chomsky-berwick-2025] Def. 3.1.5,
    eq. (3.1.4)): every character `φ : H →ₐ[R] R` factors through its Bogolyubov counterterm `φ₋`
    (via the antipode `S`) and renormalized part `φ₊ = birkhoffPlus`. The "meaningless" `φ₋` and
    "meaningful" `φ₊` of [marcolli-chomsky-berwick-2025]'s syntax–semantics interface. Derived from
    `birkhoffPlus_eq_convMul` (Def. 3.1.6 on all `H`) and the character-inverse law
    `antipodeComp_convMul_self`, by associativity in the character monoid. -/
theorem birkhoffFactorization (φ : ConnesKreimer R (Nonplanar α) →ₐ[R] ℛ) :
    WithConv.toConv φ
      = WithConv.toConv ((birkhoffMinus φ.toLinearMap RB).comp
            (HopfAlgebra.antipodeAlgHom R (ConnesKreimer R (Nonplanar α))))
          * WithConv.toConv (birkhoffPlus φ.toLinearMap RB) := by
  rw [← birkhoffPlus_eq_convMul, ← mul_assoc, antipodeComp_convMul_self, one_mul]

end Factorization

end RootedTree.ConnesKreimer
