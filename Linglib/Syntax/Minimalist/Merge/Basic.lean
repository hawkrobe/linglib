import Linglib.Core.Algebra.RootedTree.Coproduct.PruningNonplanar
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Merge operator on the Connes–Kreimer bialgebra of nonplanar forests
[marcolli-chomsky-berwick-2025]

Per [marcolli-chomsky-berwick-2025] §1.3 (Definitions 1.3.1, 1.3.2, 1.3.4),
the linguistic **Merge operator** `M_{S,S'}` for a pair `(S, S') : Nonplanar α`
of accessible terms is the composition

  M_{S,S'} = ⊔ ∘ (B ⊗ id) ∘ δ_{S,S'} ∘ Δ

on the canonical carrier `ConnesKreimer R (Nonplanar α)`, where:

- `Δ` is the merge coproduct (`comulAlgHomN`, the Δ^ρ deletion coproduct);
- `δ_{S,S'}` selects coproduct terms whose left channel equals the 2-element
  forest `{S, S'}` (Def 1.3.1);
- `B ⊗ id` grafts on the left channel: replaces the 2-element forest `{S, S'}`
  with the binary tree `Nonplanar.node lbl {S, S'}` (the label `lbl` of the new
  root is a parameter — the operator layer is agnostic to which label decorates
  the grafted node);
- `⊔` is multiplication on `ConnesKreimer R (Nonplanar α)` (forest disjoint
  union, the algebra structure).

This file builds the building blocks (`gammaMatch`, `deltaMatch`, `graftBinaryAt`)
and assembles `mergeOp`. Bridges to linguistic `Step.apply` live in
`Merge.External` (EM) and `Merge.Internal` (IM).

## Merge coproduct: Δ^ρ, not Δ^d

[marcolli-chomsky-berwick-2025] Def 1.3.4 states merge with the Δ^d
(delete-then-rebinarize) coproduct. The canonical n-ary carrier uses Δ^ρ
(`comulAlgHomN`): Δ^d and Δ^ρ extract the **same** accessible terms, differing
only in the remainder, which `mergePost` discards when grafting the pair — so
merge correctness is unaffected. Δ^ρ is the n-ary-faithful deletion (MCB's
binary Δ^d `+2` is a rebinarization artifact).

The **cost-weighted** Merge `M^ε` (eq. 1.5.1) is deferred: it needs an
ε-weighted Δ^ρ (a `cutTotalDepth` analogue on `cutSummandsN`), not yet in the
substrate.
-/

namespace Minimalist.Merge

open scoped TensorProduct
open RootedTree RootedTree.ConnesKreimer

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq (Nonplanar α)]

/-! ## §1: γ_{S,S'} matching projection (M-C-B Def 1.3.1)

For a fixed pair `(S, S') : Nonplanar α`, `gammaMatch S S'` is the linear
endomorphism of `ConnesKreimer R (Nonplanar α)` that projects onto the basis
element `of' {S, S'}`:

  gammaMatch S S' (of' F) = if F = {S, S'} then of' F else 0

Built as a `ConnesKreimer.linearLift` that maps the `{S, S'}` basis vector to
itself and every other basis vector to zero. -/

/-- The matching projection γ_{S,S'} (M-C-B Def 1.3.1): keeps the coefficient
    of the `{S, S'}` basis element, sends everything else to zero. -/
noncomputable def gammaMatch (S S' : Nonplanar α) :
    ConnesKreimer R (Nonplanar α) →ₗ[R] ConnesKreimer R (Nonplanar α) :=
  ConnesKreimer.linearLift
    (fun F => if F = ({S, S'} : Forest (Nonplanar α)) then of' F else 0)

/-- **γ_{S,S'} acts as a basis-vector projection**: on the basis element
    `of' F`, it returns `of' F` if `F = {S, S'}` and `0` otherwise.
    M-C-B Def 1.3.1. -/
theorem gammaMatch_apply_singleton (S S' : Nonplanar α)
    (F : Forest (Nonplanar α)) :
    gammaMatch (R := R) S S' (of' F) =
      if F = ({S, S'} : Forest (Nonplanar α)) then of' F else 0 := by
  rw [gammaMatch, ConnesKreimer.linearLift_of']

/-! ## §2: δ_{S,S'} matching on the left tensor channel (M-C-B Def 1.3.1)

`deltaMatch S S' = gammaMatch S S' ⊗ id` lifts the matching projection to act on
the left channel of the coproduct output. -/

/-- The matching operator δ_{S,S'} on tensored coproduct output: applies
    `gammaMatch S S'` to the left channel and identity to the right. -/
noncomputable def deltaMatch (S S' : Nonplanar α) :
    (ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) →ₗ[R]
      (ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) :=
  TensorProduct.map (gammaMatch (R := R) S S') LinearMap.id

/-! ## §3: B grafting for binary Merge (M-C-B Def 1.3.2 + Lemma 1.3.3)

`graftBinaryAt lbl S S'` replaces the 2-element forest `{S, S'}` (basis element)
with the binary tree `Nonplanar.node lbl {S, S'}` (also a basis element). All
other basis elements map to zero — we only need this specialized form because
the Merge action's preceding `δ_{S,S'}` step restricts the left channel to
multiples of `{S, S'}` anyway.

The label `lbl` of the grafted root is a parameter: the operator layer is
agnostic to which label decorates the new node (consumers supply the lexical
head). -/

/-- The grafting operator B specialized at the pair `(S, S')` with root label
    `lbl`: maps the basis element `{S, S'}` to `Nonplanar.node lbl {S, S'}`, all
    other basis elements to zero. M-C-B Lemma 1.3.3 for binary Merge. -/
noncomputable def graftBinaryAt (lbl : α) (S S' : Nonplanar α) :
    ConnesKreimer R (Nonplanar α) →ₗ[R] ConnesKreimer R (Nonplanar α) :=
  ConnesKreimer.linearLift
    (fun F => if F = ({S, S'} : Forest (Nonplanar α))
      then of' ({Nonplanar.node lbl {S, S'}} : Forest (Nonplanar α)) else 0)

/-- **B grafts on basis vectors**: on `of' F`, returns
    `of' {Nonplanar.node lbl {S, S'}}` if `F = {S, S'}`, and `0` otherwise.
    Same shape as `gammaMatch_apply_singleton` with a different target. -/
theorem graftBinaryAt_apply_singleton (lbl : α) (S S' : Nonplanar α)
    (F : Forest (Nonplanar α)) :
    graftBinaryAt (R := R) lbl S S' (of' F) =
      if F = ({S, S'} : Forest (Nonplanar α))
        then of' ({Nonplanar.node lbl {S, S'}} : Forest (Nonplanar α))
        else 0 := by
  rw [graftBinaryAt, ConnesKreimer.linearLift_of']

/-! ## §4: Merge operator (M-C-B Def 1.3.4)

`mergeOp lbl S S' = ⊔ ∘ (B ⊗ id) ∘ δ_{S,S'} ∘ Δ^ρ`

The chain:

1. `Δ^ρ` (`comulAlgHomN`) extracts accessible cuts (deletion remainder)
2. `δ_{S,S'}` filters to terms where the cut forest equals `{S, S'}`
3. `(B ⊗ id)` grafts `{S, S'}` into `Nonplanar.node lbl {S, S'}` on the left
4. `⊔` multiplies the two channels back into a single workspace

When no admissible cut produces `{S, S'}` as its cut forest, all terms are
killed by `δ_{S,S'}` and `mergeOp lbl S S' F = 0`. -/

/-- Multiplication on `ConnesKreimer R (Nonplanar α)` lifted to a linear map.
    Wraps mathlib's `Algebra.TensorProduct.lmul'`. -/
noncomputable def mulLin :
    ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) →ₗ[R]
      ConnesKreimer R (Nonplanar α) :=
  (Algebra.TensorProduct.lmul' (S := ConnesKreimer R (Nonplanar α)) R).toLinearMap

/-- **Post-coproduct chain** `⊔ ∘ (B ⊗ id) ∘ δ_{S,S'}` as a single named linear
    map. `mergeOp` factors as `mergePost lbl S S' ∘ comulAlgHomN.toLinearMap`. -/
noncomputable def mergePost (lbl : α) (S S' : Nonplanar α) :
    ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) →ₗ[R]
      ConnesKreimer R (Nonplanar α) :=
  mulLin (R := R) (α := α)
    ∘ₗ TensorProduct.map (graftBinaryAt (R := R) lbl S S') LinearMap.id
    ∘ₗ deltaMatch (R := R) S S'

/-- The Merge operator `M_{S,S'}` per M-C-B Def 1.3.4 (with root label `lbl`).
    Factors as `mergePost lbl S S' ∘ comulAlgHomN`. -/
noncomputable def mergeOp (lbl : α) (S S' : Nonplanar α) :
    ConnesKreimer R (Nonplanar α) →ₗ[R] ConnesKreimer R (Nonplanar α) :=
  mergePost (R := R) (α := α) lbl S S' ∘ₗ comulAlgHomN.toLinearMap

/-! ## §5: Post-coproduct chain on basis tensors

`mergePost lbl S S'` evaluated on an elementary tensor `of' F ⊗ r` is:
- `of' {Nonplanar.node lbl {S, S'}} * r` if `F = {S, S'}`
- `0` otherwise

This is the **load-bearing fact** for proving algebraic Merge agrees with
linguistic `Step.apply`: every basis-tensor term in the coproduct expansion of
`Δ^ρ({S, S'})` either matches the merge target or is annihilated by `δ_{S,S'}`. -/

/-- The post-coproduct chain `mergePost lbl S S'` evaluated on a basis tensor
    `of' F ⊗ r`. -/
theorem mergePost_basis_tensor (lbl : α) (S S' : Nonplanar α)
    (F : Forest (Nonplanar α)) (r : ConnesKreimer R (Nonplanar α)) :
    mergePost (R := R) (α := α) lbl S S' (of' F ⊗ₜ[R] r)
      = if F = ({S, S'} : Forest (Nonplanar α))
          then of' ({Nonplanar.node lbl {S, S'}} : Forest (Nonplanar α)) * r
          else 0 := by
  unfold mergePost deltaMatch
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
      TensorProduct.map_tmul, LinearMap.id_apply, gammaMatch_apply_singleton]
  by_cases hF : F = ({S, S'} : Forest (Nonplanar α))
  · subst hF
    rw [if_pos rfl, TensorProduct.map_tmul, LinearMap.id_apply,
        graftBinaryAt_apply_singleton, if_pos rfl, if_pos rfl]
    show Algebra.TensorProduct.lmul' (S := ConnesKreimer R (Nonplanar α)) R _ = _
    exact Algebra.TensorProduct.lmul'_apply_tmul _ _
  · rw [if_neg hF, TensorProduct.zero_tmul, if_neg hF]
    simp only [map_zero]

omit [DecidableEq (Nonplanar α)] in
/-- Left-multiplying a `single` basis vector by `of' F` concatenates forests:
    `of' F * single G r = single (F + G) r`. -/
private theorem of'_mul_single (F G : Forest (Nonplanar α)) (r : R) :
    of' (R := R) F * single G r = single (F + G) r := by
  rw [smul_single_one G r, mul_smul_comm]
  change r • (of' (R := R) F * of' G) = single (F + G) r
  rw [← of'_add]
  exact (smul_single_one (F + G) r).symm

/-- **General γ_{S,S'}-vanishing on a left-multiplied forest**: if `F` is NOT a
    sub-multiset of `{S, S'}`, then `γ_{S,S'}(of' F * a) = 0` for any `a`.

    The hypothesis `¬ F ≤ ({S, S'} : Forest (Nonplanar α))` says `F` cannot
    embed into `{S, S'}` as a sub-multiset: since `F ≤ F + G` always, every
    forest `F + G` produced by left-multiplication misses the `{S, S'}` basis
    element that `γ_{S,S'}` reads. -/
theorem gammaMatch_mul_eq_zero_of_not_le (S S' : Nonplanar α)
    (F : Forest (Nonplanar α))
    (hF : ¬ F ≤ ({S, S'} : Forest (Nonplanar α)))
    (a : ConnesKreimer R (Nonplanar α)) :
    gammaMatch (R := R) S S' (of' F * a) = 0 := by
  induction a using ConnesKreimer.induction_linear with
  | zero => rw [mul_zero, map_zero]
  | add g h hg hh => rw [mul_add, map_add, hg, hh, add_zero]
  | single G r =>
    have hne : F + G ≠ ({S, S'} : Forest (Nonplanar α)) :=
      fun heq => hF (heq ▸ Multiset.le_add_right F G)
    rw [of'_mul_single, gammaMatch]
    simp only [ConnesKreimer.linearLift_single]
    rw [if_neg hne, smul_zero]

/-- **Disjoint-singleton vanishing of γ_{S,S'}** (corollary): if `T ≠ S` and
    `T ≠ S'`, then `γ_{S,S'}(of' {T} * a) = 0`. -/
theorem gammaMatch_singleton_mul_eq_zero (S S' T : Nonplanar α)
    (hT_ne_S : T ≠ S) (hT_ne_S' : T ≠ S') (a : ConnesKreimer R (Nonplanar α)) :
    gammaMatch (R := R) S S' (of' ({T} : Forest (Nonplanar α)) * a) = 0 := by
  apply gammaMatch_mul_eq_zero_of_not_le
  intro h_le
  have hT_mem : T ∈ ({S, S'} : Forest (Nonplanar α)) :=
    Multiset.subset_of_le h_le (Multiset.mem_singleton.mpr rfl)
  have : T = S ∨ T = S' := by
    rw [show ({S, S'} : Forest (Nonplanar α)) = S ::ₘ ({S'} : Forest (Nonplanar α))
        from rfl, Multiset.mem_cons, Multiset.mem_singleton] at hT_mem
    exact hT_mem
  rcases this with h | h
  · exact hT_ne_S h
  · exact hT_ne_S' h

/-- **Vanishing of mergePost on left-multiplied disjoint factors**: if `F` is NOT
    a sub-multiset of `{S, S'}` and `b` is arbitrary, then for any `z`:

      mergePost lbl S S' ((of' F ⊗ b) * z) = 0.

    Eliminates cross-terms in the F̂-residual generalization of `mergeOp_pair`:
    any term whose LEFT contribution is a forest `F` that doesn't fit inside
    `{S, S'}` vanishes after `mergePost`. -/
theorem mergePost_left_mul_eq_zero_of_not_le (lbl : α) (S S' : Nonplanar α)
    (F : Forest (Nonplanar α)) (b : ConnesKreimer R (Nonplanar α))
    (hF : ¬ F ≤ ({S, S'} : Forest (Nonplanar α)))
    (z : ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) :
    mergePost (R := R) (α := α) lbl S S' ((of' (R := R) F ⊗ₜ[R] b) * z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b' =>
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    unfold mergePost deltaMatch
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
        TensorProduct.map_tmul, LinearMap.id_apply,
        gammaMatch_mul_eq_zero_of_not_le _ _ _ hF,
        TensorProduct.zero_tmul, map_zero, map_zero]
  | add z1 z2 ih1 ih2 =>
    rw [mul_add]
    simp only [map_add]
    rw [ih1, ih2, add_zero]

/-- **Right-multiplicativity of the post-coproduct chain** by a "pure
    right-channel" factor `1 ⊗ y`. For any `z` and any `y`:

      mergePost lbl S S' (z * (1 ⊗ y)) = mergePost lbl S S' z * y.

    Load-bearing for the F̂-residual generalization of `mergeOp_pair`: the
    all-empty-cut term of the residual coproduct has the form `1 ⊗ F̂`, so this
    propagates the residual workspace through the chain unchanged. -/
theorem mergePost_right_one_tmul (lbl : α) (S S' : Nonplanar α)
    (z : ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α))
    (y : ConnesKreimer R (Nonplanar α)) :
    mergePost (R := R) (α := α) lbl S S'
        (z * ((1 : ConnesKreimer R (Nonplanar α)) ⊗ₜ[R] y))
      = mergePost (R := R) (α := α) lbl S S' z * y := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    unfold mergePost deltaMatch
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
        LinearMap.comp_apply, LinearMap.comp_apply,
        TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.map_tmul,
        LinearMap.id_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        TensorProduct.map_tmul, LinearMap.id_apply]
    show Algebra.TensorProduct.lmul' (S := ConnesKreimer R (Nonplanar α)) R _
       = Algebra.TensorProduct.lmul' (S := ConnesKreimer R (Nonplanar α)) R _ * _
    rw [Algebra.TensorProduct.lmul'_apply_tmul,
        Algebra.TensorProduct.lmul'_apply_tmul, mul_assoc]
  | add z1 z2 ih1 ih2 =>
    rw [add_mul]
    simp only [map_add]
    rw [ih1, ih2, add_mul]

/-! ## §6: M_{β, 1} substrate (single-element matching, no grafting)

Per [marcolli-chomsky-berwick-2025] §1.4.3.1 (book p. 50), the operator
`M_{β, 1}` is the "first half" of Internal Merge per Prop 1.4.2:

  IM = M_{T/β, β} ∘ M_{β, 1}

It pulls `β` from the right channel of the coproduct to the left, leaving `T/β`
on the right; the disjoint-union product then forms `{β, T/β}` in the workspace.
**The grafting step disappears**: `B(β ⊔ 1) = M(β, 1) = β` acts as identity
(book p. 50). So

  mergeOpUnit β = ⊔ ∘ δ_{β, 1} ∘ Δ^ρ

with no `B` step.

**Important caveat (book p. 52):** "Internal Merge cannot be further decomposed"
— `M_{β, 1}` is not in itself a Merge operation; it only exists *as part of the
composition*. This file gives `mergeOpUnit` a name for substrate-level algebraic
manipulation; that name does NOT signal a stand-alone Merge. -/

/-- The single-element matching projection `γ_{β, 1}`: keeps the coefficient of
    the `{β}` basis element, sends everything else to zero. Same shape as
    `gammaMatch` but with a singleton target. -/
noncomputable def gammaMatchSingle (β : Nonplanar α) :
    ConnesKreimer R (Nonplanar α) →ₗ[R] ConnesKreimer R (Nonplanar α) :=
  ConnesKreimer.linearLift
    (fun F => if F = ({β} : Forest (Nonplanar α)) then of' F else 0)

/-- **`γ_{β, 1}` acts as a basis-vector projection**: on `of' F`, returns `of' F`
    if `F = {β}`, and `0` otherwise. Singleton counterpart of
    `gammaMatch_apply_singleton`. -/
theorem gammaMatchSingle_apply_singleton (β : Nonplanar α)
    (F : Forest (Nonplanar α)) :
    gammaMatchSingle (R := R) β (of' F) =
      if F = ({β} : Forest (Nonplanar α)) then of' F else 0 := by
  rw [gammaMatchSingle, ConnesKreimer.linearLift_of']

/-- The matching operator `δ_{β, 1}` on tensored coproduct output: applies
    `gammaMatchSingle β` to the left channel, identity to the right. -/
noncomputable def deltaMatchSingle (β : Nonplanar α) :
    (ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) →ₗ[R]
      (ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) :=
  TensorProduct.map (gammaMatchSingle (R := R) β) LinearMap.id

/-- Post-coproduct chain for `M_{β, 1}`: `⊔ ∘ δ_{β, 1}`. NO grafting step
    (book p. 50: `B(β ⊔ 1) = β` is the identity). Parallel to `mergePost`. -/
noncomputable def mergePostUnit (β : Nonplanar α) :
    ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) →ₗ[R]
      ConnesKreimer R (Nonplanar α) :=
  mulLin (R := R) (α := α) ∘ₗ deltaMatchSingle (R := R) β

/-- The "Merge-with-unit" operator `M_{β, 1}` per
    [marcolli-chomsky-berwick-2025] Prop 1.4.2 (book p. 50). The first half of
    Internal Merge. Factors as `mergePostUnit β ∘ comulAlgHomN`.

    NOT a Merge operation in its own right (book p. 52): only exists as part of
    `M_{T/β, β} ∘ M_{β, 1}`. The name is a substrate convenience for stating
    Prop 1.4.2's composition equation algebraically. -/
noncomputable def mergeOpUnit (β : Nonplanar α) :
    ConnesKreimer R (Nonplanar α) →ₗ[R] ConnesKreimer R (Nonplanar α) :=
  mergePostUnit (R := R) (α := α) β ∘ₗ comulAlgHomN.toLinearMap

/-- `mergePostUnit` evaluated on a basis tensor `of' F ⊗ r`:
    - returns `of' {β} * r` if `F = {β}`
    - returns `0` otherwise.

    Singleton counterpart of `mergePost_basis_tensor`; one fewer step. -/
theorem mergePostUnit_basis_tensor (β : Nonplanar α)
    (F : Forest (Nonplanar α)) (r : ConnesKreimer R (Nonplanar α)) :
    mergePostUnit (R := R) (α := α) β (of' F ⊗ₜ[R] r)
      = if F = ({β} : Forest (Nonplanar α))
          then of' ({β} : Forest (Nonplanar α)) * r
          else 0 := by
  unfold mergePostUnit deltaMatchSingle
  rw [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      gammaMatchSingle_apply_singleton]
  by_cases hF : F = ({β} : Forest (Nonplanar α))
  · subst hF
    rw [if_pos rfl, if_pos rfl]
    show Algebra.TensorProduct.lmul' (S := ConnesKreimer R (Nonplanar α)) R _ = _
    exact Algebra.TensorProduct.lmul'_apply_tmul _ _
  · rw [if_neg hF, TensorProduct.zero_tmul, if_neg hF]
    show Algebra.TensorProduct.lmul' (S := ConnesKreimer R (Nonplanar α)) R 0 = 0
    exact map_zero _

/-- **Sanity check**: `mergeOpUnit β` on the empty workspace `(1 : ConnesKreimer
    R (Nonplanar α))` is zero. `1 = of' 0` is the multiplicative unit / empty
    workspace; `δ_{β, 1}` projects on `{β} ≠ 0`, so all cuts are killed.
    Confirms M-C-B's caveat: `M_{β, 1}` requires β to be present. -/
theorem mergeOpUnit_one (β : Nonplanar α) :
    mergeOpUnit (R := R) β (1 : ConnesKreimer R (Nonplanar α)) = 0 := by
  show mergePostUnit (R := R) (α := α) β
        (comulAlgHomN (1 : ConnesKreimer R (Nonplanar α))) = 0
  rw [map_one]
  show mergePostUnit (R := R) (α := α) β
        (of' (R := R) (0 : Forest (Nonplanar α))
          ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α))) = 0
  rw [mergePostUnit_basis_tensor]
  rw [if_neg (by
    intro h
    have : (0 : Forest (Nonplanar α)).card = ({β} : Forest (Nonplanar α)).card := by
      rw [h]
    simp only [Multiset.card_zero, Multiset.card_singleton] at this
    omega)]

end Minimalist.Merge
