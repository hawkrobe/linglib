import Linglib.Core.Algebra.ConnesKreimer.Coproduct
import Linglib.Theories.Syntax.Minimalist.Hopf.Defs
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Merge Operator on the Bialgebra of Decorated Forests
@cite{marcolli-chomsky-berwick-2025}

Per M-C-B 2025 §1.3 (Definitions 1.3.1, 1.3.2, 1.3.4), the linguistic
**Merge operator** `M_{S,S'}` for a pair `(S, S') : TraceTree α Unit`
of accessible terms is the composition

  M_{S,S'} = ⊔ ∘ (B ⊗ id) ∘ δ_{S,S'} ∘ Δ^d

where:

- `Δ^d` is the deletion coproduct (`comulDelAlgHom`, M-C-B Def 1.2.8 with ω = d)
- `δ_{S,S'}` is the matching operator that selects coproduct terms whose
  left channel equals the 2-element forest `{S, S'}` (M-C-B Def 1.3.1)
- `B ⊗ id` applies grafting on the left channel: replaces the 2-element
  forest `{S, S'}` with the binary tree `.node S S'`
- `⊔` is the multiplication on `Hc R α` (forest disjoint union, the
  algebra structure of `Hc`)

This file builds the building blocks (`gammaMatch`, `deltaMatch`,
`graftBinary`) and assembles `mergeOp`. The bridge to the legacy
linguistic Merge (`Step.apply` from `Basic.lean`) lives in the next
file (`MergeAction.lean`, which will replace the legacy version).
-/

namespace Minimalist.Hopf

open scoped TensorProduct
open ConnesKreimer

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq α]

/-! ## §1: γ_{S,S'} matching projection (M-C-B Def 1.3.1)

For a fixed pair `(S, S') : TraceTree α Unit`, `gammaMatch S S'` is the
linear endomorphism of `Hc R α` that projects onto the basis element
`single {S, S'} 1`:

  gammaMatch S S' (single F r) = if F = {S, S'} then single F r else 0

Built as `Finsupp.lsingle ∘ Finsupp.lapply` on the matching forest. -/

/-- The matching projection γ_{S,S'} (M-C-B Def 1.3.1): keeps the
    coefficient of the `{S, S'}` basis element, sends everything else
    to zero. -/
noncomputable def gammaMatch (S S' : TraceTree α Unit) :
    Hc R α →ₗ[R] Hc R α :=
  let target : TraceForest α Unit := ({S, S'} : Multiset (TraceTree α Unit))
  show (TraceForest α Unit →₀ R) →ₗ[R] (TraceForest α Unit →₀ R) from
    (Finsupp.lsingle target).comp (Finsupp.lapply target)

/-- **γ_{S,S'} acts as a basis-vector projection**: on the basis element
    `forestToHc F`, it returns `forestToHc F` if `F = {S, S'}` and `0`
    otherwise. M-C-B Def 1.3.1. -/
theorem gammaMatch_apply_singleton (S S' : TraceTree α Unit)
    (F : TraceForest α Unit) :
    gammaMatch (R := R) S S' (forestToHc F) =
      if F = ({S, S'} : TraceForest α Unit) then forestToHc F else 0 := by
  show (Finsupp.lsingle ({S, S'} : TraceForest α Unit)).comp
        (Finsupp.lapply ({S, S'} : TraceForest α Unit))
        (Finsupp.single F (1 : R))
      = _
  rw [LinearMap.comp_apply, Finsupp.lapply_apply, Finsupp.lsingle_apply,
    Finsupp.single_apply]
  split_ifs with h
  · subst h; rfl
  · exact Finsupp.single_zero _

/-! ## §2: δ_{S,S'} matching on the left tensor channel (M-C-B Def 1.3.1)

`deltaMatch S S' = gammaMatch S S' ⊗ id` lifts the matching projection
to act on the left channel of `Hc R α ⊗ Hc R α`. -/

/-- The matching operator δ_{S,S'} on tensored coproduct output: applies
    `gammaMatch S S'` to the left channel and identity to the right. -/
noncomputable def deltaMatch (S S' : TraceTree α Unit) :
    (Hc R α ⊗[R] Hc R α) →ₗ[R] (Hc R α ⊗[R] Hc R α) :=
  TensorProduct.map (gammaMatch (R := R) S S') LinearMap.id

/-! ## §3: B grafting for binary Merge (M-C-B Def 1.3.2 + Lemma 1.3.3)

`graftBinaryAt S S'` replaces the 2-element forest `{S, S'}` (basis
element of `Hc R α`) with the binary tree `.node S S'` (also a basis
element). All other basis elements map to zero — we only need this
specialized form because the Merge action's preceding `δ_{S,S'}` step
restricts the left channel to multiples of `{S, S'}` anyway. -/

/-- The grafting operator B specialized at the pair `(S, S')`: maps the
    basis element `{S, S'}` to `.node S S'`, all other basis elements
    to zero. M-C-B Lemma 1.3.3 for binary Merge. -/
noncomputable def graftBinaryAt (S S' : TraceTree α Unit) :
    Hc R α →ₗ[R] Hc R α :=
  let source : TraceForest α Unit := ({S, S'} : Multiset (TraceTree α Unit))
  let target : TraceForest α Unit := ({.node S S'} : Multiset (TraceTree α Unit))
  show (TraceForest α Unit →₀ R) →ₗ[R] (TraceForest α Unit →₀ R) from
    (Finsupp.lsingle target).comp (Finsupp.lapply source)

/-- **B grafts on basis vectors**: on `forestToHc F`, returns
    `forestToHc {.node S S'}` if `F = {S, S'}`, and `0` otherwise.
    Same shape as `gammaMatch_apply_singleton` with a different target. -/
theorem graftBinaryAt_apply_singleton (S S' : TraceTree α Unit)
    (F : TraceForest α Unit) :
    graftBinaryAt (R := R) S S' (forestToHc F) =
      if F = ({S, S'} : TraceForest α Unit)
        then forestToHc ({.node S S'} : TraceForest α Unit)
        else 0 := by
  show (Finsupp.lsingle ({.node S S'} : TraceForest α Unit)).comp
        (Finsupp.lapply ({S, S'} : TraceForest α Unit))
        (Finsupp.single F (1 : R))
      = _
  rw [LinearMap.comp_apply, Finsupp.lapply_apply, Finsupp.lsingle_apply,
    Finsupp.single_apply]
  split_ifs with h
  · subst h; rfl
  · exact Finsupp.single_zero _

/-! ## §4: Merge operator (M-C-B Def 1.3.4)

`mergeOp S S' = ⊔ ∘ (B ⊗ id) ∘ δ_{S,S'} ∘ Δ^d`

The chain:

1. `Δ^d` extracts admissible cuts (deletion-with-rebinarization remainder)
2. `δ_{S,S'}` filters to terms where the cut forest equals `{S, S'}`
3. `(B ⊗ id)` grafts `{S, S'}` into `.node S S'` on the left channel
4. `⊔` multiplies the two channels back into a single workspace

When no admissible cut produces `{S, S'}` as its cut forest, all terms
are killed by `δ_{S,S'}` and `mergeOp S S' F = 0` (the empty workspace
in `Hc`'s sense). -/

/-- Multiplication on `Hc R α` lifted to a linear map `Hc R α ⊗[R] Hc R α →ₗ[R] Hc R α`.
    Wraps mathlib's `Algebra.TensorProduct.lmul'`, which gives the
    multiplication algebra-hom for any commutative R-algebra. -/
noncomputable def hcMulLin : Hc R α ⊗[R] Hc R α →ₗ[R] Hc R α :=
  (Algebra.TensorProduct.lmul' (S := Hc R α) R).toLinearMap

/-- The Merge operator `M_{S,S'}` per M-C-B Def 1.3.4. Composes
    `Δ^d`, `δ_{S,S'}`, `B ⊗ id`, and `⊔`. -/
noncomputable def mergeOp (S S' : TraceTree α Unit) : Hc R α →ₗ[R] Hc R α :=
  hcMulLin (R := R) (α := α)
    ∘ₗ TensorProduct.map (graftBinaryAt (R := R) S S') LinearMap.id
    ∘ₗ deltaMatch (R := R) S S'
    ∘ₗ comulDelAlgHom.toLinearMap

/-! ## §5: Post-coproduct chain on basis tensors

The composition `⊔ ∘ (B ⊗ id) ∘ δ_{S,S'}` evaluated on an elementary
tensor `forestToHc F ⊗ r` is:
- `forestToHc {.node S S'} * r` if `F = {S, S'}`
- `0` otherwise

This is the **load-bearing fact** for proving that algebraic Merge agrees
with linguistic `Step.apply`: every basis-tensor term in the expansion
of `Δ^d({S, S'})` either matches the merge target (only the primitive
`{S, S'} ⊗ 1` term) or is annihilated by `δ_{S,S'}`. -/

/-- The post-coproduct chain `⊔ ∘ (B ⊗ id) ∘ δ_{S,S'}` evaluated on a
    basis tensor `forestToHc F ⊗ r`. -/
theorem mergePost_basis_tensor (S S' : TraceTree α Unit)
    (F : TraceForest α Unit) (r : Hc R α) :
    hcMulLin (R := R) (α := α)
        (TensorProduct.map (graftBinaryAt (R := R) S S') LinearMap.id
          (deltaMatch (R := R) S S' (forestToHc F ⊗ₜ[R] r)))
      = if F = ({S, S'} : TraceForest α Unit)
          then forestToHc ({.node S S'} : TraceForest α Unit) * r
          else 0 := by
  unfold deltaMatch
  rw [TensorProduct.map_tmul, LinearMap.id_apply, gammaMatch_apply_singleton]
  by_cases hF : F = ({S, S'} : TraceForest α Unit)
  · subst hF
    rw [if_pos rfl, TensorProduct.map_tmul, LinearMap.id_apply,
        graftBinaryAt_apply_singleton, if_pos rfl, if_pos rfl]
    show Algebra.TensorProduct.lmul' (S := Hc R α) R _ = _
    exact Algebra.TensorProduct.lmul'_apply_tmul _ _
  · rw [if_neg hF, TensorProduct.zero_tmul, if_neg hF]
    simp only [map_zero]

/-- **General γ_{S,S'}-vanishing on a left-multiplied forest**: if `{S, S'}` cannot
    be decomposed as `F + d` for any `d`, then `γ_{S,S'}(forestToHc F * a) = 0`
    for any `a`. The condition `¬ ∃ d, {S, S'} = F + d` says `F` is NOT a
    left-divisor of `{S, S'}` in the multiset additive semigroup. -/
theorem gammaMatch_mul_eq_zero_of_no_decomp (S S' : TraceTree α Unit)
    (F : TraceForest α Unit)
    (h_no_decomp : ¬ ∃ d : TraceForest α Unit,
                      ({S, S'} : TraceForest α Unit) = F + d) (a : Hc R α) :
    gammaMatch (R := R) S S' (forestToHc F * a) = 0 := by
  show ((Finsupp.lsingle ({S, S'} : TraceForest α Unit)).comp
        (Finsupp.lapply ({S, S'} : TraceForest α Unit)))
      (forestToHc (R := R) F * a) = 0
  rw [LinearMap.comp_apply, Finsupp.lapply_apply, Finsupp.lsingle_apply]
  show Finsupp.single ({S, S'} : TraceForest α Unit)
        ((forestToHc (R := R) F * a) ({S, S'} : TraceForest α Unit)) = 0
  rw [show (forestToHc (R := R) F * a) ({S, S'} : TraceForest α Unit) = 0 from
    AddMonoidAlgebra.single_mul_apply_of_not_exists_add (M := TraceForest α Unit)
      (R := R) (1 : R) a h_no_decomp]
  exact Finsupp.single_zero _

/-- **Disjoint-singleton vanishing of γ_{S,S'}** (corollary): if `T ≠ S` and
    `T ≠ S'`, then `γ_{S,S'}(forestToHc {T} * a) = 0`. -/
theorem gammaMatch_singleton_mul_eq_zero (S S' T : TraceTree α Unit)
    (hT_ne_S : T ≠ S) (hT_ne_S' : T ≠ S') (a : Hc R α) :
    gammaMatch (R := R) S S' (forestToHc ({T} : TraceForest α Unit) * a) = 0 := by
  apply gammaMatch_mul_eq_zero_of_no_decomp
  rintro ⟨d, hd⟩
  have hT_mem : T ∈ ({T} : TraceForest α Unit) + d := by
    rw [Multiset.mem_add]; exact Or.inl (Multiset.mem_singleton.mpr rfl)
  rw [← hd] at hT_mem
  have : T = S ∨ T = S' := by
    rw [show ({S, S'} : TraceForest α Unit) = S ::ₘ ({S'} : TraceForest α Unit) from rfl,
        Multiset.mem_cons, Multiset.mem_singleton] at hT_mem
    exact hT_mem
  rcases this with h | h
  · exact hT_ne_S h
  · exact hT_ne_S' h

/-- **Vanishing of mergePost on left-multiplied disjoint factors**: if `F` is not
    a left-divisor of `{S, S'}` and `b : Hc R α` is arbitrary, then for any
    `z : Hc R α ⊗[R] Hc R α`:

      mergePost ((forestToHc F ⊗ b) * z) = 0.

    Used to eliminate cross-terms in the F̂-residual generalization of
    `mergeOp_pair`: any term in `comulTreeDel T * comulDelAlgHom w` whose LEFT
    contribution is a forest `F` not in `{S, S'}` (e.g., `prim_T` with `F = {T}`
    when `T ≠ S, S'`, or non-empty cuts of `T` under disjointness) vanishes after
    `mergePost`. -/
theorem mergePost_left_mul_eq_zero_of_no_decomp (S S' : TraceTree α Unit)
    (F : TraceForest α Unit) (b : Hc R α)
    (h_no_decomp : ¬ ∃ d : TraceForest α Unit,
                      ({S, S'} : TraceForest α Unit) = F + d)
    (z : Hc R α ⊗[R] Hc R α) :
    hcMulLin (R := R) (α := α)
        (TensorProduct.map (graftBinaryAt (R := R) S S') LinearMap.id
          (deltaMatch (R := R) S S'
            ((forestToHc (R := R) F ⊗ₜ[R] b) * z)))
      = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b' =>
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    unfold deltaMatch
    rw [TensorProduct.map_tmul, LinearMap.id_apply,
        gammaMatch_mul_eq_zero_of_no_decomp _ _ _ h_no_decomp,
        TensorProduct.zero_tmul, map_zero, map_zero]
  | add z1 z2 ih1 ih2 =>
    rw [mul_add]
    simp only [map_add]
    rw [ih1, ih2, add_zero]

/-- **Right-multiplicativity of the post-coproduct chain** by a "pure right-channel"
    factor `1 ⊗ y`. For any `z : Hc R α ⊗[R] Hc R α` and any `y : Hc R α`:

      mergePost (z * (1 ⊗ y)) = mergePost(z) * y.

    Load-bearing for the F̂-residual generalization of `mergeOp_pair`
    (M-C-B Lemma 1.4.1 in full): the all-empty-cut term of `comulForestDel F̂`
    has the form `1 ⊗ forestToHc F̂`, so this lemma propagates the residual
    workspace `F̂` through the post-coproduct chain unchanged. -/
theorem mergePost_right_one_tmul (S S' : TraceTree α Unit)
    (z : Hc R α ⊗[R] Hc R α) (y : Hc R α) :
    hcMulLin (R := R) (α := α)
        (TensorProduct.map (graftBinaryAt (R := R) S S') LinearMap.id
          (deltaMatch (R := R) S S' (z * ((1 : Hc R α) ⊗ₜ[R] y))))
      = hcMulLin (R := R) (α := α)
          (TensorProduct.map (graftBinaryAt (R := R) S S') LinearMap.id
            (deltaMatch (R := R) S S' z)) * y := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    unfold deltaMatch
    rw [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.map_tmul,
        LinearMap.id_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        TensorProduct.map_tmul, LinearMap.id_apply]
    show Algebra.TensorProduct.lmul' (S := Hc R α) R _
       = Algebra.TensorProduct.lmul' (S := Hc R α) R _ * _
    rw [Algebra.TensorProduct.lmul'_apply_tmul,
        Algebra.TensorProduct.lmul'_apply_tmul, mul_assoc]
  | add z1 z2 ih1 ih2 =>
    rw [add_mul]
    simp only [map_add]
    rw [ih1, ih2, add_mul]

end Minimalist.Hopf
