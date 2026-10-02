module

public import Linglib.Core.Algebra.RootedTree.Coproduct.Pruning
public import Linglib.Core.Algebra.RootedTree.Coproduct.WithCuts
public import Linglib.Core.Data.UnorderedTree.Count
public import Linglib.Syntax.Minimalist.Workspace.TraceCut
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The Merge operator on workspaces

The Merge operator of [marcolli-chomsky-berwick-2025] (Definition 1.3.4) on the workspace algebra
`ConnesKreimer R (UnorderedTree α)`: for a pair `S, S'` of accessible terms,

  M_{S,S'} = ⊔ ∘ (B ⊗ id) ∘ δ_{S,S'} ∘ Δ,

where `Δ` is a coproduct extracting accessible terms, `δ_{S,S'}` keeps the terms whose left
channel is the forest `{S, S'}` (Definition 1.3.1), `B` grafts that forest under a new root
(Definition 1.3.2), and `⊔` multiplies the two channels back into one workspace. Only `Δ` depends
on how accessible terms are cut out, so the operator is defined over an arbitrary cut enumeration
`cuts` (`mergeOpG`), with the pruning instance `mergeOp` and the trace instance `mergeOpC`. The
unit stage `M_{β,1}` of Internal Merge (Proposition 1.4.2) has no grafting step (`mergeOpUnitG`).

External, Internal and Sideward Merge are in `Merge/External.lean`, `Merge/Internal.lean` and
`Merge/Sideward.lean`; the Minimal-Search weighting is in `Economy/MinimalSearch.lean`.

## Main definitions

* `Minimalist.Merge.mergeOpG`, `mergeOp`, `mergeOpC`: Merge over a cut enumeration, at the pruning
  cuts, and at the trace cuts.
* `Minimalist.Merge.mergeOpUnitG`, `mergeOpUnit`, `mergeOpUnitC`: the unit stage `M_{β,1}`.
* `Minimalist.Merge.IsMergeCuts`: cut enumerations whose nonempty crowns have fewer edges than
  their tree.

## Main results

* `Minimalist.Merge.mergePost_basis_tensor`: the post-coproduct chain on a basis tensor.
* `Minimalist.Merge.mergeOpG_comm`: Merge does not depend on the order of the pair.

## Implementation notes

Definition 1.3.4 uses the deletion coproduct `Δ^d`, which contracts the unary vertex a cut leaves.
`mergeOp` uses the pruning coproduct `Δ^ρ`, which keeps it. The two extract the same accessible
terms and differ only in the remainder, so the forest `B` grafts is the same.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist.Merge

open scoped TensorProduct
open RoseTree UnorderedTree ConnesKreimer

variable {R : Type*} [CommSemiring R] {α : Type*} [DecidableEq (UnorderedTree α)]

/-! ### The matching projections -/

/-- The projection onto the basis element `F₀` keeps its coefficient and sends every other basis
    element to zero. -/
noncomputable def forestProj (F₀ : Forest (UnorderedTree α)) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  ConnesKreimer.linearLift (fun F => if F = F₀ then of' F else 0)

theorem forestProj_apply_of' (F₀ F : Forest (UnorderedTree α)) :
    forestProj (R := R) F₀ (of' F) = if F = F₀ then of' F else 0 := by
  rw [forestProj, ConnesKreimer.linearLift_of']

omit [DecidableEq (UnorderedTree α)] in
private theorem of'_mul_single (F G : Forest (UnorderedTree α)) (r : R) :
    of' (R := R) F * single G r = single (F + G) r := by
  rw [smul_single_one G r, mul_smul_comm]
  change r • (of' (R := R) F * of' G) = single (F + G) r
  rw [← of'_add]
  exact (smul_single_one (F + G) r).symm

/-- The projection onto `F₀` kills every product with a forest that does not fit inside `F₀`. -/
theorem forestProj_mul_eq_zero_of_not_le {F₀ F : Forest (UnorderedTree α)} (hF : ¬ F ≤ F₀)
    (a : ConnesKreimer R (UnorderedTree α)) : forestProj F₀ (of' F * a) = 0 := by
  induction a using ConnesKreimer.induction_linear with
  | zero => rw [mul_zero, map_zero]
  | add g h hg hh => rw [mul_add, map_add, hg, hh, add_zero]
  | single G r =>
    have hne : F + G ≠ F₀ := fun heq => hF (heq ▸ Multiset.le_add_right F G)
    rw [of'_mul_single, forestProj]
    simp only [ConnesKreimer.linearLift_single]
    rw [ite_eq_right hne, smul_zero]

omit [DecidableEq (UnorderedTree α)] in
/-- A chain `⊔ ∘ (f ⊗ id)` kills every term whose left channel is a product with `x` that `f`
    kills. -/
private theorem mul'_map_tmul_mul_eq_zero
    (f : ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α))
    {x : ConnesKreimer R (UnorderedTree α)} (hf : ∀ a, f (x * a) = 0)
    (b : ConnesKreimer R (UnorderedTree α))
    (z : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :
    (LinearMap.mul' R (ConnesKreimer R (UnorderedTree α)) ∘ₗ TensorProduct.map f LinearMap.id)
      ((x ⊗ₜ[R] b) * z) = 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul a b' =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.comp_apply, TensorProduct.map_tmul, hf,
      TensorProduct.zero_tmul, map_zero]
  | add z₁ z₂ h₁ h₂ => rw [mul_add, map_add, h₁, h₂, add_zero]

omit [DecidableEq (UnorderedTree α)] in
/-- A chain `⊔ ∘ (f ⊗ id)` commutes with right multiplication by a right-channel factor `1 ⊗ y`. -/
private theorem mul'_map_mul_one_tmul
    (f : ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α))
    (z : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α))
    (y : ConnesKreimer R (UnorderedTree α)) :
    (LinearMap.mul' R (ConnesKreimer R (UnorderedTree α)) ∘ₗ TensorProduct.map f LinearMap.id)
        (z * ((1 : ConnesKreimer R (UnorderedTree α)) ⊗ₜ[R] y))
      = (LinearMap.mul' R (ConnesKreimer R (UnorderedTree α)) ∘ₗ
          TensorProduct.map f LinearMap.id) z * y := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, LinearMap.comp_apply, LinearMap.comp_apply,
      TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.id_apply,
      LinearMap.mul'_apply, LinearMap.mul'_apply, mul_assoc]
  | add z₁ z₂ h₁ h₂ => rw [add_mul, map_add, map_add, h₁, h₂, add_mul]

/-- The matching projection `γ_{S,S'}` ([marcolli-chomsky-berwick-2025] Definition 1.3.1) is the
    projection onto `{S, S'}`. -/
noncomputable def gammaMatch (S S' : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  forestProj {S, S'}

theorem gammaMatch_apply_singleton (S S' : UnorderedTree α)
    (F : Forest (UnorderedTree α)) :
    gammaMatch (R := R) S S' (of' F) =
      if F = ({S, S'} : Forest (UnorderedTree α)) then of' F else 0 :=
  forestProj_apply_of' _ F

/-- The matching operator `δ_{S,S'} = γ_{S,S'} ⊗ id` acts on the left channel of a coproduct. -/
noncomputable def deltaMatch (S S' : UnorderedTree α) :
    (ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) →ₗ[R]
      (ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :=
  TensorProduct.map (gammaMatch (R := R) S S') LinearMap.id

/-! ### Grafting -/

/-- The grafting operator `B` at the pair `S, S'` sends the basis element `{S, S'}` to the tree
    `node lbl {S, S'}` and every other basis element to zero. Merge applies it only after
    `δ_{S,S'}`, so this restriction of [marcolli-chomsky-berwick-2025]'s `B` suffices. -/
noncomputable def graftBinaryAt (lbl : α) (S S' : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  ConnesKreimer.linearLift
    (fun F => if F = ({S, S'} : Forest (UnorderedTree α))
      then of' ({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α)) else 0)

theorem graftBinaryAt_apply_singleton (lbl : α) (S S' : UnorderedTree α)
    (F : Forest (UnorderedTree α)) :
    graftBinaryAt (R := R) lbl S S' (of' F) =
      if F = ({S, S'} : Forest (UnorderedTree α))
        then of' ({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α))
        else 0 := by
  rw [graftBinaryAt, ConnesKreimer.linearLift_of']

/-! ### The Merge operator -/

/-- The post-coproduct chain `⊔ ∘ (B ⊗ id) ∘ δ_{S,S'}`, shared by every cut enumeration. -/
noncomputable def mergePost (lbl : α) (S S' : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) →ₗ[R]
      ConnesKreimer R (UnorderedTree α) :=
  LinearMap.mul' R (ConnesKreimer R (UnorderedTree α))
    ∘ₗ TensorProduct.map (graftBinaryAt (R := R) lbl S S') LinearMap.id
    ∘ₗ deltaMatch (R := R) S S'

/-- The Merge operator `M_{S,S'}` of [marcolli-chomsky-berwick-2025] Definition 1.3.4 at the
    pruning coproduct, with root label `lbl`. -/
noncomputable def mergeOp (lbl : α) (S S' : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  mergePost (R := R) (α := α) lbl S S' ∘ₗ comulAlgHomN.toLinearMap

/-- On a basis tensor `of' F ⊗ r`, the post-coproduct chain grafts `F` if it is `{S, S'}` and
    vanishes otherwise. -/
theorem mergePost_basis_tensor (lbl : α) (S S' : UnorderedTree α)
    (F : Forest (UnorderedTree α)) (r : ConnesKreimer R (UnorderedTree α)) :
    mergePost (R := R) (α := α) lbl S S' (of' F ⊗ₜ[R] r)
      = if F = ({S, S'} : Forest (UnorderedTree α))
          then of' ({UnorderedTree.node lbl {S, S'}} : Forest (UnorderedTree α)) * r
          else 0 := by
  unfold mergePost deltaMatch
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
      TensorProduct.map_tmul, LinearMap.id_apply, gammaMatch_apply_singleton]
  by_cases hF : F = ({S, S'} : Forest (UnorderedTree α))
  · subst hF
    rw [ite_eq_left rfl, TensorProduct.map_tmul, LinearMap.id_apply,
        graftBinaryAt_apply_singleton, ite_eq_left rfl, ite_eq_left rfl]
    exact LinearMap.mul'_apply
  · rw [ite_eq_right hF, TensorProduct.zero_tmul, ite_eq_right hF]
    simp only [map_zero]

/-- `γ_{S,S'}` kills every product with a forest `F` that does not fit inside `{S, S'}`. -/
theorem gammaMatch_mul_eq_zero_of_not_le (S S' : UnorderedTree α)
    (F : Forest (UnorderedTree α))
    (hF : ¬ F ≤ ({S, S'} : Forest (UnorderedTree α)))
    (a : ConnesKreimer R (UnorderedTree α)) :
    gammaMatch (R := R) S S' (of' F * a) = 0 :=
  forestProj_mul_eq_zero_of_not_le hF a

/-- `γ_{S,S'}` kills every product with a tree other than `S` and `S'`. -/
theorem gammaMatch_singleton_mul_eq_zero (S S' T : UnorderedTree α)
    (hT_ne_S : T ≠ S) (hT_ne_S' : T ≠ S') (a : ConnesKreimer R (UnorderedTree α)) :
    gammaMatch (R := R) S S' (of' ({T} : Forest (UnorderedTree α)) * a) = 0 := by
  apply gammaMatch_mul_eq_zero_of_not_le
  intro h_le
  have hT_mem : T ∈ ({S, S'} : Forest (UnorderedTree α)) :=
    Multiset.subset_of_le h_le (Multiset.mem_singleton.mpr rfl)
  rw [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hT_mem
  exact hT_mem.elim hT_ne_S hT_ne_S'

private theorem mergePost_eq (lbl : α) (S S' : UnorderedTree α) :
    mergePost (R := R) lbl S S' = LinearMap.mul' R (ConnesKreimer R (UnorderedTree α)) ∘ₗ
      TensorProduct.map (graftBinaryAt lbl S S' ∘ₗ gammaMatch S S') LinearMap.id := by
  rw [mergePost, deltaMatch, ← TensorProduct.map_comp, LinearMap.id_comp]

/-- The post-coproduct chain kills every term whose left channel carries a forest that does not
    fit inside `{S, S'}`. -/
theorem mergePost_left_mul_eq_zero_of_not_le (lbl : α) (S S' : UnorderedTree α)
    (F : Forest (UnorderedTree α)) (b : ConnesKreimer R (UnorderedTree α))
    (hF : ¬ F ≤ ({S, S'} : Forest (UnorderedTree α)))
    (z : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :
    mergePost (R := R) (α := α) lbl S S' ((of' (R := R) F ⊗ₜ[R] b) * z) = 0 := by
  rw [mergePost_eq]
  exact mul'_map_tmul_mul_eq_zero _ (fun a ↦ by
    rw [LinearMap.comp_apply, gammaMatch_mul_eq_zero_of_not_le _ _ _ hF, map_zero]) b z

/-- The post-coproduct chain commutes with right multiplication by a right-channel factor
    `1 ⊗ y`, so a spectator workspace passes through it unchanged. -/
theorem mergePost_right_one_tmul (lbl : α) (S S' : UnorderedTree α)
    (z : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α))
    (y : ConnesKreimer R (UnorderedTree α)) :
    mergePost (R := R) (α := α) lbl S S'
        (z * ((1 : ConnesKreimer R (UnorderedTree α)) ⊗ₜ[R] y))
      = mergePost (R := R) (α := α) lbl S S' z * y := by
  rw [mergePost_eq]
  exact mul'_map_mul_one_tmul _ z y

/-! ### The unit stage `M_{β,1}`

The first stage of Internal Merge (Proposition 1.4.2) moves an accessible term `β` to the left
channel and leaves `T/β` on the right. Its grafting step is the identity, since
`B(β ⊔ 1) = M(β, 1) = β`. It is not a Merge in its own right: it occurs only composed with
`M_{T/β,β}` ([marcolli-chomsky-berwick-2025] Remark 1.4.3). -/

/-- The single-tree matching projection `γ_{β,1}` keeps the coefficient of the basis element
    `{β}`. -/
noncomputable def gammaMatchSingle (β : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  forestProj {β}

theorem gammaMatchSingle_apply_singleton (β : UnorderedTree α)
    (F : Forest (UnorderedTree α)) :
    gammaMatchSingle (R := R) β (of' F) =
      if F = ({β} : Forest (UnorderedTree α)) then of' F else 0 :=
  forestProj_apply_of' _ F

/-- The matching operator `δ_{β,1} = γ_{β,1} ⊗ id`. -/
noncomputable def deltaMatchSingle (β : UnorderedTree α) :
    (ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) →ₗ[R]
      (ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :=
  TensorProduct.map (gammaMatchSingle (R := R) β) LinearMap.id

/-- The post-coproduct chain `⊔ ∘ δ_{β,1}` of the unit stage. -/
noncomputable def mergePostUnit (β : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α) →ₗ[R]
      ConnesKreimer R (UnorderedTree α) :=
  LinearMap.mul' R (ConnesKreimer R (UnorderedTree α)) ∘ₗ deltaMatchSingle (R := R) β

/-- The unit stage `M_{β,1}` at the pruning coproduct. -/
noncomputable def mergeOpUnit (β : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  mergePostUnit (R := R) (α := α) β ∘ₗ comulAlgHomN.toLinearMap

theorem mergePostUnit_basis_tensor (β : UnorderedTree α)
    (F : Forest (UnorderedTree α)) (r : ConnesKreimer R (UnorderedTree α)) :
    mergePostUnit (R := R) (α := α) β (of' F ⊗ₜ[R] r)
      = if F = ({β} : Forest (UnorderedTree α))
          then of' ({β} : Forest (UnorderedTree α)) * r
          else 0 := by
  unfold mergePostUnit deltaMatchSingle
  rw [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      gammaMatchSingle_apply_singleton]
  by_cases hF : F = ({β} : Forest (UnorderedTree α))
  · subst hF
    rw [ite_eq_left rfl, ite_eq_left rfl]
    exact LinearMap.mul'_apply
  · rw [ite_eq_right hF, TensorProduct.zero_tmul, ite_eq_right hF]
    exact map_zero _

/-- The unit chain kills every term whose left channel carries a forest that does not fit inside
    `{β}`. -/
theorem mergePostUnit_left_mul_eq_zero_of_not_le (β : UnorderedTree α)
    (F : Forest (UnorderedTree α)) (b : ConnesKreimer R (UnorderedTree α))
    (hF : ¬ F ≤ ({β} : Forest (UnorderedTree α)))
    (z : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α)) :
    mergePostUnit (R := R) β ((of' (R := R) F ⊗ₜ[R] b) * z) = 0 :=
  mul'_map_tmul_mul_eq_zero _ (forestProj_mul_eq_zero_of_not_le hF) b z

/-- The unit chain commutes with right multiplication by a right-channel factor `1 ⊗ y`. -/
theorem mergePostUnit_right_one_tmul (β : UnorderedTree α)
    (z : ConnesKreimer R (UnorderedTree α) ⊗[R] ConnesKreimer R (UnorderedTree α))
    (y : ConnesKreimer R (UnorderedTree α)) :
    mergePostUnit (R := R) β (z * ((1 : ConnesKreimer R (UnorderedTree α)) ⊗ₜ[R] y))
      = mergePostUnit (R := R) β z * y :=
  mul'_map_mul_one_tmul _ z y

/-! ### Merge over a cut enumeration -/

/-- Merge `M_{S,S'}` over a cut enumeration `cuts`, whose coproduct is `comulAlgHomNG cuts`. -/
noncomputable def mergeOpG (cuts : UnorderedTree α → Multiset (Forest
    (UnorderedTree α) × UnorderedTree α))
    (lbl : α) (S S' : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  mergePost (R := R) (α := α) lbl S S' ∘ₗ (comulAlgHomNG cuts).toLinearMap

/-- The unit stage `M_{β,1}` over a cut enumeration `cuts`. -/
noncomputable def mergeOpUnitG (cuts : UnorderedTree α → Multiset (Forest
    (UnorderedTree α) × UnorderedTree α)) (β : UnorderedTree α) :
    ConnesKreimer R (UnorderedTree α) →ₗ[R] ConnesKreimer R (UnorderedTree α) :=
  mergePostUnit (R := R) (α := α) β ∘ₗ (comulAlgHomNG cuts).toLinearMap

theorem mergeOp_eq_G (lbl : α) (S S' : UnorderedTree α) :
    mergeOp (R := R) lbl S S' = mergeOpG (R := R) cutSummandsN lbl S S' := rfl

theorem mergeOpUnit_eq_G (β : UnorderedTree α) :
    mergeOpUnit (R := R) β = mergeOpUnitG (R := R) cutSummandsN β := rfl

/-- Merge does not depend on the order of the pair. -/
theorem mergeOpG_comm (cuts : UnorderedTree α → Multiset (Forest
    (UnorderedTree α) × UnorderedTree α)) (lbl : α) (S S' : UnorderedTree α) :
    mergeOpG (R := R) cuts lbl S S' = mergeOpG cuts lbl S' S := by
  simp only [mergeOpG, mergePost, deltaMatch, gammaMatch, graftBinaryAt, Multiset.pair_comm S S']

/-- The unit stage vanishes on the empty workspace: it needs `β` to be present. -/
theorem mergeOpUnitG_one (cuts : UnorderedTree α → Multiset (Forest
    (UnorderedTree α) × UnorderedTree α)) (β : UnorderedTree α) :
    mergeOpUnitG (R := R) cuts β 1 = 0 := by
  rw [mergeOpUnitG, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_one,
    Algebra.TensorProduct.one_def, ← of'_zero, mergePostUnit_basis_tensor,
    ite_eq_right (Multiset.singleton_ne_zero β).symm]

omit [DecidableEq (UnorderedTree α)] in
/-- The trace Merge operator, Merge at the trace cuts `cutSummandsCN τ`. Its trunks carry a trace
    leaf at each cut site, at the cut depth, so the Minimal-Search cost `Cut.depthC` is read off
    them. -/
noncomputable def mergeOpC {β : Type*} [DecidableEq (UnorderedTree (α ⊕ β))]
    (τ : UnorderedTree (α ⊕ β) → β) (lbl : α ⊕ β) (S S' : UnorderedTree (α ⊕ β)) :
    ConnesKreimer R (UnorderedTree (α ⊕ β)) →ₗ[R] ConnesKreimer R (UnorderedTree (α ⊕ β)) :=
  mergeOpG (R := R) (cutSummandsCN τ) lbl S S'

omit [DecidableEq (UnorderedTree α)] in
/-- The unit stage `M_{S,1}` at the trace cuts `cutSummandsCN τ`. -/
noncomputable def mergeOpUnitC {β : Type*} [DecidableEq (UnorderedTree (α ⊕ β))]
    (τ : UnorderedTree (α ⊕ β) → β) (S : UnorderedTree (α ⊕ β)) :
    ConnesKreimer R (UnorderedTree (α ⊕ β)) →ₗ[R] ConnesKreimer R (UnorderedTree (α ⊕ β)) :=
  mergeOpUnitG (R := R) (cutSummandsCN τ) S

/-! ### Cut enumerations that admit Merge -/

omit [DecidableEq (UnorderedTree α)] in
/-- A cut enumeration admits Merge when its crowns are subtrees with fewer edges in total than
    their tree, and its only empty cut is the tree itself. The edge bound makes External Merge of
    a pair exact (`mergeOpG_pair`); the other two let a spectator component pass through
    (`mergeOpG_factor_out_singleton`). -/
class IsMergeCuts
    (cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α)) : Prop where
  crown_numEdges_lt {T : UnorderedTree α} {p : Forest (UnorderedTree α) × UnorderedTree α} :
    p ∈ cuts T → p.1 ≠ 0 → (p.1.map numEdges).sum < T.numEdges
  mem_subtrees_of_mem_crown {T : UnorderedTree α} {p : Forest (UnorderedTree α) × UnorderedTree α}
    {x : UnorderedTree α} : p ∈ cuts T → x ∈ p.1 → x ∈ T.subtrees
  filter_empty (T : UnorderedTree α) : (cuts T).filter (fun p ↦ p.1.card = 0) = {(0, T)}

omit [DecidableEq (UnorderedTree α)] in
/-- No cut of an enumeration admitting Merge extracts the whole tree. -/
theorem IsMergeCuts.crown_ne_singleton
    {cuts : UnorderedTree α → Multiset (Forest (UnorderedTree α) × UnorderedTree α)}
    [IsMergeCuts cuts] {T : UnorderedTree α} {p : Forest (UnorderedTree α) × UnorderedTree α}
    (hp : p ∈ cuts T) : p.1 ≠ {T} := fun h ↦ by
  simpa [h] using IsMergeCuts.crown_numEdges_lt hp (by simp [h])

end Minimalist.Merge
