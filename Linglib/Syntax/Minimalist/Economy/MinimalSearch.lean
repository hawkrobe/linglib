import Linglib.Syntax.Minimalist.Merge.Basic
import Linglib.Syntax.Minimalist.Workspace.Conservation

/-!
# Minimal Search as a weighting of Merge

The ε-weighted Merge `M^ε = ⊔ ∘ (Bᵉ ⊗ id) ∘ δ ∘ Δ` scales the graft by `ε^c`, where `c` is the
Minimal-Search cost of the merge. Since `mergePost` is linear and the graft is its only creation,
this is the Δ^c Merge `mergeOpC` scaled by `epsWeight ε c`. The net cost is the signed sum of the
operands' depth-costs (`Cut.extractionCost`, `Cut.quotientCost`): External Merge costs `0`;
Internal Merge's extraction `+d` and its own quotient's `−d` cancel; Sideward Merge's extraction
is uncancelled, so `c = d > 0`. At `ε = 0` External and Internal Merge survive and Sideward Merge
is annihilated.

## Main definitions

* `Minimalist.Merge.epsWeight`: the weight `ε^c`.
* `Minimalist.Merge.emNetCost`, `imNetCost`, `swNetCost`: the per-case net costs.
* `Minimalist.Merge.mergeOpCEps`: the ε-weighted Δ^c Merge.

## Main results

* `Minimalist.Merge.mergeOpCEps_zero_em`, `mergeOpCEps_zero_im`, `mergeOpCEps_zero_sideward`: the
  ε → 0 limit keeps External and Internal Merge and kills Sideward Merge.

## References

* [marcolli-chomsky-berwick-2025], §1.5 (Proposition 1.5.1)
-/

namespace Minimalist.Merge

open scoped TensorProduct
open RoseTree RoseTree.Nonplanar ConnesKreimer

variable {R : Type*} [CommSemiring R] {α β : Type*}

/-! ### The weight -/

/-- The **Minimal-Search ε-weight** of a merge with net cost `c`: `ε^c`
    (MCB eq 1.5.2). -/
def epsWeight (ε : R) (c : ℕ) : R := ε ^ c

@[simp] theorem epsWeight_zero_zero : epsWeight (0 : R) 0 = 1 := pow_zero 0

theorem epsWeight_zero_of_pos {c : ℕ} (hc : 0 < c) : epsWeight (0 : R) c = 0 :=
  zero_pow (Nat.pos_iff_ne_zero.mp hc)

@[simp] theorem epsWeight_one (c : ℕ) : epsWeight (1 : R) c = 1 := one_pow c

/-! ### Net costs and the weighted operator -/

/-- **External Merge net cost** (MCB rule 4, whole operands): `0`. -/
def emNetCost : ℕ := 0

/-- **Internal Merge net cost** (MCB Prop 1.5.1, IM): the extracted crown's `+d`
    and its own quotient's `−d` cancel — the signed sum over the *same* cut `p`,
    truncated to `ℕ` (it is `0`, see `imNetCost_eq_zero`). -/
def imNetCost (p : Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) : ℕ :=
  (Cut.extractionCost p + Cut.quotientCost p).toNat

/-- **Sideward Merge net cost** (MCB Prop 1.5.1, Sideward 2b): the extracted
    crown's `+d`, with no quotient operand to cancel it. Equals `Cut.depthC p`. -/
def swNetCost (p : Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) : ℕ :=
  (Cut.extractionCost p).toNat

@[simp] theorem imNetCost_eq_zero (p : Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) :
    imNetCost p = 0 := by
  rw [imNetCost, Cut.extractionCost_add_quotientCost]; rfl

@[simp] theorem swNetCost_eq_depthC (p : Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) :
    swNetCost p = Cut.depthC p := by
  rw [swNetCost, Cut.extractionCost, Int.toNat_natCast]

/-- A Sideward Merge of a lexical-rooted object has strictly positive net cost
    (MCB Prop 1.5.1) — the uncancelled extraction depth. -/
theorem swNetCost_pos (τ : Nonplanar (α ⊕ β) → β) (T : Nonplanar (α ⊕ β)) (a₀ : α)
    (hT : T.rootValue = Sum.inl a₀)
    (p : Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) (hp : p ∈ cutSummandsCN τ T)
    (hproper : p.1 ≠ 0) :
    0 < swNetCost p := by
  rw [swNetCost_eq_depthC]
  exact Cut.depthC_pos τ T a₀ hT p hp hproper

variable [DecidableEq (Nonplanar (α ⊕ β))]

/-- The **ε-weighted Δ^c Merge operator** (MCB §1.5, eq 1.5.2): the Δ^c merge
    scaled by the Minimal-Search weight `ε^c`. -/
noncomputable def mergeOpCEps (τ : Nonplanar (α ⊕ β) → β) (ε : R) (c : ℕ)
    (lbl : α ⊕ β) (S S' : Nonplanar (α ⊕ β)) :
    ConnesKreimer R (Nonplanar (α ⊕ β)) →ₗ[R] ConnesKreimer R (Nonplanar (α ⊕ β)) :=
  epsWeight ε c • mergeOpC τ lbl S S'

/-- At ε = 1 the weight is trivial and `mergeOpCEps` recovers the unweighted Δ^c
    Merge. -/
@[simp] theorem mergeOpCEps_one (τ : Nonplanar (α ⊕ β) → β) (c : ℕ)
    (lbl : α ⊕ β) (S S' : Nonplanar (α ⊕ β)) :
    mergeOpCEps τ (1 : R) c lbl S S' = mergeOpC τ lbl S S' := by
  rw [mergeOpCEps, epsWeight_one, one_smul]

/-- **MCB Prop 1.5.1, External Merge survives ε → 0.** EM has net cost 0, so its
    weight `ε^0 = 1` is unaffected: `mergeOpCEps τ 0 emNetCost = mergeOpC τ`. -/
@[simp] theorem mergeOpCEps_zero_em (τ : Nonplanar (α ⊕ β) → β)
    (lbl : α ⊕ β) (S S' : Nonplanar (α ⊕ β)) :
    mergeOpCEps τ (0 : R) emNetCost lbl S S' = mergeOpC τ lbl S S' := by
  rw [mergeOpCEps, emNetCost, epsWeight_zero_zero, one_smul]

/-- **MCB Prop 1.5.1, Internal Merge survives ε → 0.** IM has net cost 0 — the
    extraction `+d` and its own quotient's `−d` cancel — so its weight is `1` and
    the operator is preserved at ε = 0. -/
@[simp] theorem mergeOpCEps_zero_im (τ : Nonplanar (α ⊕ β) → β)
    (p : Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β))
    (lbl : α ⊕ β) (S S' : Nonplanar (α ⊕ β)) :
    mergeOpCEps τ (0 : R) (imNetCost p) lbl S S' = mergeOpC τ lbl S S' := by
  rw [mergeOpCEps, imNetCost_eq_zero, epsWeight_zero_zero, one_smul]

/-- **MCB Prop 1.5.1, Sideward Merge vanishes ε → 0.** A Sideward Merge has net
    cost `> 0` (the uncancelled extraction depth), so its weight `ε^{>0} = 0` at
    ε = 0: the operator is annihilated. -/
theorem mergeOpCEps_zero_sideward (τ : Nonplanar (α ⊕ β) → β) {c : ℕ} (hc : 0 < c)
    (lbl : α ⊕ β) (S S' : Nonplanar (α ⊕ β)) :
    mergeOpCEps τ (0 : R) c lbl S S' = 0 := by
  rw [mergeOpCEps, epsWeight_zero_of_pos hc, zero_smul]

/-- **MCB Prop 1.5.1, Sideward Merge vanishes** — instantiated at an actual Δ^c
    extraction `p` of a lexical-rooted object: the uncancelled depth makes
    `swNetCost p > 0`, so the operator is annihilated at ε = 0. -/
theorem mergeOpCEps_zero_sideward_of_cut (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) (a₀ : α) (hT : T.rootValue = Sum.inl a₀)
    (p : Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) (hp : p ∈ cutSummandsCN τ T)
    (hproper : p.1 ≠ 0) (lbl : α ⊕ β) (S S' : Nonplanar (α ⊕ β)) :
    mergeOpCEps τ (0 : R) (swNetCost p) lbl S S' = 0 :=
  mergeOpCEps_zero_sideward τ (swNetCost_pos τ T a₀ hT p hp hproper) lbl S S'

end Minimalist.Merge
