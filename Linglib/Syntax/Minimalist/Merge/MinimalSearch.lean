import Linglib.Syntax.Minimalist.Merge.Basic
import Linglib.Core.Algebra.RootedTree.Coproduct.GenericNonplanar
import Linglib.Syntax.Minimalist.Workspace.Conservation

set_option autoImplicit false

/-!
# Minimal Search: the generic (cut-policy-parameterized) Merge operator
[marcolli-chomsky-berwick-2025]

MCB's Merge variants and the three coproducts (Δ^ρ/Δ^c/Δ^d) share one operator
shape `M = ⊔ ∘ (B ⊗ id) ∘ δ_{S,S'} ∘ Δ`, differing only in the coproduct `Δ`.
`mergeOpG cuts` parameterizes the operator over the cut enumeration (via
`comulAlgHomNG`), recovering the Δ^ρ `mergeOp` as the instance
`cuts := cutSummandsN` (definitional) and defining the Δ^c Merge `mergeOpC τ` as
`cuts := cutSummandsCN τ`. This is the operator-level companion to the
already-generic cut layer (`cutSummandsG`).

The Δ^c instance is the home of the **Minimal-Search ε arc** (MCB §1.5,
Prop 1.5.1): the trace coproduct is where extraction depth is recoverable
(`RootedTree.Cut.depthC`), so the ε-weighted graft and the ε → 0
Sideward-elimination belong on `mergeOpC`, not the Δ^ρ `mergeOp`.

## Main definitions

* `mergeOpG cuts lbl S S'` — the generic Merge operator.
* `mergeOp_eq_G` — the Δ^ρ `mergeOp` is `mergeOpG cutSummandsN` (definitional).
* `mergeOpC τ lbl S S'` — the Δ^c Merge operator.
* `epsWeight`, `emNetCost`/`imNetCost`/`swNetCost` — the Minimal-Search ε-weight
  and the per-merge net costs (EM/IM = 0, Sideward > 0).
* `mergeOpCEps τ ε c` — the ε-weighted Δ^c Merge (`ε^c • mergeOpC`).
* `mergeOpCEps_zero_em`, `mergeOpCEps_zero_im`, `mergeOpCEps_zero_sideward` —
  **MCB Proposition 1.5.1**: at ε → 0, External and Internal Merge survive
  (`1 • M = M`), Sideward Merge vanishes (`0 • M = 0`).
-/

namespace Minimalist.Merge

open scoped TensorProduct
open RootedTree RootedTree.ConnesKreimer

variable {R : Type*} [CommSemiring R] {α : Type*}

/-- The **generic Merge operator** `M_{S,S'}^{cuts}`, parameterized by the cut
    enumeration `cuts`: `mergePost lbl S S' ∘ comulAlgHomNG cuts`. The
    coproduct-agnostic post-chain `mergePost` (graft `B`, δ-projection, and
    multiplication `⊔`) is shared; only the coproduct `comulAlgHomNG cuts`
    varies. -/
noncomputable def mergeOpG [DecidableEq (Nonplanar α)]
    (cuts : Nonplanar α → Multiset (Forest (Nonplanar α) × Nonplanar α))
    (lbl : α) (S S' : Nonplanar α) :
    ConnesKreimer R (Nonplanar α) →ₗ[R] ConnesKreimer R (Nonplanar α) :=
  mergePost (R := R) (α := α) lbl S S' ∘ₗ (comulAlgHomNG cuts).toLinearMap

/-- The Δ^ρ Merge operator `mergeOp` is the generic operator at
    `cuts := cutSummandsN` — definitional, since `comulAlgHomN = comulAlgHomNG
    cutSummandsN`. -/
theorem mergeOp_eq_G [DecidableEq (Nonplanar α)] (lbl : α) (S S' : Nonplanar α) :
    mergeOp (R := R) lbl S S' = mergeOpG (R := R) cutSummandsN lbl S S' := rfl

/-- The **Δ^c (trace) Merge operator** `mergeOpC τ`, the generic operator at
    `cuts := cutSummandsCN τ`. Unlike the Δ^ρ `mergeOp`, this coproduct's
    quotients carry a trace leaf at each cut site at exactly the cut depth, so
    the Minimal-Search cost `Cut.depthC` is recoverable — making `mergeOpC` the
    faithful home of MCB's ε-weighted Merge (§1.5). -/
noncomputable def mergeOpC {β : Type*} [DecidableEq (Nonplanar (α ⊕ β))]
    (τ : Nonplanar (α ⊕ β) → β) (lbl : α ⊕ β) (S S' : Nonplanar (α ⊕ β)) :
    ConnesKreimer R (Nonplanar (α ⊕ β)) →ₗ[R] ConnesKreimer R (Nonplanar (α ⊕ β)) :=
  mergeOpG (R := R) (cutSummandsCN τ) lbl S S'

/-! ## The Minimal-Search ε arc (MCB §1.5, Prop 1.5.1)

The ε-weighted Merge `M^ε = ⊔ ∘ (Bᵉ ⊗ id) ∘ δ ∘ Δ` (eq 1.5.1) scales the graft
`Bᵉ(α⊔β) = ε^{c(𝔐(α,β))} B(α⊔β)` (eq 1.5.2) by the Minimal-Search cost `ε^c`.
Since `mergePost` is linear and the graft is its only creation, scaling the
graft by `ε^c` equals scaling the whole operator: `mergeOpCEps = ε^c • mergeOpC`.
The net cost `c` is the sum of the two operands' signed depth-costs (MCB rules
1–2, `RootedTree.Cut.extractionCost`/`quotientCost`):

* **EM** `𝔐(T_i, T_j)`: both whole, `c = 0`.
* **IM** `𝔐(T_v, T_i/T_v)`: extracted crown `+d` and its own quotient `−d`
  cancel, `c = 0`.
* **Sideward** `𝔐(T_v, T')`: the crown's `+d` is uncancelled (no quotient
  operand), `c = d > 0`.

At ε → 0, `ε^0 = 1` keeps EM/IM, `ε^{d>0} = 0` drops Sideward. -/

/-- The **Minimal-Search ε-weight** of a merge with net cost `c`: `ε^c`
    (MCB eq 1.5.2). -/
def epsWeight (ε : R) (c : ℕ) : R := ε ^ c

@[simp] theorem epsWeight_zero_zero : epsWeight (0 : R) 0 = 1 := pow_zero 0

theorem epsWeight_zero_of_pos {c : ℕ} (hc : 0 < c) : epsWeight (0 : R) c = 0 :=
  zero_pow (Nat.pos_iff_ne_zero.mp hc)

@[simp] theorem epsWeight_one (c : ℕ) : epsWeight (1 : R) c = 1 := one_pow c

end Minimalist.Merge

namespace Minimalist.Merge

open scoped TensorProduct
open RootedTree RootedTree.ConnesKreimer

variable {R : Type*} [CommSemiring R] {α β : Type*}

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
