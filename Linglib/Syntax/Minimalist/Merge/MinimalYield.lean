import Linglib.Syntax.Minimalist.Merge.External
import Linglib.Core.Order.PullbackPreorder
import Mathlib.Order.OrderDual

/-!
# Minimal Yield (MCB Definition 1.6.1)
[marcolli-chomsky-berwick-2025] §1.6.1, Def 1.6.1 on book p. 63

Realises M-C-B's **Minimal Yield principle** as a predicate on forest
transformations and proves the per-merge counting characterizations of
**Prop 1.6.4** (EM/IM, book p. 66) and **Prop 1.6.8** (Sideward, book p. 69).

The principle (Def 1.6.1, eq. 1.6.2) asks three things of a transformation
`Φ`: `b₀(Φ F) ≤ b₀ F` (no divergence), `α(Φ F) ≥ α F` (no information loss),
and `σ(Φ F) = σ F + 1` (minimality of yield). MCB's parenthetical **weak
form** drops the last condition; we provide `MinimalYield` (strong) and
`MinimalYieldWeak` (the first two bounds only). The strong form rules out
Sideward 3(a)/3(b) under Δ^c, the weak form under Δ^d (p. 69).

## Per-merge signatures (Prop 1.6.4 + Prop 1.6.8)

| Merge | Δb₀ | Δα | Δσ | Strong | Weak |
|---|---|---|---|---|---|
| External (Δ^c, Δ^d) | −1 | +2 | +1 | ✓ | ✓ |
| Internal w/ Δ^c | 0 | +1 | +1 | ✓ | ✓ |
| Internal w/ Δ^d | 0 | 0 | 0 | ✗ (Δσ=0) | ✓ |
| Sideward 2(b) Δ^c | 0 | +1 | +1 | ✓ | ✓ |
| Sideward 2(b) Δ^d | 0 | 0 | 0 | ✗ (Δσ=0) | ✓ |
| Sideward 3(a) Δ^c | +1 | 0 | +1 | ✗ (Δb₀>0) | ✗ (Δb₀>0) |
| Sideward 3(a) Δ^d | +1 | −2 | −1 | ✗ (Δb₀>0) | ✗ (Δb₀>0) |
| Sideward 3(b) Δ^c | +1 | 0 | +1 | ✗ (Δb₀>0) | ✗ (Δb₀>0) |
| Sideward 3(b) Δ^d | +1 | −2 | −1 | ✗ (Δb₀>0) | ✗ (Δb₀>0) |

`sideward_3a_size_deltas_deletion` proves the 3(a)/Δ^d row generalized over
`numContractions c_i`, with `..._specific` recovering MCB's stated
(+1, −2, −1) for the 2-edge cut via `numContractions_twoEdge`.

IM/Δ^d and Sideward 2(b)/Δ^d share the (0, 0, 0) signature (**Remark 1.6.9**,
book p. 71): indistinguishable by sizes, separated only by No Complexity Loss
(`InducedMapNCL` / `sideward_2b_violatesInducedMapNCL` in `NoComplexityLoss.lean`).
Sideward 3(a)/3(b) are ruled out by both forms via Δb₀ > 0.

## TODO

Define the per-transformation lift `MinimalYieldTransformation Φ := ∀ F, MinimalYield F (Φ F)`
(and its weak analogue); the violation theorems here are currently stated on the
case-specific workspace shapes rather than on a `Φ`.
-/

namespace Minimalist.Merge

open ConnesKreimer TraceTree TraceForest

variable {α β : Type*}

/-- The weak Minimal Yield principle: a forest transformation does not
    increase `b₀` and does not decrease `α`. -/
structure MinimalYieldWeak (F F' : TraceForest α β) : Prop where
  noDivergence  : F'.b₀ ≤ F.b₀
  noInfoLoss    : F.alpha ≤ F'.alpha

/-- The Minimal Yield principle: the weak form together with `σ` increasing
    by exactly one. -/
structure MinimalYield (F F' : TraceForest α β) : Prop extends MinimalYieldWeak F F' where
  minimalYield  : F'.sigma = F.sigma + 1

/-! ### `MinimalYieldWeak` as a Pareto pullback preorder

The two `MinimalYieldWeak` bounds are a Pareto comparison on the `(b₀ᵒᵈ, α)`
signature (`b₀` dualised so fewer components ranks higher), sharing the
`PullbackPreorder` shape of `DerivationCost.pullbackPreorder` and
`Core.Optimization.paretoPullbackPreorder`. The strong form is outside this
picture: its `σ = +1` is an equality, not a ≤. -/

/-- The Pareto signature `(b₀ᵒᵈ, α)` of a forest, with `b₀` dualised so that
    fewer components ranks higher. -/
def MinimalYieldSignature (F : TraceForest α β) : ℕᵒᵈ × ℕ :=
  (OrderDual.toDual F.b₀, F.alpha)

/-- `MinimalYieldWeak F F'` is exactly the Pareto order on the `(b₀ᵒᵈ, α)`
    signature. -/
theorem minimalYieldWeak_iff_signature_le {F F' : TraceForest α β} :
    MinimalYieldWeak F F' ↔ MinimalYieldSignature F ≤ MinimalYieldSignature F' :=
  ⟨fun ⟨h_b, h_a⟩ => ⟨h_b, h_a⟩,
   fun ⟨h_b, h_a⟩ => ⟨h_b, h_a⟩⟩

/-- `MinimalYieldWeak` packaged as a `Core.Order.PullbackPreorder` via
    `MinimalYieldSignature`. Not a `Preorder TraceForest` instance:
    `TraceForest` already carries the multiset order. -/
def minimalYieldWeakPullbackPreorder :
    Core.Order.PullbackPreorder (TraceForest α β) (ℕᵒᵈ × ℕ) :=
  Core.Order.PullbackPreorder.ofProj MinimalYieldSignature
    (fun _ _ => inferInstance)

/-! ### External Merge -/

/-- External Merge of a pair satisfies Minimal Yield: Δb₀ = −1, Δα = +2, Δσ = +1. -/
theorem em_pair_satisfiesMinimalYield (S S' : TraceTree α β) :
    MinimalYield ({S, S'} : TraceForest α β)
                 ({.node S S'} : TraceForest α β) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;>
    simp only [Multiset.insert_eq_cons, b₀_singleton, b₀_cons, alpha_singleton, alpha_cons,
      accCount_merge, sigma_singleton, sigma_cons] <;>
    omega

/-! ### Internal Merge, Δ^d -/

/-- Internal Merge via composition leaves `b₀`, `α`, and `σ` unchanged (Δ^d counting). -/
theorem im_pair_size_deltas_deletion {T mover Q : TraceTree α β}
    (h : T.accCount = mover.accCount + Q.accCount + 2) :
    b₀ ({.node mover Q} : TraceForest α β)
        = b₀ ({T} : TraceForest α β)
      ∧
    alpha ({.node mover Q} : TraceForest α β)
        = alpha ({T} : TraceForest α β)
      ∧
    sigma ({.node mover Q} : TraceForest α β)
        = sigma ({T} : TraceForest α β) := by
  refine ⟨rfl, ?_, ?_⟩ <;>
    simp only [alpha_singleton, sigma_singleton, accCount_merge, h]

/-- `im_pair_size_deltas_deletion` with the size hypothesis discharged from a
    single-edge cut. -/
theorem im_pair_size_deltas_deletion_of_cut {T mover Q : TraceTree α β}
    (c : CutShape T) (h_cf : c.cutForest = ({mover} : TraceForest α β))
    (h_rd : c.remainderDeletion = some Q) :
    b₀ ({.node mover Q} : TraceForest α β)
        = b₀ ({T} : TraceForest α β)
      ∧
    alpha ({.node mover Q} : TraceForest α β)
        = alpha ({T} : TraceForest α β)
      ∧
    sigma ({.node mover Q} : TraceForest α β)
        = sigma ({T} : TraceForest α β) :=
  im_pair_size_deltas_deletion (CutShape.singleEdgeCut_deletion_alpha c mover Q h_cf h_rd)

/-! ### Internal Merge, Δ^c -/

/-- Internal Merge via composition leaves `b₀` fixed and raises `αᶜ` and `σᶜ`
    by one (Δ^c counting). -/
theorem im_pair_size_deltas_contraction [Inhabited β]
    {T β_t : TraceTree α β} (c : CutShape T)
    (h_tf : T.nonTraceSize = T.size)
    (h_cf : c.cutForest = ({β_t} : TraceForest α β)) :
    b₀ ({(.node β_t c.remainder : TraceTree α β)} : TraceForest α β)
        = b₀ ({T} : TraceForest α β)
      ∧
    alphaC ({(.node β_t c.remainder : TraceTree α β)} : TraceForest α β)
        = alphaC ({T} : TraceForest α β) + 1
      ∧
    sigmaC ({(.node β_t c.remainder : TraceTree α β)} : TraceForest α β)
        = sigmaC ({T} : TraceForest α β) + 1 := by
  have h_β_tf := CutShape.nonTraceSize_eq_size_of_cutForest_singleton c β_t h_tf h_cf
  have h_rem_pos : c.remainder.nonTraceSize ≥ 1 :=
    CutShape.nonTraceSize_remainder_pos_of_cutForest_singleton c β_t h_cf
  have h_β_pos : β_t.nonTraceSize ≥ 1 := by rw [h_β_tf]; exact β_t.size_pos
  refine ⟨rfl, ?_, ?_⟩ <;>
    simp only [alphaC_singleton, sigmaC_singleton,
      accCountC_merge β_t c.remainder h_β_pos h_rem_pos,
      CutShape.singleEdgeCut_contraction_alpha c β_t h_tf h_cf]
  omega

/-! ### Sideward Merge -/

/-- Sideward Merge of type 2(b) leaves the component count `b₀` unchanged. -/
theorem sideward_2b_b₀_preserved (T_i T_j Tnode T_j_q : TraceTree α β) :
    b₀ ({Tnode, T_j_q} : TraceForest α β)
      = b₀ ({T_i, T_j} : TraceForest α β) := by
  simp only [Multiset.insert_eq_cons, b₀_cons, b₀_singleton]

/-- Sideward Merge of type 2(b) leaves `b₀`, `α`, and `σ` unchanged (Δ^d counting). -/
theorem sideward_2b_size_deltas_deletion
    {T_i T_j β_t Tnode T_j_q : TraceTree α β}
    (h_T_j : T_j.accCount = β_t.accCount + T_j_q.accCount + 2)
    (h_node : Tnode.accCount = T_i.accCount + β_t.accCount + 2) :
    b₀ ({Tnode, T_j_q} : TraceForest α β)
        = b₀ ({T_i, T_j} : TraceForest α β)
      ∧
    alpha ({Tnode, T_j_q} : TraceForest α β)
        = alpha ({T_i, T_j} : TraceForest α β)
      ∧
    sigma ({Tnode, T_j_q} : TraceForest α β)
        = sigma ({T_i, T_j} : TraceForest α β) := by
  refine ⟨sideward_2b_b₀_preserved T_i T_j Tnode T_j_q, ?_, ?_⟩ <;>
    simp only [Multiset.insert_eq_cons, alpha_cons, alpha_singleton, sigma_cons,
      sigma_singleton, h_T_j, h_node] <;>
    omega

/-- `sideward_2b_size_deltas_deletion` with both hypotheses discharged from a
    single-edge cut. -/
theorem sideward_2b_size_deltas_deletion_of_cut
    {T_i T_j β_t T_j_q : TraceTree α β}
    (c : CutShape T_j) (h_cf : c.cutForest = ({β_t} : TraceForest α β))
    (h_rd : c.remainderDeletion = some T_j_q) :
    b₀ ({(.node T_i β_t : TraceTree α β), T_j_q} : TraceForest α β)
        = b₀ ({T_i, T_j} : TraceForest α β)
      ∧
    alpha ({(.node T_i β_t : TraceTree α β), T_j_q}
                          : TraceForest α β)
        = alpha ({T_i, T_j} : TraceForest α β)
      ∧
    sigma ({(.node T_i β_t : TraceTree α β), T_j_q}
                          : TraceForest α β)
        = sigma ({T_i, T_j} : TraceForest α β) :=
  sideward_2b_size_deltas_deletion
    (CutShape.singleEdgeCut_deletion_alpha c β_t T_j_q h_cf h_rd)
    (accCount_merge T_i β_t)

/-- Sideward Merge of type 2(b) leaves `b₀` fixed and raises `αᶜ` and `σᶜ`
    by one (Δ^c counting). -/
theorem sideward_2b_size_deltas_contraction [Inhabited β]
    {T_i T_j β_t : TraceTree α β}
    (c : CutShape T_j) (h_T_j_tf : T_j.nonTraceSize = T_j.size)
    (h_T_i_tf : T_i.nonTraceSize = T_i.size)
    (h_cf : c.cutForest = ({β_t} : TraceForest α β)) :
    b₀ ({(.node T_i β_t : TraceTree α β), c.remainder} : TraceForest α β)
        = b₀ ({T_i, T_j} : TraceForest α β)
      ∧
    alphaC ({(.node T_i β_t : TraceTree α β), c.remainder} : TraceForest α β)
        = alphaC ({T_i, T_j} : TraceForest α β) + 1
      ∧
    sigmaC ({(.node T_i β_t : TraceTree α β), c.remainder} : TraceForest α β)
        = sigmaC ({T_i, T_j} : TraceForest α β) + 1 := by
  have h_β_tf := CutShape.nonTraceSize_eq_size_of_cutForest_singleton c β_t h_T_j_tf h_cf
  have h_rem_pos : c.remainder.nonTraceSize ≥ 1 :=
    CutShape.nonTraceSize_remainder_pos_of_cutForest_singleton c β_t h_cf
  have h_β_pos : β_t.nonTraceSize ≥ 1 := by rw [h_β_tf]; exact β_t.size_pos
  have h_T_i_pos : T_i.nonTraceSize ≥ 1 := by rw [h_T_i_tf]; exact T_i.size_pos
  refine ⟨sideward_2b_b₀_preserved T_i T_j _ c.remainder, ?_, ?_⟩ <;>
    simp only [Multiset.insert_eq_cons, alphaC_cons, alphaC_singleton, sigmaC_cons,
      sigmaC_singleton, accCountC_merge T_i β_t h_T_i_pos h_β_pos,
      CutShape.singleEdgeCut_contraction_alpha c β_t h_T_j_tf h_cf] <;>
    omega

/-- Sideward Merge of type 3(a) increases the component count `b₀` by one. -/
theorem sideward_3a_b₀_increases (T_i Tnode T_iq : TraceTree α β) :
    b₀ ({Tnode, T_iq} : TraceForest α β)
      = b₀ ({T_i} : TraceForest α β) + 1 := by
  simp only [Multiset.insert_eq_cons, b₀_cons, b₀_singleton]

/-- Sideward Merge of type 3(b) increases the component count `b₀` by one. -/
theorem sideward_3b_b₀_increases
    (T_i T_j Tnode T_iq T_jq : TraceTree α β) :
    b₀ ({Tnode, T_iq, T_jq} : TraceForest α β)
      = b₀ ({T_i, T_j} : TraceForest α β) + 1 := by
  simp only [Multiset.insert_eq_cons, b₀_cons, b₀_singleton]

/-- Sideward Merge of type 3(b): Δb₀ = +1, Δα = −2, Δσ = −1 (Δ^d counting). -/
theorem sideward_3b_size_deltas_deletion
    {T_i T_j a b T_iq T_jq : TraceTree α β}
    (h_i : T_i.accCount = a.accCount + T_iq.accCount + 2)
    (h_j : T_j.accCount = b.accCount + T_jq.accCount + 2) :
    b₀ ({(.node a b : TraceTree α β), T_iq, T_jq} : TraceForest α β)
        = b₀ ({T_i, T_j} : TraceForest α β) + 1
      ∧
    alpha ({(.node a b : TraceTree α β), T_iq, T_jq}
                          : TraceForest α β) + 2
        = alpha ({T_i, T_j} : TraceForest α β)
      ∧
    sigma ({(.node a b : TraceTree α β), T_iq, T_jq}
                          : TraceForest α β) + 1
        = sigma ({T_i, T_j} : TraceForest α β) := by
  refine ⟨sideward_3b_b₀_increases T_i T_j _ T_iq T_jq, ?_, ?_⟩ <;>
    simp only [Multiset.insert_eq_cons, alpha_cons, alpha_singleton, sigma_cons,
      sigma_singleton, accCount_merge, h_i, h_j] <;>
    omega

/-- `sideward_3b_size_deltas_deletion` with both size hypotheses discharged from
    single-edge cuts. -/
theorem sideward_3b_size_deltas_deletion_of_cut
    {T_i T_j a b T_iq T_jq : TraceTree α β}
    (c_i : CutShape T_i) (h_cf_i : c_i.cutForest = ({a} : TraceForest α β))
    (h_rd_i : c_i.remainderDeletion = some T_iq)
    (c_j : CutShape T_j) (h_cf_j : c_j.cutForest = ({b} : TraceForest α β))
    (h_rd_j : c_j.remainderDeletion = some T_jq) :
    b₀ ({(.node a b : TraceTree α β), T_iq, T_jq} : TraceForest α β)
        = b₀ ({T_i, T_j} : TraceForest α β) + 1
      ∧
    alpha ({(.node a b : TraceTree α β), T_iq, T_jq}
                          : TraceForest α β) + 2
        = alpha ({T_i, T_j} : TraceForest α β)
      ∧
    sigma ({(.node a b : TraceTree α β), T_iq, T_jq}
                          : TraceForest α β) + 1
        = sigma ({T_i, T_j} : TraceForest α β) :=
  sideward_3b_size_deltas_deletion
    (CutShape.singleEdgeCut_deletion_alpha c_i a T_iq h_cf_i h_rd_i)
    (CutShape.singleEdgeCut_deletion_alpha c_j b T_jq h_cf_j h_rd_j)

/-! ### Sideward 3(a): two-edge cut full deltas -/

/-- Sideward Merge of type 3(a): Δb₀ = +1, with Δα and Δσ governed by the
    cut's contraction count `numContractions c_i` (Δ^d counting). -/
theorem sideward_3a_size_deltas_deletion
    {T_i a b T_iq : TraceTree α β} (c_i : CutShape T_i)
    (h_cf : c_i.cutForest = ({a, b} : TraceForest α β))
    (h_rd : c_i.remainderDeletion = some T_iq) :
    b₀ ({(.node a b : TraceTree α β), T_iq} : TraceForest α β)
        = b₀ ({T_i} : TraceForest α β) + 1
      ∧
    alpha ({(.node a b : TraceTree α β), T_iq} : TraceForest α β)
        + CutShape.numContractions c_i
        = alpha ({T_i} : TraceForest α β)
      ∧
    sigma ({(.node a b : TraceTree α β), T_iq} : TraceForest α β)
        + CutShape.numContractions c_i
        = sigma ({T_i} : TraceForest α β) + 1 := by
  have h := CutShape.pairCut_deletion_alpha c_i a b T_iq h_cf h_rd
  refine ⟨sideward_3a_b₀_increases T_i _ T_iq, ?_, ?_⟩ <;>
    simp only [Multiset.insert_eq_cons, alpha_cons, alpha_singleton, sigma_cons,
      sigma_singleton, accCount_merge, h] <;>
    omega

/-- `sideward_3a_size_deltas_deletion` for a genuine 2-edge cut: Δb₀ = +1,
    Δα = −2, Δσ = −1 (the contraction count is `2`). -/
theorem sideward_3a_size_deltas_deletion_specific
    {T_i a b T_iq : TraceTree α β} (c_i : CutShape T_i)
    (h_cf : c_i.cutForest = ({a, b} : TraceForest α β))
    (h_rd : c_i.remainderDeletion = some T_iq) :
    b₀ ({(.node a b : TraceTree α β), T_iq} : TraceForest α β)
        = b₀ ({T_i} : TraceForest α β) + 1
      ∧
    alpha ({(.node a b : TraceTree α β), T_iq} : TraceForest α β) + 2
        = alpha ({T_i} : TraceForest α β)
      ∧
    sigma ({(.node a b : TraceTree α β), T_iq} : TraceForest α β) + 1
        = sigma ({T_i} : TraceForest α β) := by
  have h_card : c_i.cutForest.card = 2 := by
    rw [h_cf, show ({a, b} : TraceForest α β) = a ::ₘ ({b} : TraceForest α β) from rfl,
        Multiset.card_cons, Multiset.card_singleton]
  have h_nc := CutShape.numContractions_twoEdge c_i T_iq h_card h_rd
  have ⟨h_b₀, h_α, h_σ⟩ := sideward_3a_size_deltas_deletion c_i h_cf h_rd
  rw [h_nc] at h_α h_σ
  refine ⟨h_b₀, h_α, ?_⟩
  omega

/-- Sideward Merge of type 3(a): Δb₀ = +1, Δαᶜ = 0, Δσᶜ = +1 (Δ^c counting). -/
theorem sideward_3a_size_deltas_contraction [Inhabited β]
    {T_i a b : TraceTree α β} (c_i : CutShape T_i)
    (h_T_i_tf : T_i.nonTraceSize = T_i.size)
    (h_cf : c_i.cutForest = ({a, b} : TraceForest α β)) :
    b₀ ({(.node a b : TraceTree α β), c_i.remainder} : TraceForest α β)
        = b₀ ({T_i} : TraceForest α β) + 1
      ∧
    alphaC ({(.node a b : TraceTree α β), c_i.remainder} : TraceForest α β)
        = alphaC ({T_i} : TraceForest α β)
      ∧
    sigmaC ({(.node a b : TraceTree α β), c_i.remainder} : TraceForest α β)
        = sigmaC ({T_i} : TraceForest α β) + 1 := by
  have h_a_tf : a.nonTraceSize = a.size := by
    apply CutShape.nonTraceSize_eq_size_of_mem_cutForest c_i a h_T_i_tf
    rw [h_cf]; exact Multiset.mem_cons_self _ _
  have h_b_tf : b.nonTraceSize = b.size := by
    apply CutShape.nonTraceSize_eq_size_of_mem_cutForest c_i b h_T_i_tf
    rw [h_cf]
    rw [show ({a, b} : TraceForest α β) = a ::ₘ ({b} : TraceForest α β) from rfl,
        Multiset.mem_cons]
    right; exact Multiset.mem_singleton.mpr rfl
  have h_rem_pos : c_i.remainder.nonTraceSize ≥ 1 := by
    cases T_i with
    | leaf _ =>
        cases c_i; simp only [CutShape.cutForest] at h_cf
        have : a ∈ ({a, b} : TraceForest α β) := Multiset.mem_cons_self _ _
        rw [← h_cf] at this; exact absurd this (Multiset.notMem_zero _)
    | trace _ =>
        cases c_i; simp only [CutShape.cutForest] at h_cf
        have : a ∈ ({a, b} : TraceForest α β) := Multiset.mem_cons_self _ _
        rw [← h_cf] at this; exact absurd this (Multiset.notMem_zero _)
    | node _ _ => exact CutShape.nonTraceSize_remainder_pos_of_node c_i
  have h_a_pos : a.nonTraceSize ≥ 1 := by rw [h_a_tf]; exact a.size_pos
  have h_b_pos : b.nonTraceSize ≥ 1 := by rw [h_b_tf]; exact b.size_pos
  refine ⟨sideward_3a_b₀_increases T_i _ c_i.remainder, ?_, ?_⟩ <;>
    simp only [Multiset.insert_eq_cons, alphaC_cons, alphaC_singleton, sigmaC_cons,
      sigmaC_singleton, accCountC_merge a b h_a_pos h_b_pos,
      CutShape.pairCut_contraction_alpha c_i a b h_T_i_tf h_cf h_rem_pos] <;>
    omega

/-- Sideward Merge of type 3(b): Δb₀ = +1, Δαᶜ = 0, Δσᶜ = +1 (Δ^c counting). -/
theorem sideward_3b_size_deltas_contraction [Inhabited β]
    {T_i T_j a b : TraceTree α β}
    (c_i : CutShape T_i) (h_T_i_tf : T_i.nonTraceSize = T_i.size)
    (h_cf_i : c_i.cutForest = ({a} : TraceForest α β))
    (c_j : CutShape T_j) (h_T_j_tf : T_j.nonTraceSize = T_j.size)
    (h_cf_j : c_j.cutForest = ({b} : TraceForest α β)) :
    b₀ ({(.node a b : TraceTree α β), c_i.remainder, c_j.remainder}
                       : TraceForest α β)
        = b₀ ({T_i, T_j} : TraceForest α β) + 1
      ∧
    alphaC ({(.node a b : TraceTree α β), c_i.remainder, c_j.remainder}
                          : TraceForest α β)
        = alphaC ({T_i, T_j} : TraceForest α β)
      ∧
    sigmaC ({(.node a b : TraceTree α β), c_i.remainder, c_j.remainder}
                          : TraceForest α β)
        = sigmaC ({T_i, T_j} : TraceForest α β) + 1 := by
  have h_a_tf := CutShape.nonTraceSize_eq_size_of_cutForest_singleton c_i a h_T_i_tf h_cf_i
  have h_b_tf := CutShape.nonTraceSize_eq_size_of_cutForest_singleton c_j b h_T_j_tf h_cf_j
  have h_a_pos : a.nonTraceSize ≥ 1 := by rw [h_a_tf]; exact a.size_pos
  have h_b_pos : b.nonTraceSize ≥ 1 := by rw [h_b_tf]; exact b.size_pos
  refine ⟨sideward_3b_b₀_increases _ _ _ c_i.remainder c_j.remainder, ?_, ?_⟩ <;>
    simp only [Multiset.insert_eq_cons, alphaC_cons, alphaC_singleton, sigmaC_cons,
      sigmaC_singleton, accCountC_merge a b h_a_pos h_b_pos,
      CutShape.singleEdgeCut_contraction_alpha c_i a h_T_i_tf h_cf_i,
      CutShape.singleEdgeCut_contraction_alpha c_j b h_T_j_tf h_cf_j] <;>
    omega

/-- Sideward Merge of type 3(a) violates the weak Minimal Yield principle, since
    `b₀` increases. -/
theorem sideward_3a_violates_noDivergenceWeak
    (T_i Tnode T_iq : TraceTree α β) :
    ¬ MinimalYieldWeak ({T_i} : TraceForest α β)
                       ({Tnode, T_iq} : TraceForest α β) := by
  intro h
  have hd := h.noDivergence
  rw [sideward_3a_b₀_increases T_i Tnode T_iq] at hd
  omega

/-- Sideward Merge of type 3(b) violates the weak Minimal Yield principle, since
    `b₀` increases. -/
theorem sideward_3b_violates_noDivergenceWeak
    (T_i T_j Tnode T_iq T_jq : TraceTree α β) :
    ¬ MinimalYieldWeak ({T_i, T_j} : TraceForest α β)
                       ({Tnode, T_iq, T_jq} : TraceForest α β) := by
  intro h
  have hd := h.noDivergence
  rw [sideward_3b_b₀_increases T_i T_j Tnode T_iq T_jq] at hd
  omega

/-- Strong-form corollary of `sideward_3a_violates_noDivergenceWeak`. -/
theorem sideward_3a_violates_noDivergence (T_i Tnode T_iq : TraceTree α β) :
    ¬ MinimalYield ({T_i} : TraceForest α β)
                   ({Tnode, T_iq} : TraceForest α β) :=
  fun h => sideward_3a_violates_noDivergenceWeak T_i Tnode T_iq h.toMinimalYieldWeak

/-- Strong-form corollary of `sideward_3b_violates_noDivergenceWeak`. -/
theorem sideward_3b_violates_noDivergence
    (T_i T_j Tnode T_iq T_jq : TraceTree α β) :
    ¬ MinimalYield ({T_i, T_j} : TraceForest α β)
                   ({Tnode, T_iq, T_jq} : TraceForest α β) :=
  fun h => sideward_3b_violates_noDivergenceWeak T_i T_j Tnode T_iq T_jq h.toMinimalYieldWeak

/-! ### Unit merge -/

/-- The unit-merge stage `{T} → {β, T/β}` violates the weak Minimal Yield
    principle, since `b₀` increases. -/
theorem unitMerge_violates_noDivergenceWeak (T β_t Q : TraceTree α β) :
    ¬ MinimalYieldWeak ({T} : TraceForest α β)
                       ({β_t, Q} : TraceForest α β) :=
  sideward_3a_violates_noDivergenceWeak T β_t Q

/-- Strong-form corollary of `unitMerge_violates_noDivergenceWeak`. -/
theorem unitMerge_violates_noDivergence (T β_t Q : TraceTree α β) :
    ¬ MinimalYield ({T} : TraceForest α β)
                   ({β_t, Q} : TraceForest α β) :=
  sideward_3a_violates_noDivergence T β_t Q

end Minimalist.Merge
