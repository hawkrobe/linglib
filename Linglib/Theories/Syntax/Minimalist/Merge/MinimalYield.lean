import Linglib.Theories.Syntax.Minimalist.Merge.External
import Linglib.Theories.Syntax.Minimalist.Merge.Internal
import Linglib.Core.Order.FeaturePreorder
import Mathlib.Order.OrderDual

/-!
# Minimal Yield (MCB Definition 1.6.1)
@cite{marcolli-chomsky-berwick-2025} §1.6.1, book p. 63

Realises M-C-B's **Minimal Yield principle** (Def 1.6.1) as a predicate on
forest transformations, plus the per-merge counting characterization of
**Proposition 1.6.4** (book p. 66) and **Proposition 1.6.8** (book p. 69)
for the EM/IM/Sideward cases.

## Definition (verbatim, MCB Def 1.6.1, book p. 63 + eq. 1.6.2)

A transformation `Φ : 𝓕_SO₀ → 𝓕_SO₀` satisfies the Minimal Yield principle
if the following conditions hold:

  b₀(Φ(F)) ≤ b₀(F)        (no divergence)
  α(Φ(F)) ≥ α(F)          (no information loss)
  σ(Φ(F)) = σ(F) + 1      (minimality of yield)

MCB also implicitly invokes a **weak form** that drops the third condition
(book p. 69 says Sideward 3(a)/3(b) are "ruled out by the Minimal Yield
principle, in the strong form (for Δ^c) or in the weak form (for Δ^d)").
We provide both `MinimalYield` (strong) and `MinimalYieldWeak` (drops
`minimalYield`).

## Per-merge characterization (MCB Prop 1.6.4 + Prop 1.6.8)

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

The 3(a)/Δ^d row matches MCB Prop 1.6.8 (book p. 69) for the elementary
admissible 2-edge cut on T_a (where `numContractions = 2`). Our
`sideward_3a_size_deltas_deltaD` proves a strict generalization
parameterized by `numContractions c_i ∈ {1, 2}`, with
`sideward_3a_size_deltas_deltaD_specific` (corollary via
`numContractions_twoEdge`) recovering MCB's stated (+1, −2, −1).

The Sideward 2(b)/Δ^c row is **the same as IM/Δ^c** for sizes — Remark
1.6.9 (book p. 71) explicitly notes that 2(b) is indistinguishable from
IM by sizes alone in either Δ^c or Δ^d. NCL (`InducedMapNCL`) is what
discriminates them.

EM survives both forms unconditionally. IM/Δ^d and Sideward 2(b) produce
identical (Δb₀, Δα, Δσ) signatures (Remark 1.6.9, book p. 71) — they are
distinguished only by NCL (`NoComplexityLoss`). Sideward 3(a)/3(b) are
ruled out by the strong AND weak forms via Δb₀ > 0 (`noDivergence` violation).

## Out of scope (queued)

- Full (Δα, Δσ) tables for Sideward 2(b)/3(a)/3(b) under Δ^c (need Δ^c
  substrate; only Δ^d is implemented).
- Sideward NCL negative direction (MCB Prop 1.6.10 negative): linglib's
  `NCLBetween` is existential; MCB Def 1.6.2 specifies the unique induced
  map `Φ₀ : π₀(F) → π₀(Φ(F))`. Bridging requires either strengthening
  `NCLBetween` or adding an `InducedMapNCL` predicate.
- Per-transformation lifting `MinimalYieldTransformation Φ := ∀ F, MinimalYield F (Φ F)`.
-/

namespace Minimalist.Merge

open ConnesKreimer

variable {α β : Type*}

/-- **Minimal Yield principle, weak form** (M-C-B Def 1.6.1, book p. 63
    parenthetical: "One can consider a weaker form by only requiring the
    two bounds on b₀ and α."). Used at p. 69 to rule out Sideward
    3(a)/3(b) under Δ^d. Keeps `noDivergence` and `noInfoLoss`; drops the
    `minimalYield` (σ = +1) condition that the strong form has. -/
structure MinimalYieldWeak (F F' : TraceForest α β) : Prop where
  noDivergence  : F'.b₀ ≤ F.b₀
  noInfoLoss    : F.alpha ≤ F'.alpha

/-- **Minimal Yield principle, strong form** (M-C-B Def 1.6.1, book p. 63 +
    eq. 1.6.2). The strong form `extends` the weak form by adding the
    third condition `σ(F') = σ(F) + 1` ("minimality of yield"). The
    `toWeak` projection is now automatic via `MinimalYield.toMinimalYieldWeak`. -/
structure MinimalYield (F F' : TraceForest α β) : Prop extends MinimalYieldWeak F F' where
  minimalYield  : F'.sigma = F.sigma + 1

/-- Strong implies weak (auto-projection alias). -/
abbrev MinimalYield.toWeak {F F' : TraceForest α β} (h : MinimalYield F F') :
    MinimalYieldWeak F F' :=
  h.toMinimalYieldWeak

/-! ## §0.5: `MinimalYieldWeak` as a Pareto pullback preorder

The two `MinimalYieldWeak` conditions are exactly a Pareto comparison
on the `(b₀ᵒᵈ, α)` signature: `noDivergence` reverses the order on `b₀`
(smaller is "better"), `noInfoLoss` keeps `α` in the natural direction
(larger is "better"). Wrapping the relation as a
`Core.Order.FeaturePreorder` exposes this Pareto structure: same shape
as `Minimalist.DerivationCost.featurePreorder` (4-d cost) and
`Core.Constraint.ConstraintSystem.paretoFeaturePreorder` (OT/HG
violation profile).

Reflexivity (`MYWeak F F`) and transitivity (`MYWeak F F' → MYWeak F' F'' →
MYWeak F F''`) come for free as the underlying `Preorder.lift` instance.
The strong form (`MinimalYield`) drops out of this picture because its
`σ = +1` constraint is an *equality*, not a ≤; treat it as MY-Weak plus
a separate σ-step witness. -/

/-- The Pareto signature for MinimalYieldWeak: pull a forest back to
    the `(b₀ᵒᵈ, α)` feature space. The `OrderDual` on `b₀` flips its
    ≤ so that "smaller `b₀`" becomes "larger feature" — matching the
    MCB sign convention where merges that reduce workspace component
    count are preferred. -/
def MinimalYieldSignature (F : TraceForest α β) : ℕᵒᵈ × ℕ :=
  (OrderDual.toDual F.b₀, F.alpha)

/-- `MinimalYieldWeak F F'` is exactly the pullback Pareto-≤ on the
    `(b₀ᵒᵈ, α)` signature. By `OrderDual.toDual_le_toDual := Iff.rfl`
    and `Prod`'s componentwise preorder, this collapses to MYWeak's
    two ≤ conditions definitionally. -/
@[simp] theorem minimalYieldWeak_iff_signature_le {F F' : TraceForest α β} :
    MinimalYieldWeak F F' ↔ MinimalYieldSignature F ≤ MinimalYieldSignature F' :=
  ⟨fun ⟨h_b, h_a⟩ => ⟨h_b, h_a⟩,
   fun ⟨h_b, h_a⟩ => ⟨h_b, h_a⟩⟩

/-- `MinimalYieldWeak` packaged as a `Core.Order.FeaturePreorder` over
    `TraceForest α β`, with feature space `ℕᵒᵈ × ℕ` (Pareto pullback
    via `MinimalYieldSignature`). Same shape as
    `Minimalist.DerivationCost.featurePreorder`.

    Note: not registered as a `Preorder TraceForest` instance because
    `TraceForest = Multiset` already carries other order structures
    (multiset ⊆); use `.toPreorder` explicitly when chain reasoning is
    needed. -/
def minimalYieldWeakFeaturePreorder :
    Core.Order.FeaturePreorder (TraceForest α β) (ℕᵒᵈ × ℕ) :=
  Core.Order.FeaturePreorder.ofFeature MinimalYieldSignature
    (fun _ _ => inferInstance)

/-! ## §1: EM Case 1 satisfies MinimalYield (MCB Prop 1.6.4 EM row)
-/

/-- **EM Case 1, F̂ = ∅** (MCB Prop 1.6.4 EM row, book p. 66). External
    Merge of two member components `S, S'` produces the singleton
    `{.node S S'}`. Δb₀ = −1, Δα = +2, Δσ = +1. -/
theorem em_pair_satisfiesMinimalYield (S S' : TraceTree α β) :
    MinimalYield ({S, S'} : TraceForest α β)
                 ({.node S S'} : TraceForest α β) := by
  have hS := S.size_pos
  have hS' := S'.size_pos
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [TraceForest.b₀_singleton, Multiset.insert_eq_cons, TraceForest.b₀_cons,
        TraceForest.b₀_singleton]
    omega
  · rw [TraceForest.alpha_singleton, TraceTree.accCount_node, Multiset.insert_eq_cons,
        TraceForest.alpha_cons, TraceForest.alpha_singleton]
    show TraceTree.accCount S + TraceTree.accCount S' ≤ S.size + S'.size
    show S.size - 1 + (S'.size - 1) ≤ S.size + S'.size
    omega
  · rw [TraceForest.sigma_singleton, TraceTree.accCount_node, Multiset.insert_eq_cons,
        TraceForest.sigma_cons, TraceForest.sigma_singleton]
    show 1 + (S.size + S'.size) = 1 + TraceTree.accCount S + (1 + TraceTree.accCount S') + 1
    show 1 + (S.size + S'.size) = 1 + (S.size - 1) + (1 + (S'.size - 1)) + 1
    omega

/-! ## §2: IM size deltas under Δ^d (MCB Prop 1.6.4 IM/Δ^d row)
-/

/-- **IM via composition (Δ^d)** (MCB Prop 1.6.4 IM/Δ^d row, book p. 66).
    Under the size-conservation hypothesis `T.size = mover.size + Q.size + 1`
    (the size analog of `cut_leafCount_conservation`), IM `{T} → {.node mover Q}`
    preserves all three measures: Δb₀ = 0, Δα = 0, Δσ = 0.

    IM under Δ^d satisfies `MinimalYieldWeak` but NOT `MinimalYield` (the
    strong form requires Δσ = +1; under Δ^c IM gives Δσ = +1 instead).
    See MCB Remark 1.6.6 (book p. 67) on the Δ^c vs Δ^d counting difference.

    The hypothesis `h_size : T.size = mover.size + Q.size + 1` is the size
    analog of `cut_leafCount_conservation`; `im_pair_size_deltas_deltaD_of_cut`
    below discharges it from a single-edge cut on `T`. -/
theorem im_pair_size_deltas_deltaD {T mover Q : TraceTree α β}
    (h_size : T.size = mover.size + Q.size + 1) :
    TraceForest.b₀ ({.node mover Q} : TraceForest α β)
        = TraceForest.b₀ ({T} : TraceForest α β)
      ∧
    TraceForest.alpha ({.node mover Q} : TraceForest α β)
        = TraceForest.alpha ({T} : TraceForest α β)
      ∧
    TraceForest.sigma ({.node mover Q} : TraceForest α β)
        = TraceForest.sigma ({T} : TraceForest α β) := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [TraceForest.alpha_singleton, TraceForest.alpha_singleton,
        TraceTree.accCount_node]
    show mover.size + Q.size = T.size - 1
    omega
  · rw [TraceForest.sigma_singleton, TraceForest.sigma_singleton,
        TraceTree.accCount_node]
    show 1 + (mover.size + Q.size) = 1 + (T.size - 1)
    omega

/-- **IM via composition (Δ^d), discharged from cut data**: drop the
    `h_size` hypothesis from `im_pair_size_deltas_deltaD` by deriving it
    from a single-edge cut on `T` (`c.cutForest = {mover}`,
    `c.remainderDeletion = some Q`). Uses
    `CutShape.singleEdgeCut_size_relation`. -/
theorem im_pair_size_deltas_deltaD_of_cut {T mover Q : TraceTree α β}
    (c : CutShape T) (h_cf : c.cutForest = ({mover} : TraceForest α β))
    (h_rd : c.remainderDeletion = some Q) :
    TraceForest.b₀ ({.node mover Q} : TraceForest α β)
        = TraceForest.b₀ ({T} : TraceForest α β)
      ∧
    TraceForest.alpha ({.node mover Q} : TraceForest α β)
        = TraceForest.alpha ({T} : TraceForest α β)
      ∧
    TraceForest.sigma ({.node mover Q} : TraceForest α β)
        = TraceForest.sigma ({T} : TraceForest α β) :=
  im_pair_size_deltas_deltaD (CutShape.singleEdgeCut_size_relation c mover Q h_cf h_rd)

/-! ## §2.5: IM size deltas under Δ^c (MCB Prop 1.6.4 IM/Δ^c row)
-/

/-- **IM via composition (Δ^c)** (MCB Prop 1.6.4 IM/Δ^c row, book p. 66).
    For a single-edge cut `c` on a trace-free `T` extracting `β_t`, the
    Δ^c-IM workspace transformation `{T} → {.node β_t (T/^c β_t)}`
    increases αᶜ and σᶜ by exactly 1: Δb₀ = 0, Δαᶜ = +1, Δσᶜ = +1.

    Contrast with IM/Δ^d (`im_pair_size_deltas_deltaD`): Δ^d keeps both
    measures at 0, while Δ^c shows the +1 increase that distinguishes IM
    from EM in MCB's preferred (Δ^c) counting. The trace marker in T/^c β_t
    is correctly EXCLUDED from αᶜ via `accCountC` (MCB's "cancellation of
    the deeper copy"). -/
theorem im_pair_size_deltas_contraction [Inhabited β]
    {T β_t : TraceTree α β} (c : CutShape T)
    (h_tf : T.nonTraceSize = T.size)
    (h_cf : c.cutForest = ({β_t} : TraceForest α β)) :
    TraceForest.b₀ ({(.node β_t c.remainder : TraceTree α β)} : TraceForest α β)
        = TraceForest.b₀ ({T} : TraceForest α β)
      ∧
    TraceForest.alphaC ({(.node β_t c.remainder : TraceTree α β)} : TraceForest α β)
        = TraceForest.alphaC ({T} : TraceForest α β) + 1
      ∧
    TraceForest.sigmaC ({(.node β_t c.remainder : TraceTree α β)} : TraceForest α β)
        = TraceForest.sigmaC ({T} : TraceForest α β) + 1 := by
  have hβ := β_t.size_pos
  have hT := T.size_pos
  -- β_t is trace-free (subtree of trace-free T).
  have h_β_tf : β_t.nonTraceSize = β_t.size := by
    apply CutShape.nonTraceSize_eq_size_of_mem_cutForest c β_t h_tf
    rw [h_cf]; exact Multiset.mem_singleton.mpr rfl
  -- αᶜ on trace-free trees equals α.
  have h_T_alphaC : T.accCountC = T.accCount := by
    unfold TraceTree.accCountC TraceTree.accCount; rw [h_tf]
  have h_β_alphaC : β_t.accCountC = β_t.accCount := by
    unfold TraceTree.accCountC TraceTree.accCount; rw [h_β_tf]
  have h_size := CutShape.cut_size_conservation_contraction c h_tf
  rw [h_cf, TraceForest.sizeForest_singleton] at h_size
  obtain ⟨l, r, rfl⟩ := CutShape.isNode_of_cutForest_singleton c β_t h_cf
  have h_rem_pos : c.remainder.nonTraceSize ≥ 1 :=
    CutShape.nonTraceSize_remainder_pos_of_node c
  refine ⟨rfl, ?_, ?_⟩
  · rw [TraceForest.alphaC_singleton, TraceForest.alphaC_singleton,
        TraceTree.accCountC_node, h_T_alphaC, h_β_tf]
    show β_t.size + c.remainder.nonTraceSize = (l.node r).accCount + 1
    show β_t.size + c.remainder.nonTraceSize = (l.node r).size - 1 + 1
    omega
  · rw [TraceForest.sigmaC_singleton, TraceForest.sigmaC_singleton,
        TraceTree.accCountC_node, h_T_alphaC, h_β_tf]
    show 1 + (β_t.size + c.remainder.nonTraceSize) = 1 + (l.node r).accCount + 1
    show 1 + (β_t.size + c.remainder.nonTraceSize) = 1 + ((l.node r).size - 1) + 1
    omega

/-! ## §3: Sideward Minimal Yield analysis (MCB Prop 1.6.8 + Remark 1.6.9)
-/

/-- **Sideward 2(b)** preserves b₀ (MCB Prop 1.6.8 2(b) row, book p. 69).
    Workspace `{T_i, T_j} → {.node T_i β, T_j/β}` retains 2 components. -/
theorem sideward_2b_b₀_preserved (T_i T_j Tnode T_j_q : TraceTree α β) :
    TraceForest.b₀ ({Tnode, T_j_q} : TraceForest α β)
      = TraceForest.b₀ ({T_i, T_j} : TraceForest α β) := by
  rw [Multiset.insert_eq_cons, Multiset.insert_eq_cons]
  show Multiset.card _ = Multiset.card _
  simp only [Multiset.card_cons, Multiset.card_singleton]

/-- **Sideward 2(b) (Δα, Δσ) deltas under size conservation** (MCB Prop 1.6.8
    2(b)/Δ^d row, book p. 69). Under `h_size : T_j.size = β_t.size + T_j_q.size + 1`
    (the size-conservation hypothesis on the cut producing β_t from T_j)
    AND `h_node : Tnode.size = T_i.size + β_t.size + 1` (the merged-node size
    relation, automatic when Tnode = .node T_i β_t), Sideward 2(b) preserves α
    and σ:

    | Measure | Before `{T_i, T_j}` | After `{Tnode, T_j_q}` | Δ |
    |---|---|---|---|
    | b₀ | 2 | 2 | 0 |
    | α | (T_i.size − 1) + (T_j.size − 1) | Tnode.size − 1 + T_j_q.size − 1 | 0 |
    | σ | 2 + α(F) | 2 + α(F) | 0 |

    **Realises Remark 1.6.9 (book p. 71)**: "the Sideward Merge of type 2(b)
    cannot be distinguished solely in terms of its effect on the sizes b₀,
    α, and σ from Internal Merge." Both produce (0, 0, 0). NCL (`NCLBetween`)
    is what discriminates them.

    The tree variable is named `β_t` (per `Sideward.lean` convention) to
    avoid clashing with the type-level `β : Type*` from the file's `variable`
    declaration. MCB's notation `β` (as in eq. 1.6.7-1.6.10) corresponds. -/
theorem sideward_2b_size_deltas_deltaD
    {T_i T_j β_t Tnode T_j_q : TraceTree α β}
    (h_size : T_j.size = β_t.size + T_j_q.size + 1)
    (h_node : Tnode.size = T_i.size + β_t.size + 1) :
    TraceForest.b₀ ({Tnode, T_j_q} : TraceForest α β)
        = TraceForest.b₀ ({T_i, T_j} : TraceForest α β)
      ∧
    TraceForest.alpha ({Tnode, T_j_q} : TraceForest α β)
        = TraceForest.alpha ({T_i, T_j} : TraceForest α β)
      ∧
    TraceForest.sigma ({Tnode, T_j_q} : TraceForest α β)
        = TraceForest.sigma ({T_i, T_j} : TraceForest α β) := by
  have hβ := β_t.size_pos
  have hT_i := T_i.size_pos
  have hT_j_q := T_j_q.size_pos
  refine ⟨sideward_2b_b₀_preserved T_i T_j Tnode T_j_q, ?_, ?_⟩
  · rw [Multiset.insert_eq_cons, Multiset.insert_eq_cons,
        TraceForest.alpha_cons, TraceForest.alpha_cons,
        TraceForest.alpha_singleton, TraceForest.alpha_singleton]
    show Tnode.accCount + T_j_q.accCount = T_i.accCount + T_j.accCount
    show Tnode.size - 1 + (T_j_q.size - 1) = T_i.size - 1 + (T_j.size - 1)
    omega
  · rw [Multiset.insert_eq_cons, Multiset.insert_eq_cons,
        TraceForest.sigma_cons, TraceForest.sigma_cons,
        TraceForest.sigma_singleton, TraceForest.sigma_singleton]
    show 1 + Tnode.accCount + (1 + T_j_q.accCount)
       = 1 + T_i.accCount + (1 + T_j.accCount)
    show 1 + (Tnode.size - 1) + (1 + (T_j_q.size - 1))
       = 1 + (T_i.size - 1) + (1 + (T_j.size - 1))
    omega

/-- **Sideward 2(b) (Δα, Δσ) deltas, discharged from cut data**: drop both
    `h_size` and `h_node` hypotheses from `sideward_2b_size_deltas_deltaD`.
    `h_size` comes from a single-edge cut `c` on `T_j` extracting `β_t`
    and leaving `T_j_q`; `h_node` from `Tnode = .node T_i β_t` (so
    `size_node` gives the size relation). -/
theorem sideward_2b_size_deltas_deltaD_of_cut
    {T_i T_j β_t T_j_q : TraceTree α β}
    (c : CutShape T_j) (h_cf : c.cutForest = ({β_t} : TraceForest α β))
    (h_rd : c.remainderDeletion = some T_j_q) :
    TraceForest.b₀ ({(.node T_i β_t : TraceTree α β), T_j_q} : TraceForest α β)
        = TraceForest.b₀ ({T_i, T_j} : TraceForest α β)
      ∧
    TraceForest.alpha ({(.node T_i β_t : TraceTree α β), T_j_q}
                          : TraceForest α β)
        = TraceForest.alpha ({T_i, T_j} : TraceForest α β)
      ∧
    TraceForest.sigma ({(.node T_i β_t : TraceTree α β), T_j_q}
                          : TraceForest α β)
        = TraceForest.sigma ({T_i, T_j} : TraceForest α β) := by
  have h_size := CutShape.singleEdgeCut_size_relation c β_t T_j_q h_cf h_rd
  have h_node : (TraceTree.node T_i β_t).size = T_i.size + β_t.size + 1 := by
    rw [TraceTree.size_node]; omega
  exact sideward_2b_size_deltas_deltaD h_size h_node

/-- **Sideward 2(b) under Δ^c** (MCB Prop 1.6.8 2(b)/Δ^c row, book p. 69).
    `{T_i, T_j} → {.node T_i β_t, T_j/^c β_t}` for a single-edge cut on
    trace-free `T_j` extracting `β_t`. Δb₀ = 0, Δαᶜ = +1, Δσᶜ = +1.

    Like IM/Δ^c, the trace marker in the contraction-quotient is
    excluded from `αᶜ` per MCB's Lemma 1.6.3 eq. 1.6.8. -/
theorem sideward_2b_size_deltas_contraction [Inhabited β]
    {T_i T_j β_t : TraceTree α β}
    (c : CutShape T_j) (h_T_j_tf : T_j.nonTraceSize = T_j.size)
    (h_T_i_tf : T_i.nonTraceSize = T_i.size)
    (h_cf : c.cutForest = ({β_t} : TraceForest α β)) :
    TraceForest.b₀ ({(.node T_i β_t : TraceTree α β), c.remainder} : TraceForest α β)
        = TraceForest.b₀ ({T_i, T_j} : TraceForest α β)
      ∧
    TraceForest.alphaC ({(.node T_i β_t : TraceTree α β), c.remainder} : TraceForest α β)
        = TraceForest.alphaC ({T_i, T_j} : TraceForest α β) + 1
      ∧
    TraceForest.sigmaC ({(.node T_i β_t : TraceTree α β), c.remainder} : TraceForest α β)
        = TraceForest.sigmaC ({T_i, T_j} : TraceForest α β) + 1 := by
  have h_β_tf : β_t.nonTraceSize = β_t.size := by
    apply CutShape.nonTraceSize_eq_size_of_mem_cutForest c β_t h_T_j_tf
    rw [h_cf]; exact Multiset.mem_singleton.mpr rfl
  have h_size := CutShape.cut_size_conservation_contraction c h_T_j_tf
  rw [h_cf, TraceForest.sizeForest_singleton] at h_size
  obtain ⟨l, r, rfl⟩ := CutShape.isNode_of_cutForest_singleton c β_t h_cf
  have h_rem_pos : c.remainder.nonTraceSize ≥ 1 :=
    CutShape.nonTraceSize_remainder_pos_of_node c
  have hβ := β_t.size_pos
  have hT_i := T_i.size_pos
  have hT_j := (l.node r).size_pos
  refine ⟨?_, ?_, ?_⟩
  · rw [Multiset.insert_eq_cons, Multiset.insert_eq_cons]
    show Multiset.card _ = Multiset.card _
    simp only [Multiset.card_cons, Multiset.card_singleton]
  · rw [Multiset.insert_eq_cons, Multiset.insert_eq_cons,
        TraceForest.alphaC_cons, TraceForest.alphaC_cons,
        TraceForest.alphaC_singleton, TraceForest.alphaC_singleton,
        TraceTree.accCountC_node]
    have h_T_i_C : T_i.accCountC = T_i.accCount := by
      unfold TraceTree.accCountC TraceTree.accCount; rw [h_T_i_tf]
    have h_T_j_C : (l.node r).accCountC = (l.node r).accCount := by
      unfold TraceTree.accCountC TraceTree.accCount; rw [h_T_j_tf]
    have h_T_i_acc : T_i.accCount = T_i.size - 1 := rfl
    have h_T_j_acc : (l.node r).accCount = (l.node r).size - 1 := rfl
    have h_rem_acc : c.remainder.accCountC = c.remainder.nonTraceSize - 1 := rfl
    rw [h_β_tf, h_T_i_C, h_T_j_C]
    show T_i.nonTraceSize + β_t.size + c.remainder.accCountC
       = T_i.accCount + (l.node r).accCount + 1
    rw [h_T_i_tf, h_T_i_acc, h_T_j_acc, h_rem_acc]
    omega
  · rw [Multiset.insert_eq_cons, Multiset.insert_eq_cons,
        TraceForest.sigmaC_cons, TraceForest.sigmaC_cons,
        TraceForest.sigmaC_singleton, TraceForest.sigmaC_singleton,
        TraceTree.accCountC_node]
    have h_T_i_C : T_i.accCountC = T_i.accCount := by
      unfold TraceTree.accCountC TraceTree.accCount; rw [h_T_i_tf]
    have h_T_j_C : (l.node r).accCountC = (l.node r).accCount := by
      unfold TraceTree.accCountC TraceTree.accCount; rw [h_T_j_tf]
    have h_T_i_acc : T_i.accCount = T_i.size - 1 := rfl
    have h_T_j_acc : (l.node r).accCount = (l.node r).size - 1 := rfl
    have h_rem_acc : c.remainder.accCountC = c.remainder.nonTraceSize - 1 := rfl
    rw [h_β_tf, h_T_i_C, h_T_j_C]
    show 1 + (T_i.nonTraceSize + β_t.size) + (1 + c.remainder.accCountC)
       = 1 + T_i.accCount + (1 + (l.node r).accCount) + 1
    rw [h_T_i_tf, h_T_i_acc, h_T_j_acc, h_rem_acc]
    omega

/-- **Sideward 3(a) increases b₀ by 1** (MCB Prop 1.6.8 3(a) row, book p. 69).
    Workspace `{T_i} → {.node α β, T_i/(α⊔β)}`: 1 component becomes 2. -/
theorem sideward_3a_b₀_increases (T_i Tnode T_iq : TraceTree α β) :
    TraceForest.b₀ ({Tnode, T_iq} : TraceForest α β)
      = TraceForest.b₀ ({T_i} : TraceForest α β) + 1 := by
  rw [Multiset.insert_eq_cons, TraceForest.b₀_cons, TraceForest.b₀_singleton,
      TraceForest.b₀_singleton]

/-- **Sideward 3(b) increases b₀ by 1** (MCB Prop 1.6.8 3(b) row, book p. 69).
    Workspace `{T_i, T_j} → {.node α β, T_i/α, T_j/β}`: 2 components become 3. -/
theorem sideward_3b_b₀_increases
    (T_i T_j Tnode T_iq T_jq : TraceTree α β) :
    TraceForest.b₀ ({Tnode, T_iq, T_jq} : TraceForest α β)
      = TraceForest.b₀ ({T_i, T_j} : TraceForest α β) + 1 := by
  show Multiset.card _ = Multiset.card _ + 1
  rw [show ({Tnode, T_iq, T_jq} : TraceForest α β)
        = Tnode ::ₘ T_iq ::ₘ ({T_jq} : TraceForest α β) from rfl,
      Multiset.insert_eq_cons]
  simp only [Multiset.card_cons, Multiset.card_singleton]

/-- **Sideward 3(b) full (Δb₀, Δα, Δσ) under Δ^d** (MCB Prop 1.6.8 3(b) row,
    book p. 69 — full table). Workspace `{T_i, T_j} → {.node a b, T_iq, T_jq}`
    where `T_iq` is the deletion-quotient of a single-edge cut on `T_i`
    extracting `a`, and similarly for `T_jq` from `T_j` extracting `b`.

    | Measure | Before | After | Δ |
    |---|---|---|---|
    | b₀ | 2 | 3 | +1 |
    | α  | (T_i.size − 1) + (T_j.size − 1) | (.node a b).size − 1 + (T_iq − 1) + (T_jq − 1) | −2 |
    | σ  | 2 + α(F) | 3 + α(F) − 2 | −1 |

    Δb₀ = +1 alone rules out Sideward 3(b) (`sideward_3b_violates_noDivergenceWeak`);
    here we record the full numerical signature for Remark 1.6.9-style
    discrimination. -/
theorem sideward_3b_size_deltas_deltaD
    {T_i T_j a b T_iq T_jq : TraceTree α β}
    (h_i : T_i.size = a.size + T_iq.size + 1)
    (h_j : T_j.size = b.size + T_jq.size + 1) :
    TraceForest.b₀ ({(.node a b : TraceTree α β), T_iq, T_jq} : TraceForest α β)
        = TraceForest.b₀ ({T_i, T_j} : TraceForest α β) + 1
      ∧
    TraceForest.alpha ({(.node a b : TraceTree α β), T_iq, T_jq}
                          : TraceForest α β) + 2
        = TraceForest.alpha ({T_i, T_j} : TraceForest α β)
      ∧
    TraceForest.sigma ({(.node a b : TraceTree α β), T_iq, T_jq}
                          : TraceForest α β) + 1
        = TraceForest.sigma ({T_i, T_j} : TraceForest α β) := by
  have hT_i := T_i.size_pos
  have hT_j := T_j.size_pos
  have hT_iq := T_iq.size_pos
  have hT_jq := T_jq.size_pos
  have ha := a.size_pos
  have hb := b.size_pos
  -- Triple {x, y, z} for Multiset: definitionally x ::ₘ y ::ₘ {z}.
  have h_triple : ({(.node a b : TraceTree α β), T_iq, T_jq} : TraceForest α β)
                  = (.node a b) ::ₘ T_iq ::ₘ ({T_jq} : TraceForest α β) := rfl
  refine ⟨sideward_3b_b₀_increases T_i T_j _ T_iq T_jq, ?_, ?_⟩
  · -- α delta: α(F') + 2 = α(F)
    rw [h_triple, Multiset.insert_eq_cons,
        TraceForest.alpha_cons, TraceForest.alpha_cons,
        TraceForest.alpha_cons, TraceForest.alpha_singleton,
        TraceForest.alpha_singleton, TraceTree.accCount_node]
    show a.size + b.size + (T_iq.accCount + (T_jq.accCount + 0)) + 2
         = T_i.accCount + (T_j.accCount + 0)
    show a.size + b.size + ((T_iq.size - 1) + ((T_jq.size - 1) + 0)) + 2
         = (T_i.size - 1) + ((T_j.size - 1) + 0)
    omega
  · -- σ delta: σ(F') + 1 = σ(F)
    rw [h_triple, Multiset.insert_eq_cons,
        TraceForest.sigma_cons, TraceForest.sigma_cons,
        TraceForest.sigma_cons, TraceForest.sigma_singleton,
        TraceForest.sigma_singleton, TraceTree.accCount_node]
    show 1 + (a.size + b.size) + (1 + T_iq.accCount + (1 + T_jq.accCount)) + 1
         = 1 + T_i.accCount + (1 + T_j.accCount)
    show 1 + (a.size + b.size) + (1 + (T_iq.size - 1) + (1 + (T_jq.size - 1))) + 1
         = 1 + (T_i.size - 1) + (1 + (T_j.size - 1))
    omega

/-- **Sideward 3(b) full deltas, discharged from cut data**: drop both
    `h_i` and `h_j` size hypotheses by deriving them from single-edge cuts
    `c_i` on `T_i` and `c_j` on `T_j`. -/
theorem sideward_3b_size_deltas_deltaD_of_cut
    {T_i T_j a b T_iq T_jq : TraceTree α β}
    (c_i : CutShape T_i) (h_cf_i : c_i.cutForest = ({a} : TraceForest α β))
    (h_rd_i : c_i.remainderDeletion = some T_iq)
    (c_j : CutShape T_j) (h_cf_j : c_j.cutForest = ({b} : TraceForest α β))
    (h_rd_j : c_j.remainderDeletion = some T_jq) :
    TraceForest.b₀ ({(.node a b : TraceTree α β), T_iq, T_jq} : TraceForest α β)
        = TraceForest.b₀ ({T_i, T_j} : TraceForest α β) + 1
      ∧
    TraceForest.alpha ({(.node a b : TraceTree α β), T_iq, T_jq}
                          : TraceForest α β) + 2
        = TraceForest.alpha ({T_i, T_j} : TraceForest α β)
      ∧
    TraceForest.sigma ({(.node a b : TraceTree α β), T_iq, T_jq}
                          : TraceForest α β) + 1
        = TraceForest.sigma ({T_i, T_j} : TraceForest α β) :=
  sideward_3b_size_deltas_deltaD
    (CutShape.singleEdgeCut_size_relation c_i a T_iq h_cf_i h_rd_i)
    (CutShape.singleEdgeCut_size_relation c_j b T_jq h_cf_j h_rd_j)

/-! ### Sideward 3(a): two-edge cut full deltas -/

/-- **Sideward 3(a) full (Δb₀, Δα, Δσ) under Δ^d** (MCB Prop 1.6.8 3(a) row,
    book p. 69 — full table, parameterized by contraction count).

    Workspace `{T_i} → {.node a b, T_iq}` where `T_iq` is the deletion-
    quotient of a TWO-edge cut `c_i` on `T_i` extracting both `a` and `b`.

    The cut's `numContractions c_i` depends on the relative position of
    the two extracted subtrees in `T_i`:
    - 1 contraction if a, b are siblings (single `.bothCut`)
    - 2+ contractions otherwise (the two cut paths each contract a parent)

    Hence Δα and Δσ "vary" per MCB's prose, but the variation is captured
    by `numContractions c_i`:

    | Measure | Before | After | Δ |
    |---|---|---|---|
    | b₀ | 1 | 2 | +1 |
    | α  | T_i.size − 1 | (a + b) + (T_iq − 1) | −numContractions c_i |
    | σ  | T_i.size | 1 + a + b + T_iq | 1 − numContractions c_i |

    Δb₀ = +1 alone rules out 3(a) (`sideward_3a_violates_noDivergenceWeak`);
    here we record the full numerical signature parameterized by the
    cut's contraction count, derivable from `cut_size_conservation`. -/
theorem sideward_3a_size_deltas_deltaD
    {T_i a b T_iq : TraceTree α β} (c_i : CutShape T_i)
    (h_cf : c_i.cutForest = ({a, b} : TraceForest α β))
    (h_rd : c_i.remainderDeletion = some T_iq) :
    TraceForest.b₀ ({(.node a b : TraceTree α β), T_iq} : TraceForest α β)
        = TraceForest.b₀ ({T_i} : TraceForest α β) + 1
      ∧
    TraceForest.alpha ({(.node a b : TraceTree α β), T_iq} : TraceForest α β)
        + CutShape.numContractions c_i
        = TraceForest.alpha ({T_i} : TraceForest α β)
      ∧
    TraceForest.sigma ({(.node a b : TraceTree α β), T_iq} : TraceForest α β)
        + CutShape.numContractions c_i
        = TraceForest.sigma ({T_i} : TraceForest α β) + 1 := by
  -- T_i.size = a.size + b.size + T_iq.size + numContractions c_i
  have h_size := CutShape.cut_size_conservation c_i
  rw [h_cf, h_rd, TraceForest.sizeForest_pair] at h_size
  simp only [Option.elim] at h_size
  have ha := a.size_pos
  have hb := b.size_pos
  have hT_iq := T_iq.size_pos
  refine ⟨sideward_3a_b₀_increases T_i _ T_iq, ?_, ?_⟩
  · -- α delta
    rw [Multiset.insert_eq_cons,
        TraceForest.alpha_cons, TraceForest.alpha_singleton,
        TraceForest.alpha_singleton, TraceTree.accCount_node]
    show a.size + b.size + T_iq.accCount + CutShape.numContractions c_i
         = T_i.accCount
    show a.size + b.size + (T_iq.size - 1) + CutShape.numContractions c_i
         = T_i.size - 1
    omega
  · -- σ delta
    rw [Multiset.insert_eq_cons,
        TraceForest.sigma_cons, TraceForest.sigma_singleton,
        TraceForest.sigma_singleton, TraceTree.accCount_node]
    show 1 + (a.size + b.size) + (1 + T_iq.accCount) + CutShape.numContractions c_i
         = 1 + T_i.accCount + 1
    show 1 + (a.size + b.size) + (1 + (T_iq.size - 1)) + CutShape.numContractions c_i
         = 1 + (T_i.size - 1) + 1
    omega

/-- **Sideward 3(a), MCB-specific (+1, −2, −1) form** (Prop 1.6.8 3(a)/Δ^d
    row, book p. 69 — table form). MCB's proof (book p. 70) restricts to
    a genuine 2-edge cut leaving a non-trivial deletion-quotient `T_iq`;
    in that setting `numContractions c_i = 2` always (sibling extractions
    pass through `.bothCut` collapsing the parent → 1 contraction;
    separated paths give 2 contractions; either way for the hypothesis
    `cutForest.card = 2 ∧ remainderDeletion = some _` we get exactly 2,
    by `numContractions_twoEdge`). -/
theorem sideward_3a_size_deltas_deltaD_specific
    {T_i a b T_iq : TraceTree α β} (c_i : CutShape T_i)
    (h_cf : c_i.cutForest = ({a, b} : TraceForest α β))
    (h_rd : c_i.remainderDeletion = some T_iq) :
    TraceForest.b₀ ({(.node a b : TraceTree α β), T_iq} : TraceForest α β)
        = TraceForest.b₀ ({T_i} : TraceForest α β) + 1
      ∧
    TraceForest.alpha ({(.node a b : TraceTree α β), T_iq} : TraceForest α β) + 2
        = TraceForest.alpha ({T_i} : TraceForest α β)
      ∧
    TraceForest.sigma ({(.node a b : TraceTree α β), T_iq} : TraceForest α β) + 1
        = TraceForest.sigma ({T_i} : TraceForest α β) := by
  have h_card : c_i.cutForest.card = 2 := by
    rw [h_cf, show ({a, b} : TraceForest α β) = a ::ₘ ({b} : TraceForest α β) from rfl,
        Multiset.card_cons, Multiset.card_singleton]
  have h_nc := CutShape.numContractions_twoEdge c_i T_iq h_card h_rd
  have ⟨h_b₀, h_α, h_σ⟩ := sideward_3a_size_deltas_deltaD c_i h_cf h_rd
  rw [h_nc] at h_α h_σ
  refine ⟨h_b₀, h_α, ?_⟩
  omega

/-- **Sideward 3(a) under Δ^c** (MCB Prop 1.6.8 3(a)/Δ^c row, book p. 69).
    For a 2-edge cut on trace-free `T_i` extracting `a` and `b`:
    Δb₀ = +1, Δαᶜ = 0, Δσᶜ = +1. (Δb₀ = +1 still rules out 3(a) under
    Minimal Yield even with Δ^c counting.) -/
theorem sideward_3a_size_deltas_contraction [Inhabited β]
    {T_i a b : TraceTree α β} (c_i : CutShape T_i)
    (h_T_i_tf : T_i.nonTraceSize = T_i.size)
    (h_cf : c_i.cutForest = ({a, b} : TraceForest α β)) :
    TraceForest.b₀ ({(.node a b : TraceTree α β), c_i.remainder} : TraceForest α β)
        = TraceForest.b₀ ({T_i} : TraceForest α β) + 1
      ∧
    TraceForest.alphaC ({(.node a b : TraceTree α β), c_i.remainder} : TraceForest α β)
        = TraceForest.alphaC ({T_i} : TraceForest α β)
      ∧
    TraceForest.sigmaC ({(.node a b : TraceTree α β), c_i.remainder} : TraceForest α β)
        = TraceForest.sigmaC ({T_i} : TraceForest α β) + 1 := by
  have h_a_tf : a.nonTraceSize = a.size := by
    apply CutShape.nonTraceSize_eq_size_of_mem_cutForest c_i a h_T_i_tf
    rw [h_cf]; exact Multiset.mem_cons_self _ _
  have h_b_tf : b.nonTraceSize = b.size := by
    apply CutShape.nonTraceSize_eq_size_of_mem_cutForest c_i b h_T_i_tf
    rw [h_cf]
    rw [show ({a, b} : TraceForest α β) = a ::ₘ ({b} : TraceForest α β) from rfl,
        Multiset.mem_cons]
    right; exact Multiset.mem_singleton.mpr rfl
  have h_size := CutShape.cut_size_conservation_contraction c_i h_T_i_tf
  rw [h_cf, TraceForest.sizeForest_pair] at h_size
  have ha := a.size_pos
  have hb := b.size_pos
  have hT_i := T_i.size_pos
  have h_a_acc : a.accCount = a.size - 1 := rfl
  have h_b_acc : b.accCount = b.size - 1 := rfl
  have h_T_i_acc : T_i.accCount = T_i.size - 1 := rfl
  have h_T_i_C : T_i.accCountC = T_i.accCount := by
    unfold TraceTree.accCountC TraceTree.accCount; rw [h_T_i_tf]
  have h_rem_acc : c_i.remainder.accCountC = c_i.remainder.nonTraceSize - 1 := rfl
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
  refine ⟨sideward_3a_b₀_increases T_i _ c_i.remainder, ?_, ?_⟩
  · rw [Multiset.insert_eq_cons,
        TraceForest.alphaC_cons, TraceForest.alphaC_singleton,
        TraceForest.alphaC_singleton, TraceTree.accCountC_node, h_T_i_C, h_a_tf, h_b_tf,
        h_T_i_acc, h_rem_acc]
    omega
  · rw [Multiset.insert_eq_cons,
        TraceForest.sigmaC_cons, TraceForest.sigmaC_singleton,
        TraceForest.sigmaC_singleton, TraceTree.accCountC_node, h_T_i_C, h_a_tf, h_b_tf,
        h_T_i_acc, h_rem_acc]
    omega

/-- **Sideward 3(b) under Δ^c** (MCB Prop 1.6.8 3(b)/Δ^c row, book p. 69).
    For single-edge cuts `c_i` on trace-free `T_i` extracting `a` and
    `c_j` on trace-free `T_j` extracting `b`:
    Δb₀ = +1, Δαᶜ = 0, Δσᶜ = +1. -/
theorem sideward_3b_size_deltas_contraction [Inhabited β]
    {T_i T_j a b : TraceTree α β}
    (c_i : CutShape T_i) (h_T_i_tf : T_i.nonTraceSize = T_i.size)
    (h_cf_i : c_i.cutForest = ({a} : TraceForest α β))
    (c_j : CutShape T_j) (h_T_j_tf : T_j.nonTraceSize = T_j.size)
    (h_cf_j : c_j.cutForest = ({b} : TraceForest α β)) :
    TraceForest.b₀ ({(.node a b : TraceTree α β), c_i.remainder, c_j.remainder}
                       : TraceForest α β)
        = TraceForest.b₀ ({T_i, T_j} : TraceForest α β) + 1
      ∧
    TraceForest.alphaC ({(.node a b : TraceTree α β), c_i.remainder, c_j.remainder}
                          : TraceForest α β)
        = TraceForest.alphaC ({T_i, T_j} : TraceForest α β)
      ∧
    TraceForest.sigmaC ({(.node a b : TraceTree α β), c_i.remainder, c_j.remainder}
                          : TraceForest α β)
        = TraceForest.sigmaC ({T_i, T_j} : TraceForest α β) + 1 := by
  have h_a_tf : a.nonTraceSize = a.size := by
    apply CutShape.nonTraceSize_eq_size_of_mem_cutForest c_i a h_T_i_tf
    rw [h_cf_i]; exact Multiset.mem_singleton.mpr rfl
  have h_b_tf : b.nonTraceSize = b.size := by
    apply CutShape.nonTraceSize_eq_size_of_mem_cutForest c_j b h_T_j_tf
    rw [h_cf_j]; exact Multiset.mem_singleton.mpr rfl
  have h_size_i := CutShape.cut_size_conservation_contraction c_i h_T_i_tf
  rw [h_cf_i, TraceForest.sizeForest_singleton] at h_size_i
  have h_size_j := CutShape.cut_size_conservation_contraction c_j h_T_j_tf
  rw [h_cf_j, TraceForest.sizeForest_singleton] at h_size_j
  have ha := a.size_pos
  have hb := b.size_pos
  have hT_i := T_i.size_pos
  have hT_j := T_j.size_pos
  have h_T_i_C : T_i.accCountC = T_i.accCount := by
    unfold TraceTree.accCountC TraceTree.accCount; rw [h_T_i_tf]
  have h_T_j_C : T_j.accCountC = T_j.accCount := by
    unfold TraceTree.accCountC TraceTree.accCount; rw [h_T_j_tf]
  have h_T_i_acc : T_i.accCount = T_i.size - 1 := rfl
  have h_T_j_acc : T_j.accCount = T_j.size - 1 := rfl
  have h_rem_i_acc : c_i.remainder.accCountC = c_i.remainder.nonTraceSize - 1 := rfl
  have h_rem_j_acc : c_j.remainder.accCountC = c_j.remainder.nonTraceSize - 1 := rfl
  have h_triple : ({(.node a b : TraceTree α β), c_i.remainder, c_j.remainder}
                       : TraceForest α β)
                = (.node a b) ::ₘ c_i.remainder
                              ::ₘ ({c_j.remainder} : TraceForest α β) := rfl
  have h_rem_i_pos : c_i.remainder.nonTraceSize ≥ 1 :=
    CutShape.nonTraceSize_remainder_pos_of_cutForest_singleton c_i a h_cf_i
  have h_rem_j_pos : c_j.remainder.nonTraceSize ≥ 1 :=
    CutShape.nonTraceSize_remainder_pos_of_cutForest_singleton c_j b h_cf_j
  refine ⟨sideward_3b_b₀_increases _ _ _ c_i.remainder c_j.remainder, ?_, ?_⟩
  · rw [h_triple, Multiset.insert_eq_cons,
        TraceForest.alphaC_cons, TraceForest.alphaC_cons,
        TraceForest.alphaC_cons, TraceForest.alphaC_singleton,
        TraceForest.alphaC_singleton,
        TraceTree.accCountC_node, h_T_i_C, h_T_j_C, h_a_tf, h_b_tf]
    show a.size + b.size + (c_i.remainder.accCountC + (c_j.remainder.accCountC + 0))
       = T_i.accCount + (T_j.accCount + 0)
    rw [h_rem_i_acc, h_rem_j_acc, h_T_i_acc, h_T_j_acc]
    omega
  · rw [h_triple, Multiset.insert_eq_cons,
        TraceForest.sigmaC_cons, TraceForest.sigmaC_cons,
        TraceForest.sigmaC_cons, TraceForest.sigmaC_singleton,
        TraceForest.sigmaC_singleton,
        TraceTree.accCountC_node, h_T_i_C, h_T_j_C, h_a_tf, h_b_tf]
    show 1 + (a.size + b.size) + (1 + c_i.remainder.accCountC
                                     + (1 + c_j.remainder.accCountC + 0))
       = 1 + T_i.accCount + (1 + T_j.accCount + 0) + 1
    rw [h_rem_i_acc, h_rem_j_acc, h_T_i_acc, h_T_j_acc]
    omega

/-- **Sideward 3(a) violates `MinimalYieldWeak.noDivergence`** (a fortiori
    violates the strong form). Δb₀ = +1 rules out Sideward 3(a) under
    either form. -/
theorem sideward_3a_violates_noDivergenceWeak
    (T_i Tnode T_iq : TraceTree α β) :
    ¬ MinimalYieldWeak ({T_i} : TraceForest α β)
                       ({Tnode, T_iq} : TraceForest α β) := by
  intro h
  have h_b₀ := h.noDivergence
  have h_F  : TraceForest.b₀ ({T_i} : TraceForest α β) = 1 :=
    TraceForest.b₀_singleton _
  have h_F' : TraceForest.b₀ ({Tnode, T_iq} : TraceForest α β) = 2 :=
    (sideward_3a_b₀_increases T_i Tnode T_iq).trans (by rw [h_F])
  rw [h_F, h_F'] at h_b₀
  omega

/-- **Sideward 3(b) violates `MinimalYieldWeak.noDivergence`** (a fortiori
    violates the strong form). Δb₀ = +1 rules out Sideward 3(b). -/
theorem sideward_3b_violates_noDivergenceWeak
    (T_i T_j Tnode T_iq T_jq : TraceTree α β) :
    ¬ MinimalYieldWeak ({T_i, T_j} : TraceForest α β)
                       ({Tnode, T_iq, T_jq} : TraceForest α β) := by
  intro h
  have h_b₀ := h.noDivergence
  have h_F : TraceForest.b₀ ({T_i, T_j} : TraceForest α β) = 2 := by
    rw [Multiset.insert_eq_cons]
    show Multiset.card _ = 2
    simp only [Multiset.card_cons, Multiset.card_singleton]
  have h_F' : TraceForest.b₀ ({Tnode, T_iq, T_jq} : TraceForest α β) = 3 :=
    (sideward_3b_b₀_increases T_i T_j Tnode T_iq T_jq).trans (by rw [h_F])
  rw [h_F, h_F'] at h_b₀
  omega

/-- Strong-form corollary of `sideward_3a_violates_noDivergenceWeak`. -/
theorem sideward_3a_violates_noDivergence (T_i Tnode T_iq : TraceTree α β) :
    ¬ MinimalYield ({T_i} : TraceForest α β)
                   ({Tnode, T_iq} : TraceForest α β) :=
  fun h => sideward_3a_violates_noDivergenceWeak T_i Tnode T_iq h.toWeak

/-- Strong-form corollary of `sideward_3b_violates_noDivergenceWeak`. -/
theorem sideward_3b_violates_noDivergence
    (T_i T_j Tnode T_iq T_jq : TraceTree α β) :
    ¬ MinimalYield ({T_i, T_j} : TraceForest α β)
                   ({Tnode, T_iq, T_jq} : TraceForest α β) :=
  fun h => sideward_3b_violates_noDivergenceWeak T_i T_j Tnode T_iq T_jq h.toWeak

/-! ## §4: Unit-merge violation (MCB Remark 1.6.7, book p. 67)
-/

/-- **M_{S,1} alone violates MinimalYield** (MCB Remark 1.6.7, book p. 67).
    The unit-merge stage of IM via composition transforms `{T} → {β, T/β}`
    (extracting an accessible term β from T, leaving the deletion-quotient
    Q = T/β as the other component). Δb₀ = +1 violates `noDivergence`.

    MCB's argument: this shows M_{S,1} cannot occur **standalone** as a
    Merge operation — it can occur only in the composition
    `M_{β, T/β} ∘ M_{β, 1}` that gives Internal Merge (Prop 1.4.2). The
    "virtual particles" caveat in `Internal.lean §4` corresponds to this
    same observation.

    Proof: structurally identical to `sideward_3a_b₀_increases` —
    `{T} → {β, T/β}` is one-component-in, two-components-out. -/
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
