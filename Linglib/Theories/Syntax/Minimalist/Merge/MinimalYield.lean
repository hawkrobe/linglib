import Linglib.Theories.Syntax.Minimalist.Merge.External
import Linglib.Theories.Syntax.Minimalist.Merge.Internal

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
| Sideward 2(b) Δ^d | 0 | 0 | 0 | ✗ (Δσ=0) | ✓ |
| Sideward 3(a)/3(b) | +1 | varies | varies | ✗ (Δb₀>0) | ✗ (Δb₀>0) |

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

/-- Helper: `{a, b} = a ::ₘ {b}` definitionally. Extracted for the
    repetitive multiset-rewrites in this file. -/
private theorem pair_eq_cons (a b : TraceTree α β) :
    ({a, b} : TraceForest α β) = a ::ₘ ({b} : TraceForest α β) := rfl

/-- **Minimal Yield principle, strong form** (M-C-B Def 1.6.1, book p. 63 + eq. 1.6.2).
    A forest transformation `F → F'` satisfies the strong form iff:
    - `b₀(F') ≤ b₀(F)` (no divergence in component count)
    - `α(F') ≥ α(F)` (no information loss in accessible terms)
    - `σ(F') = σ(F) + 1` (size grows by exactly 1) -/
structure MinimalYield (F F' : TraceForest α β) : Prop where
  noDivergence  : F'.b₀ ≤ F.b₀
  noInfoLoss    : F.alpha ≤ F'.alpha
  minimalYield  : F'.sigma = F.sigma + 1

/-- **Minimal Yield principle, weak form** (M-C-B p. 69 — the form
    sufficient under Δ^d to rule out Sideward 3(a)/3(b)). Drops the
    `minimalYield` condition; keeps `noDivergence` and `noInfoLoss`. -/
structure MinimalYieldWeak (F F' : TraceForest α β) : Prop where
  noDivergence  : F'.b₀ ≤ F.b₀
  noInfoLoss    : F.alpha ≤ F'.alpha

/-- Strong implies weak. -/
theorem MinimalYield.toWeak {F F' : TraceForest α β} (h : MinimalYield F F') :
    MinimalYieldWeak F F' :=
  ⟨h.noDivergence, h.noInfoLoss⟩

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
  refine ⟨?_, ?_, ?_⟩
  · rw [TraceForest.b₀_singleton, pair_eq_cons, TraceForest.b₀_cons,
        TraceForest.b₀_singleton]
    omega
  · rw [TraceForest.alpha_singleton, TraceTree.accCount_node, pair_eq_cons,
        TraceForest.alpha_cons, TraceForest.alpha_singleton]
    show TraceTree.accCount S + TraceTree.accCount S' ≤ S.size + S'.size
    show S.size - 1 + (S'.size - 1) ≤ S.size + S'.size
    omega
  · rw [TraceForest.sigma_singleton, TraceTree.accCount_node, pair_eq_cons,
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
    analog of `cut_leafCount_conservation`; the substrate lemma deriving it
    from cut data (analogous to `deletionLeafCount`) is queued. -/
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

/-! ## §3: Sideward Minimal Yield analysis (MCB Prop 1.6.8 + Remark 1.6.9)
-/

/-- **Sideward 2(b)** preserves b₀ (MCB Prop 1.6.8 2(b) row, book p. 69).
    Workspace `{T_i, T_j} → {.node T_i β, T_j/β}` retains 2 components. -/
theorem sideward_2b_b₀_preserved (T_i T_j Tnode T_j_q : TraceTree α β) :
    TraceForest.b₀ ({Tnode, T_j_q} : TraceForest α β)
      = TraceForest.b₀ ({T_i, T_j} : TraceForest α β) := by
  rw [pair_eq_cons, pair_eq_cons]
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
  · rw [pair_eq_cons, pair_eq_cons,
        TraceForest.alpha_cons, TraceForest.alpha_cons,
        TraceForest.alpha_singleton, TraceForest.alpha_singleton]
    show Tnode.accCount + T_j_q.accCount = T_i.accCount + T_j.accCount
    show Tnode.size - 1 + (T_j_q.size - 1) = T_i.size - 1 + (T_j.size - 1)
    omega
  · rw [pair_eq_cons, pair_eq_cons,
        TraceForest.sigma_cons, TraceForest.sigma_cons,
        TraceForest.sigma_singleton, TraceForest.sigma_singleton]
    show 1 + Tnode.accCount + (1 + T_j_q.accCount)
       = 1 + T_i.accCount + (1 + T_j.accCount)
    show 1 + (Tnode.size - 1) + (1 + (T_j_q.size - 1))
       = 1 + (T_i.size - 1) + (1 + (T_j.size - 1))
    omega

/-- **Sideward 3(a) increases b₀ by 1** (MCB Prop 1.6.8 3(a) row, book p. 69).
    Workspace `{T_i} → {.node α β, T_i/(α⊔β)}`: 1 component becomes 2. -/
theorem sideward_3a_b₀_increases (T_i Tnode T_iq : TraceTree α β) :
    TraceForest.b₀ ({Tnode, T_iq} : TraceForest α β)
      = TraceForest.b₀ ({T_i} : TraceForest α β) + 1 := by
  rw [pair_eq_cons, TraceForest.b₀_cons, TraceForest.b₀_singleton,
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
      pair_eq_cons]
  simp only [Multiset.card_cons, Multiset.card_singleton]

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
    rw [pair_eq_cons]
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
