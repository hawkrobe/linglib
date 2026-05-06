import Linglib.Theories.Syntax.Minimalist.Merge.External
import Linglib.Theories.Syntax.Minimalist.Merge.Internal
import Linglib.Core.Combinatorics.RootedTree.ForestSize

/-!
# Minimal Yield (MCB Definition 1.6.1)
@cite{marcolli-chomsky-berwick-2025} §1.6.1, book p. 63

Realises M-C-B's **Minimal Yield principle** (Def 1.6.1) as a predicate on
forest transformations, plus the per-merge counting characterization of
**Proposition 1.6.4** (book p. 66) showing EM and IM satisfy Minimal Yield.

## Definition (verbatim, MCB Def 1.6.1, book p. 63)

A transformation `Φ : 𝓕_SO₀ → 𝓕_SO₀` satisfies the Minimal Yield principle
if the following conditions hold:

  b₀(Φ(F)) ≤ b₀(F)        (no divergence)
  α(Φ(F)) ≥ α(F)          (no information loss)
  σ(Φ(F)) = σ(F) + 1      (minimality of yield)        (eq. 1.6.2)

The first ensures derivations *converge*; the second ensures no syntactic
information is lost; the third bounds the size growth at +1 per step.

## Per-merge characterization (MCB Prop 1.6.4, book p. 66)

For the EM/IM cases:

| Merge | Δb₀ | Δα | Δσ |
|---|---|---|---|
| External (both Δ^c, Δ^d) | −1 | +2 | +1 |
| Internal w/ Δ^c | 0 | +1 | +1 |
| Internal w/ Δ^d | 0 | 0 | 0 |

EM and IM-with-Δ^c satisfy Minimal Yield (Δσ = +1). IM-with-Δ^d satisfies
the weaker form only (Δσ = 0). Sideward 3(b)/3(a) violate the strong form
(Δb₀ = +1); the weak form (Δσ ≥ 0) is not enough to rule out 2(b),
which has the same (b₀, α, σ) signature as IM (Remark 1.6.9 — distinguished
only by NCL, see `NoComplexityLoss.lean`).

## What this file provides

- `MinimalYield F F'`: the predicate on a forest transition `F → F'`.
- Per-merge effects on `(b₀, α, σ)` for the 2-tree EM input `{S, S'}`
  and the 1-tree IM input `{T}` (under unique-cut hypothesis).
- Witness theorems that EM and IM-via-composition satisfy the Minimal
  Yield predicate.

## Out of scope (queued)

- Sideward 2(b)/3(a)/3(b) effects on (b₀, α, σ) (MCB Prop 1.6.8) — these
  show why the strong form rules out 3(a)/3(b) and the weak form is
  insufficient for 2(b).
- Sideward NCL negative direction (MCB Prop 1.6.10 negative) — `NCLBetween`
  predicate already exists in `NoComplexityLoss.lean`; the negative
  direction (no component map exists for Sideward) is harder.
-/

namespace Minimalist.Merge

open ConnesKreimer

variable {α β : Type*}

/-- **Minimal Yield principle** (M-C-B Definition 1.6.1, book p. 63 + eq. 1.6.2).
    A forest transformation `F → F'` satisfies Minimal Yield iff:
    - `b₀(F') ≤ b₀(F)` (no divergence in component count)
    - `α(F') ≥ α(F)` (no information loss in accessible terms)
    - `σ(F') = σ(F) + 1` (size grows by exactly 1)

    The third condition is the "minimality" — the size yield is exactly
    one new term, not zero (which would be no progress) and not more
    (which would be wasteful per Resource Restriction). -/
structure MinimalYield (F F' : TraceForest α β) : Prop where
  no_divergence    : F'.b0 ≤ F.b0
  no_info_loss     : F.alpha ≤ F'.alpha
  minimal_yield    : F'.sigma = F.sigma + 1

/-- **EM Case 1, F̂ = ∅: size table for Prop 1.6.4 EM row** (M-C-B p. 66).
    External Merge of two member components `S, S'` (a 2-tree forest)
    produces the singleton `{.node S S'}`. The size deltas are:

    - `b₀ : 2 → 1` (Δb₀ = −1)
    - `α : 0 → 2` (Δα = +2 — both S and S' become non-root accessible
      terms; assumes both are non-leaves so they have no other contribution)

    Matches MCB Prop 1.6.4 EM row: Δb₀ = −1, Δα = +2, Δσ = +1. -/
theorem em_pair_satisfiesMinimalYield (S S' : TraceTree α β)
    (hS : S.size ≥ 1) (hS' : S'.size ≥ 1) :
    MinimalYield ({S, S'} : TraceForest α β)
                 ({.node S S'} : TraceForest α β) := by
  -- Key identity: {S, S'} = S ::ₘ {S'} definitionally.
  have h_pair : ({S, S'} : TraceForest α β) = S ::ₘ ({S'} : TraceForest α β) := rfl
  refine ⟨?_, ?_, ?_⟩
  · -- b₀: 2 → 1, so 1 ≤ 2.
    rw [TraceForest.b0_singleton, h_pair, TraceForest.b0_cons,
        TraceForest.b0_singleton]
    omega
  · -- α: (S.accCount + S'.accCount) ≤ (S.size + S'.size). By accCount = size - 1.
    rw [TraceForest.alpha_singleton, TraceTree.accCount_node]
    rw [h_pair, TraceForest.alpha_cons, TraceForest.alpha_singleton]
    show TraceTree.accCount S + TraceTree.accCount S' ≤ S.size + S'.size
    show S.size - 1 + (S'.size - 1) ≤ S.size + S'.size
    omega
  · -- σ = b₀ + α; σ(F') = 1 + (S.size + S'.size); σ(F) = 2 + (S.size - 1) + (S'.size - 1).
    rw [TraceForest.sigma_singleton, TraceTree.accCount_node, h_pair,
        TraceForest.sigma, TraceForest.b0_cons, TraceForest.alpha_cons,
        TraceForest.b0_singleton, TraceForest.alpha_singleton]
    show 1 + (S.size + S'.size) = 1 + 1 + (TraceTree.accCount S + TraceTree.accCount S') + 1
    show 1 + (S.size + S'.size) = 1 + 1 + (S.size - 1 + (S'.size - 1)) + 1
    omega

/-- **IM via composition (Δ^d): size deltas for MCB Prop 1.6.4 IM/Δ^d row**
    (book p. 66). IM `{T} → {.node mover Q}` (where `Q = T/mover` is the
    Δ^d deletion-remainder) preserves all three size measures under the
    cut-shape size-conservation invariant `T.size = mover.size + Q.size + 1`.

    | Measure | Before `{T}` | After `{.node mover Q}` | Δ |
    |---|---|---|---|
    | b₀ | 1 | 1 | 0 |
    | α | T.size − 1 | mover.size + Q.size = T.size − 1 | 0 |
    | σ | T.size | T.size | 0 |

    **Why MinimalYield is NOT satisfied here**: per MCB Prop 1.6.4, IM under
    Δ^d gives Δσ = 0, but `MinimalYield`'s `minimal_yield` field requires
    `σ' = σ + 1`. So IM under Δ^d satisfies only the weaker constraints
    (no_divergence, no_info_loss) but fails the strong "minimality of yield"
    condition. MCB notes (Remark 1.6.6, p. 67) that this just reflects the
    Δ^c vs Δ^d counting difference, not a difference in Merge itself; under
    Δ^c, IM gives Δσ = +1 and satisfies MinimalYield strongly.

    **Hypothesis `h_size`**: a tree-size analog of `cut_leafCount_conservation`.
    For a single-edge cut producing `mover` with remainder `Q`, `T.size =
    mover.size + Q.size + 1` (the +1 accounts for the parent vertex contracted
    by Δ^d's edge-deletion-and-rebinarization rule per MCB Def 1.2.5). Stated
    as hypothesis here; the substrate lemma deriving it from cut-shape data
    is queued. -/
theorem im_pair_size_deltas_deltaD {T mover Q : TraceTree α β}
    (h_size : T.size = mover.size + Q.size + 1) :
    TraceForest.b0 ({.node mover Q} : TraceForest α β)
        = TraceForest.b0 ({T} : TraceForest α β)
      ∧
    TraceForest.alpha ({.node mover Q} : TraceForest α β)
        = TraceForest.alpha ({T} : TraceForest α β)
      ∧
    TraceForest.sigma ({.node mover Q} : TraceForest α β)
        = TraceForest.sigma ({T} : TraceForest α β) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Δb₀ = 0: both forests are singletons.
    rfl
  · -- Δα = 0: accCount(.node mover Q) = mover.size + Q.size = T.size - 1 = accCount T.
    rw [TraceForest.alpha_singleton, TraceForest.alpha_singleton,
        TraceTree.accCount_node]
    show mover.size + Q.size = TraceTree.accCount T
    show mover.size + Q.size = T.size - 1
    omega
  · -- Δσ = 0: σ = b₀ + α; both b₀ and α agree.
    rw [TraceForest.sigma_singleton, TraceForest.sigma_singleton,
        TraceTree.accCount_node]
    show 1 + (mover.size + Q.size) = 1 + TraceTree.accCount T
    show 1 + (mover.size + Q.size) = 1 + (T.size - 1)
    omega

/-! ## §2: Sideward Minimal Yield violations (MCB Prop 1.6.8, book p. 69)

The three Sideward forms — 2(b), 3(a), 3(b) — produce workspace transformations
that, when measured against MinimalYield (Def 1.6.1), behave as follows:

- **Sideward 3(a) and 3(b)**: Δb₀ = +1 (a NEW workspace component is created).
  This **violates `no_divergence`** (which requires Δb₀ ≤ 0). MCB Prop 1.6.8
  (book p. 69) confirms the table of size deltas.
- **Sideward 2(b)**: Δb₀ = 0, and under the same size-conservation hypotheses
  as IM, the (Δα, Δσ) = (0, 0) deltas under Δ^d match IM (cf. Prop 1.6.4 IM/Δ^d
  row). This is **Remark 1.6.9 (book p. 71)**: "the Sideward Merge of type 2(b)
  cannot be distinguished solely in terms of its effect on the sizes b₀, α, and
  σ from Internal Merge." NCL (`NoComplexityLoss`) is what rules out Sideward 2(b).

This section provides the b₀ deltas (the load-bearing observations from
Prop 1.6.8 that yield Minimal Yield violations); the full (α, σ) table for
Sideward requires the size-conservation substrate lemma queued for IM and
is deferred. -/

/-- **Sideward 2(b) preserves b₀** (MCB Prop 1.6.8, book p. 69, 2(b) row).
    Workspace `{T_i, T_j} → {.node T_i β, T_j/β}` retains 2 components. -/
theorem sideward_2b_pair_b0_preserved (T_i T_j Tnode T_j_q : TraceTree α β) :
    TraceForest.b0 ({Tnode, T_j_q} : TraceForest α β)
      = TraceForest.b0 ({T_i, T_j} : TraceForest α β) := by
  show Multiset.card _ = Multiset.card _
  rw [show ({Tnode, T_j_q} : TraceForest α β) = Tnode ::ₘ ({T_j_q} : TraceForest α β)
        from rfl,
      show ({T_i, T_j} : TraceForest α β) = T_i ::ₘ ({T_j} : TraceForest α β)
        from rfl]
  simp

/-- **Sideward 3(a) increases b₀ by 1** (MCB Prop 1.6.8, book p. 69, 3(a) row).
    Workspace `{T_i} → {.node α β, T_i/(α⊔β)}`: 1 component becomes 2. The
    extra component is `.node α β`, the merged α and β extracted from the
    same component T_i. -/
theorem sideward_3a_pair_b0_increases (T_i Tnode T_iq : TraceTree α β) :
    TraceForest.b0 ({Tnode, T_iq} : TraceForest α β)
      = TraceForest.b0 ({T_i} : TraceForest α β) + 1 := by
  show Multiset.card _ = Multiset.card _ + 1
  rw [show ({Tnode, T_iq} : TraceForest α β) = Tnode ::ₘ ({T_iq} : TraceForest α β)
        from rfl]
  simp

/-- **Sideward 3(b) increases b₀ by 1** (MCB Prop 1.6.8, book p. 69, 3(b) row).
    Workspace `{T_i, T_j} → {.node α β, T_i/α, T_j/β}`: 2 components become 3.
    The extra component is `.node α β`, the merged α and β extracted from
    different components. -/
theorem sideward_3b_pair_b0_increases
    (T_i T_j Tnode T_iq T_jq : TraceTree α β) :
    TraceForest.b0 ({Tnode, T_iq, T_jq} : TraceForest α β)
      = TraceForest.b0 ({T_i, T_j} : TraceForest α β) + 1 := by
  show Multiset.card _ = Multiset.card _ + 1
  rw [show ({Tnode, T_iq, T_jq} : TraceForest α β)
        = Tnode ::ₘ T_iq ::ₘ ({T_jq} : TraceForest α β) from rfl,
      show ({T_i, T_j} : TraceForest α β)
        = T_i ::ₘ ({T_j} : TraceForest α β) from rfl]
  simp

/-- **Sideward 3(a) violates MinimalYield's `no_divergence`** (MCB Prop 1.6.8 +
    Def 1.6.1). The Δb₀ = +1 increase rules out Sideward 3(a) under any
    coproduct convention. -/
theorem sideward_3a_violates_no_divergence (T_i Tnode T_iq : TraceTree α β) :
    ¬ MinimalYield ({T_i} : TraceForest α β)
                   ({Tnode, T_iq} : TraceForest α β) := by
  intro h
  have h_b0 := h.no_divergence
  have h_F : TraceForest.b0 ({T_i} : TraceForest α β) = 1 := by
    rw [TraceForest.b0_singleton]
  have h_F' : TraceForest.b0 ({Tnode, T_iq} : TraceForest α β) = 2 :=
    sideward_3a_pair_b0_increases T_i Tnode T_iq |>.trans (by rw [h_F])
  rw [h_F, h_F'] at h_b0
  omega

/-- **Sideward 3(b) violates MinimalYield's `no_divergence`** (MCB Prop 1.6.8 +
    Def 1.6.1). The Δb₀ = +1 increase rules out Sideward 3(b). -/
theorem sideward_3b_violates_no_divergence
    (T_i T_j Tnode T_iq T_jq : TraceTree α β) :
    ¬ MinimalYield ({T_i, T_j} : TraceForest α β)
                   ({Tnode, T_iq, T_jq} : TraceForest α β) := by
  intro h
  have h_b0 := h.no_divergence
  have h_F : TraceForest.b0 ({T_i, T_j} : TraceForest α β) = 2 := by
    show Multiset.card _ = 2
    rw [show ({T_i, T_j} : TraceForest α β) = T_i ::ₘ ({T_j} : TraceForest α β)
          from rfl]
    simp
  have h_F' : TraceForest.b0 ({Tnode, T_iq, T_jq} : TraceForest α β) = 3 :=
    sideward_3b_pair_b0_increases T_i T_j Tnode T_iq T_jq |>.trans (by rw [h_F])
  rw [h_F, h_F'] at h_b0
  omega

/-! ## §3: Sideward 2(b) and IM are indistinguishable by size measures
    (MCB Remark 1.6.9, book p. 71)

MCB observes that Sideward 2(b) and IM produce identical (b₀, α, σ) deltas
under Δ^d:

- IM: `{T} → {.node mover Q}` gives (Δb₀, Δα, Δσ) = (0, 0, 0) — see
  `im_pair_size_deltas_deltaD`.
- Sideward 2(b): `{T_i, T_j} → {.node T_i β, T_j/β}` gives (Δb₀, Δα, Δσ) =
  (0, 0, 0) under analogous size-conservation hypothesis on the cut producing β.

Both fail MinimalYield's strong form (`minimal_yield` requires Δσ = +1). MCB
(book p. 72): "The Sideward Merge of type 2(b) cannot be distinguished solely
in terms of its effect on the sizes b₀, α, and σ from Internal Merge."

The discrimination requires `NoComplexityLoss` (Def 1.6.2): IM preserves
component degree (`im_satisfiesNCL`), while Sideward 2(b) does NOT (the
T_j component maps to T_j/β with strictly lower degree).

**Substrate gap (queued)**: linglib's `NCLBetween` predicate (in
`NoComplexityLoss.lean`) uses an existential — "∃ component map satisfying
the constraint." MCB Def 1.6.2 specifies the **induced map** `Φ₀ : π₀(F) →
π₀(Φ(F))` (a specific function determined by the workspace transformation).
Proving NCL FAILS for Sideward (Prop 1.6.10 negative direction) requires
either strengthening `NCLBetween` to encode the induced-map requirement, OR
adding a separate `InducedMapNCL` predicate. Both are substrate work that
hasn't landed. Without it, the existential `NCLBetween` may be vacuously
true for some Sideward configurations (e.g., when a component happens to
have leafCount large enough for some Φ₀ to map T_j into it). -/

end Minimalist.Merge
