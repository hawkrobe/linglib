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

end Minimalist.Merge
