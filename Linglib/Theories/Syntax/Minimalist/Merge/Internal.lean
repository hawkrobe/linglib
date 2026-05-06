import Linglib.Theories.Syntax.Minimalist.Merge.External

/-!
# Internal Merge bridge: algebraic ↔ linguistic
@cite{marcolli-chomsky-berwick-2025}

Realizes M-C-B Proposition 1.4.2 (book p. 50): Internal Merge as a
**composition of two algebraic Merges** —

  IM(mover, T) = mergeOp mover (T/mover) ∘ mergeOpUnit mover

where the first stage `mergeOpUnit mover` selects the cut on T whose
cutForest equals `{mover}` (yielding `T/mover ⊗ mover`), and the second
stage performs External Merge between mover and the deletion-quotient.

## Contents

- `mergeOpUnit_apply_singleton{,_unique}`: per-cut decomposition of the
  unit-mover stage `mergeOpUnit β`. Surviving contributions are exactly
  the cuts `c` with `cutForest c = {β}`. Under uniqueness (single such
  cut `c0`), the sum collapses.
- `mergeOp_im_composition`, `mergeOp_im_composition_moverLeft`: the IM
  composition theorem. Under unique-cut-witness hypotheses, the two-stage
  pipeline reduces to EM Case 1 (`mergeOp_pair_residual` with empty F̂).
- `mergeOp_im_matches_Step`: bridge to linguistic `Step.im` via
  `((Step.im mover traceId).apply current).toHc`. Closes the IM gap.

## Status

All theorems sorry-free as of Phase 7c (commits 0.230.766-0.230.767).

**Caveat (M-C-B p. 52 "virtual particles"):** the `mergeOpUnit` stage
M_{β,1} is virtual — not a stand-alone Merge in M-C-B's formalism. It is
introduced as a bookkeeping device to factor IM as composition; the
linguistic Merge is the full IM, not the unit stage on its own.
-/

namespace Minimalist.Merge

open scoped TensorProduct
open ConnesKreimer

/-- **Per-cut reduction of `mergeOpUnit β (forestToHc {T})`.** Unfolds the
    operator chain through `comulTreeDel`'s primitive-plus-cut-sum
    decomposition; each cut's contribution is filtered by `mergePostUnit`'s
    `δ_{β, 1}` projection, surviving only when the cut-forest equals `{β}`.

    The primitive `T ⊗ 1` term contributes `forestToHc {β}` if `T = β`,
    else 0. -/
theorem mergeOpUnit_apply_singleton {α : Type*} [DecidableEq α]
    {R : Type*} [CommSemiring R] (β T : TraceTree α Unit) :
    mergeOpUnit (R := R) β (forestToHc ({T} : TraceForest α Unit))
      = (if T = β then forestToHc ({β} : TraceForest α Unit) else 0)
        + ∑ c : CutShape T,
            if c.cutForest = ({β} : TraceForest α Unit)
              then forestToHc (R := R) ({β} : TraceForest α Unit)
                * deletionRightChannel (R := R) c.remainderDeletion
              else 0 := by
  -- Step 1: unfold mergeOpUnit and reduce to mergePostUnit (comulTreeDel T).
  show mergePostUnit (R := R) (α := α) β
        (comulDelAlgHom (Finsupp.single ({T} : TraceForest α Unit) (1 : R))) = _
  rw [comulDelAlgHom_apply_single, comulForestDel_singleton,
      comulTreeDel_eq_prim_add_sum]
  -- Step 2: distribute mergePostUnit through the (primitive + sum).
  rw [map_add, map_sum]
  -- Step 3: reduce primitive part via mergePostUnit_basis_tensor.
  rw [mergePostUnit_basis_tensor]
  congr 1
  · -- Primitive part: if {T} = {β} then forestToHc {β} * 1 else 0
    --              ↔ if T = β       then forestToHc {β}     else 0
    by_cases hTβ : T = β
    · rw [if_pos hTβ, if_pos (by rw [hTβ]), mul_one]
    · rw [if_neg hTβ, if_neg (by intro h; exact hTβ (Multiset.singleton_inj.mp h))]
  · -- Cut sum: each cut term reduces via mergePostUnit_basis_tensor.
    apply Finset.sum_congr rfl
    intro c _
    rw [mergePostUnit_basis_tensor]

/-- **Unique-cut specialization of `mergeOpUnit_apply_singleton`.** Under
    the hypotheses that
    1. `T ≠ β` (β is not the whole tree, so the primitive part vanishes), and
    2. `c0` is the *unique* admissible cut on T whose cut-forest is `{β}`,

    the per-cut sum collapses to a single contribution. This is the form used
    by the IM composition theorem: it pulls β out of T and leaves the
    deletion-remainder of c0 on the right channel.

    **Note: uniqueness is a substrate convenience, NOT a M-C-B requirement.**
    M-C-B's Prop 1.4.2 (book p. 50) only requires "β is an accessible term
    of a connected component of F isomorphic to T" — it does NOT stipulate
    uniqueness, and multi-occurrence is genuinely allowed (yielding a sum
    output, structurally parallel to the EM multi-matching issue resolved
    for the F̂-residual case in Phase 7b-A). The unique-cut hypothesis here
    matches the *worked example* on book pp. 52–53 (which happens to have a
    single occurrence) but specializes the proposition. Generalizing to the
    sum-output case is queued. -/
theorem mergeOpUnit_apply_singleton_unique
    {α : Type*} [DecidableEq α]
    {R : Type*} [CommSemiring R]
    (β T : TraceTree α Unit) (c0 : CutShape T)
    (h_cf : c0.cutForest = ({β} : TraceForest α Unit))
    (h_unique : ∀ c : CutShape T,
      c.cutForest = ({β} : TraceForest α Unit) → c = c0)
    (hTβ : T ≠ β) :
    mergeOpUnit (R := R) β (forestToHc ({T} : TraceForest α Unit))
      = forestToHc (R := R) ({β} : TraceForest α Unit)
          * deletionRightChannel (R := R) c0.remainderDeletion := by
  rw [mergeOpUnit_apply_singleton]
  rw [if_neg hTβ, zero_add]
  rw [Finset.sum_eq_single c0]
  · rw [if_pos h_cf]
  · intro c _ hc_ne
    rw [if_neg]
    intro h
    exact hc_ne (h_unique c h)
  · intro h
    exact absurd (Finset.mem_univ c0) h

/-- **M-C-B Proposition 1.4.2 (book p. 50): Internal Merge as composition.**

    The two-step composition `mergeOp Q β ∘ mergeOpUnit β` applied to the
    singleton workspace `{T}` produces the merged tree `.node Q β`, where
    `Q = T/β` is identified via the deletion-remainder of the unique cut
    extracting β from T.

    **Hypotheses:**
    - `c0` is the unique admissible cut on T with `cutForest = {β}` (the
      "β is uniquely positioned in T" hypothesis; multi-occurrence case
      defers to a sum-output formulation).
    - `c0.remainderDeletion = some Q` (the cut produces a non-trivial
      remainder; for IM we always have at least the trace-replaced root).
    - `T ≠ β` (β is a proper subtree, not the whole workspace).

    Note: no `β ≠ Q` hypothesis is required — `mergeOp_pair` handles the
    diagonal case `Q = β` correctly (the workspace becomes `{β, β}` and
    the merged tree is `.node β β`).

    Quotient-structure note: under `comulDelAlgHom` (the deletion variant
    Δ^d, which `mergeOp` uses), the deeper copy of β is *removed* from T
    via edge contraction — book p. 53 eq. (1.4.2) shows `T₁ = T/^d T₂`
    with `{the, apple}` struck through, not replaced by a trace. Trace
    replacement is the Δ^c story (book p. 53 bottom). So the algebraic
    quotient `Q = T/β` here has β's leaves removed entirely, which makes
    `β ≠ Q` typical but not enforced by the substrate. The Step.im
    bridge (Phase 7c.4) reconciles this with the linguistic-layer
    `mkTrace` sentinel via a trace-aware `SyntacticObject.toHc`
    projection.

    The proof is two steps:
    1. Apply `mergeOpUnit_apply_singleton_unique` to reduce the inner
       `mergeOpUnit β (forestToHc {T})` to `forestToHc {β, Q}`.
    2. Apply EM Case 1 (`mergeOp_eps_zero_pair` after collapsing to the
       unweighted form via `mergeOp_eps_one`) to merge `Q` and `β` into
       `.node Q β`.

    **Caveat (book p. 52):** This composition is the algebraic realization
    of IM, but `mergeOpUnit` (= `M_{β, 1}`) is NOT itself a Merge operation —
    it only exists as the first half of this composition, like virtual
    particles in physics. -/
theorem mergeOp_im_composition
    {α : Type*} [DecidableEq α]
    {R : Type*} [CommSemiring R]
    (β T Q : TraceTree α Unit) (c0 : CutShape T)
    (h_cf : c0.cutForest = ({β} : TraceForest α Unit))
    (h_remainder : c0.remainderDeletion = some Q)
    (h_unique : ∀ c : CutShape T,
      c.cutForest = ({β} : TraceForest α Unit) → c = c0)
    (hTβ : T ≠ β) :
    mergeOp (R := R) Q β
        (mergeOpUnit (R := R) β (forestToHc ({T} : TraceForest α Unit)))
      = forestToHc (R := R) ({.node Q β} : TraceForest α Unit) := by
  -- Step 1: mergeOpUnit β (forestToHc {T}) = forestToHc {β} * forestToHc {Q}
  --                                        = forestToHc ({β} + {Q})
  --                                        = forestToHc {β, Q}
  rw [mergeOpUnit_apply_singleton_unique β T c0 h_cf h_unique hTβ,
      h_remainder]
  -- Now: mergeOp Q β (forestToHc {β} * deletionRightChannel (some Q)) = ...
  -- deletionRightChannel (some Q) = forestToHc {Q}.
  show mergeOp (R := R) Q β
        (forestToHc ({β} : TraceForest α Unit) *
         forestToHc ({Q} : TraceForest α Unit)) = _
  rw [← forestToHc_add]
  -- Goal: mergeOp Q β (forestToHc ({β} + {Q})) = forestToHc {.node Q β}
  -- Rewrite {β} + {Q} = {Q, β} (multiset).
  -- Multiset add commutes; {Q, β} = {Q} + {β} = {β} + {Q} definitionally.
  have h_swap : ({β} : TraceForest α Unit) + ({Q} : TraceForest α Unit)
              = ({Q, β} : TraceForest α Unit) :=
    add_comm _ _
  rw [h_swap]
  -- Now apply EM Case 1: mergeOp Q β (forestToHc {Q, β}) = forestToHc {.node Q β}
  -- Use mergeOp_eps_zero_pair (which is for ε = 0) and mergeOp_eps_one to bridge.
  -- Actually the cleanest is to use mergeOp_pair directly. Let me check what's available.
  -- Since mergeOp = mergeOp_eps 1, we use mergeOp_pair (the ε=1 EM Case 1 theorem).
  exact mergeOp_pair Q β

/-- **Step.im argument-order variant of `mergeOp_im_composition`.**

    `Step.im mover traceId current = .node mover (current.replace mover (mkTrace traceId))`
    has mover LEFT, traced (= the algebraic Q) RIGHT. M-C-B's `M_{T/β, β}`
    has Q LEFT, β RIGHT (the convention `mergeOp_im_composition` follows).

    This swap-variant produces `forestToHc {.node β Q}` instead of
    `{.node Q β}`, matching `Step.im`'s constructor order. The proof is
    structurally simpler than the swap-needing version:
    `{β} + {Q} = {β, Q}` definitionally (no `add_comm` needed). -/
theorem mergeOp_im_composition_moverLeft
    {α : Type*} [DecidableEq α]
    {R : Type*} [CommSemiring R]
    (β T Q : TraceTree α Unit) (c0 : CutShape T)
    (h_cf : c0.cutForest = ({β} : TraceForest α Unit))
    (h_remainder : c0.remainderDeletion = some Q)
    (h_unique : ∀ c : CutShape T,
      c.cutForest = ({β} : TraceForest α Unit) → c = c0)
    (hTβ : T ≠ β) :
    mergeOp (R := R) β Q
        (mergeOpUnit (R := R) β (forestToHc ({T} : TraceForest α Unit)))
      = forestToHc (R := R) ({.node β Q} : TraceForest α Unit) := by
  rw [mergeOpUnit_apply_singleton_unique β T c0 h_cf h_unique hTβ, h_remainder]
  show mergeOp (R := R) β Q
        (forestToHc ({β} : TraceForest α Unit) *
         forestToHc ({Q} : TraceForest α Unit)) = _
  rw [← forestToHc_add]
  -- {β} + {Q} = {β, Q} definitionally (no swap needed for mover-LEFT order)
  show mergeOp (R := R) β Q
        (forestToHc ({β, Q} : TraceForest α Unit)) = _
  exact mergeOp_pair β Q

/-- **Step.im algebraic bridge (M-C-B Prop 1.4.2 specialization).**

    Given the cut data `c0` linking the algebraic deletion-quotient on
    `current.toHc` to the trace-replaced linguistic quotient
    `(current.replace mover (mkTrace traceId)).toHc`, the IM composition
    `mergeOp mover.toHc Q ∘ mergeOpUnit mover.toHc` reproduces
    `((Step.im mover traceId).apply current).toHc`.

    Closes the IM gap in the algebraic-↔-linguistic Merge bridge,
    completing Phase 7c. -/
theorem mergeOp_im_matches_Step
    (current mover : Minimalist.SyntacticObject) (traceId : Nat)
    (c0 : CutShape current.toHc)
    (h_cf : c0.cutForest = ({mover.toHc} : TraceForest LIToken Unit))
    (h_remainder : c0.remainderDeletion =
      some (current.replace mover (Minimalist.mkTrace traceId)).toHc)
    (h_unique : ∀ c : CutShape current.toHc,
      c.cutForest = ({mover.toHc} : TraceForest LIToken Unit) → c = c0)
    (h_curr_ne_mover : current.toHc ≠ mover.toHc) :
    mergeOp (R := ℤ) mover.toHc
        (current.replace mover (Minimalist.mkTrace traceId)).toHc
        (mergeOpUnit (R := ℤ) mover.toHc
          (forestToHc ({current.toHc} : TraceForest LIToken Unit)))
      = forestToHc (R := ℤ)
          ({((Step.im mover traceId).apply current).toHc}
            : TraceForest LIToken Unit) := by
  -- Apply the mover-LEFT IM composition with β = mover.toHc, T = current.toHc,
  -- Q = (current.replace mover (mkTrace traceId)).toHc.
  rw [mergeOp_im_composition_moverLeft mover.toHc current.toHc
        (current.replace mover (Minimalist.mkTrace traceId)).toHc
        c0 h_cf h_remainder h_unique h_curr_ne_mover]
  -- Result: forestToHc {.node mover.toHc (current.replace mover (mkTrace _)).toHc}
  -- Need: forestToHc {((Step.im mover traceId).apply current).toHc}
  -- Step.im mover traceId current = .node mover (current.replace mover (mkTrace traceId))
  -- toHc_node: (.node a b).toHc = .node a.toHc b.toHc
  rfl

/-! ## §4: IM cost-survival at ε = 0 (M-C-B Prop 1.5.1 bullet 3)

@cite{marcolli-chomsky-berwick-2025} Proposition 1.5.1 says: "in the
limit ε → 0, only derivations in which all the Merge operations are
Internal Merge and External Merge remain." Sideward suppression is
proven in `Sideward.lean` §4.1; this section proves the **IM positive
direction** — IM via composition at ε = 0 produces a non-zero result
(weight 1).

Operationally, IM's cost-zero status follows from rule 4
(`c(ℳ(T, 1)) = 0`) for stage 1 plus rule 5 (member-depth 0) for stage 2,
with no need for rule 2's negative quotient weight `ε^{-d_v}` to be
separately tracked in substrate.

**Caveat (MCB virtual-particles, §1.4.3).** Our two-stage realization
materializes the workspace `{T_v, T_i/T_v}` between stages 1 and 2,
whereas MCB's signed-weight cost calculation `c(ℳ(T_v, T_i/T_v)) =
d_v − d_v = 0` works directly on a single `ℳ` action without
instantiating the intermediate workspace. The two formulations agree
numerically; the operational substitution requires accepting `ℳ_{β,1}`
as a (virtual) intermediate stage. See @cite{marcolli-chomsky-berwick-2025}
on the "virtual particles" caveat for the unit-stage operator.

**Scope.** This section directly realizes Prop 1.5.1 bullets 1+3 (cost-0
characterization + ε=0 limit) at the per-merge level. Bullet 2 ("for ε < 1,
IM/EM are leading-order terms in any derivation") follows compositionally
from bullet 3 plus non-negativity of the cost weights: each merge step's
constant (ε^0) coefficient is non-zero for EM/IM (this section + EM
analogues in `External.lean`) and zero for Sideward (`Sideward.lean` §4.1),
so a derivation chain's constant coefficient equals the product of
per-step constant coefficients — yielding the EM/IM-only contribution.
The chain-level bullet 2 statement is queued as a small follow-up
(induction over the derivation chain length).
-/

/-- **IM cost-survival, ε = 0** (M-C-B Prop 1.5.1 bullet 3, IM positive
    direction). At ε = 0, the IM composition `mergeOp_eps 0 mover (T/mover)
    ∘ mergeOpUnit mover` produces a NON-ZERO output of weight 1
    (= `forestToHc {.node mover (T/mover)}`), confirming that IM is one
    of the surviving derivations in the cost limit.

    Compare with `mergeOp_eps_zero_for_sideward_2b/3a/3b` (in `Sideward.lean`
    §4.1) which prove that Sideward variants vanish at ε = 0. Together
    they realize MCB Prop 1.5.1's "only IM and EM survive" claim.

    Structurally identical to `mergeOp_im_composition_moverLeft` (above)
    but using `mergeOp_eps 0` instead of `mergeOp` for stage 2. The proof
    swaps `mergeOp_pair` for `mergeOp_eps_zero_pair`. -/
theorem mergeOp_eps_zero_im_composition_moverLeft
    {α : Type*} [DecidableEq α]
    {R : Type*} [CommSemiring R]
    (β T Q : TraceTree α Unit) (c0 : CutShape T)
    (h_cf : c0.cutForest = ({β} : TraceForest α Unit))
    (h_remainder : c0.remainderDeletion = some Q)
    (h_unique : ∀ c : CutShape T,
      c.cutForest = ({β} : TraceForest α Unit) → c = c0)
    (hTβ : T ≠ β) :
    mergeOp_eps (R := R) 0 β Q
        (mergeOpUnit (R := R) β (forestToHc ({T} : TraceForest α Unit)))
      = forestToHc (R := R) ({.node β Q} : TraceForest α Unit) := by
  rw [mergeOpUnit_apply_singleton_unique β T c0 h_cf h_unique hTβ, h_remainder]
  show mergeOp_eps (R := R) 0 β Q
        (forestToHc ({β} : TraceForest α Unit) *
         forestToHc ({Q} : TraceForest α Unit)) = _
  rw [← forestToHc_add]
  -- {β} + {Q} = {β, Q} definitionally (no swap needed for mover-LEFT order)
  show mergeOp_eps (R := R) 0 β Q
        (forestToHc ({β, Q} : TraceForest α Unit)) = _
  exact mergeOp_eps_zero_pair β Q

/-- **IM cost-survival, ε = 0, original (Q-LEFT) argument order.** Analog
    of `mergeOp_im_composition`. Q is the LEFT argument of the second
    Merge stage; the result has Q-LEFT, β-RIGHT structure. -/
theorem mergeOp_eps_zero_im_composition
    {α : Type*} [DecidableEq α]
    {R : Type*} [CommSemiring R]
    (β T Q : TraceTree α Unit) (c0 : CutShape T)
    (h_cf : c0.cutForest = ({β} : TraceForest α Unit))
    (h_remainder : c0.remainderDeletion = some Q)
    (h_unique : ∀ c : CutShape T,
      c.cutForest = ({β} : TraceForest α Unit) → c = c0)
    (hTβ : T ≠ β) :
    mergeOp_eps (R := R) 0 Q β
        (mergeOpUnit (R := R) β (forestToHc ({T} : TraceForest α Unit)))
      = forestToHc (R := R) ({.node Q β} : TraceForest α Unit) := by
  rw [mergeOpUnit_apply_singleton_unique β T c0 h_cf h_unique hTβ, h_remainder]
  show mergeOp_eps (R := R) 0 Q β
        (forestToHc ({β} : TraceForest α Unit) *
         forestToHc ({Q} : TraceForest α Unit)) = _
  rw [← forestToHc_add]
  -- {β} + {Q} = {Q} + {β} = {Q, β} (multiset commutativity)
  have h_swap : ({β} : TraceForest α Unit) + ({Q} : TraceForest α Unit)
              = ({Q, β} : TraceForest α Unit) := add_comm _ _
  rw [h_swap]
  exact mergeOp_eps_zero_pair Q β

/-- **Step.im algebraic bridge at ε = 0** (M-C-B Prop 1.5.1, IM positive
    direction, linguistic specialization). The IM composition at ε = 0
    reproduces `((Step.im mover traceId).apply current).toHc` with
    weight 1, demonstrating that IM survives the Minimal Search cost
    limit and is therefore one of the dominant Merge operations in
    actual derivations. -/
theorem mergeOp_eps_zero_im_matches_Step
    (current mover : Minimalist.SyntacticObject) (traceId : Nat)
    (c0 : CutShape current.toHc)
    (h_cf : c0.cutForest = ({mover.toHc} : TraceForest LIToken Unit))
    (h_remainder : c0.remainderDeletion =
      some (current.replace mover (Minimalist.mkTrace traceId)).toHc)
    (h_unique : ∀ c : CutShape current.toHc,
      c.cutForest = ({mover.toHc} : TraceForest LIToken Unit) → c = c0)
    (h_curr_ne_mover : current.toHc ≠ mover.toHc) :
    mergeOp_eps (R := ℤ) 0 mover.toHc
        (current.replace mover (Minimalist.mkTrace traceId)).toHc
        (mergeOpUnit (R := ℤ) mover.toHc
          (forestToHc ({current.toHc} : TraceForest LIToken Unit)))
      = forestToHc (R := ℤ)
          ({((Step.im mover traceId).apply current).toHc}
            : TraceForest LIToken Unit) := by
  rw [mergeOp_eps_zero_im_composition_moverLeft mover.toHc current.toHc
        (current.replace mover (Minimalist.mkTrace traceId)).toHc
        c0 h_cf h_remainder h_unique h_curr_ne_mover]
  rfl

end Minimalist.Merge
