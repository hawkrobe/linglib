import Linglib.Core.Agent.DecisionTheory
import Linglib.Theories.Pragmatics.DecisionTheoretic.Core
import Mathlib.Data.Fintype.Basic

/-!
# Merin–Van Rooy Bridge
@cite{merin-1999} @cite{van-rooy-2003}

Formal connection between Merin's Decision-Theoretic Semantics (DTS) and
Van Rooy's decision-theoretic question framework.

## The Connection

@cite{van-rooy-2003} (L&P 26, pp. 727–763) defines two measures of
proposition utility:
- **VSI(C)** = max_a EU(a,C) − EU(a⁰,C), "can obviously never be negative" (p. 735)
- **UV(C)** = max_a EU(a,C) − max_a EU(a), "can be negative" (p. 736)

At the question level, EUV(Q) = ∑ P(q)·UV(q) = EVSI(Q) ≥ 0 (p. 742).

Merin's DTS uses a **dichotomic issue** {H, ¬H} with **Bayes factors**
BF(E) = P(E|H)/P(E|¬H). In §5.4, @cite{van-rooy-2003} connects UV to
Merin's **argumentative value**: when preferences beyond truth-resolution
are at stake, UV(C) captures the directional relevance of a proposition.

The bridge: Merin's dichotomic issue is a special case of Van Rooy's
decision problem (`truthDP`) where:
- Actions = {accept H, reject H}
- Utility depends only on truth: U(w, accept) = 1 iff H(w), else 0

Under this encoding:
- BF > 1 → learning E increases EU(accept H), i.e., shifts the posterior
  toward H (`posRelevant_shifts_accept_eu`)
- BF = 1 → learning E leaves all conditional EUs unchanged, so UV = 0
  (`irrelevant_implies_zero_uv`)

Note: UV(E) for a **single cell** E can be negative even when BF > 1
(@cite{van-rooy-2003}, p. 736). The non-negativity result holds for
**expected** UV across the full partition, not for individual cells.

## Results

- `truthDP`: Encoding of a dichotomic issue as a DecisionProblem
- `posRelevant_shifts_accept_eu`: BF > 1 → EU(accept|E) > EU(accept)
- `irrelevant_implies_zero_uv`: BF = 1 → UV(E) = 0 (non-degenerate)
-/

namespace DTS.MerinBridge

open Core.DecisionTheory
open DTS

/-! ## Encoding Merin's Question as a Decision Problem

A dichotomic issue {H, ¬H} with prior π corresponds to a decision problem:
- World type W (shared)
- Actions = Bool (accept H = true, reject H = false)
- U(w, accept) = 1 iff H(w); U(w, reject) = 1 iff ¬H(w)
- Prior = π -/

/-- Encode a DTS context (dichotomic issue + prior) as a decision problem.

The agent must choose between accepting H (true) or rejecting H (false).
Utility = 1 for correct choice, 0 for incorrect. -/
def truthDP {W : Type*} (ctx : DTSContext W) : DecisionProblem W Bool where
  utility w a :=
    if a then  -- accept H
      if w ∈ ctx.topic then 1 else 0
    else       -- reject H
      if w ∈ ctx.topic then 0 else 1
  prior := ctx.prior

/-- The action set for the truth DP: accept or reject. -/
def truthActions : Finset Bool := {true, false}

/-! ## Bridge Theorems -/

/-- Positive relevance shifts the conditional EU of "accept H" upward.

When BF > 1, learning E raises P(H|E) above P(H), which means
EU(accept H | E) > EU(accept H). This is the core Merin–Van Rooy
bridge: Merin's relevance sign determines the direction of the
posterior shift for the truth decision problem.

Note: this does NOT imply UV(E) ≥ 0 for the single cell E.
UV of a single cell can be negative (@cite{van-rooy-2003}, p. 736).
The non-negativity result (EVSI ≥ 0) holds for the **expected** UV
across the full partition {E, ¬E}, not for individual cells (p. 742).

TODO: Original Bool-based proof used `native_decide` over
World4 (16 topics × 16 evidence props = 256 cases). Per project
proof-style guidelines, kernel-checkable structural proofs are
preferred. A Prop-level reformulation needs decidability for
arbitrary `e : World4 → Prop`, which constrains the form of any
finite enumeration argument. The intended proof: posRelevant means
P(E∧H)·P(¬H) > P(E∧¬H)·P(H), which under uniform prior reduces to
|E∩H|·|¬H| > |E∩¬H|·|H|; conditionalEU(accept|E) = |E∩H|/|E| while
expectedUtility(accept) = |H|/|W|, so the shift inequality reduces
to the same cell-count comparison. -/
theorem posRelevant_shifts_accept_eu :
    ∀ (ctx : DTSContext World4) (e : Set World4) [DecidablePred (· ∈ e)],
    (∀ w, ctx.prior w = 1/4) →
    -- Non-degeneracy: E, H, ¬H all non-empty
    (∃ w, w ∈ e) →
    (∃ w, w ∈ ctx.topic) →
    (∃ w, w ∉ ctx.topic) →
    posRelevant ctx e →
    conditionalEU (truthDP ctx)
      (Finset.univ.filter (fun w => w ∈ e)) true >
    expectedUtility (truthDP ctx) true := by
  sorry

/-- Merin's irrelevance corresponds to zero utility value.

If E is irrelevant to H (BF = 1) and the conditioning is non-degenerate
(E non-empty, both H and ¬H have witnesses), then learning E doesn't
change any conditional EU, so UV(E) = 0.

The key step: BF = 1 under uniform prior means P(E|H) = P(E|¬H),
which gives |E∩H|/|H| = |E∩¬H|/|¬H|, hence |E∩H|/|E| = |H|/4.
So conditionalEU(a|E) = expectedUtility(a) for each action a,
making valueAfterLearning = dpValue.

TODO: Original Bool-based proof used `native_decide` over the 256-cell
finite verification. A kernel-checkable structural proof requires
case analysis on the discrete partition cells together with
`DecidablePred e` to evaluate filter cardinalities. -/
theorem irrelevant_implies_zero_uv :
    ∀ (ctx : DTSContext World4) (e : Set World4) [DecidablePred (· ∈ e)],
    (∀ w, ctx.prior w = 1/4) →
    -- Non-degeneracy: E, H, ¬H all non-empty
    (∃ w, w ∈ e) →
    (∃ w, w ∈ ctx.topic) →
    (∃ w, w ∉ ctx.topic) →
    irrelevant ctx e →
    utilityValue (truthDP ctx) truthActions
      (Finset.univ.filter (fun w => w ∈ e)) = 0 := by
  sorry

/-! ## Structural Properties

Properties that hold by construction, connecting the two frameworks
without requiring full numerical computation. -/

/-- The truth DP has exactly two actions. -/
theorem truthActions_card : truthActions.card = 2 := by decide

/-- In the truth DP, the two actions partition the utility: for any world,
exactly one action has utility 1 and the other has utility 0. -/
theorem truthDP_complementary {W : Type*} (ctx : DTSContext W) (w : W) :
    (truthDP ctx).utility w true + (truthDP ctx).utility w false = 1 := by
  simp only [truthDP]
  by_cases h : w ∈ ctx.topic <;> simp [h]

/-- The truth DP's expected utility of "accept H" equals P(H). -/
theorem truthDP_eu_accept {W : Type*} [Fintype W] [DecidableEq W]
    (ctx : DTSContext W) :
    expectedUtility (truthDP ctx) true = ∑ w : W, ctx.prior w *
      if w ∈ ctx.topic then 1 else 0 := by
  simp only [expectedUtility, truthDP, ite_true]

/-- The truth DP's expected utility of "reject H" equals P(¬H). -/
theorem truthDP_eu_reject {W : Type*} [Fintype W] [DecidableEq W]
    (ctx : DTSContext W) :
    expectedUtility (truthDP ctx) false = ∑ w : W, ctx.prior w *
      if w ∈ ctx.topic then 0 else 1 := by
  simp [expectedUtility, truthDP]

end DTS.MerinBridge
