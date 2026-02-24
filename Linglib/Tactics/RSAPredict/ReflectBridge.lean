import Lean
import Linglib.Core.Interval.RSAVerify
import Linglib.Core.Interval.ReflectInterval
import Linglib.Tactics.RSAPredict.Helpers
import Linglib.Tactics.RSAPredict.Reify

set_option autoImplicit false

/-!
# RSAPredict Reflection Bridge

Direct RExpr reification for all RSA comparison goals.

## Design

The proof-emitting reifier merges reification and bridge construction into a single pass:

1. **Reify + prove**: Convert both sides of the comparison to `RExpr` AST,
   emitting a proof `goalExpr = denote(rexpr)` alongside each `RExpr` node.
   Transparent steps (unfold, whnf) pass proofs through unchanged; structural
   steps (HAdd, Real.exp, ite) compose sub-proofs via congruence lemmas.
2. **Check**: `native_decide` on batched `checkGt`/`checkNotGt` (evalValid + separation).
3. **Assign**: Combine equality proofs + interval proof to close the goal.

This eliminates the old two-phase approach (reify, then rebuild equality proof via
`buildIteResolutionProof`) and avoids the kernel `Decidable` synthesis failure
that occurred when `isDefEq` tried to unfold `Real.log` inside `denote(rexpr)`.
-/

namespace Linglib.Tactics.RSAPredict

open Lean Meta Elab Tactic
open Linglib.Interval

-- ============================================================================
-- Direct RExpr Pipeline
-- ============================================================================

/-- Prove a Prop via `native_decide`. Returns the proof term. -/
private def nativeDecideProof (propType : Expr) : TacticM Expr := do
  let mvar ← mkFreshExprMVar propType
  let savedGoals ← getGoals
  setGoals [mvar.mvarId!]
  evalTactic (← `(tactic| native_decide))
  setGoals savedGoals
  return mvar

/-- Direct RExpr reification for `lhs > rhs` goals.
    Uses proof-emitting reifier — no rfl bridge or ite-resolution bridge needed. -/
def tryDirectRExprCompare (goal : MVarId) (lhsExpr rhsExpr : Expr) : TacticM Bool := do
  let t0 ← IO.monoMsNow
  let cache ← IO.mkRef (∅ : Std.HashMap UInt64 (Expr × MetaBounds × Expr))
  let (lhsRExpr, lhsBounds, lhsProof) ← reifyToRExpr cache lhsExpr maxDepth
  let (rhsRExpr, rhsBounds, rhsProof) ← reifyToRExpr cache rhsExpr maxDepth

  unless lhsBounds.lo > rhsBounds.hi do
    logInfo m!"rsa_predict: [direct] bounds don't separate"
    return false

  let t1 ← IO.monoMsNow
  logInfo m!"rsa_predict: [direct] reified ({t1 - t0}ms)"

  try
    -- Single batched native_decide: evalBoth + separation
    let checkExpr ← mkAppM ``RExpr.checkGt #[lhsRExpr, rhsRExpr]
    let checkType ← mkEq checkExpr (mkConst ``Bool.true)
    let hcheck ← nativeDecideProof checkType

    let t2 ← IO.monoMsNow
    logInfo m!"rsa_predict: [direct] native_decide ({t2 - t1}ms)"

    -- Build proof with explicit arguments to avoid mkAppM isDefEq overhead.
    -- gt_of_checkGt : (lhs rhs : RExpr) → checkGt lhs rhs = true → denote lhs > denote rhs
    let intervalProof := mkApp3 (mkConst ``RExpr.gt_of_checkGt) lhsRExpr rhsRExpr hcheck
    -- gt_of_eq_gt_eq {a b c d : ℝ} (hac : a = c) (hbd : b = d) (h : c > d) : a > b
    let denoteLhs := mkApp (mkConst ``RExpr.denote) lhsRExpr
    let denoteRhs := mkApp (mkConst ``RExpr.denote) rhsRExpr
    let finalProof := Lean.mkApp7 (mkConst ``RExpr.gt_of_eq_gt_eq)
      lhsExpr rhsExpr denoteLhs denoteRhs
      lhsProof rhsProof intervalProof

    let t2b ← IO.monoMsNow
    logInfo m!"rsa_predict: [direct] proof built ({t2b - t2}ms)"

    goal.assign finalProof

    let t3 ← IO.monoMsNow
    logInfo m!"rsa_predict: [direct] assigned ({t3 - t0}ms)"
    return true
  catch e =>
    logInfo m!"rsa_predict: [direct] failed: {e.toMessageData}"
    return false

/-- Direct RExpr reification for `not (lhs > rhs)` goals.
    Uses proof-emitting reifier — no rfl bridge or ite-resolution bridge needed. -/
def tryDirectRExprNotGt (goal : MVarId) (lhsExpr rhsExpr : Expr) : TacticM Bool := do
  let t0 ← IO.monoMsNow
  let cache ← IO.mkRef (∅ : Std.HashMap UInt64 (Expr × MetaBounds × Expr))
  let (lhsRExpr, lhsBounds, lhsProof) ← reifyToRExpr cache lhsExpr maxDepth
  let (rhsRExpr, rhsBounds, rhsProof) ← reifyToRExpr cache rhsExpr maxDepth

  let t1 ← IO.monoMsNow
  logInfo m!"rsa_predict: [direct/not-gt] reified ({t1 - t0}ms)"

  try
    let denoteLhs := mkApp (mkConst ``RExpr.denote) lhsRExpr
    let denoteRhs := mkApp (mkConst ``RExpr.denote) rhsRExpr

    -- Fast path: structurally equal RExpr → ¬(x > x) by irrefl
    let eqType ← mkEq lhsRExpr rhsRExpr
    if let some heq ← try? (nativeDecideProof eqType) then
      let denoteFn := mkConst ``RExpr.denote
      let denoteCongr ← mkAppM ``congrArg #[denoteFn, heq]
      let denoteLevelProof := mkApp3 (mkConst ``RExpr.not_gt_of_denote_eq)
        lhsRExpr rhsRExpr denoteCongr
      let finalProof := Lean.mkApp7 (mkConst ``RExpr.not_gt_of_eq_not_gt_eq)
        lhsExpr rhsExpr denoteLhs denoteRhs
        lhsProof rhsProof denoteLevelProof
      goal.assign finalProof
      let t2 ← IO.monoMsNow
      logInfo m!"rsa_predict: [direct/not-gt] assigned via structural equality ({t2 - t0}ms)"
      return true

    -- Exact ℚ evaluation path: for pure arithmetic RExpr (no exp/log),
    -- evaluate both to exact ℚ and check ¬(>).
    let exactCheckExpr ← mkAppM ``RExpr.checkExactNotGt #[lhsRExpr, rhsRExpr]
    let exactCheckType ← mkEq exactCheckExpr (mkConst ``Bool.true)
    if let some hexact ← try? (nativeDecideProof exactCheckType) then
      let exactProof := mkApp3 (mkConst ``RExpr.not_gt_of_checkExactNotGt)
        lhsRExpr rhsRExpr hexact
      let finalProof := Lean.mkApp7 (mkConst ``RExpr.not_gt_of_eq_not_gt_eq)
        lhsExpr rhsExpr denoteLhs denoteRhs
        lhsProof rhsProof exactProof
      goal.assign finalProof
      let t2 ← IO.monoMsNow
      logInfo m!"rsa_predict: [direct/not-gt] assigned via exact ℚ ({t2 - t0}ms)"
      return true

    -- Interval separation path: need lhs.eval.hi ≤ rhs.eval.lo
    unless lhsBounds.hi ≤ rhsBounds.lo do
      logInfo m!"rsa_predict: [direct/not-gt] bounds don't prove le, exact ℚ not available"
      return false

    let checkExpr ← mkAppM ``RExpr.checkNotGt #[lhsRExpr, rhsRExpr]
    let checkType ← mkEq checkExpr (mkConst ``Bool.true)
    let hcheck ← nativeDecideProof checkType

    let intervalProof := mkApp3 (mkConst ``RExpr.not_gt_of_checkNotGt)
      lhsRExpr rhsRExpr hcheck
    let finalProof := Lean.mkApp7 (mkConst ``RExpr.not_gt_of_eq_not_gt_eq)
      lhsExpr rhsExpr denoteLhs denoteRhs
      lhsProof rhsProof intervalProof
    goal.assign finalProof

    let t2 ← IO.monoMsNow
    logInfo m!"rsa_predict: [direct/not-gt] assigned via interval ({t2 - t0}ms)"
    return true
  catch e =>
    logInfo m!"rsa_predict: [direct/not-gt] failed: {e.toMessageData}"
    return false

-- ============================================================================
-- Reflection-Based Proof Builders (unified direct RExpr strategy)
-- ============================================================================

/-- Try to prove `cfg.L1 u w1 > cfg.L1 u w2` via direct RExpr reification.
    Returns true if successful, false to fall back to CProof. -/
def tryReflectL1Compare (goal : MVarId) (cfg u w₁ w₂ : Expr) : TacticM Bool := do
  let lhs ← mkAppM ``RSA.RSAConfig.L1 #[cfg, u, w₁]
  let rhs ← mkAppM ``RSA.RSAConfig.L1 #[cfg, u, w₂]
  tryDirectRExprCompare goal lhs rhs

/-- Try to prove `cfg.L1agent.score u1 w1 > cfg.L1agent.score u2 w2` via reflection.
    Used for marginal/cross-utterance comparisons at the score level. -/
def tryReflectL1ScoreGt (goal : MVarId) (cfg u₁ w₁ u₂ w₂ : Expr) : TacticM Bool := do
  let l1agent ← mkAppM ``RSA.RSAConfig.L1agent #[cfg]
  let lhs ← mkAppM ``Core.RationalAction.score #[l1agent, u₁, w₁]
  let rhs ← mkAppM ``Core.RationalAction.score #[l1agent, u₂, w₂]
  tryDirectRExprCompare goal lhs rhs

/-- Try to prove `not (cfg.L1 u w1 > cfg.L1 u w2)` via reflection. -/
def tryReflectL1NotGt (goal : MVarId) (cfg u w₁ w₂ : Expr) : TacticM Bool := do
  let lhs ← mkAppM ``RSA.RSAConfig.L1 #[cfg, u, w₁]
  let rhs ← mkAppM ``RSA.RSAConfig.L1 #[cfg, u, w₂]
  tryDirectRExprNotGt goal lhs rhs

/-- Try to prove `cfg.S1 l w u1 > cfg.S1 l w u2` via reflection. -/
def tryReflectS1Compare (goal : MVarId) (cfg l w u₁ u₂ : Expr) : TacticM Bool := do
  let lhs ← mkAppM ``RSA.RSAConfig.S1 #[cfg, l, w, u₁]
  let rhs ← mkAppM ``RSA.RSAConfig.S1 #[cfg, l, w, u₂]
  tryDirectRExprCompare goal lhs rhs

/-- Try to prove `not (cfg.S1 l w u1 > cfg.S1 l w u2)` via reflection. -/
def tryReflectS1NotGt (goal : MVarId) (cfg l w u₁ u₂ : Expr) : TacticM Bool := do
  let lhs ← mkAppM ``RSA.RSAConfig.S1 #[cfg, l, w, u₁]
  let rhs ← mkAppM ``RSA.RSAConfig.S1 #[cfg, l, w, u₂]
  tryDirectRExprNotGt goal lhs rhs

end Linglib.Tactics.RSAPredict
