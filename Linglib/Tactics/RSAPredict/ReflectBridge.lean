import Lean
import Linglib.Core.Interval.RSAVerify
import Linglib.Tactics.RSAPredict.Helpers

set_option autoImplicit false

/-!
# RSAPredict Reflection Bridge

Meta-level helpers for the reflection-based verification path. When the
RSA config is built via `RSAConfigData.toRSAConfig`, the tactic can
bypass the expensive CProof pipeline and use `native_decide` directly
on the computable `checkL1ScoreGt` function.

## Design

The reflection path works in three steps:

1. **Detection**: Check if `cfg` unfolds to `d.toRSAConfig` for some
   `RSAConfigData d`.
2. **Compilation**: Build `checkL1ScoreGt d u w₁ u w₂ = true` and
   close it with `native_decide` (~2s compilation, ~100ms execution).
3. **Bridging**: Apply `l1_gt_of_check` to produce the ℝ-valued proof.

If any step fails (no RSAConfigData, bounds don't separate, compilation
error), the tactic falls back to the CProof pipeline transparently.
-/

namespace Linglib.Tactics.RSAPredict

open Lean Meta Elab Tactic

-- ============================================================================
-- ConfigData Detection
-- ============================================================================

/-- Try to extract `RSAConfigData d` from a config expression `cfg`,
    where `cfg` unfolds to `RSAConfigData.toRSAConfig d`.
    Returns `d` if successful. -/
def extractConfigData? (cfg : Expr) : MetaM (Option Expr) := do
  let mut current := cfg
  for _ in List.range 20 do
    let fn := current.getAppFn
    if fn.isConstOf ``RSA.RSAConfigData.toRSAConfig then
      let args := current.getAppArgs
      -- toRSAConfig args: U, W, FintypeU, FintypeW, DecEqU, DecEqW, d
      if args.size >= 7 then
        return some args[6]!
      -- Fewer args: try the last one
      if args.size >= 1 then
        return some args.back!
      return none
    if let some e' ← unfoldDefinition? current then
      current := e'.headBeta
    else break
  return none

-- ============================================================================
-- Reflection-Based Proof Builders
-- ============================================================================

/-- Try to prove `cfg.L1 u w₁ > cfg.L1 u w₂` via reflection.

    1. Check cfg unfolds to `d.toRSAConfig` for some RSAConfigData d
    2. Build `checkL1ScoreGt d u w₁ u w₂ = true`
    3. Close via native_decide
    4. Apply l1_gt_of_check

    Returns true if successful, false to fall back to CProof. -/
def tryReflectL1Compare (goal : MVarId) (cfg u w₁ w₂ : Expr) : TacticM Bool := do
  let some d ← extractConfigData? cfg
    | return false
  logInfo m!"rsa_predict: [reflect] found RSAConfigData, trying reflection path..."
  try
    -- Build checkL1ScoreGt d u w₁ u w₂ = true
    let checkExpr ← mkAppM ``RSA.Verify.checkL1ScoreGt #[d, u, w₁, u, w₂]
    let trueExpr := mkConst ``Bool.true
    let eqType ← mkEq checkExpr trueExpr
    let eqMVar ← mkFreshExprMVar eqType
    -- Prove via native_decide (saves/restores goals to avoid side effects)
    let savedGoals ← getGoals
    setGoals [eqMVar.mvarId!]
    try
      evalTactic (← `(tactic| native_decide))
    catch e =>
      setGoals savedGoals
      logInfo m!"rsa_predict: [reflect] native_decide failed (bounds may not separate): {e.toMessageData}"
      return false
    setGoals savedGoals
    -- Build the proof: l1_gt_of_check d u w₁ w₂ eqProof
    let proof ← mkAppM ``RSA.Verify.l1_gt_of_check #[d, u, w₁, w₂, eqMVar]
    -- Check type compatibility (cfg.L1 vs d.toRSAConfig.L1)
    let proofType ← inferType proof
    let goalType ← goal.getType
    if ← isDefEq proofType goalType then
      goal.assign proof
      return true
    else
      logInfo m!"rsa_predict: [reflect] proof type mismatch (cfg ≠ d.toRSAConfig definitionally)"
      return false
  catch e =>
    logInfo m!"rsa_predict: [reflect] failed: {e.toMessageData}"
    return false

/-- Try to prove `cfg.L1agent.score u₁ w₁ > cfg.L1agent.score u₂ w₂` via reflection.
    Used for marginal/cross-utterance comparisons at the score level. -/
def tryReflectL1ScoreGt (goal : MVarId) (cfg u₁ w₁ u₂ w₂ : Expr) : TacticM Bool := do
  let some d ← extractConfigData? cfg
    | return false
  logInfo m!"rsa_predict: [reflect/score] found RSAConfigData, trying reflection path..."
  try
    let checkExpr ← mkAppM ``RSA.Verify.checkL1ScoreGt #[d, u₁, w₁, u₂, w₂]
    let trueExpr := mkConst ``Bool.true
    let eqType ← mkEq checkExpr trueExpr
    let eqMVar ← mkFreshExprMVar eqType
    let savedGoals ← getGoals
    setGoals [eqMVar.mvarId!]
    try
      evalTactic (← `(tactic| native_decide))
    catch _ =>
      setGoals savedGoals
      return false
    setGoals savedGoals
    let proof ← mkAppM ``RSA.Verify.l1_score_gt_of_check #[d, u₁, w₁, u₂, w₂, eqMVar]
    let proofType ← inferType proof
    let goalType ← goal.getType
    if ← isDefEq proofType goalType then
      goal.assign proof
      return true
    else return false
  catch _ => return false

end Linglib.Tactics.RSAPredict
