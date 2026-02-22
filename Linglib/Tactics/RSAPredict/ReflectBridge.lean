import Lean
import Linglib.Core.Interval.RSAVerify
import Linglib.Tactics.RSAPredict.Helpers
import Linglib.Tactics.RSAPredict.AutoDetect

set_option autoImplicit false

/-!
# RSAPredict Reflection Bridge

Meta-level helpers for the reflection-based verification path. When the
RSA config is built via `RSAConfigData.toRSAConfig`, the tactic can
bypass the expensive CProof pipeline and use `native_decide` directly
on the computable `checkL1ScoreGt` function.

## Design

The reflection path works in three tiers:

1. **Tier 1 — ConfigData detection**: Check if `cfg` unfolds to
   `d.toRSAConfig` for some `RSAConfigData d`. Use `native_decide`
   on the computable ℚ pipeline + `isDefEq` bridge.

2. **Tier 2 — Auto-detection**: Pattern-match the `s1Score` lambda
   to classify it into a known `S1ScoreSpec` variant, extract ℚ
   parameters, build `RSAConfigData` internally, verify via
   `native_decide`, bridge via `_ext` theorems.

3. **Tier 3 — CProof fallback**: If both tiers fail, the main tactic
   falls back to the compositional CProof pipeline.
-/

namespace Linglib.Tactics.RSAPredict

open Lean Meta Elab Tactic

-- ============================================================================
-- ConfigData Detection (Tier 1)
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

    Tier 1: Check cfg unfolds to `d.toRSAConfig`, use `l1_gt_of_check`.
    Tier 2: Auto-detect s1Score pattern, build RSAConfigData, use `l1_gt_of_check_ext`.

    Returns true if successful, false to fall back to CProof. -/
def tryReflectL1Compare (goal : MVarId) (cfg u w₁ w₂ : Expr) : TacticM Bool := do
  let some d ← extractConfigData? cfg
    | do -- Tier 2: auto-detect from raw RSAConfig
         return ← tryAutoDetectL1Compare goal cfg u w₁ w₂
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
    | return ← tryAutoDetectL1ScoreGt goal cfg u₁ w₁ u₂ w₂
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

/-- Try to prove `¬(cfg.L1 u w₁ > cfg.L1 u w₂)` via reflection.
    Uses checkL1ScoreNotGt + native_decide + l1_not_gt_of_check. -/
def tryReflectL1NotGt (goal : MVarId) (cfg u w₁ w₂ : Expr) : TacticM Bool := do
  let some d ← extractConfigData? cfg
    | return ← tryAutoDetectL1NotGt goal cfg u w₁ w₂
  logInfo m!"rsa_predict: [reflect/¬L1] found RSAConfigData, trying reflection path..."
  try
    let checkExpr ← mkAppM ``RSA.Verify.checkL1ScoreNotGt #[d, u, w₁, u, w₂]
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
    let proof ← mkAppM ``RSA.Verify.l1_not_gt_of_check #[d, u, w₁, w₂, eqMVar]
    let proofType ← inferType proof
    let goalType ← goal.getType
    if ← isDefEq proofType goalType then
      goal.assign proof
      return true
    else return false
  catch e =>
    logInfo m!"rsa_predict: [reflect/¬L1] failed: {e.toMessageData}"
    return false

/-- Try to prove `cfg.S1 l w u₁ > cfg.S1 l w u₂` via reflection.
    Uses checkS1PolicyGt + native_decide + s1_gt_of_check. -/
def tryReflectS1Compare (goal : MVarId) (cfg l w u₁ u₂ : Expr) : TacticM Bool := do
  let some d ← extractConfigData? cfg
    | return ← tryAutoDetectS1Compare goal cfg l w u₁ u₂
  logInfo m!"rsa_predict: [reflect/S1] found RSAConfigData, trying reflection path..."
  try
    let checkExpr ← mkAppM ``RSA.Verify.checkS1PolicyGt #[d, l, w, u₁, u₂]
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
    let proof ← mkAppM ``RSA.Verify.s1_gt_of_check #[d, l, w, u₁, u₂, eqMVar]
    let proofType ← inferType proof
    let goalType ← goal.getType
    if ← isDefEq proofType goalType then
      goal.assign proof
      return true
    else return false
  catch e =>
    logInfo m!"rsa_predict: [reflect/S1] failed: {e.toMessageData}"
    return false

/-- Try to prove `¬(cfg.S1 l w u₁ > cfg.S1 l w u₂)` via reflection.
    Uses checkS1PolicyNotGt + native_decide + s1_not_gt_of_check. -/
def tryReflectS1NotGt (goal : MVarId) (cfg l w u₁ u₂ : Expr) : TacticM Bool := do
  let some d ← extractConfigData? cfg
    | return ← tryAutoDetectS1NotGt goal cfg l w u₁ u₂
  logInfo m!"rsa_predict: [reflect/¬S1] found RSAConfigData, trying reflection path..."
  try
    let checkExpr ← mkAppM ``RSA.Verify.checkS1PolicyNotGt #[d, l, w, u₁, u₂]
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
    let proof ← mkAppM ``RSA.Verify.s1_not_gt_of_check #[d, l, w, u₁, u₂, eqMVar]
    let proofType ← inferType proof
    let goalType ← goal.getType
    if ← isDefEq proofType goalType then
      goal.assign proof
      return true
    else return false
  catch e =>
    logInfo m!"rsa_predict: [reflect/¬S1] failed: {e.toMessageData}"
    return false

end Linglib.Tactics.RSAPredict
