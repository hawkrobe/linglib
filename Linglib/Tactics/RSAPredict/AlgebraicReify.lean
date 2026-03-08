import Lean
import Linglib.Tactics.RSAPredict.AutoDetect

set_option autoImplicit false

/-!
# Cache-Seeded RSA Reification

Fast-path reification for RSA score-level expressions. Instead of letting the
generic `reifyToRExpr` discover leaf values by unfolding through 8+ RSA
definition layers (~15,000 `unfoldDefinition?` calls at ~1ms each), this
module pre-seeds the reification cache with L0 policy values for every
(latent, utterance, world) triple.

When the generic reifier subsequently processes L1 scores, it only needs to
unfold through the L1/S1 structure (~3-4 layers), hitting cache on every L0
policy sub-expression. The kernel verification is correct by construction
because the generic reifier builds the RExpr tree by tracing the actual
definition chain.

Falls back to the generic reifier with no pre-seeding if config detection fails.
-/

namespace Linglib.Tactics.RSAPredict

open Lean Meta Elab Tactic
open Linglib.Interval

-- ============================================================================
-- Config Detection
-- ============================================================================

/-- Scan an expression tree for RSA.RSAConfig.L1agent applied to a cfg argument.
    Returns the cfg Expr if found. Handles:
    - Direct: `RationalAction.score (L1agent cfg) u w`
    - Marginal: `Finset.sum finset (fun w => score (L1agent cfg) u w)` -/
partial def findL1AgentCfg (e : Expr) (depth : ℕ := 20) : MetaM (Option Expr) := do
  if depth == 0 then return none
  let mut current := e
  for _ in List.range 10 do
    let fn := current.getAppFn
    let args := current.getAppArgs
    if fn.isConstOf ``RSA.RSAConfig.L1agent then
      if args.size ≥ 3 then
        return some args[args.size - 1]!
    if fn.isConstOf ``Core.RationalAction.score then
      if args.size ≥ 4 then
        let ra := args[3]!
        if let some cfg ← findL1AgentCfg ra (depth - 1) then
          return some cfg
    -- Check for HMul — look inside operands (cross-utterance pattern)
    if fn.isConstOf ``HMul.hMul && args.size ≥ 6 then
      if let some cfg ← findL1AgentCfg args[4]! (depth - 1) then
        return some cfg
      if let some cfg ← findL1AgentCfg args[5]! (depth - 1) then
        return some cfg
    -- Check for Finset.sum — look inside the lambda body
    if fn.isConstOf ``Finset.sum && args.size ≥ 5 then
      let fBody := args[args.size - 1]!
      if fBody.isLambda then
        let bodyInst := fBody.bindingBody!
        if let some cfg ← findL1AgentCfgInBody bodyInst (depth - 1) then
          return some cfg
    if let some e' ← unfoldDefinition? current then
      current := e'.headBeta
    else break
  return none
where
  findL1AgentCfgInBody (body : Expr) (depth : ℕ) : MetaM (Option Expr) := do
    if depth == 0 then return none
    let fn := body.getAppFn
    let args := body.getAppArgs
    if fn.isConstOf ``RSA.RSAConfig.L1agent then
      if args.size ≥ 3 then
        return some args[args.size - 1]!
    if fn.isConstOf ``Core.RationalAction.score then
      if args.size ≥ 4 then
        let ra := args[3]!
        return ← findL1AgentCfgInBody ra (depth - 1)
    for arg in args do
      if let some cfg ← findL1AgentCfgInBody arg (depth - 1) then
        return some cfg
    return none

-- ============================================================================
-- Cache Pre-Seeding
-- ============================================================================

/-- Pre-seed the reification cache with all L0 policy values.

    For each (l, u, w) triple, reifies `(L0agent cfg l).policy u w` via the
    generic reifier. These are the innermost leaves of the L1 score expression
    tree. By pre-seeding them, the generic reifier only needs to unfold through
    the L1/S1 structure (~3-4 layers) instead of the full 8+ layers.

    Returns `true` if pre-seeding succeeded, `false` to skip. -/
private def preseedL0Policies (cache : ReifyCache) (cfg : Expr)
    (allLElems allUElems allWElems : Array Expr) : MetaM Bool := do
  for l in allLElems do
    let l0agent ← mkAppM ``RSA.RSAConfig.L0agent #[cfg, l]
    for u in allUElems do
      for w in allWElems do
        let policyExpr ← mkAppM ``Core.RationalAction.policy #[l0agent, u, w]
        let _ ← reifyToRExpr cache policyExpr maxDepth
  return true

/-- Pre-seed the reification cache with all S1 score values.

    For each (l, w, u) triple, reifies `(S1agent cfg l).score w u`.
    After L0 policies are cached, this only needs to unfold through the
    s1Score function (~2-3 layers). -/
private def preseedS1Scores (cache : ReifyCache) (cfg : Expr)
    (allLElems allUElems allWElems : Array Expr) : MetaM Bool := do
  for l in allLElems do
    let s1agent ← mkAppM ``RSA.RSAConfig.S1agent #[cfg, l]
    for w in allWElems do
      for u in allUElems do
        let scoreExpr ← mkAppM ``Core.RationalAction.score #[s1agent, w, u]
        let _ ← reifyToRExpr cache scoreExpr maxDepth
  return true

-- ============================================================================
-- Top-Level Orchestrator
-- ============================================================================

/-- Try cache-seeded RSA reification for score-level expressions.

    1. Detect RSAConfig from the expression
    2. Pre-seed cache with L0 policies and S1 scores
    3. Return `none` — the caller's generic `reifyToRExpr` will then run
       with a warm cache, hitting cache hits on inner expressions

    This is not a replacement for `reifyToRExpr` — it's a cache warmer.
    Returns `true` if pre-seeding was done. -/
def tryPreseedRSACache (cache : ReifyCache) (lhs rhs : Expr) : MetaM Bool := do
  let t0 ← IO.monoMsNow

  -- Step 1: Find RSAConfig from either side
  let some cfg ← findL1AgentCfg lhs | return false
  -- Verify rhs uses the same config
  let some cfg2 ← findL1AgentCfg rhs | return false
  unless ← isDefEq cfg cfg2 do return false

  -- Step 2: Extract type info and enumerate elements
  let cfgType ← whnf (← inferType cfg)
  let cfgArgs := cfgType.getAppArgs
  unless cfgArgs.size ≥ 2 do return false
  let U := cfgArgs[0]!
  let W := cfgArgs[1]!
  let latentExpr ← mkAppM ``RSA.RSAConfig.Latent #[cfg]
  let L ← whnf latentExpr

  let (_, allUElems) ← getFiniteElems U
  let (_, allWElems) ← getFiniteElems W
  let (_, allLElems) ← getFiniteElems L
  let nU := allUElems.size
  let nW := allWElems.size
  let nL := allLElems.size

  logInfo m!"rsa_predict: [preseed] |U|={nU}, |W|={nW}, |L|={nL}"

  -- Step 3: Pre-seed L0 policies
  let _ ← preseedL0Policies cache cfg allLElems allUElems allWElems
  let t1 ← IO.monoMsNow
  logInfo m!"rsa_predict: [preseed] L0 policies cached ({t1 - t0}ms)"

  -- Step 4: Pre-seed S1 scores (with L0 cache hits)
  let _ ← preseedS1Scores cache cfg allLElems allUElems allWElems
  let t2 ← IO.monoMsNow
  logInfo m!"rsa_predict: [preseed] S1 scores cached ({t2 - t1}ms)"

  let cacheSize ← do let c ← cache.get; pure c.size
  logInfo m!"rsa_predict: [preseed] cache size: {cacheSize} ({t2 - t0}ms total)"
  return true

end Linglib.Tactics.RSAPredict
