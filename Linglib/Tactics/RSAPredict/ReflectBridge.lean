import Lean
import Linglib.Core.Interval.RSAVerify
import Linglib.Core.Interval.ReflectInterval
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

The reflection path works in four tiers:

1. **Tier 1 -- ConfigData detection**: Check if `cfg` unfolds to
   `d.toRSAConfig` for some `RSAConfigData d`. Use `native_decide`
   on the computable Q pipeline + `isDefEq` bridge.

2. **Tier 1.5 -- Direct RExpr reification**: Reify the goal expression
   directly into `RExpr`, use `native_decide` for interval separation,
   and bridge via equality proofs. Resolves stuck `Decidable.rec` nodes
   from `RationalAction.policy`'s `if totalScore = 0` via `if_neg` proofs.

3. **Tier 2 -- Auto-detection**: Pattern-match the `s1Score` lambda
   to classify it into a known `S1ScoreSpec` variant, extract Q
   parameters, build `RSAConfigData` internally, verify via
   `native_decide`, bridge via `_ext` theorems.

4. **Tier 3 -- CProof fallback**: If all tiers fail, the main tactic
   falls back to the compositional CProof pipeline.
-/

namespace Linglib.Tactics.RSAPredict

open Lean Meta Elab Tactic
open Linglib.Interval

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
-- Direct RExpr Pipeline (Tier 1.5)
-- ============================================================================

/-- Prove a Prop via `native_decide`. Returns the proof term. -/
private def nativeDecideProof (propType : Expr) : TacticM Expr := do
  let mvar ← mkFreshExprMVar propType
  let savedGoals ← getGoals
  setGoals [mvar.mvarId!]
  evalTactic (← `(tactic| native_decide))
  setGoals savedGoals
  return mvar

/-- Prove `denote(rexpr) > 0` via `gt_of_eval_separated rexpr (nat 0)`. -/
private def proveDenotePosViaInterval (rexpr : Expr) : TacticM Expr := do
  let zeroRExpr ← mkAppM ``RExpr.nat #[mkRawNatLit 0]
  -- evalValid proofs
  let hvx ← nativeDecideProof
    (← mkEq (← mkAppM ``RExpr.evalValid #[rexpr]) (mkConst ``Bool.true))
  let hv0 ← nativeDecideProof
    (← mkEq (← mkAppM ``RExpr.evalValid #[zeroRExpr]) (mkConst ``Bool.true))
  -- separation proof: (nat 0).eval.hi < rexpr.eval.lo
  let zeroEval ← mkAppM ``RExpr.eval #[zeroRExpr]
  let xEval ← mkAppM ``RExpr.eval #[rexpr]
  let zeroHi := mkProj ``Linglib.Interval.QInterval 1 zeroEval
  let xLo := mkProj ``Linglib.Interval.QInterval 0 xEval
  let sepType ← mkAppM ``LT.lt #[zeroHi, xLo]
  let hsep ← nativeDecideProof sepType
  mkAppM ``RExpr.gt_of_eval_separated #[rexpr, zeroRExpr, hvx, hv0, hsep]

/-- Build a proof that `goalExpr = denote(rexpr)` by resolving stuck ites
    and descending through arithmetic structure.

    The rexpr (from reification) is pure arithmetic — ites have been resolved.
    The goalExpr may have stuck `Decidable.rec` from `RationalAction.policy`.
    This function walks both in parallel:
    - Arithmetic ops (add, mul, div, sub, exp, log, neg): extract sub-expressions
      from goalW, match against rexpr sub-expressions, build congruence proofs
    - Stuck ites: resolve via `if_neg` proofs from interval arithmetic -/
private partial def buildIteResolutionProof (cache : ReifyCache) (goalExpr rexpr : Expr)
    (depth : Nat := 50) : TacticM Expr := do
  if depth == 0 then
    throwError "rsa_predict: [ite-resolution] max depth reached"

  -- Fast path: already definitionally equal?
  let denoteExpr ← mkAppM ``RExpr.denote #[rexpr]
  if ← isDefEq goalExpr denoteExpr then
    return ← mkAppM ``Eq.refl #[goalExpr]

  -- whnf the goal expression to expose structure
  let goalW ← whnf goalExpr

  -- Debug: log at shallow depths only (first few levels)
  if depth ≥ 45 then
    let goalHead := goalExpr.getAppFn
    let goalHdName := if goalHead.isConst then s!"{goalHead.constName!}" else s!"{goalHead.ctorName}"
    logInfo m!"rsa_predict: [ite-res] depth={depth}, goalExpr head: {goalHdName}({goalExpr.getAppNumArgs}), rexpr: {rexpr.getAppFn}"

  -- Check for Decidable.rec / Decidable.casesOn (stuck ite)
  let whnfHead := goalW.getAppFn
  let isDecRec := whnfHead.isConstOf ``Decidable.rec || whnfHead.isConstOf ``Decidable.casesOn
  if isDecRec && goalW.getAppNumArgs >= 5 then
    let args := goalW.getAppArgs
    let prop := args[0]!
    let isFalseBr := args[2]!
    let isTrueBr := args[3]!
    let decInst := args[4]!

    -- Extract then/else branch bodies via beta-reduction
    let negProp ← mkAppM ``Not #[prop]
    let dummyFalseProof := mkApp2 (mkConst ``sorryAx [levelZero]) negProp (toExpr true)
    let elseBrBody := (Expr.app isFalseBr dummyFalseProof).headBeta
    let dummyTrueProof := mkApp2 (mkConst ``sorryAx [levelZero]) prop (toExpr true)
    let thenBrBody := (Expr.app isTrueBr dummyTrueProof).headBeta

    if prop.isAppOfArity ``Eq 3 then
      let condVal := prop.getAppArgs[1]!
      let zeroVal := prop.getAppArgs[2]!

      -- Try getOfNat? first, then fall back to resolveNat? for reduced forms
      let zeroOk := getOfNat? zeroVal == some 0
      let zeroOk ← if zeroOk then pure true
        else do
          let r ← resolveNat? zeroVal
          pure (r == some 0)

      if zeroOk then
        let (condRExpr, condBounds) ← reifyToRExpr cache condVal maxDepth

        if condBounds.lo > 0 then
          -- condVal > 0 → else branch taken (if_neg)
          let condEqProof ← buildIteResolutionProof cache condVal condRExpr (depth - 1)
          let denoteGtZero ← proveDenotePosViaInterval condRExpr
          let condGtZero ← mkAppM ``RExpr.gt_of_eq #[condEqProof, denoteGtZero]
          let condNeqZero ← mkAppM ``ne_of_gt #[condGtZero]

          -- Build if_neg explicitly (avoids mkAppM metavar issue)
          let realType := mkConst ``Real
          let ifNegConst := mkConst ``if_neg [mkLevelSucc levelZero]
          let ifNegProof := mkApp6 ifNegConst prop decInst condNeqZero realType thenBrBody elseBrBody

          -- Recursively resolve the else branch
          let branchEqProof ← buildIteResolutionProof cache elseBrBody rexpr (depth - 1)
          return ← mkAppM ``Eq.trans #[ifNegProof, branchEqProof]

        else if condBounds.lo == 0 && condBounds.hi == 0 then
          -- condVal = 0 → then branch taken (if_pos)
          let condEqProof ← buildIteResolutionProof cache condVal condRExpr (depth - 1)

          -- Prove denote(condRExpr) = 0 via eval_zero
          let hvProof ← nativeDecideProof
            (← mkEq (← mkAppM ``RExpr.evalValid #[condRExpr]) (mkConst ``Bool.true))
          let condEval ← mkAppM ``RExpr.eval #[condRExpr]
          let loExpr := mkProj ``Linglib.Interval.QInterval 0 condEval
          let hiExpr := mkProj ``Linglib.Interval.QInterval 1 condEval
          let zeroQ := mkApp2 (mkConst ``OfNat.ofNat [levelZero])
            (mkConst ``Rat) (mkRawNatLit 0)
          let hloProof ← nativeDecideProof (← mkEq loExpr zeroQ)
          let hhiProof ← nativeDecideProof (← mkEq hiExpr zeroQ)
          let denoteEqZero ← mkAppM ``RExpr.eq_zero_of_eval_zero
            #[condRExpr, hvProof, hloProof, hhiProof]
          let condEqZero ← mkAppM ``RExpr.eq_zero_of_eq #[condEqProof, denoteEqZero]

          -- Build if_pos explicitly
          let realType := mkConst ``Real
          let ifPosConst := mkConst ``if_pos [mkLevelSucc levelZero]
          let ifPosProof := mkApp6 ifPosConst prop decInst condEqZero realType thenBrBody elseBrBody

          -- Recursively resolve the then branch
          let branchEqProof ← buildIteResolutionProof cache thenBrBody rexpr (depth - 1)
          return ← mkAppM ``Eq.trans #[ifPosProof, branchEqProof]

  -- Structural descent: use isDefEq with metavars to extract sub-expressions.
  -- This handles whnf reducing through definitions (e.g., Real.exp → Complex.exp.re)
  -- by letting isDefEq match at the semantic level.
  let realType := mkConst ``Real

  -- Binary operators: add, mul, div, sub
  let binOps : Array (Name × Name × Name) := #[
    (``RExpr.add, ``RExpr.congr_add, ``HAdd.hAdd),
    (``RExpr.mul, ``RExpr.congr_mul, ``HMul.hMul),
    (``RExpr.div, ``RExpr.congr_div, ``HDiv.hDiv),
    (``RExpr.sub, ``RExpr.congr_sub, ``HSub.hSub)]
  for (ctor, congr, op) in binOps do
    if rexpr.isAppOfArity ctor 2 then
      let ra := rexpr.getAppArgs[0]!
      let rb := rexpr.getAppArgs[1]!
      let aMVar ← mkFreshExprMVar realType
      let bMVar ← mkFreshExprMVar realType
      if let some expectedExpr ← try? (mkAppM op #[aMVar, bMVar]) then
        if ← isDefEq goalExpr expectedExpr then
          let actualA ← instantiateMVars aMVar
          let actualB ← instantiateMVars bMVar
          let ha ← buildIteResolutionProof cache actualA ra (depth - 1)
          let hb ← buildIteResolutionProof cache actualB rb (depth - 1)
          return ← mkAppM congr #[ha, hb]

  -- Unary operators: exp, log, neg
  let unaryOps : Array (Name × Name × Name) := #[
    (``RExpr.rexp, ``RExpr.congr_exp, ``Real.exp),
    (``RExpr.rlog, ``RExpr.congr_log, ``Real.log),
    (``RExpr.neg, ``RExpr.congr_neg, ``Neg.neg)]
  for (ctor, congr, op) in unaryOps do
    if rexpr.isAppOfArity ctor 1 then
      let r := rexpr.getAppArgs[0]!
      let argMVar ← mkFreshExprMVar realType
      if let some expectedExpr ← try? (mkAppM op #[argMVar]) then
        if ← isDefEq goalExpr expectedExpr then
          let actualArg ← instantiateMVars argMVar
          let ha ← buildIteResolutionProof cache actualArg r (depth - 1)
          return ← mkAppM congr #[ha]

  -- Check whnf form one more time
  if ← isDefEq goalW denoteExpr then
    return ← mkAppM ``Eq.refl #[goalExpr]

  -- Diagnostic: why did we fail?
  let hd := goalW.getAppFn
  let hdName := if hd.isConst then s!"{hd.constName!}" else s!"(not a const: {hd.ctorName})"
  let decRecInfo := if isDecRec then
    let args := goalW.getAppArgs
    let prop := args[0]!
    let isEq3 := prop.isAppOfArity ``Eq 3
    if isEq3 then
      let zeroVal := prop.getAppArgs[2]!
      let zeroNat := getOfNat? zeroVal
      s!", prop=Eq(3), getOfNat?(rhs)={zeroNat}, rhs_head={zeroVal.getAppFn}"
    else
      s!", prop_head={prop.getAppFn}, prop_arity={prop.getAppNumArgs}"
  else ""
  -- Log the goalExpr head (pre-whnf) and whether binary op matching was attempted
  let goalHead := goalExpr.getAppFn
  let goalHdName := if goalHead.isConst then s!"{goalHead.constName!}" else s!"{goalHead.ctorName}"
  let binOpAttempted := if rexpr.isAppOfArity ``RExpr.sub 2 then
    s!", goalExpr_head={goalHdName}({goalExpr.getAppNumArgs})"
  else ""
  throwError "rsa_predict: [ite-resolution] cannot resolve at depth={depth}, whnf head: {hdName}, nargs: {goalW.getAppNumArgs}, rexpr: {rexpr.getAppFn}{decRecInfo}{binOpAttempted}"

/-- Direct RExpr reification for `lhs > rhs` goals. -/
def tryDirectRExprCompare (goal : MVarId) (lhsExpr rhsExpr : Expr) : TacticM Bool := do
  let t0 ← IO.monoMsNow
  let cache ← IO.mkRef (∅ : Std.HashMap UInt64 (Expr × MetaBounds))
  let (lhsRExpr, lhsBounds) ← reifyToRExpr cache lhsExpr maxDepth
  let (rhsRExpr, rhsBounds) ← reifyToRExpr cache rhsExpr maxDepth

  unless lhsBounds.lo > rhsBounds.hi do
    logInfo m!"rsa_predict: [direct] bounds don't separate"
    return false

  let t1 ← IO.monoMsNow
  logInfo m!"rsa_predict: [direct] reified ({t1 - t0}ms)"

  try
    -- native_decide proofs
    let hvl ← nativeDecideProof
      (← mkEq (← mkAppM ``RExpr.evalValid #[lhsRExpr]) (mkConst ``Bool.true))
    let hvr ← nativeDecideProof
      (← mkEq (← mkAppM ``RExpr.evalValid #[rhsRExpr]) (mkConst ``Bool.true))
    let rhsEval ← mkAppM ``RExpr.eval #[rhsRExpr]
    let lhsEval ← mkAppM ``RExpr.eval #[lhsRExpr]
    let rhsHi := mkProj ``Linglib.Interval.QInterval 1 rhsEval
    let lhsLo := mkProj ``Linglib.Interval.QInterval 0 lhsEval
    let hsep ← nativeDecideProof (← mkAppM ``LT.lt #[rhsHi, lhsLo])

    let t2 ← IO.monoMsNow
    logInfo m!"rsa_predict: [direct] native_decide ({t2 - t1}ms)"

    let intervalProof ← mkAppM ``RExpr.gt_of_eval_separated
      #[lhsRExpr, rhsRExpr, hvl, hvr, hsep]

    -- Check if denote(rexpr) is definitionally equal to the goal sides (no stuck ites)
    let denLhs ← mkAppM ``RExpr.denote #[lhsRExpr]
    let denRhs ← mkAppM ``RExpr.denote #[rhsRExpr]
    let rflOk ← withoutModifyingState do
      let a ← isDefEq lhsExpr denLhs
      let b ← isDefEq rhsExpr denRhs
      return a && b
    if rflOk then
      goal.assign intervalProof
      let t3 ← IO.monoMsNow
      logInfo m!"rsa_predict: [direct] assigned via rfl bridge ({t3 - t0}ms)"
      return true

    -- Stuck ites: build equality proofs via if_neg chain
    logInfo m!"rsa_predict: [direct] rfl bridge failed (stuck ites), resolving..."
    let hEqLhs ← buildIteResolutionProof cache lhsExpr lhsRExpr
    let hEqRhs ← buildIteResolutionProof cache rhsExpr rhsRExpr

    let finalProof ← mkAppM ``RExpr.gt_of_eq_gt_eq
      #[hEqLhs, hEqRhs, intervalProof]
    goal.assign finalProof

    let t3 ← IO.monoMsNow
    logInfo m!"rsa_predict: [direct] assigned via ite-bridge ({t3 - t0}ms)"
    return true
  catch e =>
    logInfo m!"rsa_predict: [direct] failed: {e.toMessageData}"
    return false

/-- Direct RExpr reification for `not (lhs > rhs)` goals. -/
def tryDirectRExprNotGt (goal : MVarId) (lhsExpr rhsExpr : Expr) : TacticM Bool := do
  let t0 ← IO.monoMsNow
  let cache ← IO.mkRef (∅ : Std.HashMap UInt64 (Expr × MetaBounds))
  let (lhsRExpr, lhsBounds) ← reifyToRExpr cache lhsExpr maxDepth
  let (rhsRExpr, rhsBounds) ← reifyToRExpr cache rhsExpr maxDepth

  let t1 ← IO.monoMsNow
  logInfo m!"rsa_predict: [direct/not-gt] reified ({t1 - t0}ms)"

  try
    -- Fast path: structurally equal RExpr → ¬(x > x) by irrefl
    let eqType ← mkEq lhsRExpr rhsRExpr
    if let some heq ← try? (nativeDecideProof eqType) then
      let denoteFn := mkConst ``RExpr.denote
      let denoteCongr ← mkAppM ``congrArg #[denoteFn, heq]
      let proof ← mkAppM ``RExpr.not_gt_of_denote_eq #[lhsRExpr, rhsRExpr, denoteCongr]

      let denLhs ← mkAppM ``RExpr.denote #[lhsRExpr]
      let denRhs ← mkAppM ``RExpr.denote #[rhsRExpr]
      let rflOk ← withoutModifyingState do
        let a ← isDefEq lhsExpr denLhs
        let b ← isDefEq rhsExpr denRhs
        return a && b
      if rflOk then
        goal.assign proof
        let t2 ← IO.monoMsNow
        logInfo m!"rsa_predict: [direct/not-gt] assigned via structural equality ({t2 - t0}ms)"
        return true

    -- Interval separation path: need lhs.eval.hi ≤ rhs.eval.lo
    unless lhsBounds.hi ≤ rhsBounds.lo do
      logInfo m!"rsa_predict: [direct/not-gt] bounds don't prove le"
      return false

    let hvl ← nativeDecideProof
      (← mkEq (← mkAppM ``RExpr.evalValid #[lhsRExpr]) (mkConst ``Bool.true))
    let hvr ← nativeDecideProof
      (← mkEq (← mkAppM ``RExpr.evalValid #[rhsRExpr]) (mkConst ``Bool.true))
    let lhsEval ← mkAppM ``RExpr.eval #[lhsRExpr]
    let rhsEval ← mkAppM ``RExpr.eval #[rhsRExpr]
    let lhsHi := mkProj ``Linglib.Interval.QInterval 1 lhsEval
    let rhsLo := mkProj ``Linglib.Interval.QInterval 0 rhsEval
    let hbound ← nativeDecideProof (← mkAppM ``LE.le #[lhsHi, rhsLo])

    let intervalProof ← mkAppM ``RExpr.not_gt_of_eval_bounded
      #[lhsRExpr, rhsRExpr, hvl, hvr, hbound]

    let denLhs ← mkAppM ``RExpr.denote #[lhsRExpr]
    let denRhs ← mkAppM ``RExpr.denote #[rhsRExpr]
    let rflOk ← withoutModifyingState do
      let a ← isDefEq lhsExpr denLhs
      let b ← isDefEq rhsExpr denRhs
      return a && b
    if rflOk then
      goal.assign intervalProof
      let t2 ← IO.monoMsNow
      logInfo m!"rsa_predict: [direct/not-gt] assigned via rfl bridge ({t2 - t0}ms)"
      return true

    logInfo m!"rsa_predict: [direct/not-gt] rfl bridge failed (stuck ites), resolving..."
    let hEqLhs ← buildIteResolutionProof cache lhsExpr lhsRExpr
    let hEqRhs ← buildIteResolutionProof cache rhsExpr rhsRExpr

    let finalProof ← mkAppM ``RExpr.not_gt_of_eq_not_gt_eq
      #[hEqLhs, hEqRhs, intervalProof]
    goal.assign finalProof

    let t2 ← IO.monoMsNow
    logInfo m!"rsa_predict: [direct/not-gt] assigned via ite-bridge ({t2 - t0}ms)"
    return true
  catch e =>
    logInfo m!"rsa_predict: [direct/not-gt] failed: {e.toMessageData}"
    return false

-- ============================================================================
-- Reflection-Based Proof Builders (Tiers 1, 1.5, 2)
-- ============================================================================

/-- Try to prove `cfg.L1 u w1 > cfg.L1 u w2` via reflection.

    Tier 1: Check cfg unfolds to `d.toRSAConfig`, use `l1_gt_of_check`.
    Tier 1.5: Direct RExpr reification with ite resolution.
    Tier 2: Auto-detect s1Score pattern, build RSAConfigData, use `l1_gt_of_check_ext`.

    Returns true if successful, false to fall back to CProof. -/
def tryReflectL1Compare (goal : MVarId) (cfg u w₁ w₂ : Expr) : TacticM Bool := do
  let some d ← extractConfigData? cfg
    | do -- Tier 1.5: direct RExpr reification
         let lhs ← mkAppM ``RSA.RSAConfig.L1 #[cfg, u, w₁]
         let rhs ← mkAppM ``RSA.RSAConfig.L1 #[cfg, u, w₂]
         if ← tryDirectRExprCompare goal lhs rhs then return true
         -- Tier 2: auto-detect fallback
         return ← tryAutoDetectL1Compare goal cfg u w₁ w₂
  logInfo m!"rsa_predict: [reflect] found RSAConfigData, trying reflection path..."
  try
    -- Build checkL1ScoreGt d u w1 u w2 = true
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
    -- Build the proof: l1_gt_of_check d u w1 w2 eqProof
    let proof ← mkAppM ``RSA.Verify.l1_gt_of_check #[d, u, w₁, w₂, eqMVar]
    -- Check type compatibility (cfg.L1 vs d.toRSAConfig.L1)
    let proofType ← inferType proof
    let goalType ← goal.getType
    if ← isDefEq proofType goalType then
      goal.assign proof
      return true
    else
      logInfo m!"rsa_predict: [reflect] proof type mismatch (cfg != d.toRSAConfig definitionally)"
      return false
  catch e =>
    logInfo m!"rsa_predict: [reflect] failed: {e.toMessageData}"
    return false

/-- Try to prove `cfg.L1agent.score u1 w1 > cfg.L1agent.score u2 w2` via reflection.
    Used for marginal/cross-utterance comparisons at the score level. -/
def tryReflectL1ScoreGt (goal : MVarId) (cfg u₁ w₁ u₂ w₂ : Expr) : TacticM Bool := do
  let some d ← extractConfigData? cfg
    | do -- Tier 1.5: direct RExpr reification
         let l1agent ← mkAppM ``RSA.RSAConfig.L1agent #[cfg]
         let lhs ← mkAppM ``Core.RationalAction.score #[l1agent, u₁, w₁]
         let rhs ← mkAppM ``Core.RationalAction.score #[l1agent, u₂, w₂]
         if ← tryDirectRExprCompare goal lhs rhs then return true
         -- Tier 2: auto-detect fallback
         return ← tryAutoDetectL1ScoreGt goal cfg u₁ w₁ u₂ w₂
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

/-- Try to prove `not (cfg.L1 u w1 > cfg.L1 u w2)` via reflection.
    Uses checkL1ScoreNotGt + native_decide + l1_not_gt_of_check. -/
def tryReflectL1NotGt (goal : MVarId) (cfg u w₁ w₂ : Expr) : TacticM Bool := do
  let some d ← extractConfigData? cfg
    | do -- Tier 1.5: direct RExpr reification
         let lhs ← mkAppM ``RSA.RSAConfig.L1 #[cfg, u, w₁]
         let rhs ← mkAppM ``RSA.RSAConfig.L1 #[cfg, u, w₂]
         if ← tryDirectRExprNotGt goal lhs rhs then return true
         -- Tier 2: auto-detect fallback
         return ← tryAutoDetectL1NotGt goal cfg u w₁ w₂
  logInfo m!"rsa_predict: [reflect/not-L1] found RSAConfigData, trying reflection path..."
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
    logInfo m!"rsa_predict: [reflect/not-L1] failed: {e.toMessageData}"
    return false

/-- Try to prove `cfg.S1 l w u1 > cfg.S1 l w u2` via reflection.
    Uses checkS1PolicyGt + native_decide + s1_gt_of_check. -/
def tryReflectS1Compare (goal : MVarId) (cfg l w u₁ u₂ : Expr) : TacticM Bool := do
  let some d ← extractConfigData? cfg
    | do -- Tier 1.5: direct RExpr reification
         let lhs ← mkAppM ``RSA.RSAConfig.S1 #[cfg, l, w, u₁]
         let rhs ← mkAppM ``RSA.RSAConfig.S1 #[cfg, l, w, u₂]
         if ← tryDirectRExprCompare goal lhs rhs then return true
         -- Tier 2: auto-detect fallback
         return ← tryAutoDetectS1Compare goal cfg l w u₁ u₂
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

/-- Try to prove `not (cfg.S1 l w u1 > cfg.S1 l w u2)` via reflection.
    Uses checkS1PolicyNotGt + native_decide + s1_not_gt_of_check. -/
def tryReflectS1NotGt (goal : MVarId) (cfg l w u₁ u₂ : Expr) : TacticM Bool := do
  let some d ← extractConfigData? cfg
    | do -- Tier 1.5: direct RExpr reification
         let lhs ← mkAppM ``RSA.RSAConfig.S1 #[cfg, l, w, u₁]
         let rhs ← mkAppM ``RSA.RSAConfig.S1 #[cfg, l, w, u₂]
         if ← tryDirectRExprNotGt goal lhs rhs then return true
         -- Tier 2: auto-detect fallback
         return ← tryAutoDetectS1NotGt goal cfg l w u₁ u₂
  logInfo m!"rsa_predict: [reflect/not-S1] found RSAConfigData, trying reflection path..."
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
    logInfo m!"rsa_predict: [reflect/not-S1] failed: {e.toMessageData}"
    return false

end Linglib.Tactics.RSAPredict
