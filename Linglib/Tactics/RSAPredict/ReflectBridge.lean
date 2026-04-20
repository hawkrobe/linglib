import Lean
import Linglib.Tactics.RSAPredict.Backend.ReflectInterval
import Linglib.Tactics.RSAPredict.Helpers
import Linglib.Tactics.RSAPredict.Reify
import Linglib.Tactics.RSAPredict.RSABuilder

set_option autoImplicit false

/-!
# RSAPredict Reflection Bridge

Direct RExpr reification for all RSA comparison goals.

## Design

The proof-free reifier builds RExpr AST nodes whose `denote` is definitionally
equal to the original expression. The kernel verifies this via iota-reduction
of `denote` (structural recursion, O(1) per node).

1. **Reify**: Convert both sides of the comparison to `RExpr` AST + meta-level bounds.
   No congruence proof trees — the kernel handles definitional equality.
2. **Check**: `native_decide` on `checkGtOptMemo`/`checkNotGtOpt` (evalValid + separation).
3. **Assign**: Directly assign `gt_of_checkGtOptMemo lhsRExpr rhsRExpr hcheck` — the kernel
   verifies `denote(lhsRExpr) ≡ lhsExpr` and `denote(rhsRExpr) ≡ rhsExpr`.

This eliminates the congruence proof tree (O(n) nodes → O(1) proof term) and the
equality bridge (`gt_of_eq_gt_eq`), reducing both reification time and proof term size.
-/

namespace Tactics.RSAPredict

open Lean Meta Elab Tactic
open Interval

-- ============================================================================
-- Policy Expression Parsing
-- ============================================================================

/-- Try to unfold an expression to `RationalAction.policy ra s a`. -/
def unfoldToPolicy (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let mut current := e
  for _ in List.range 10 do
    let fn := current.getAppFn
    let args := current.getAppArgs
    if fn.isConstOf ``Core.RationalAction.policy && args.size ≥ 6 then
      return some (args[3]!, args[4]!, args[5]!)  -- ra, s, a
    if let some e' ← unfoldDefinition? current then
      current := e'.headBeta
    else break
  return none

/-- Extract RSA config and arguments from a policy expression.
    Returns (cfg, u, w) where the expression is `cfg.L1 u w`. -/
def parseL1Policy (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  if let some (ra, u, w) := ← unfoldToPolicy e then
    let mut raC := ra
    for _ in List.range 5 do
      let fn := raC.getAppFn
      let args := raC.getAppArgs
      if fn.isConstOf ``RSA.RSAConfig.L1agent && args.size ≥ 5 then
        let cfg := args[4]!
        return some (cfg, u, w)
      if let some ra' ← unfoldDefinition? raC then
        raC := ra'.headBeta
      else break
  return none

/-- Extract RSA config and arguments from a policy expression.
    Returns (cfg, l, w, u) where the expression is `cfg.S1 l w u`. -/
def parseS1Policy (e : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
  if let some (ra, w, u) := ← unfoldToPolicy e then
    let mut raC := ra
    for _ in List.range 5 do
      let fn := raC.getAppFn
      let args := raC.getAppArgs
      if fn.isConstOf ``RSA.RSAConfig.S1agent && args.size ≥ 6 then
        let cfg := args[4]!
        let l := args[5]!
        return some (cfg, l, w, u)
      if let some ra' ← unfoldDefinition? raC then
        raC := ra'.headBeta
      else break
  return none

-- ============================================================================
-- Persistent Reification Cache
-- ============================================================================

/-- Module-scope reification cache shared across all `rsa_predict` invocations
    within a file. The first theorem pays the full reification cost; subsequent
    theorems for the same model get cache hits on shared sub-expressions
    (L0 policies, S1 scores, belief distributions, etc.). -/
initialize persistentReifyCache : IO.Ref (Std.HashMap Expr (Expr × MetaBounds)) ←
  IO.mkRef ∅

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

/-- Detect L1_marginal in an expression, returning (cfg, u, P) without
    evaluating the predicate. -/
private def detectL1Marginal (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let mut current := e
  for _ in List.range 5 do
    if current.getAppFn.isConstOf ``RSA.RSAConfig.L1_marginal then
      let args := current.getAppArgs
      if args.size ≥ 7 then
        return some (args[4]!, args[5]!, args[6]!)
    if let some e' ← unfoldDefinition? current then
      current := e'.headBeta
    else break
  return none

/-- Detect L1_latent in an expression, returning (cfg, u, l). -/
private def detectL1Latent (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let mut current := e
  for _ in List.range 5 do
    if current.getAppFn.isConstOf ``RSA.RSAConfig.L1_latent then
      let args := current.getAppArgs
      if args.size ≥ 7 then
        return some (args[4]!, args[5]!, args[6]!)
    if let some e' ← unfoldDefinition? current then
      current := e'.headBeta
    else break
  return none

/-- Unfold an expression until we reach a `Finset.sum` head. -/
private def unfoldToFinsetSum (e : Expr) : MetaM (Option Expr) := do
  let mut current := e
  for _ in List.range 10 do
    if current.getAppFn.isConstOf ``Finset.sum && current.getAppArgs.size ≥ 5 then
      return some current
    if let some e' ← unfoldDefinition? current then
      current := e'.headBeta
    else break
  return none

/-- Cancel shared L1 denominator in marginal comparisons.
    L1_marginal cfg u P = Σ_{w∈P} L1agent.policy u w
    → reduce to Σ_{w∈P} L1agent.score u w > Σ_{w∈Q} L1agent.score u w -/
private def tryMarginalDenomCancel (goal : MVarId) (lhsExpr rhsExpr : Expr) :
    TacticM (Option (MVarId × Expr × Expr)) := do
  let some (cfgL, uL, pL) ← detectL1Marginal lhsExpr | return none
  let some (cfgR, uR, pR) ← detectL1Marginal rhsExpr | return none
  unless ← isDefEq cfgL cfgR do return none
  unless ← isDefEq uL uR do return none
  -- Unfold L1_marginal to Finset.sum form
  let some lhsSum ← unfoldToFinsetSum lhsExpr | return none
  let some rhsSum ← unfoldToFinsetSum rhsExpr | return none
  let lhsArgs := lhsSum.getAppArgs
  let rhsArgs := rhsSum.getAppArgs
  -- Build score function: fun w => L1agent.score u w
  let W := lhsArgs[0]!
  let l1agent ← mkAppM ``RSA.RSAConfig.L1agent #[cfgL]
  let scoreFn ← withLocalDecl `w BinderInfo.default W fun w => do
    let body ← mkAppM ``Core.RationalAction.score #[l1agent, uL, w]
    mkLambdaFVars #[w] body
  -- Build score sum expressions by replacing summand function (arg[4])
  let scoreSumLhs := mkAppN lhsSum.getAppFn (lhsArgs.set! 4 scoreFn)
  let scoreSumRhs := mkAppN rhsSum.getAppFn (rhsArgs.set! 4 scoreFn)
  let scoreGoalType ← mkAppM ``GT.gt #[scoreSumLhs, scoreSumRhs]
  let scoreGoal ← mkFreshExprMVar scoreGoalType
  -- Proof: L1_marginal_gt_of_score_sum_gt cfg u P Q hScore
  let proof ← mkAppM ``RSA.RSAConfig.L1_marginal_gt_of_score_sum_gt
    #[cfgL, uL, pL, pR, scoreGoal]
  goal.assign proof
  return some (scoreGoal.mvarId!, scoreSumLhs, scoreSumRhs)

/-- Cancel shared denominator in L1_latent comparisons.
    L1_latent cfg u l = L1_latent_agent.policy () l
    → reduce to L1_latent_agent.score () l₁ > L1_latent_agent.score () l₂ -/
private def tryLatentDenomCancel (goal : MVarId) (lhsExpr rhsExpr : Expr) :
    TacticM (Option (MVarId × Expr × Expr)) := do
  let some (cfgL, uL, l₁) ← detectL1Latent lhsExpr | return none
  let some (cfgR, uR, l₂) ← detectL1Latent rhsExpr | return none
  unless ← isDefEq cfgL cfgR do return none
  unless ← isDefEq uL uR do return none
  -- Build L1_latent_agent score expressions
  let latentAgent ← mkAppM ``RSA.RSAConfig.L1_latent_agent #[cfgL, uL]
  let unitVal := mkConst ``Unit.unit
  let scoreLhs ← mkAppM ``Core.RationalAction.score #[latentAgent, unitVal, l₁]
  let scoreRhs ← mkAppM ``Core.RationalAction.score #[latentAgent, unitVal, l₂]
  let scoreGoalType ← mkAppM ``GT.gt #[scoreLhs, scoreRhs]
  let scoreGoal ← mkFreshExprMVar scoreGoalType
  -- Proof: L1_latent_gt_of_score_gt cfg u l₁ l₂ hScore
  let proof ← mkAppM ``RSA.RSAConfig.L1_latent_gt_of_score_gt
    #[cfgL, uL, l₁, l₂, scoreGoal]
  goal.assign proof
  return some (scoreGoal.mvarId!, scoreLhs, scoreRhs)

/-- Try to cancel shared denominators in RSA comparison goals.

    Supported patterns:
    1. **Direct policy**: `policy ra s a₁ > policy ra s a₂` → `score s a₁ > score s a₂`
    2. **L1_marginal**: `L1_marginal cfg u P > L1_marginal cfg u Q` → score sums
    3. **L1_latent**: `L1_latent cfg u l₁ > L1_latent cfg u l₂` → latent agent scores

    Returns `some (scoreGoal, scoreLhs, scoreRhs)` on success, where
    `scoreGoal` is a new MVarId for the score comparison. -/
private def tryDenominatorCancel (goal : MVarId) (lhsExpr rhsExpr : Expr) :
    TacticM (Option (MVarId × Expr × Expr)) := do
  -- Pattern 1: Direct policy comparison (L1, S1, L0, S2)
  if let some (raL, sL, aL) ← unfoldToPolicy lhsExpr then
    if let some (raR, sR, aR) ← unfoldToPolicy rhsExpr then
      if (← isDefEq raL raR) then
        if (← isDefEq sL sR) then
          -- Pattern 1a: same stimulus → cancel shared denominator
          let scoreLhs ← mkAppM ``Core.RationalAction.score #[raL, sL, aL]
          let scoreRhs ← mkAppM ``Core.RationalAction.score #[raR, sR, aR]
          let scoreGoalType ← mkAppM ``GT.gt #[scoreLhs, scoreRhs]
          let scoreGoal ← mkFreshExprMVar scoreGoalType
          let proof ← mkAppM ``Core.RationalAction.policy_gt_of_score_gt
            #[raL, sL, aL, aR, scoreGoal]
          goal.assign proof
          return some (scoreGoal.mvarId!, scoreLhs, scoreRhs)
        else if (← isDefEq aL aR) then
          -- Pattern 1b: same action, different stimuli → cross-product
          -- policy(s₁,a) > policy(s₂,a) ← score(s₁,a)*total(s₂) > score(s₂,a)*total(s₁)
          -- Positivity of both totalScores is derived from the cross-product itself.
          logInfo m!"rsa_predict: [denom] cross-stimulus detected, reducing to cross-product"
          let scoreLhs ← mkAppM ``Core.RationalAction.score #[raL, sL, aL]
          let scoreRhs ← mkAppM ``Core.RationalAction.score #[raR, sR, aR]
          let totalLhs ← mkAppM ``Core.RationalAction.totalScore #[raL, sL]
          let totalRhs ← mkAppM ``Core.RationalAction.totalScore #[raR, sR]
          let crossLhs ← mkAppM ``HMul.hMul #[scoreLhs, totalRhs]
          let crossRhs ← mkAppM ``HMul.hMul #[scoreRhs, totalLhs]
          let crossGoalType ← mkAppM ``GT.gt #[crossLhs, crossRhs]
          let crossGoal ← mkFreshExprMVar crossGoalType
          let proof ← mkAppM ``Core.RationalAction.policy_gt_cross_of_cross_gt
            #[raL, sL, sR, aL, crossGoal]
          goal.assign proof
          return some (crossGoal.mvarId!, crossLhs, crossRhs)
  -- Pattern 2: L1_marginal comparison (sum of policies with shared denominator)
  if let some result ← tryMarginalDenomCancel goal lhsExpr rhsExpr then
    return some result
  -- Pattern 3: L1_latent comparison (inline division with shared denominator)
  if let some result ← tryLatentDenomCancel goal lhsExpr rhsExpr then
    return some result
  return none

/-- Direct RExpr reification for `lhs > rhs` goals.
    Runs `native_decide` on tree-based `checkGtOptMemo` (sorry-free soundness).

    When both sides are `policy ra s a₁/a₂` with the same `ra` and `s`,
    applies denominator cancellation first via `policy_gt_of_score_gt`,
    reducing the goal to a score comparison that skips the shared
    normalization constant. -/
def tryDirectRExprCompare (goal : MVarId) (lhsExpr rhsExpr : Expr) : TacticM Bool := do
  let t0 ← IO.monoMsNow

  -- Denominator cancellation: if both sides share the same policy denominator,
  -- reduce to a score comparison (roughly halves the expression tree).
  -- Safe to assign goal here since we've committed to the reflection path.
  let cancelResult ← try
    tryDenominatorCancel goal lhsExpr rhsExpr
  catch _ => pure none
  let mut activeGoal := goal
  let mut activeLhs := lhsExpr
  let mut activeRhs := rhsExpr
  let mut denomNote := ""
  if let some (scoreGoal, scoreLhs, scoreRhs) := cancelResult then
    logInfo m!"rsa_predict: [direct] denominator cancelled (score-level comparison)"
    activeGoal := scoreGoal
    activeLhs := scoreLhs
    activeRhs := scoreRhs
    denomNote := " [denom-cancelled]"

  let cacheBefore ← persistentReifyCache.get

  -- Try the RSA builder first (bottom-up construction, bypasses unfoldDefinition? chain)
  let builderResult ← try
    tryRSABuild persistentReifyCache activeLhs activeRhs
  catch ex =>
    logInfo m!"rsa_predict: [builder] failed: {ex.toMessageData}"
    pure none

  let (lhsRExpr, lhsBounds, rhsRExpr, rhsBounds) ← match builderResult with
    | some (lr, lb, rr, rb) => pure (lr, lb, rr, rb)
    | none => do
      -- NOTE: tryPreseedL1 removed — builder-seeded RExprs have structural
      -- mismatches with actual L1/L1_latent definitions (sum fold direction,
      -- intermediate iteZero/rpow structure), causing kernel type mismatch
      -- when the generic reifier picks them up via normal cache lookup.
      -- The generic reifier handles L1 expressions correctly via unfoldDefinition?.
      let (lr, lb) ← reifyToRExpr persistentReifyCache activeLhs maxDepth
      let (rr, rb) ← reifyToRExpr persistentReifyCache activeRhs maxDepth
      pure (lr, lb, rr, rb)

  let cacheAfter ← persistentReifyCache.get
  let t1 ← IO.monoMsNow
  let builderNote := if builderResult.isSome then " [builder]" else ""
  logInfo m!"rsa_predict: [direct] reified ({t1 - t0}ms, cache {cacheBefore.size}→{cacheAfter.size}){denomNote}{builderNote}"

  -- Exact ℚ evaluation path: when both sides are pure arithmetic (no exp/log),
  -- evaluate to exact ℚ and compare. Skip for cross-utterance (too large).
  let exactOk ← try
    let exactCheckExpr ← mkAppM ``RExpr.checkExactGt #[lhsRExpr, rhsRExpr]
    let exactCheckType ← mkEq exactCheckExpr (mkConst ``Bool.true)
    let hexact ← nativeDecideProof exactCheckType
    let proof := mkApp3 (mkConst ``RExpr.gt_of_checkExactGt) lhsRExpr rhsRExpr hexact
    activeGoal.assign proof
    let t2 ← IO.monoMsNow
    logInfo m!"rsa_predict: [direct] assigned via exact ℚ ({t2 - t0}ms)"
    pure true
  catch _ => pure false
  if exactOk then return true

  unless lhsBounds.lo > rhsBounds.hi do
    logInfo m!"rsa_predict: [direct] bounds don't separate at meta-level, trying tree check"

  -- Tree-based proof: native_decide on checkGtOptMemo (sorry-free soundness)
  try
    let checkExpr ← mkAppM ``RExpr.checkGtOptMemo #[lhsRExpr, rhsRExpr]
    let checkType ← mkEq checkExpr (mkConst ``Bool.true)
    let hcheck ← nativeDecideProof checkType
    let proof := mkApp3 (mkConst ``RExpr.gt_of_checkGtOptMemo) lhsRExpr rhsRExpr hcheck
    activeGoal.assign proof
    let t2 ← IO.monoMsNow
    logInfo m!"rsa_predict: [direct] assigned ({t2 - t0}ms)"
    return true
  catch e =>
    logInfo m!"rsa_predict: [direct] tree check failed: {e.toMessageData}"
    return false

/-- Direct RExpr reification for `not (lhs > rhs)` goals.
    Assigns proofs directly — the kernel verifies denote ≡ original. -/
def tryDirectRExprNotGt (goal : MVarId) (lhsExpr rhsExpr : Expr) : TacticM Bool := do
  let t0 ← IO.monoMsNow
  let (lhsRExpr, _lhsBounds) ← reifyToRExpr persistentReifyCache lhsExpr maxDepth
  let (rhsRExpr, _rhsBounds) ← reifyToRExpr persistentReifyCache rhsExpr maxDepth

  let t1 ← IO.monoMsNow
  logInfo m!"rsa_predict: [direct/not-gt] reified ({t1 - t0}ms)"

  try
    -- Fast path: structurally equal RExpr → ¬(x > x) by irrefl
    let eqType ← mkEq lhsRExpr rhsRExpr
    if let some heq ← try? (nativeDecideProof eqType) then
      let denoteFn := mkConst ``RExpr.denote
      let denoteCongr ← mkAppM ``congrArg #[denoteFn, heq]
      let proof := mkApp3 (mkConst ``RExpr.not_gt_of_denote_eq)
        lhsRExpr rhsRExpr denoteCongr
      goal.assign proof
      let t2 ← IO.monoMsNow
      logInfo m!"rsa_predict: [direct/not-gt] assigned via structural equality ({t2 - t0}ms)"
      return true

    -- Exact ℚ evaluation path
    let exactCheckExpr ← mkAppM ``RExpr.checkExactNotGt #[lhsRExpr, rhsRExpr]
    let exactCheckType ← mkEq exactCheckExpr (mkConst ``Bool.true)
    if let some hexact ← try? (nativeDecideProof exactCheckType) then
      let proof := mkApp3 (mkConst ``RExpr.not_gt_of_checkExactNotGt)
        lhsRExpr rhsRExpr hexact
      goal.assign proof
      let t2 ← IO.monoMsNow
      logInfo m!"rsa_predict: [direct/not-gt] assigned via exact ℚ ({t2 - t0}ms)"
      return true

    -- Semantic equality path
    let semCheckExpr ← mkAppM ``RExpr.checkSemanticEq #[lhsRExpr, rhsRExpr]
    let semCheckType ← mkEq semCheckExpr (mkConst ``Bool.true)
    if let some hsem ← try? (nativeDecideProof semCheckType) then
      let proof := mkApp3 (mkConst ``RExpr.not_gt_of_checkSemanticEq)
        lhsRExpr rhsRExpr hsem
      goal.assign proof
      let t2 ← IO.monoMsNow
      logInfo m!"rsa_predict: [direct/not-gt] assigned via semantic equality ({t2 - t0}ms)"
      return true
    -- Interval separation: tree-based check (fast — O(n) via evalBothOpt)
    let checkExpr ← mkAppM ``RExpr.checkNotGtOptMemo #[lhsRExpr, rhsRExpr]
    let checkType ← mkEq checkExpr (mkConst ``Bool.true)
    if let some hcheck ← try? (nativeDecideProof checkType) then
      let proof := mkApp3 (mkConst ``RExpr.not_gt_of_checkNotGtOptMemo)
        lhsRExpr rhsRExpr hcheck
      goal.assign proof
      let t2 ← IO.monoMsNow
      logInfo m!"rsa_predict: [direct/not-gt] assigned via interval ({t2 - t0}ms)"
      return true

    -- Normalize both sides (dead-branch elimination) then check structural equality.
    -- After normalization, symmetric RSA expressions collapse to identical trees.
    -- This is O(n²) so only tried after faster paths fail.
    let normLhs ← mkAppM ``RExpr.normalize #[lhsRExpr]
    let normRhs ← mkAppM ``RExpr.normalize #[rhsRExpr]
    let normEqType ← mkEq normLhs normRhs
    let heq ← nativeDecideProof normEqType
    let proof := mkApp3 (mkConst ``RExpr.not_gt_of_normalize_eq)
      lhsRExpr rhsRExpr heq
    goal.assign proof
    let t2 ← IO.monoMsNow
    logInfo m!"rsa_predict: [direct/not-gt] assigned via normalize equality ({t2 - t0}ms)"
    return true
  catch e =>
    logInfo m!"rsa_predict: [direct/not-gt] failed: {e.toMessageData}"
    return false

-- ============================================================================
-- Direct RExpr Equality Pipeline
-- ============================================================================

/-- Direct RExpr reification for `lhs = rhs` goals.
    Tries structural equality first (same RExpr), then exact ℚ evaluation. -/
def tryDirectRExprEq (goal : MVarId) (lhsExpr rhsExpr : Expr) : TacticM Bool := do
  let t0 ← IO.monoMsNow
  let (lhsRExpr, _) ← reifyToRExpr persistentReifyCache lhsExpr maxDepth
  let (rhsRExpr, _) ← reifyToRExpr persistentReifyCache rhsExpr maxDepth

  let t1 ← IO.monoMsNow
  logInfo m!"rsa_predict: [direct/eq] reified ({t1 - t0}ms)"

  try
    -- Fast path: structurally equal RExpr → congrArg denote
    let eqType ← mkEq lhsRExpr rhsRExpr
    if let some heq ← try? (nativeDecideProof eqType) then
      let denoteFn := mkConst ``RExpr.denote
      let proof ← mkAppM ``congrArg #[denoteFn, heq]
      goal.assign proof
      let t2 ← IO.monoMsNow
      logInfo m!"rsa_predict: [direct/eq] assigned via structural equality ({t2 - t0}ms)"
      return true

    -- Exact ℚ evaluation path
    let checkExpr ← mkAppM ``RExpr.checkExactEq #[lhsRExpr, rhsRExpr]
    let checkType ← mkEq checkExpr (mkConst ``Bool.true)
    if let some hcheck ← try? (nativeDecideProof checkType) then
      let proof := mkApp3 (mkConst ``RExpr.eq_of_checkExactEq) lhsRExpr rhsRExpr hcheck
      goal.assign proof
      let t2 ← IO.monoMsNow
      logInfo m!"rsa_predict: [direct/eq] assigned via exact ℚ ({t2 - t0}ms)"
      return true

    -- Semantic equality path: handles exp/log cases by structural match
    -- with recursive evalExact on arithmetic subtrees
    let semCheckExpr ← mkAppM ``RExpr.checkSemanticEq #[lhsRExpr, rhsRExpr]
    let semCheckType ← mkEq semCheckExpr (mkConst ``Bool.true)
    if let some hsem ← try? (nativeDecideProof semCheckType) then
      let proof := mkApp3 (mkConst ``RExpr.eq_of_checkSemanticEq) lhsRExpr rhsRExpr hsem
      goal.assign proof
      let t2 ← IO.monoMsNow
      logInfo m!"rsa_predict: [direct/eq] assigned via semantic equality ({t2 - t0}ms)"
      return true

    logInfo m!"rsa_predict: [direct/eq] no equality strategy succeeded"
    return false
  catch e =>
    logInfo m!"rsa_predict: [direct/eq] failed: {e.toMessageData}"
    return false

end Tactics.RSAPredict
