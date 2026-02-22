import Lean
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Core.Interval.ReflectInterval
import Linglib.Tactics.RSAPredict.Helpers
import Linglib.Tactics.RSAPredict.Reify
import Linglib.Tactics.RSAPredict.GoalParsing
import Linglib.Tactics.RSAPredict.ProofBuilder
import Linglib.Tactics.RSAPredict.ReflectBridge

set_option autoImplicit false

/-!
# RSAPredict — Level-Aware Verified RSA Predictions

The `rsa_predict` tactic proves ℝ comparison goals on RSA models by:

1. Pattern-matching the goal to identify the comparison form (L1, L1_latent, sums)
2. Reifying each S1 score individually via RExpr → ℚ interval arithmetic
3. Computing L1/L1_latent/marginal bounds entirely at meta level
4. Applying a bridge axiom from `RSA.Verified` with the computed ℚ separation

## Supported Goal Forms

- `cfg.L1 u w₁ > cfg.L1 u w₂` — L1 world comparison
- `cfg.L1_latent u l₁ > cfg.L1_latent u l₂` — latent variable inference
- `Σ cfg.L1 u wᵢ > Σ cfg.L1 u wⱼ` — marginal comparison (same utterance)
- `Σ cfg.L1 u₁ wᵢ > Σ cfg.L1 u₂ wⱼ` — cross-utterance sum comparison

## Usage

```lean
theorem prediction : cfg.L1 u w₁ > cfg.L1 u w₂ := by rsa_predict
```
-/

namespace Linglib.Tactics

open Lean Meta Elab Tactic
open Linglib.Interval
open Linglib.Tactics.RSAPredict

-- ============================================================================
-- L0 Cache Lifecycle
-- ============================================================================

/-- Enable lazy L0 caching for action-based models. No-op for belief-based. -/
private def enableL0Cache (cfg : Expr) (allWElems : Array Expr)
    (isBeliefBased : Bool) : TacticM Unit := do
  if isBeliefBased then return
  let build (l u w : Expr) : TacticM CProof := do
    let wIdx ← findElemIdx allWElems w
    buildL0PolicyCProof cfg l u allWElems wIdx
  l0CacheCtxRef.set (some { build })
  l0CacheMapRef.set {}

private def disableL0Cache : TacticM Unit := do
  l0CacheCtxRef.set none
  l0CacheMapRef.set {}

-- ============================================================================
-- Proof Construction Helpers (tactic-level)
-- ============================================================================

/-- Prove `hi₂ < lo₁` via native_decide and return the proof term. -/
private def proveQSeparation (hi₂ lo₁ : ℚ) : TacticM Expr := do
  let hi2Expr ← mkRatExpr hi₂
  let lo1Expr ← mkRatExpr lo₁
  let sepType ← mkAppM ``LT.lt #[hi2Expr, lo1Expr]
  let sepMVar ← mkFreshExprMVar sepType
  let savedGoals ← getGoals
  setGoals [sepMVar.mvarId!]
  try
    evalTactic (← `(tactic| native_decide))
  catch e =>
    setGoals savedGoals
    throwError "rsa_predict: native_decide failed on ℚ comparison: {e.toMessageData}"
  setGoals savedGoals
  return sepMVar

private def proveQLeq (hi₁ lo₂ : ℚ) : TacticM Expr := do
  let hi1Expr ← mkRatExpr hi₁
  let lo2Expr ← mkRatExpr lo₂
  let leType ← mkAppM ``LE.le #[hi1Expr, lo2Expr]
  let leMVar ← mkFreshExprMVar leType
  let savedGoals ← getGoals
  setGoals [leMVar.mvarId!]
  try
    evalTactic (← `(tactic| native_decide))
  catch e =>
    setGoals savedGoals
    throwError "rsa_predict: native_decide failed on ℚ comparison: {e.toMessageData}"
  setGoals savedGoals
  return leMVar

/-- Assign proof to goal, with cast/simp fallbacks. -/
private def assignWithCastFallback (goal : MVarId) (proof : Expr) : TacticM Unit := do
  let proofType ← inferType proof
  let goalType ← goal.getType
  if ← isDefEq proofType goalType then
    goal.assign proof
  else
    let goalWithH ← goal.assert `h_rsa proofType proof
    let (_, finalGoal) ← goalWithH.intro1
    setGoals [finalGoal]
    -- Try various simplification strategies to bridge the gap
    -- between List.map/sum form and direct addition form
    try
      evalTactic (← `(tactic| simp only [List.map, List.sum_cons, List.sum_nil, add_zero] at *))
      evalTactic (← `(tactic| linarith))
    catch _ =>
    try evalTactic (← `(tactic| assumption_mod_cast))
    catch _ =>
      try evalTactic (← `(tactic| push_cast at *; assumption))
      catch _ => evalTactic (← `(tactic| norm_cast at *; assumption))

-- ============================================================================
-- Main Tactic
-- ============================================================================

/-- `rsa_predict` proves RSA prediction goals by level-aware interval arithmetic.

    Supported goal forms:
    - `cfg.L1 u w₁ > cfg.L1 u w₂` — L1 world comparison
    - `¬(cfg.L1 u w₁ > cfg.L1 u w₂)` — L1 non-strict (implicature canceled)
    - `cfg.L1_latent u l₁ > cfg.L1_latent u l₂` — latent inference
    - `cfg.S1 l w u₁ > cfg.S1 l w u₂` — S1 speaker comparison
    - `¬(cfg.S1 l w u₁ > cfg.S1 l w u₂)` — S1 non-strict
    - `Σ s, cfg.L1 u (s, a₁) > Σ s, cfg.L1 u (s, a₂)` — marginal comparison
    - `cfg.L1 u₁ w₁ + ... > cfg.L1 u₂ w₃ + ...` — cross-utterance sum
    - `cfg₁.L1 u₁ w₁ + ... > cfg₂.L1 u₂ w₃ + ...` — cross-config sum -/
elab "rsa_predict" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType

  -- Try native_decide first (handles ℚ, Bool, finite types)
  try
    evalTactic (← `(tactic| native_decide))
    return
  catch _ => pure ()

  -- ¬(_ > _): detect as P → False (Not is @[reducible], so whnf reduces @Not P)
  let goalTypeWhnf ← whnf goalType
  if let .forallE _ inner (.const ``False []) _ := goalTypeWhnf then do
    let innerFn := inner.getAppFn
    let innerArgs := inner.getAppArgs
    unless innerFn.isConstOf ``GT.gt && innerArgs.size ≥ 4 do
      throwError "rsa_predict: expected goal of the form `¬(_ > _)`, got: {← ppExpr goalType}"
    let lhs := innerArgs[2]!
    let rhs := innerArgs[3]!
    let goalForm ← parseGoalForm lhs rhs
    match goalForm with
    | .l1Compare cfg u w₁ w₂ => do
      logInfo m!"rsa_predict: parsed goal as ¬(L1 comparison)"
      let (_, _, _, allUElems, allWElems, allLElems, s1Bounds, wpValues, lpValues) ←
        reifyS1Scores cfg
      let uIdx ← findElemIdx allUElems u
      let w1Idx ← findElemIdx allWElems w₁
      let w2Idx ← findElemIdx allWElems w₂
      let l1_w1 := metaL1Score allLElems.size allWElems.size allUElems.size
        s1Bounds wpValues lpValues uIdx w1Idx
      let l1_w2 := metaL1Score allLElems.size allWElems.size allUElems.size
        s1Bounds wpValues lpValues uIdx w2Idx
      logInfo m!"rsa_predict: L1(u, w₁) ∈ [{l1_w1.lo}, {l1_w1.hi}]"
      logInfo m!"rsa_predict: L1(u, w₂) ∈ [{l1_w2.lo}, {l1_w2.hi}]"
      unless l1_w1.hi ≤ l1_w2.lo do
        throwError "rsa_predict: cannot prove ¬(L1 w₁ > L1 w₂): w₁.hi = {l1_w1.hi} > w₂.lo = {l1_w2.lo}"
      -- Extract α for compositional proof
      let αExpr ← mkAppM ``RSA.RSAConfig.α #[cfg]
      let some αNat ← resolveNat? αExpr
        | throwError "rsa_predict: cannot extract α as ℕ"
      let isBeliefBased ← detectBeliefBased cfg
      logInfo m!"rsa_predict: building compositional proof (α={αNat}, {if isBeliefBased then "belief" else "action"})..."
      enableL0Cache cfg allWElems isBeliefBased
      let score1 ← buildL1ScoreCProof cfg u w₁ allUElems allWElems allLElems wpValues lpValues αNat isBeliefBased
      let score2 ← buildL1ScoreCProof cfg u w₂ allUElems allWElems allLElems wpValues lpValues αNat isBeliefBased
      disableL0Cache
      -- Prove score₁ ≤ score₂ from interval bounds
      if score1.hi ≤ score2.lo then
        let hi1E ← mkAppM ``QInterval.hi #[score1.iExpr]
        let lo2E ← mkAppM ``QInterval.lo #[score2.iExpr]
        let leProof ← proveQPropND (← mkAppM ``LE.le #[hi1E, lo2E])
        let hle ← mkAppM ``QInterval.le_of_separated #[score1.proof, score2.proof, leProof]
        -- policy_not_gt_of_score_le lifts to ¬(L1 policy comparison)
        let l1Agent ← mkAppM ``RSA.RSAConfig.L1agent #[cfg]
        let proof ← mkAppM ``Core.RationalAction.policy_not_gt_of_score_le
          #[l1Agent, u, w₁, w₂, hle]
        assignWithCastFallback goal proof
        logInfo m!"rsa_predict: ✓ proved via compositional proof (¬L1 comparison)"
      else
        -- Interval width from exp/log prevents direct comparison.
        -- Fallback: prove score₁ ≤ score₂ via le_refl when scores reduce to equal.
        let l1Agent ← mkAppM ``RSA.RSAConfig.L1agent #[cfg]
        let scoreExpr1 ← mkAppM ``Core.RationalAction.score #[l1Agent, u, w₁]
        let scoreExpr2 ← mkAppM ``Core.RationalAction.score #[l1Agent, u, w₂]
        -- Try reducible isDefEq first (fast), then full isDefEq
        let areEq ← withNewMCtxDepth do
          try isDefEq scoreExpr1 scoreExpr2 catch _ => return false
        if areEq then
          let hle ← mkAppM ``le_refl #[scoreExpr1]
          let proof ← mkAppM ``Core.RationalAction.policy_not_gt_of_score_le
            #[l1Agent, u, w₁, w₂, hle]
          assignWithCastFallback goal proof
          logInfo m!"rsa_predict: ✓ proved via score equality (¬L1 comparison)"
        else
          -- Try whnf reduction then isDefEq
          let whnf1 ← whnf scoreExpr1
          let whnf2 ← whnf scoreExpr2
          let areEqW ← withNewMCtxDepth do
            try isDefEq whnf1 whnf2 catch _ => return false
          if areEqW then
            let hle ← mkAppM ``le_refl #[scoreExpr1]
            let proof ← mkAppM ``Core.RationalAction.policy_not_gt_of_score_le
              #[l1Agent, u, w₁, w₂, hle]
            assignWithCastFallback goal proof
            logInfo m!"rsa_predict: ✓ proved via whnf score equality (¬L1 comparison)"
          else
            throwError "rsa_predict: cannot prove ¬(L1 w₁ > L1 w₂): compositional bounds overlap [{score1.lo}, {score1.hi}] vs [{score2.lo}, {score2.hi}], and scores are not defEq"
      return
    | .s1Compare cfg l w u₁ u₂ => do
      logInfo m!"rsa_predict: parsed goal as ¬(S1 comparison)"
      let (_, _, _, allUElems, allWElems, allLElems, s1Bounds, _, _) ←
        reifyS1Scores cfg
      let lIdx ← findElemIdx allLElems l
      let wIdx ← findElemIdx allWElems w
      let u1Idx ← findElemIdx allUElems u₁
      let u2Idx ← findElemIdx allUElems u₂
      let nU := allUElems.size
      let nW := allWElems.size
      let idx1 := lIdx * nW * nU + wIdx * nU + u1Idx
      let idx2 := lIdx * nW * nU + wIdx * nU + u2Idx
      let s1_u1 := s1Bounds[idx1]!
      let s1_u2 := s1Bounds[idx2]!
      logInfo m!"rsa_predict: S1_score(u₁) ∈ [{s1_u1.lo}, {s1_u1.hi}]"
      logInfo m!"rsa_predict: S1_score(u₂) ∈ [{s1_u2.lo}, {s1_u2.hi}]"
      unless s1_u1.hi ≤ s1_u2.lo do
        throwError "rsa_predict: cannot prove ¬(S1 u₁ > S1 u₂): u₁.hi = {s1_u1.hi} > u₂.lo = {s1_u2.lo}"
      -- Extract α for compositional proof
      let αExpr ← mkAppM ``RSA.RSAConfig.α #[cfg]
      let some αNat ← resolveNat? αExpr
        | throwError "rsa_predict: cannot extract α as ℕ"
      let isBeliefBased ← detectBeliefBased cfg
      logInfo m!"rsa_predict: building compositional proof (α={αNat}, {if isBeliefBased then "belief" else "action"})..."
      enableL0Cache cfg allWElems isBeliefBased
      let score1 ← buildS1ScoreCProof cfg l w u₁ allWElems αNat isBeliefBased
      let score2 ← buildS1ScoreCProof cfg l w u₂ allWElems αNat isBeliefBased
      disableL0Cache
      let s1Agent ← mkAppM ``RSA.RSAConfig.S1agent #[cfg, l]
      -- Prove score₁ ≤ score₂ from interval bounds
      if score1.hi ≤ score2.lo then
        let hi1E ← mkAppM ``QInterval.hi #[score1.iExpr]
        let lo2E ← mkAppM ``QInterval.lo #[score2.iExpr]
        let leProof ← proveQPropND (← mkAppM ``LE.le #[hi1E, lo2E])
        let hle ← mkAppM ``QInterval.le_of_separated #[score1.proof, score2.proof, leProof]
        let proof ← mkAppM ``Core.RationalAction.policy_not_gt_of_score_le
          #[s1Agent, w, u₁, u₂, hle]
        assignWithCastFallback goal proof
        logInfo m!"rsa_predict: ✓ proved via compositional proof (¬S1 comparison)"
      else
        -- Interval width from exp/log prevents direct comparison.
        -- Fallback: prove score₁ ≤ score₂ via le_refl when scores reduce to equal.
        let scoreExpr1 ← mkAppM ``Core.RationalAction.score #[s1Agent, w, u₁]
        let scoreExpr2 ← mkAppM ``Core.RationalAction.score #[s1Agent, w, u₂]
        let areEq ← withNewMCtxDepth do
          try isDefEq scoreExpr1 scoreExpr2 catch _ => return false
        if areEq then
          let hle ← mkAppM ``le_refl #[scoreExpr1]
          let proof ← mkAppM ``Core.RationalAction.policy_not_gt_of_score_le
            #[s1Agent, w, u₁, u₂, hle]
          assignWithCastFallback goal proof
          logInfo m!"rsa_predict: ✓ proved via score equality (¬S1 comparison)"
        else
          let whnf1 ← whnf scoreExpr1
          let whnf2 ← whnf scoreExpr2
          let areEqW ← withNewMCtxDepth do
            try isDefEq whnf1 whnf2 catch _ => return false
          if areEqW then
            let hle ← mkAppM ``le_refl #[scoreExpr1]
            let proof ← mkAppM ``Core.RationalAction.policy_not_gt_of_score_le
              #[s1Agent, w, u₁, u₂, hle]
            assignWithCastFallback goal proof
            logInfo m!"rsa_predict: ✓ proved via whnf score equality (¬S1 comparison)"
          else
            throwError "rsa_predict: cannot prove ¬(S1 u₁ > S1 u₂): compositional bounds overlap [{score1.lo}, {score1.hi}] vs [{score2.lo}, {score2.hi}], and scores are not defEq"
      return
    | _ => throwError "rsa_predict: ¬(_ > _) only supported for L1 and S1 comparisons, got: {← ppExpr goalType}"

  let fn := goalType.getAppFn
  let args := goalType.getAppArgs

  -- GT.gt: lhs > rhs
  unless fn.isConstOf ``GT.gt && args.size ≥ 4 do
    throwError "rsa_predict: expected goal of the form `_ > _` or `¬(_ > _)`, got: {← ppExpr goalType}"

  let lhs := args[2]!
  let rhs := args[3]!

  let goalForm ← parseGoalForm lhs rhs

  match goalForm with
  | .l1Compare cfg u w₁ w₂ => do
    logInfo m!"rsa_predict: parsed goal as L1 comparison"
    let t0 ← IO.monoMsNow
    -- Try reflection path first (fast, <5s vs ~39s for CProof)
    if ← tryReflectL1Compare goal cfg u w₁ w₂ then
      let t1 ← IO.monoMsNow
      logInfo m!"rsa_predict: ✓ proved via reflection ({t1 - t0}ms)"
      return
    -- Fall back to CProof pipeline
    let (_, _, _, allUElems, allWElems, allLElems, s1Bounds, wpValues, lpValues) ←
      reifyS1Scores cfg
    let t1 ← IO.monoMsNow
    logInfo m!"rsa_predict: [timing] reify: {t1 - t0}ms"

    let uIdx ← findElemIdx allUElems u
    let w1Idx ← findElemIdx allWElems w₁
    let w2Idx ← findElemIdx allWElems w₂

    let l1_w1 := metaL1Score allLElems.size allWElems.size allUElems.size
      s1Bounds wpValues lpValues uIdx w1Idx
    let l1_w2 := metaL1Score allLElems.size allWElems.size allUElems.size
      s1Bounds wpValues lpValues uIdx w2Idx

    logInfo m!"rsa_predict: L1(u, w₁) ∈ [{l1_w1.lo}, {l1_w1.hi}]"
    logInfo m!"rsa_predict: L1(u, w₂) ∈ [{l1_w2.lo}, {l1_w2.hi}]"

    unless l1_w2.hi < l1_w1.lo do
      throwError "rsa_predict: L1 scores not separated: w₂.hi = {l1_w2.hi} ≥ w₁.lo = {l1_w1.lo}"

    -- Extract α as ℕ for belief-based scoring
    let αExpr ← mkAppM ``RSA.RSAConfig.α #[cfg]
    let some αNat ← resolveNat? αExpr
      | throwError "rsa_predict: cannot extract α as ℕ"
    -- Build compositional proof terms for L1 scores
    let isBeliefBased ← detectBeliefBased cfg
    logInfo m!"rsa_predict: building compositional proof (α={αNat}, {if isBeliefBased then "belief" else "action"})..."
    let t2 ← IO.monoMsNow
    enableL0Cache cfg allWElems isBeliefBased
    let score1 ← buildL1ScoreCProof cfg u w₁ allUElems allWElems allLElems wpValues lpValues αNat isBeliefBased
    let t3 ← IO.monoMsNow
    logInfo m!"rsa_predict: [timing] L1 score w₁: {t3 - t2}ms"
    let score2 ← buildL1ScoreCProof cfg u w₂ allUElems allWElems allLElems wpValues lpValues αNat isBeliefBased
    let t4 ← IO.monoMsNow
    logInfo m!"rsa_predict: [timing] L1 score w₂: {t4 - t3}ms"
    disableL0Cache
    logInfo m!"rsa_predict: compositional bounds: w₁ ∈ [{score1.lo}, {score1.hi}], w₂ ∈ [{score2.lo}, {score2.hi}]"
    -- Prove separation using actual interval bounds
    let hi2E ← mkAppM ``QInterval.hi #[score2.iExpr]
    let lo1E ← mkAppM ``QInterval.lo #[score1.iExpr]
    let sepProof ← proveQPropND (← mkAppM ``LT.lt #[hi2E, lo1E])
    -- Compose: gt_of_separated gives score₁ > score₂
    let hgt ← mkAppM ``QInterval.gt_of_separated #[score1.proof, score2.proof, sepProof]
    -- policy_gt_of_score_gt lifts to L1 policy comparison
    let l1Agent ← mkAppM ``RSA.RSAConfig.L1agent #[cfg]
    let proof ← mkAppM ``Core.RationalAction.policy_gt_of_score_gt #[l1Agent, u, w₁, w₂, hgt]
    let t5 ← IO.monoMsNow
    logInfo m!"rsa_predict: [timing] separation+compose: {t5 - t4}ms"
    assignWithCastFallback goal proof
    let t6 ← IO.monoMsNow
    logInfo m!"rsa_predict: [timing] assign: {t6 - t5}ms, total: {t6 - t0}ms"
    logInfo m!"rsa_predict: ✓ proved via compositional proof (L1 comparison)"

  | .l1Marginal cfg u ws₁ ws₂ => do
    logInfo m!"rsa_predict: parsed goal as marginal L1 comparison ({ws₁.size} vs {ws₂.size} worlds)"
    let (_, _, _, allUElems, allWElems, allLElems, s1Bounds, wpValues, lpValues) ←
      reifyS1Scores cfg

    let uIdx ← findElemIdx allUElems u

    -- Sum L1 scores over each world set
    let mut marg1 : MetaBounds := ⟨0, 0⟩
    for w in ws₁ do
      let wIdx ← findElemIdx allWElems w
      let score := metaL1Score allLElems.size allWElems.size allUElems.size
        s1Bounds wpValues lpValues uIdx wIdx
      marg1 := metaQIAdd marg1 score
    marg1 := roundBounds marg1

    let mut marg2 : MetaBounds := ⟨0, 0⟩
    for w in ws₂ do
      let wIdx ← findElemIdx allWElems w
      let score := metaL1Score allLElems.size allWElems.size allUElems.size
        s1Bounds wpValues lpValues uIdx wIdx
      marg2 := metaQIAdd marg2 score
    marg2 := roundBounds marg2

    logInfo m!"rsa_predict: marginal₁ ∈ [{marg1.lo}, {marg1.hi}]"
    logInfo m!"rsa_predict: marginal₂ ∈ [{marg2.lo}, {marg2.hi}]"

    unless marg2.hi < marg1.lo do
      throwError "rsa_predict: marginal scores not separated: hi₂ = {marg2.hi} ≥ lo₁ = {marg1.lo}"

    -- Build compositional L1 score CProofs (all worlds at once, reused)
    let αExpr ← mkAppM ``RSA.RSAConfig.α #[cfg]
    let some αNat ← resolveNat? αExpr
      | throwError "rsa_predict: cannot extract α as ℕ"
    let isBeliefBased ← detectBeliefBased cfg
    logInfo m!"rsa_predict: building compositional proof (α={αNat}, {if isBeliefBased then "belief" else "action"})..."
    enableL0Cache cfg allWElems isBeliefBased

    -- Build all L1 scores once, reuse for both sides and total
    let (allScoreProofs, totalProof) ← buildAllL1ScoreCProofs cfg u
      allUElems allWElems allLElems wpValues lpValues αNat isBeliefBased
    disableL0Cache

    -- Sum scores for each side
    let mut side1 : Array CProof := #[]
    for w in ws₁ do
      let wIdx ← findElemIdx allWElems w
      side1 := side1.push allScoreProofs[wIdx]!
    let sum1 ← buildChainAdd side1

    let mut side2 : Array CProof := #[]
    for w in ws₂ do
      let wIdx ← findElemIdx allWElems w
      side2 := side2.push allScoreProofs[wIdx]!
    let sum2 ← buildChainAdd side2

    -- Prove score-sum separation
    let hi2E ← mkAppM ``QInterval.hi #[sum2.iExpr]
    let lo1E ← mkAppM ``QInterval.lo #[sum1.iExpr]
    let sepProof ← proveQPropND (← mkAppM ``LT.lt #[hi2E, lo1E])
    let hgt ← mkAppM ``QInterval.gt_of_separated #[sum1.proof, sum2.proof, sepProof]

    -- Prove totalScore > 0
    let l1Agent ← mkAppM ``RSA.RSAConfig.L1agent #[cfg]
    let zeroQ ← mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, mkRawNatLit 0, none]
    let totLo ← mkAppM ``QInterval.lo #[totalProof.iExpr]
    let htotLoPos ← proveQPropND (← mkAppM ``LT.lt #[zeroQ, totLo])
    let htotPos ← mkAppM ``QInterval.pos_of_lo_pos #[totalProof.proof, htotLoPos]

    -- Apply policy_list_sum_gt
    let W ← inferType ws₁[0]!
    let ws1ListExpr ← mkListLit W ws₁.toList
    let ws2ListExpr ← mkListLit W ws₂.toList
    let proof ← mkAppM ``Core.RationalAction.policy_list_sum_gt
      #[l1Agent, u, ws1ListExpr, ws2ListExpr, hgt, htotPos]
    assignWithCastFallback goal proof
    logInfo m!"rsa_predict: ✓ proved via compositional proof (marginal)"

  | .l1Latent cfg u l₁ l₂ => do
    logInfo m!"rsa_predict: parsed goal as L1_latent comparison"
    let (_, _, _, allUElems, allWElems, allLElems, s1Bounds, wpValues, lpValues) ←
      reifyS1Scores cfg

    let uIdx ← findElemIdx allUElems u
    let l1Idx ← findElemIdx allLElems l₁
    let l2Idx ← findElemIdx allLElems l₂

    let score1 := metaL1LatentScore allLElems.size allWElems.size allUElems.size
      s1Bounds wpValues lpValues uIdx l1Idx
    let score2 := metaL1LatentScore allLElems.size allWElems.size allUElems.size
      s1Bounds wpValues lpValues uIdx l2Idx

    logInfo m!"rsa_predict: latent_score(l₁) ∈ [{score1.lo}, {score1.hi}]"
    logInfo m!"rsa_predict: latent_score(l₂) ∈ [{score2.lo}, {score2.hi}]"

    unless score2.hi < score1.lo do
      throwError "rsa_predict: latent scores not separated: hi₂ = {score2.hi} ≥ lo₁ = {score1.lo}"

    -- Build compositional latent score CProofs
    let αExpr ← mkAppM ``RSA.RSAConfig.α #[cfg]
    let some αNat ← resolveNat? αExpr
      | throwError "rsa_predict: cannot extract α as ℕ"
    let isBeliefBased ← detectBeliefBased cfg
    logInfo m!"rsa_predict: building compositional proof (α={αNat}, {if isBeliefBased then "belief" else "action"})..."
    enableL0Cache cfg allWElems isBeliefBased

    let cproof1 ← buildL1LatentScoreCProof cfg u l₁ allUElems allWElems allLElems wpValues lpValues αNat isBeliefBased
    let cproof2 ← buildL1LatentScoreCProof cfg u l₂ allUElems allWElems allLElems wpValues lpValues αNat isBeliefBased
    disableL0Cache

    -- Prove score separation
    let hi2E ← mkAppM ``QInterval.hi #[cproof2.iExpr]
    let lo1E ← mkAppM ``QInterval.lo #[cproof1.iExpr]
    let sepProof ← proveQPropND (← mkAppM ``LT.lt #[hi2E, lo1E])
    let hgt ← mkAppM ``QInterval.gt_of_separated #[cproof1.proof, cproof2.proof, sepProof]

    -- policy_gt_of_score_gt on L1_latent_agent
    let latentAgent ← mkAppM ``RSA.RSAConfig.L1_latent_agent #[cfg, u]
    let unitVal ← mkAppOptM ``Unit.unit #[]
    let policyGt ← mkAppM ``Core.RationalAction.policy_gt_of_score_gt
      #[latentAgent, unitVal, l₁, l₂, hgt]

    -- Rewrite via L1_latent_eq_policy to match goal
    -- eq1: L1_latent u l₁ = policy () l₁
    -- eq2: L1_latent u l₂ = policy () l₂
    -- policyGt : policy () l₁ > policy () l₂ (i.e. policy () l₂ < policy () l₁)
    -- Goal: L1_latent u l₁ > L1_latent u l₂ (i.e. L1_latent u l₂ < L1_latent u l₁)
    let eq1 ← mkAppM ``RSA.RSAConfig.L1_latent_eq_policy #[cfg, u, l₁]
    let eq2 ← mkAppM ``RSA.RSAConfig.L1_latent_eq_policy #[cfg, u, l₂]
    let eq1sym ← mkAppM ``Eq.symm #[eq1]
    let inner ← mkAppM ``lt_of_lt_of_eq #[policyGt, eq1sym]
    let proof ← mkAppM ``lt_of_eq_of_lt #[eq2, inner]
    assignWithCastFallback goal proof
    logInfo m!"rsa_predict: ✓ proved via compositional proof (L1_latent)"

  | .l1CrossUtterance cfg u₁ ws₁ u₂ ws₂ => do
    logInfo m!"rsa_predict: parsed goal as cross-utterance L1 sum ({ws₁.size} vs {ws₂.size})"
    let t0 ← IO.monoMsNow
    let (_, _, _, allUElems, allWElems, allLElems, s1Bounds, wpValues, lpValues) ←
      reifyS1Scores cfg
    let t1 ← IO.monoMsNow
    logInfo m!"rsa_predict: [timing] reify: {t1 - t0}ms"

    let nL := allLElems.size
    let nW := allWElems.size
    let nU := allUElems.size

    -- Compute policy bounds for each utterance (meta-level check)
    let allWIndices := Array.range nW

    let u1Idx ← findElemIdx allUElems u₁
    let mut psum1 : MetaBounds := ⟨0, 0⟩
    for w in ws₁ do
      let wIdx ← findElemIdx allWElems w
      let policy := metaL1Policy nL nW nU s1Bounds wpValues lpValues u1Idx allWIndices wIdx
      psum1 := metaQIAdd psum1 policy
    psum1 := roundBounds psum1

    let u2Idx ← findElemIdx allUElems u₂
    let mut psum2 : MetaBounds := ⟨0, 0⟩
    for w in ws₂ do
      let wIdx ← findElemIdx allWElems w
      let policy := metaL1Policy nL nW nU s1Bounds wpValues lpValues u2Idx allWIndices wIdx
      psum2 := metaQIAdd psum2 policy
    psum2 := roundBounds psum2

    logInfo m!"rsa_predict: policy_sum₁ ∈ [{psum1.lo}, {psum1.hi}]"
    logInfo m!"rsa_predict: policy_sum₂ ∈ [{psum2.lo}, {psum2.hi}]"

    unless psum2.hi < psum1.lo do
      throwError "rsa_predict: policy sums not separated: hi₂ = {psum2.hi} ≥ lo₁ = {psum1.lo}"

    -- Build compositional L1 policy CProofs (cached per utterance)
    let αExpr ← mkAppM ``RSA.RSAConfig.α #[cfg]
    let some αNat ← resolveNat? αExpr
      | throwError "rsa_predict: cannot extract α as ℕ"
    let isBeliefBased ← detectBeliefBased cfg
    logInfo m!"rsa_predict: building compositional proof (α={αNat}, {if isBeliefBased then "belief" else "action"})..."
    enableL0Cache cfg allWElems isBeliefBased

    -- Phase 1: Pre-build S1 cache once, shared across both utterances
    let tp1 ← IO.monoMsNow
    logInfo m!"rsa_predict: [phase 1/5] building S1 score cache ({allLElems.size}×{allWElems.size}×{allUElems.size} = {allLElems.size * allWElems.size * allUElems.size} entries)..."
    let s1Cache ← buildAllS1ScoreCProofs cfg allUElems allWElems allLElems αNat isBeliefBased s1Bounds
    let tp1e ← IO.monoMsNow
    logInfo m!"rsa_predict: [timing] phase 1 (S1 cache): {tp1e - tp1}ms"

    -- Phase 1b: Pre-build leaf CProofs (worldPrior, latentPrior) shared across u₁ and u₂
    let tp1b ← IO.monoMsNow
    let leafCache ← buildLeafCache cfg allWElems allLElems wpValues lpValues
    let tp1be ← IO.monoMsNow
    logInfo m!"rsa_predict: [timing] phase 1b (leaf cache): {tp1be - tp1b}ms"

    -- Phase 2: Build all L1 scores for u₁ (with shared S1 + leaf caches)
    let tp2 ← IO.monoMsNow
    logInfo m!"rsa_predict: [phase 2/5] building L1 scores for u₁ ({allWElems.size} worlds)..."
    let (allScores1, total1) ← buildAllL1ScoreCProofs cfg u₁
      allUElems allWElems allLElems wpValues lpValues αNat isBeliefBased (some s1Cache) (some leafCache)
    let tp2e ← IO.monoMsNow
    logInfo m!"rsa_predict: [timing] phase 2 (L1 u₁): {tp2e - tp2}ms"

    -- Phase 3: Build all L1 scores for u₂ (with shared S1 + leaf caches)
    let tp3 ← IO.monoMsNow
    logInfo m!"rsa_predict: [phase 3/5] building L1 scores for u₂ ({allWElems.size} worlds)..."
    let (allScores2, total2) ← buildAllL1ScoreCProofs cfg u₂
      allUElems allWElems allLElems wpValues lpValues αNat isBeliefBased (some s1Cache) (some leafCache)
    let tp3e ← IO.monoMsNow
    logInfo m!"rsa_predict: [timing] phase 3 (L1 u₂): {tp3e - tp3}ms"
    disableL0Cache

    -- Phase 4: Build L1 policy CProofs per world per side
    let tp4 ← IO.monoMsNow
    logInfo m!"rsa_predict: [phase 4/5] building L1 policy CProofs ({ws₁.size}+{ws₂.size} worlds)..."
    let mut policyProofs1 : Array CProof := #[]
    for w in ws₁ do
      policyProofs1 := policyProofs1.push
        (← buildL1PolicyFromScores cfg u₁ w allWElems allScores1 total1)
    let sum1 ← buildLeftAdd policyProofs1

    let mut policyProofs2 : Array CProof := #[]
    for w in ws₂ do
      policyProofs2 := policyProofs2.push
        (← buildL1PolicyFromScores cfg u₂ w allWElems allScores2 total2)
    let sum2 ← buildLeftAdd policyProofs2
    let tp4e ← IO.monoMsNow
    logInfo m!"rsa_predict: [timing] phase 4 (policies): {tp4e - tp4}ms"

    -- Phase 5: Prove policy-sum separation and assign
    let tp5 ← IO.monoMsNow
    logInfo m!"rsa_predict: [phase 5/5] proving separation and assigning..."
    let hi2E ← mkAppM ``QInterval.hi #[sum2.iExpr]
    let lo1E ← mkAppM ``QInterval.lo #[sum1.iExpr]
    let sepProof ← proveQPropND (← mkAppM ``LT.lt #[hi2E, lo1E])
    let proof ← mkAppM ``QInterval.gt_of_separated #[sum1.proof, sum2.proof, sepProof]
    assignWithCastFallback goal proof
    let tp5e ← IO.monoMsNow
    logInfo m!"rsa_predict: [timing] phase 5 (sep+assign): {tp5e - tp5}ms, total: {tp5e - t0}ms"
    logInfo m!"rsa_predict: ✓ proved via compositional proof (cross-utterance)"

  | .l1CrossConfig cfg₁ u₁ ws₁ cfg₂ u₂ ws₂ => do
    logInfo m!"rsa_predict: parsed goal as cross-config L1 sum ({ws₁.size} vs {ws₂.size})"
    let (_, _, _, allUElems1, allWElems1, allLElems1, s1Bounds1, wpValues1, lpValues1) ←
      reifyS1Scores cfg₁
    let (_, _, _, allUElems2, allWElems2, allLElems2, s1Bounds2, wpValues2, lpValues2) ←
      reifyS1Scores cfg₂
    let nL1 := allLElems1.size
    let nW1 := allWElems1.size
    let nU1 := allUElems1.size
    let nL2 := allLElems2.size
    let nW2 := allWElems2.size
    let nU2 := allUElems2.size
    let allWIndices1 := Array.range nW1
    let allWIndices2 := Array.range nW2

    let u1Idx ← findElemIdx allUElems1 u₁
    let mut psum1 : MetaBounds := ⟨0, 0⟩
    for w in ws₁ do
      let wIdx ← findElemIdx allWElems1 w
      let policy := metaL1Policy nL1 nW1 nU1 s1Bounds1 wpValues1 lpValues1 u1Idx allWIndices1 wIdx
      psum1 := metaQIAdd psum1 policy
    psum1 := roundBounds psum1

    let u2Idx ← findElemIdx allUElems2 u₂
    let mut psum2 : MetaBounds := ⟨0, 0⟩
    for w in ws₂ do
      let wIdx ← findElemIdx allWElems2 w
      let policy := metaL1Policy nL2 nW2 nU2 s1Bounds2 wpValues2 lpValues2 u2Idx allWIndices2 wIdx
      psum2 := metaQIAdd psum2 policy
    psum2 := roundBounds psum2

    logInfo m!"rsa_predict: policy_sum₁ ∈ [{psum1.lo}, {psum1.hi}]"
    logInfo m!"rsa_predict: policy_sum₂ ∈ [{psum2.lo}, {psum2.hi}]"

    unless psum2.hi < psum1.lo do
      throwError "rsa_predict: cross-config policy sums not separated: hi₂ = {psum2.hi} ≥ lo₁ = {psum1.lo}"

    -- Build compositional L1 policy CProofs for each config (cached per utterance)
    let αExpr1 ← mkAppM ``RSA.RSAConfig.α #[cfg₁]
    let some αNat1 ← resolveNat? αExpr1
      | throwError "rsa_predict: cannot extract α as ℕ (config 1)"
    let isBeliefBased1 ← detectBeliefBased cfg₁
    let αExpr2 ← mkAppM ``RSA.RSAConfig.α #[cfg₂]
    let some αNat2 ← resolveNat? αExpr2
      | throwError "rsa_predict: cannot extract α as ℕ (config 2)"
    let isBeliefBased2 ← detectBeliefBased cfg₂
    logInfo m!"rsa_predict: building compositional proof..."

    -- Config 1: build with L0 + leaf caches
    enableL0Cache cfg₁ allWElems1 isBeliefBased1
    let s1Cache1 ← buildAllS1ScoreCProofs cfg₁ allUElems1 allWElems1 allLElems1 αNat1 isBeliefBased1 s1Bounds1
    let leafCache1 ← buildLeafCache cfg₁ allWElems1 allLElems1 wpValues1 lpValues1
    let (allScores1, total1) ← buildAllL1ScoreCProofs cfg₁ u₁
      allUElems1 allWElems1 allLElems1 wpValues1 lpValues1 αNat1 isBeliefBased1 (some s1Cache1) (some leafCache1)
    disableL0Cache
    let mut policyProofs1 : Array CProof := #[]
    for w in ws₁ do
      policyProofs1 := policyProofs1.push
        (← buildL1PolicyFromScores cfg₁ u₁ w allWElems1 allScores1 total1)
    let sum1 ← buildLeftAdd policyProofs1

    -- Config 2: build with L0 + leaf caches
    enableL0Cache cfg₂ allWElems2 isBeliefBased2
    let s1Cache2 ← buildAllS1ScoreCProofs cfg₂ allUElems2 allWElems2 allLElems2 αNat2 isBeliefBased2 s1Bounds2
    let leafCache2 ← buildLeafCache cfg₂ allWElems2 allLElems2 wpValues2 lpValues2
    let (allScores2, total2) ← buildAllL1ScoreCProofs cfg₂ u₂
      allUElems2 allWElems2 allLElems2 wpValues2 lpValues2 αNat2 isBeliefBased2 (some s1Cache2) (some leafCache2)
    disableL0Cache
    let mut policyProofs2 : Array CProof := #[]
    for w in ws₂ do
      policyProofs2 := policyProofs2.push
        (← buildL1PolicyFromScores cfg₂ u₂ w allWElems2 allScores2 total2)
    let sum2 ← buildLeftAdd policyProofs2

    -- Prove policy-sum separation
    let hi2E ← mkAppM ``QInterval.hi #[sum2.iExpr]
    let lo1E ← mkAppM ``QInterval.lo #[sum1.iExpr]
    let sepProof ← proveQPropND (← mkAppM ``LT.lt #[hi2E, lo1E])
    let proof ← mkAppM ``QInterval.gt_of_separated #[sum1.proof, sum2.proof, sepProof]
    assignWithCastFallback goal proof
    logInfo m!"rsa_predict: ✓ proved via compositional proof (cross-config)"

  | .s1Compare cfg l w u₁ u₂ => do
    logInfo m!"rsa_predict: parsed goal as S1 comparison"
    let (_, _, _, allUElems, allWElems, allLElems, s1Bounds, _, _) ←
      reifyS1Scores cfg

    let lIdx ← findElemIdx allLElems l
    let wIdx ← findElemIdx allWElems w
    let u1Idx ← findElemIdx allUElems u₁
    let u2Idx ← findElemIdx allUElems u₂

    let nU := allUElems.size
    let nW := allWElems.size
    let idx1 := lIdx * nW * nU + wIdx * nU + u1Idx
    let idx2 := lIdx * nW * nU + wIdx * nU + u2Idx
    let s1_u1 := s1Bounds[idx1]!
    let s1_u2 := s1Bounds[idx2]!

    logInfo m!"rsa_predict: S1_score(u₁) ∈ [{s1_u1.lo}, {s1_u1.hi}]"
    logInfo m!"rsa_predict: S1_score(u₂) ∈ [{s1_u2.lo}, {s1_u2.hi}]"

    unless s1_u2.hi < s1_u1.lo do
      throwError "rsa_predict: S1 scores not separated: hi₂ = {s1_u2.hi} ≥ lo₁ = {s1_u1.lo}"

    -- Extract α for compositional proof
    let αExpr ← mkAppM ``RSA.RSAConfig.α #[cfg]
    let some αNat ← resolveNat? αExpr
      | throwError "rsa_predict: cannot extract α as ℕ"
    let isBeliefBased ← detectBeliefBased cfg
    logInfo m!"rsa_predict: building compositional proof (α={αNat}, {if isBeliefBased then "belief" else "action"})..."
    enableL0Cache cfg allWElems isBeliefBased
    let score1 ← buildS1ScoreCProof cfg l w u₁ allWElems αNat isBeliefBased
    let score2 ← buildS1ScoreCProof cfg l w u₂ allWElems αNat isBeliefBased
    disableL0Cache
    -- Prove separation
    let hi2E ← mkAppM ``QInterval.hi #[score2.iExpr]
    let lo1E ← mkAppM ``QInterval.lo #[score1.iExpr]
    let sepProof ← proveQPropND (← mkAppM ``LT.lt #[hi2E, lo1E])
    let hgt ← mkAppM ``QInterval.gt_of_separated #[score1.proof, score2.proof, sepProof]
    -- policy_gt_of_score_gt lifts to S1 policy comparison
    let s1Agent ← mkAppM ``RSA.RSAConfig.S1agent #[cfg, l]
    let proof ← mkAppM ``Core.RationalAction.policy_gt_of_score_gt #[s1Agent, w, u₁, u₂, hgt]
    assignWithCastFallback goal proof
    logInfo m!"rsa_predict: ✓ proved via compositional proof (S1 comparison)"

end Linglib.Tactics
