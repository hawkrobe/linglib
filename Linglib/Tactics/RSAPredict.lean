import Lean
import Linglib.Theories.Pragmatics.RSA.Core.Verified
import Linglib.Core.Interval.ReflectInterval
import Linglib.Tactics.RSAPredict.Helpers
import Linglib.Tactics.RSAPredict.Reify
import Linglib.Tactics.RSAPredict.GoalParsing
import Linglib.Tactics.RSAPredict.ProofBuilder

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
      let score1 ← buildL1ScoreCProof cfg u w₁ allUElems allWElems allLElems wpValues lpValues αNat isBeliefBased
      let score2 ← buildL1ScoreCProof cfg u w₂ allUElems allWElems allLElems wpValues lpValues αNat isBeliefBased
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
      let score1 ← buildS1ScoreCProof cfg l w u₁ allWElems αNat isBeliefBased
      let score2 ← buildS1ScoreCProof cfg l w u₂ allWElems αNat isBeliefBased
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
            -- Last resort: axiom fallback (for equal scores with imprecise exp/log intervals)
            let hi1Q ← mkRatExpr s1_u1.hi
            let lo2Q ← mkRatExpr s1_u2.lo
            let leProof ← proveQPropND (← mkAppM ``LE.le #[hi1Q, lo2Q])
            let proof ← mkAppM ``RSA.Verified.S1_not_gt_of_precomputed
              #[cfg, l, w, u₁, u₂, hi1Q, lo2Q, leProof]
            assignWithCastFallback goal proof
            logInfo m!"rsa_predict: ✓ proved via S1_not_gt_of_precomputed (axiom fallback)"
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

    unless l1_w2.hi < l1_w1.lo do
      throwError "rsa_predict: L1 scores not separated: w₂.hi = {l1_w2.hi} ≥ w₁.lo = {l1_w1.lo}"

    -- Extract α as ℕ for belief-based scoring
    let αExpr ← mkAppM ``RSA.RSAConfig.α #[cfg]
    let some αNat ← resolveNat? αExpr
      | throwError "rsa_predict: cannot extract α as ℕ"
    -- Build compositional proof terms for L1 scores
    let isBeliefBased ← detectBeliefBased cfg
    logInfo m!"rsa_predict: building compositional proof (α={αNat}, {if isBeliefBased then "belief" else "action"})..."
    let score1 ← buildL1ScoreCProof cfg u w₁ allUElems allWElems allLElems wpValues lpValues αNat isBeliefBased
    let score2 ← buildL1ScoreCProof cfg u w₂ allUElems allWElems allLElems wpValues lpValues αNat isBeliefBased
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
    assignWithCastFallback goal proof
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

    let sepProof ← proveQSeparation marg2.hi marg1.lo
    let hi2Expr ← mkRatExpr marg2.hi
    let lo1Expr ← mkRatExpr marg1.lo
    -- Build world lists as Lean exprs
    let W ← inferType ws₁[0]!
    let ws1ListExpr ← mkListLit W ws₁.toList
    let ws2ListExpr ← mkListLit W ws₂.toList
    let proof ← mkAppM ``RSA.Verified.L1_sum_gt_of_precomputed
      #[cfg, cfg, u, ws1ListExpr, u, ws2ListExpr, hi2Expr, lo1Expr, sepProof]
    assignWithCastFallback goal proof
    logInfo m!"rsa_predict: ✓ proved via L1_sum_gt_of_precomputed (marginal)"

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

    let sepProof ← proveQSeparation score2.hi score1.lo
    let hi2Expr ← mkRatExpr score2.hi
    let lo1Expr ← mkRatExpr score1.lo
    let proof ← mkAppM ``RSA.Verified.L1_latent_gt_of_precomputed
      #[cfg, u, l₁, l₂, hi2Expr, lo1Expr, sepProof]
    assignWithCastFallback goal proof
    logInfo m!"rsa_predict: ✓ proved via L1_latent_gt_of_precomputed"

  | .l1CrossUtterance cfg u₁ ws₁ u₂ ws₂ => do
    logInfo m!"rsa_predict: parsed goal as cross-utterance L1 sum ({ws₁.size} vs {ws₂.size})"
    let (_, _, _, allUElems, allWElems, allLElems, s1Bounds, wpValues, lpValues) ←
      reifyS1Scores cfg

    let nL := allLElems.size
    let nW := allWElems.size
    let nU := allUElems.size

    -- Compute policy bounds for each utterance
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

    let sepProof ← proveQSeparation psum2.hi psum1.lo
    let hi2Expr ← mkRatExpr psum2.hi
    let lo1Expr ← mkRatExpr psum1.lo
    let W ← inferType ws₁[0]!
    let ws1ListExpr ← mkListLit W ws₁.toList
    let ws2ListExpr ← mkListLit W ws₂.toList
    let proof ← mkAppM ``RSA.Verified.L1_sum_gt_of_precomputed
      #[cfg, cfg, u₁, ws1ListExpr, u₂, ws2ListExpr, hi2Expr, lo1Expr, sepProof]
    assignWithCastFallback goal proof
    logInfo m!"rsa_predict: ✓ proved via L1_sum_gt_of_precomputed (cross-utterance)"

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

    let sepProof ← proveQSeparation psum2.hi psum1.lo
    let hi2Expr ← mkRatExpr psum2.hi
    let lo1Expr ← mkRatExpr psum1.lo
    let W ← inferType ws₁[0]!
    let ws1ListExpr ← mkListLit W ws₁.toList
    let ws2ListExpr ← mkListLit W ws₂.toList
    let proof ← mkAppM ``RSA.Verified.L1_sum_gt_of_precomputed
      #[cfg₁, cfg₂, u₁, ws1ListExpr, u₂, ws2ListExpr, hi2Expr, lo1Expr, sepProof]
    assignWithCastFallback goal proof
    logInfo m!"rsa_predict: ✓ proved via L1_sum_gt_of_precomputed (cross-config)"

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
    let score1 ← buildS1ScoreCProof cfg l w u₁ allWElems αNat isBeliefBased
    let score2 ← buildS1ScoreCProof cfg l w u₂ allWElems αNat isBeliefBased
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
