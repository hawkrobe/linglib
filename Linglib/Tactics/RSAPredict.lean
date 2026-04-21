import Lean
import Linglib.Theories.Pragmatics.RSA.Basic
import Linglib.Tactics.RSAPredict.Backend.Reflection
import Linglib.Tactics.RSAPredict.Helpers
import Linglib.Tactics.RSAPredict.Reify
import Linglib.Tactics.RSAPredict.ReflectBridge

set_option autoImplicit false

/-!
# RSAPredict — Verified RSA Predictions via Reflection

The `rsa_predict` tactic proves ℝ comparison goals on RSA models by:

1. Reifying both sides to `RExpr` (rational expression trees)
2. Evaluating via exact ℚ arithmetic or tree-based intervals
3. Building kernel-verifiable proofs from the interval separation

All invocations use this reflection path exclusively (no `native_decide` fallback).

## Supported Goal Forms

- `cfg.L0 l u w₁ > cfg.L0 l u w₂` — L0 world comparison
- `cfg.L0_marginal l u P₁ > cfg.L0_marginal l u P₂` — L0 marginal comparison
- `cfg.L1 u w₁ > cfg.L1 u w₂` — L1 world comparison
- `¬(cfg.L1 u w₁ > cfg.L1 u w₂)` — L1 non-strict (implicature canceled)
- `cfg.L1_latent u l₁ > cfg.L1_latent u l₂` — latent variable inference
- `cfg.S1 l w u₁ > cfg.S1 l w u₂` — S1 speaker comparison
- `¬(cfg.S1 l w u₁ > cfg.S1 l w u₂)` — S1 non-strict
- `cfg.S2 w₁ u > cfg.S2 w₂ u` — S2 cross-world endorsement
- `cfg.S1 l w u₁ = cfg.S1 l w u₂` — S1 equality (score symmetry)
- `cfg.L1 u w₁ = cfg.L1 u w₂` — L1 equality (score symmetry)
- `Σ s, cfg.L1 u (s, a₁) > Σ s, cfg.L1 u (s, a₂)` — marginal comparison
- `cfg.L1_marginal u P₁ > cfg.L1_marginal u P₂` — marginal via predicate
- `cfg.L1 u₁ w₁ +... > cfg.L1 u₂ w₃ +...` — cross-utterance sum
- `cfg₁.L1 u₁ w₁ +... > cfg₂.L1 u₂ w₃ +...` — cross-config sum

## Usage

```lean
theorem prediction : cfg.L1 u w₁ > cfg.L1 u w₂ := by rsa_predict
```
-/

namespace Tactics

open Lean Meta Elab Tactic
open Interval
open Tactics.RSAPredict

-- ============================================================================
-- Main Tactic
-- ============================================================================

/-- `rsa_predict` proves RSA prediction goals by RExpr reflection.

    The tactic reifies both sides of a comparison to `RExpr` (rational expression
    trees), then proves the comparison via exact ℚ evaluation or tree-based interval
    arithmetic. The kernel verifies that `RExpr.denote` matches the original ℝ
    expression via iota-reduction. -/
elab "rsa_predict" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType

  -- ¬(_ > _): detect as P → False (Not is @[reducible], so whnf reduces @Not P)
  let goalTypeWhnf ← whnf goalType
  if let .forallE _ inner (.const ``False []) _ := goalTypeWhnf then do
    let innerFn := inner.getAppFn
    let innerArgs := inner.getAppArgs
    unless innerFn.isConstOf ``GT.gt && innerArgs.size ≥ 4 do
      throwError "rsa_predict: expected goal of the form `¬(_ > _)`, got: {← ppExpr goalType}"
    let lhs := innerArgs[2]!
    let rhs := innerArgs[3]!

    -- Generic direct RExpr reflection (handles all ¬(>) patterns)
    if ← tryDirectRExprNotGt goal lhs rhs then
      logInfo m!"rsa_predict: ✓ proved via reflection (¬gt, generic)"
      return

    -- Fallback: try proving equality (lhs = rhs), then derive ¬(lhs > rhs).
    -- This handles symmetric cases where interval arithmetic can't prove ¬(>)
    -- because exp/log intervals have width, but the values are actually equal.
    -- L1 equality via score equality
    if let some (cfg, u, w₁) ← try parseL1Policy lhs catch _ => pure none then
      if let some (cfg₂, _u₂, w₂) ← try parseL1Policy rhs catch _ => pure none then
        if ← isDefEq cfg cfg₂ then
          let scoreOk ← try
            let l1Agent ← mkAppM ``RSA.RSAConfig.L1agent #[cfg]
            let scoreExpr1 ← mkAppM ``Core.RationalAction.score #[l1Agent, u, w₁]
            let scoreExpr2 ← mkAppM ``Core.RationalAction.score #[l1Agent, u, w₂]
            let scoreEqGoal ← mkFreshExprMVar (← mkEq scoreExpr1 scoreExpr2)
            if ← tryDirectRExprEq scoreEqGoal.mvarId! scoreExpr1 scoreExpr2 then
              let policyEq ← mkAppM ``Core.RationalAction.policy_eq_of_score_eq
                #[l1Agent, u, w₁, w₂, scoreEqGoal]
              let leProof ← mkAppM ``le_of_eq #[policyEq]
              let notGtProof ← mkAppM ``not_lt_of_ge #[leProof]
              goal.assign notGtProof
              logInfo m!"rsa_predict: ✓ proved ¬(>) via L1 score equality"
              pure true
            else pure false
          catch _ => pure false
          if scoreOk then return

    throwError "rsa_predict: reflection failed for ¬(_ > _) goal: {← ppExpr goalType}"

  -- Eq goal: lhs = rhs (handles S1/L1 score equality)
  if goalTypeWhnf.isAppOf ``Eq then
    let eqArgs := goalTypeWhnf.getAppArgs
    if eqArgs.size ≥ 3 then
      let lhs := eqArgs[1]!
      let rhs := eqArgs[2]!

      -- Try direct RExpr equality on the raw expressions
      if ← tryDirectRExprEq goal lhs rhs then
        logInfo m!"rsa_predict: ✓ proved equality via reflection"
        return

      -- Try parsing as L1 equality → score equality → policy_eq_of_score_eq
      if let some (cfg, u, w₁) ← parseL1Policy lhs then
        if let some (cfg₂, _u₂, w₂) ← parseL1Policy rhs then
          if ← isDefEq cfg cfg₂ then
            let l1Agent ← mkAppM ``RSA.RSAConfig.L1agent #[cfg]
            let scoreExpr1 ← mkAppM ``Core.RationalAction.score #[l1Agent, u, w₁]
            let scoreExpr2 ← mkAppM ``Core.RationalAction.score #[l1Agent, u, w₂]
            let scoreEqGoal ← mkFreshExprMVar (← mkEq scoreExpr1 scoreExpr2)
            if ← tryDirectRExprEq scoreEqGoal.mvarId! scoreExpr1 scoreExpr2 then
              let proof ← mkAppM ``Core.RationalAction.policy_eq_of_score_eq
                #[l1Agent, u, w₁, w₂, scoreEqGoal]
              goal.assign proof
              logInfo m!"rsa_predict: ✓ proved L1 equality via score equality"
              return

      -- Try parsing as S1 equality → score equality → policy_eq_of_score_eq
      if let some (cfg, l, w, u₁) ← parseS1Policy lhs then
        if let some (cfg₂, _l₂, _w₂, u₂) ← parseS1Policy rhs then
          if ← isDefEq cfg cfg₂ then
            let s1Agent ← mkAppM ``RSA.RSAConfig.S1agent #[cfg, l]
            let scoreExpr1 ← mkAppM ``Core.RationalAction.score #[s1Agent, w, u₁]
            let scoreExpr2 ← mkAppM ``Core.RationalAction.score #[s1Agent, w, u₂]
            let scoreEqGoal ← mkFreshExprMVar (← mkEq scoreExpr1 scoreExpr2)
            if ← tryDirectRExprEq scoreEqGoal.mvarId! scoreExpr1 scoreExpr2 then
              let proof ← mkAppM ``Core.RationalAction.policy_eq_of_score_eq
                #[s1Agent, w, u₁, u₂, scoreEqGoal]
              goal.assign proof
              logInfo m!"rsa_predict: ✓ proved S1 equality via score equality"
              return

      throwError "rsa_predict: cannot prove equality goal: {← ppExpr goalType}"

  let fn := goalType.getAppFn
  let args := goalType.getAppArgs

  -- GT.gt: lhs > rhs
  unless fn.isConstOf ``GT.gt && args.size ≥ 4 do
    throwError "rsa_predict: expected goal of the form `_ > _`, `_ = _`, or `¬(_ > _)`, got: {← ppExpr goalType}"

  let lhs := args[2]!
  let rhs := args[3]!

  -- Generic direct RExpr reflection (handles all > patterns)
  let t0 ← IO.monoMsNow
  let reflectOk ← try
    tryDirectRExprCompare goal lhs rhs
  catch e =>
    logInfo m!"rsa_predict: reflection failed: {e.toMessageData}"
    pure false
  if reflectOk then
    let t1 ← IO.monoMsNow
    logInfo m!"rsa_predict: ✓ proved via reflection (generic, {t1 - t0}ms)"
    return

  throwError "rsa_predict: reflection failed for (>) goal: {← ppExpr goalType}"

end Tactics
