import Lean
import Linglib.Theories.Pragmatics.RSA.Core.Config

set_option autoImplicit false

/-!
# RSAPredict Goal Parsing

Recognize comparison goal forms and extract RSA config/utterance/world arguments
from `L1`, `L1_latent`, and `S1` policy expressions.
-/

namespace Linglib.Tactics.RSAPredict

open Lean Meta Elab Tactic

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
  -- Try to unfold to cfg.L1agent.policy u w
  if let some (ra, u, w) := ← unfoldToPolicy e then
    -- Check if ra is cfg.L1agent
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
  -- Try to unfold to cfg.S1agent(l).policy w u
  if let some (ra, w, u) := ← unfoldToPolicy e then
    -- Check if ra is cfg.S1agent l
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
-- Goal Form
-- ============================================================================

/-- Parsed goal forms that rsa_predict can handle. -/
inductive GoalForm where
  /-- cfg.L1 u w₁ > cfg.L1 u w₂ -/
  | l1Compare (cfg u w₁ w₂ : Expr)
  /-- (ws₁.map (cfg.L1 u)).sum > (ws₂.map (cfg.L1 u)).sum (marginal) -/
  | l1Marginal (cfg u : Expr) (ws₁ ws₂ : Array Expr)
  /-- cfg.L1_latent u l₁ > cfg.L1_latent u l₂ -/
  | l1Latent (cfg u l₁ l₂ : Expr)
  /-- (ws₁.map (cfg.L1 u₁)).sum > (ws₂.map (cfg.L1 u₂)).sum (cross-utterance) -/
  | l1CrossUtterance (cfg u₁ : Expr) (ws₁ : Array Expr) (u₂ : Expr) (ws₂ : Array Expr)
  /-- (ws₁.map (cfg₁.L1 u₁)).sum > (ws₂.map (cfg₂.L1 u₂)).sum (cross-config) -/
  | l1CrossConfig (cfg₁ u₁ : Expr) (ws₁ : Array Expr) (cfg₂ u₂ : Expr) (ws₂ : Array Expr)
  /-- cfg.S1 l w u₁ > cfg.S1 l w u₂ -/
  | s1Compare (cfg l w u₁ u₂ : Expr)

-- ============================================================================
-- Goal Form Parsing Helpers
-- ============================================================================

/-- Try to unfold an expression to `cfg.L1_latent u l`. -/
def parseL1Latent (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let mut current := e
  for _ in List.range 10 do
    let fn := current.getAppFn
    let args := current.getAppArgs
    if fn.isConstOf ``RSA.RSAConfig.L1_latent && args.size ≥ 5 then
      return some (args[4]!, args[5]!, args[6]!)  -- cfg, u, l
    if let some e' ← unfoldDefinition? current then
      current := e'.headBeta
    else break
  return none

private def isAppOfMin (e : Expr) (name : Name) (minArgs : ℕ) : Bool :=
  e.getAppFn.isConstOf name && e.getAppNumArgs ≥ minArgs

/-- Collect L1 policy summands from an expression.
    Returns (cfg, u, ws) where ws are the world arguments, or none.
    Handles Finset.sum, List.sum of map, and nested HAdd of L1 terms. -/
partial def collectL1Summands (e : Expr) : MetaM (Option (Expr × Expr × Array Expr)) := do
  -- Try single L1 term first
  if let some (cfg, u, w) ← parseL1Policy e then
    return some (cfg, u, #[w])
  -- Try HAdd of L1 terms
  if isAppOfMin e ``HAdd.hAdd 6 then
    let a := e.getAppArgs[4]!
    let b := e.getAppArgs[5]!
    if let some (cfg1, u1, ws1) ← collectL1Summands a then
      if let some (cfg2, u2, ws2) ← collectL1Summands b then
        if (← isDefEq cfg1 cfg2) && (← isDefEq u1 u2) then
          return some (cfg1, u1, ws1 ++ ws2)
        -- Different utterances: return cfg1, u1, ws1 for LHS; caller handles
  -- Try Finset.sum: unfold and recurse
  let fn := e.getAppFn
  if fn.constName? == some ``Finset.sum ||
     fn.constName? == some ``Multiset.sum ||
     fn.constName? == some ``Multiset.fold ||
     fn.constName? == some ``List.foldr ||
     fn.constName? == some ``List.foldl ||
     fn.constName? == some ``List.sum ||
     fn.constName? == some ``Quot.lift then
    let e' ← whnf e
    if !e.equal e' then
      return ← collectL1Summands e'
  -- Try unfolding
  if let some e' ← unfoldDefinition? e then
    return ← collectL1Summands e'.headBeta
  return none

/-- Collect L1 summands allowing different utterances on each side.
    Returns (cfg, u, ws) pairs. For cross-utterance goals, the two sides
    may have different u values. -/
partial def collectL1SummandsAnyU (e : Expr) :
    MetaM (Option (Expr × Array (Expr × Array Expr))) := do
  -- Try single L1 term first
  if let some (cfg, u, w) ← parseL1Policy e then
    return some (cfg, #[(u, #[w])])
  -- Try HAdd of L1 terms (may have different utterances)
  if isAppOfMin e ``HAdd.hAdd 6 then
    let a := e.getAppArgs[4]!
    let b := e.getAppArgs[5]!
    if let some (cfg1, groups1) ← collectL1SummandsAnyU a then
      if let some (cfg2, groups2) ← collectL1SummandsAnyU b then
        if ← isDefEq cfg1 cfg2 then
          -- Merge groups by utterance
          let mut merged := groups1
          for (u2, ws2) in groups2 do
            let mut found := false
            for i in List.range merged.size do
              if ← isDefEq merged[i]!.1 u2 then
                merged := merged.set! i (merged[i]!.1, merged[i]!.2 ++ ws2)
                found := true
                break
            unless found do
              merged := merged.push (u2, ws2)
          return some (cfg1, merged)
  -- Try Finset.sum: unfold and recurse
  let fn := e.getAppFn
  if fn.constName? == some ``Finset.sum ||
     fn.constName? == some ``Multiset.sum ||
     fn.constName? == some ``Multiset.fold ||
     fn.constName? == some ``List.foldr ||
     fn.constName? == some ``List.foldl ||
     fn.constName? == some ``List.sum ||
     fn.constName? == some ``Quot.lift then
    let e' ← whnf e
    if !e.equal e' then
      return ← collectL1SummandsAnyU e'
  -- Try unfolding
  if let some e' ← unfoldDefinition? e then
    return ← collectL1SummandsAnyU e'.headBeta
  return none

-- ============================================================================
-- Main Goal Parser
-- ============================================================================

/-- Parse the goal into a GoalForm. -/
def parseGoalForm (lhs rhs : Expr) : MetaM GoalForm := do
  -- Path A: Both sides are cfg.L1 u w
  if let some (cfg, u, w₁) ← parseL1Policy lhs then
    if let some (cfg₂, u₂, w₂) ← parseL1Policy rhs then
      if ← isDefEq cfg cfg₂ then
        return .l1Compare cfg u w₁ w₂
      else
        return .l1CrossConfig cfg u #[w₁] cfg₂ u₂ #[w₂]

  -- Path B: cfg.L1_latent u l₁ > cfg.L1_latent u l₂
  if let some (cfg, u, l₁) ← parseL1Latent lhs then
    if let some (cfg₂, _u₂, l₂) ← parseL1Latent rhs then
      if ← isDefEq cfg cfg₂ then
        return .l1Latent cfg u l₁ l₂

  -- Path B2: cfg.S1 l w u₁ > cfg.S1 l w u₂
  if let some (cfg, l, w, u₁) ← parseS1Policy lhs then
    if let some (cfg₂, _l₂, _w₂, u₂) ← parseS1Policy rhs then
      if ← isDefEq cfg cfg₂ then
        return .s1Compare cfg l w u₁ u₂

  -- Path C/D: sums of L1 terms
  if let some (cfg1, groups1) ← collectL1SummandsAnyU lhs then
    if let some (cfg2, groups2) ← collectL1SummandsAnyU rhs then
      if ← isDefEq cfg1 cfg2 then
        -- Same utterance on both sides → marginal
        if groups1.size == 1 && groups2.size == 1 then
          let (u1, ws1) := groups1[0]!
          let (u2, ws2) := groups2[0]!
          if ← isDefEq u1 u2 then
            return .l1Marginal cfg1 u1 ws1 ws2
          else
            return .l1CrossUtterance cfg1 u1 ws1 u2 ws2
        -- Different utterances → cross-utterance
        -- Flatten all groups into one side each
        let allWs1 := groups1.foldl (init := #[]) fun acc (_, ws) => acc ++ ws
        let allWs2 := groups2.foldl (init := #[]) fun acc (_, ws) => acc ++ ws
        -- For cross-utterance, we need exactly one u per side
        if groups1.size == 1 && groups2.size == 1 then
          return .l1CrossUtterance cfg1 groups1[0]!.1 allWs1 groups2[0]!.1 allWs2
      else
        -- Cross-config: different RSAConfigs on each side
        if groups1.size == 1 && groups2.size == 1 then
          let (u1, ws1) := groups1[0]!
          let (u2, ws2) := groups2[0]!
          return .l1CrossConfig cfg1 u1 ws1 cfg2 u2 ws2

  throwError "rsa_predict: cannot parse goal. Expected one of:\n\
    • cfg.L1 u w₁ > cfg.L1 u w₂\n\
    • cfg.L1_latent u l₁ > cfg.L1_latent u l₂\n\
    • cfg.S1 l w u₁ > cfg.S1 l w u₂\n\
    • Σ ... cfg.L1 u ... > Σ ... cfg.L1 u ...\n\
    • (cfg.L1 u₁ w₁ + ...) > (cfg.L1 u₂ w₃ + ...)\n\
    • (cfg₁.L1 u₁ w₁ + ...) > (cfg₂.L1 u₂ w₃ + ...)"

end Linglib.Tactics.RSAPredict
