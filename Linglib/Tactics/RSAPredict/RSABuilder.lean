import Lean
import Linglib.Tactics.RSAPredict.Reify
import Linglib.Tactics.RSAPredict.Helpers

set_option autoImplicit false

/-!
# RSA Bottom-Up RExpr Builder

Constructs RExpr trees for RSA expressions bottom-up from evaluated leaf values,
completely bypassing the generic reifier's top-down `unfoldDefinition?` chain.

The generic reifier discovers expression structure by unfolding definitions one
at a time (~31K `unfoldDefinition?` calls for the first cross-utterance theorem).
The builder knows the RSA layered structure and constructs RExpr trees directly:

1. **Leaf evaluation**: Evaluate meaning Bool values natively, reify priors/costs
   via the generic reifier (small expressions, ~0.1ms each).
2. **Layer composition**: Build L0 → S1 → L1 RExpr trees by direct construction.
3. **Direct return**: Return the full RExpr to the caller, bypassing `reifyToRExpr`.

The kernel verifies `denote(rexpr) ≡ original_expr` by reducing both sides.
The builder's RExpr matches because:
- Left-fold sums match `Finset.sum` reduction (via `0 + x ≡ x` for ℝ)
- iteZero matches `if totalScore = 0 then 0 else score / totalScore`
- expMulLogSub matches `exp(α * (log x - c))`
- Leaf values are reified by the generic reifier (denote matches by construction)
-/

namespace Linglib.Tactics.RSAPredict

open Lean Meta Elab Tactic
open Linglib.Interval

-- ============================================================================
-- RExpr Construction Helpers
-- ============================================================================

private def rexprNat (n : ℕ) : Expr × MetaBounds :=
  (mkApp (mkConst ``RExpr.nat) (mkRawNatLit n), ⟨n, n⟩)

private def rexprAdd (a b : Expr × MetaBounds) : Expr × MetaBounds :=
  (mkApp2 (mkConst ``RExpr.add) a.1 b.1, ⟨a.2.lo + b.2.lo, a.2.hi + b.2.hi⟩)

private def rexprMul (a b : Expr × MetaBounds) : Expr × MetaBounds :=
  (mkApp2 (mkConst ``RExpr.mul) a.1 b.1, metaEvalMul a.2 b.2)

private def rexprDiv (a b : Expr × MetaBounds) : Expr × MetaBounds :=
  let bounds := if a.2.lo ≥ 0 && b.2.lo > 0 then ⟨a.2.lo / b.2.hi, a.2.hi / b.2.lo⟩
                else ⟨-1, 1⟩
  (mkApp2 (mkConst ``RExpr.div) a.1 b.1, bounds)

private def rexprIteZero (c t e : Expr × MetaBounds) : Expr × MetaBounds :=
  let bounds := if c.2.lo > 0 then e.2
                else if c.2.lo == 0 && c.2.hi == 0 then t.2
                else ⟨min t.2.lo e.2.lo, max t.2.hi e.2.hi⟩
  (mkApp3 (mkConst ``RExpr.iteZero) c.1 t.1 e.1, bounds)

private def rexprExpMulLogSub (α x c : Expr × MetaBounds) (αVal : ℚ) :
    Expr × MetaBounds :=
  let n := αVal.num.toNat
  let xPowBounds : MetaBounds :=
    if n == 1 then x.2 else ⟨x.2.lo ^ n, x.2.hi ^ n⟩
  let expFactorBounds : MetaBounds :=
    let lo_arg := -(αVal * c.2.hi)
    let hi_arg := -(αVal * c.2.lo)
    if lo_arg == 0 && hi_arg == 0 then ⟨1, 1⟩
    else ⟨(Linglib.Interval.expPoint lo_arg).lo,
          (Linglib.Interval.expPoint hi_arg).hi⟩
  (mkApp3 (mkConst ``RExpr.expMulLogSub) α.1 x.1 c.1,
   metaEvalMul xPowBounds expFactorBounds)

/-- Build a right-fold sum RExpr matching Finset.sum's reduction.
    Finset.sum reduces via Multiset.fold → Multiset.foldr → List.foldr,
    producing `a₀ + (a₁ + (... + (aₙ₋₁ + 0)))`. -/
private def rexprSum (items : Array (Expr × MetaBounds)) : Expr × MetaBounds :=
  items.foldr (init := rexprNat 0) fun item acc => rexprAdd item acc

/-- Build policy RExpr: iteZero(total, 0, div(score, total)). -/
private def rexprPolicy (score total : Expr × MetaBounds) : Expr × MetaBounds :=
  rexprIteZero total (rexprNat 0) (rexprDiv score total)

-- ============================================================================
-- S1 Score Pattern Detection
-- ============================================================================

/-- Detected s1Score pattern. -/
private inductive S1Pattern where
  | beliefAction (costLambda : Expr)
  | beliefBased

/-- Strip n lambda binders. -/
private def stripLambdas (e : Expr) (n : ℕ) : Option (Array Expr × Expr) := Id.run do
  let mut current := e
  let mut types : Array Expr := #[]
  for _ in List.range n do
    if !current.isLambda then return none
    types := types.push current.bindingDomain!
    current := current.bindingBody!
  return some (types, current)

/-- Detect s1Score pattern from the whnf'd lambda body.
    Expects 5 binders: l0 (#4), α (#3), l (#2), w (#1), u (#0). -/
private def detectS1Pattern (s1ScoreLambda : Expr) : Option S1Pattern :=
  match stripLambdas s1ScoreLambda 5 with
  | none => none
  | some (_, body) =>
    let fn := body.getAppFn
    if fn.isConstOf ``Real.rpow then
      some .beliefBased
    else if fn.isConstOf ``ite then
      let args := body.getAppArgs
      if args.size < 5 then none
      else
        let elseBr := args[4]!
        let expFn := elseBr.getAppFn
        if !expFn.isConstOf ``Real.exp then none
        else if elseBr.getAppArgs.isEmpty then none
        else
          let inner := elseBr.getAppArgs[0]!
          let mulArgs := inner.getAppArgs
          let subExpr := if mulArgs.size ≥ 6 then mulArgs[5]!
                         else if mulArgs.size ≥ 4 then mulArgs[3]!
                         else inner
          let subArgs := subExpr.getAppArgs
          let costExpr := if subArgs.size ≥ 6 then subArgs[5]!
                          else if subArgs.size ≥ 4 then subArgs[3]!
                          else subExpr
          some (.beliefAction costExpr)
    else none

-- ============================================================================
-- RSA Builder Core
-- ============================================================================

/-- Stored state for a built RSA model — all layer RExprs indexed by (l, u, w). -/
structure RSABuildResult where
  nU : ℕ
  nW : ℕ
  nL : ℕ
  /-- L1.score(u, w): index u * nW + w -/
  l1Scores : Array (Expr × MetaBounds)
  /-- L1.totalScore(u): index u -/
  l1Totals : Array (Expr × MetaBounds)

-- ============================================================================
-- Persistent Build Cache
-- ============================================================================

/-- Module-scope cache for RSA build results. Keyed by config expression hash.
    Avoids rebuilding the full layer stack (L0→S1→L1) when the same RSAConfig
    is used across multiple theorems in the same file. -/
initialize persistentBuildCache : IO.Ref (Std.HashMap UInt64
    (Array Expr × Array Expr ×  -- allU, allW
     RSABuildResult)) ←
  IO.mkRef ∅

/-- Build the full RSA layer stack and return L1 scores/totals. -/
private def buildRSALayers (cache : ReifyCache) (cfg : Expr)
    (allU allW allL : Array Expr) (s1Pattern : S1Pattern)
    (αRExpr : Expr × MetaBounds) (αVal : ℚ) : MetaM RSABuildResult := do
  let nU := allU.size
  let nW := allW.size
  let nL := allL.size

  -- Get meaning lambda (unfold ONCE, reuse for all leaves)
  let meaningExpr ← mkAppM ``RSA.RSAConfig.meaning #[cfg]
  let meaningLambda ← whnf meaningExpr
  let initialExpr ← mkAppM ``RSA.RSAConfig.initial #[cfg]

  -- Pre-compute prior RExprs for each w
  let mut worldPriors : Array (Expr × MetaBounds) := #[]
  for w in allW do
    let e ← mkAppM ``RSA.RSAConfig.worldPrior #[cfg, w]
    worldPriors := worldPriors.push (← reifyToRExpr cache e maxDepth)

  -- Pre-compute latentPrior RExprs for each (w, l)
  let mut latentPriors : Array (Expr × MetaBounds) := Array.mkEmpty (nW * nL)
  for w in allW do
    for l in allL do
      let e ← mkAppM ``RSA.RSAConfig.latentPrior #[cfg, w, l]
      latentPriors := latentPriors.push (← reifyToRExpr cache e maxDepth)

  -- Pre-compute cost RExprs for each u (beliefAction only)
  let costRExprs ← match s1Pattern with
    | .beliefAction costBody => do
      let mut costs : Array (Expr × MetaBounds) := #[]
      for u in allU do
        let costInst := costBody.instantiate1 u
        costs := costs.push (← reifyToRExpr cache costInst maxDepth)
      pure costs
    | .beliefBased => pure #[]

  -- L0 layer: evaluate meaning values and build scores/totals/policies
  -- L0.score(l, u, w) = cfg.meaning initial l u w
  -- Index: l * nU * nW + u * nW + w
  let mut l0Scores : Array (Expr × MetaBounds) := Array.mkEmpty (nL * nU * nW)
  for l in allL do
    for u in allU do
      for w in allW do
        let applied := Expr.app (Expr.app (Expr.app (Expr.app meaningLambda initialExpr) l) u) w
        let body := applied.headBeta
        l0Scores := l0Scores.push (← reifyToRExpr cache body maxDepth)

  -- L0.totalScore(l, u) = Σ_w L0.score
  let mut l0Totals : Array (Expr × MetaBounds) := Array.mkEmpty (nL * nU)
  for li in List.range nL do
    for ui in List.range nU do
      let items := (List.range nW).toArray.map fun wi => l0Scores[li * nU * nW + ui * nW + wi]!
      l0Totals := l0Totals.push (rexprSum items)

  -- L0.policy(l, u, w) = iteZero(total, 0, score/total)
  let mut l0Policies : Array (Expr × MetaBounds) := Array.mkEmpty (nL * nU * nW)
  for li in List.range nL do
    for ui in List.range nU do
      let total := l0Totals[li * nU + ui]!
      for wi in List.range nW do
        l0Policies := l0Policies.push (rexprPolicy l0Scores[li * nU * nW + ui * nW + wi]! total)

  -- S1 layer
  -- S1.score(l, w, u): index l * nW * nU + w * nU + u
  let mut s1Scores : Array (Expr × MetaBounds) := Array.mkEmpty (nL * nW * nU)
  for li in List.range nL do
    for wi in List.range nW do
      for ui in List.range nU do
        let l0p := l0Policies[li * nU * nW + ui * nW + wi]!
        let s1s := match s1Pattern with
          | .beliefAction _ =>
            rexprIteZero l0p (rexprNat 0) (rexprExpMulLogSub αRExpr l0p costRExprs[ui]! αVal)
          | .beliefBased =>
            -- beliefBased: rpow(l0policy, α) — no iteZero guard
            let n := αVal.num.toNat
            let rpowE := mkApp2 (mkConst ``RExpr.rpow) l0p.1 (mkRawNatLit n)
            let rpowB : MetaBounds :=
              if l0p.2.lo ≥ 0 then ⟨l0p.2.lo ^ n, l0p.2.hi ^ n⟩ else ⟨0, 1⟩
            (rpowE, rpowB)
        s1Scores := s1Scores.push s1s

  -- S1.totalScore(l, w) = Σ_u S1.score
  let mut s1Totals : Array (Expr × MetaBounds) := Array.mkEmpty (nL * nW)
  for li in List.range nL do
    for wi in List.range nW do
      let items := (List.range nU).toArray.map fun ui => s1Scores[li * nW * nU + wi * nU + ui]!
      s1Totals := s1Totals.push (rexprSum items)

  -- S1.policy(l, w, u) = iteZero(total, 0, score/total)
  let mut s1Policies : Array (Expr × MetaBounds) := Array.mkEmpty (nL * nW * nU)
  for li in List.range nL do
    for wi in List.range nW do
      let total := s1Totals[li * nW + wi]!
      for ui in List.range nU do
        s1Policies := s1Policies.push (rexprPolicy s1Scores[li * nW * nU + wi * nU + ui]! total)

  -- L1 layer
  -- L1.score(u, w) = worldPrior(w) * Σ_l latentPrior(w,l) * S1.policy(l,w,u)
  let mut l1Scores : Array (Expr × MetaBounds) := Array.mkEmpty (nU * nW)
  for ui in List.range nU do
    for wi in List.range nW do
      let mut innerTerms : Array (Expr × MetaBounds) := Array.mkEmpty nL
      for li in List.range nL do
        let lp := latentPriors[wi * nL + li]!
        let s1p := s1Policies[li * nW * nU + wi * nU + ui]!
        innerTerms := innerTerms.push (rexprMul lp s1p)
      let l1Score := rexprMul worldPriors[wi]! (rexprSum innerTerms)
      l1Scores := l1Scores.push l1Score

  -- L1.totalScore(u) = Σ_w L1.score(u, w)
  let mut l1Totals : Array (Expr × MetaBounds) := Array.mkEmpty nU
  for ui in List.range nU do
    let items := (List.range nW).toArray.map fun wi => l1Scores[ui * nW + wi]!
    l1Totals := l1Totals.push (rexprSum items)

  return { nU, nW, nL, l1Scores, l1Totals }

-- ============================================================================
-- Config Detection (moved from AlgebraicReify)
-- ============================================================================

/-- Scan an expression tree for RSA.RSAConfig.L1agent applied to a cfg argument.
    Returns the cfg Expr if found. -/
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
    if fn.isConstOf ``HMul.hMul && args.size ≥ 6 then
      if let some cfg ← findL1AgentCfg args[4]! (depth - 1) then
        return some cfg
      if let some cfg ← findL1AgentCfg args[5]! (depth - 1) then
        return some cfg
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

/-- Try to build RExpr trees for an RSA comparison, bypassing the generic reifier.
    Returns `(lhsRExpr, lhsBounds, rhsRExpr, rhsBounds)` on success. -/
def tryRSABuild (cache : ReifyCache) (activeLhs activeRhs : Expr)
    : TacticM (Option (Expr × MetaBounds × Expr × MetaBounds)) := do
  let t0 ← IO.monoMsNow

  -- Detect RSAConfig from the expression
  let some cfg ← findL1AgentCfg activeLhs | return none
  if let some cfg2 ← findL1AgentCfg activeRhs then
    unless ← isDefEq cfg cfg2 do return none

  -- Extract types and enumerate elements
  let cfgType ← whnf (← inferType cfg)
  let cfgArgs := cfgType.getAppArgs
  unless cfgArgs.size ≥ 2 do return none
  let U := cfgArgs[0]!
  let W := cfgArgs[1]!
  let L ← whnf (← mkAppM ``RSA.RSAConfig.Latent #[cfg])

  let (_, allU) ← getFiniteElems U
  let (_, allW) ← getFiniteElems W
  let (_, allL) ← getFiniteElems L
  let nU := allU.size
  let nW := allW.size
  let nL := allL.size

  -- Only use builder for models large enough to benefit
  if nL * nU * nW < 500 then return none

  -- Check persistent build cache
  let cfgHash := hash cfg
  let cachedMap ← persistentBuildCache.get
  let cached? : Option (Array Expr × Array Expr × RSABuildResult) :=
    match cachedMap[cfgHash]? with
    | some (cachedU, cachedW, cachedResult) =>
      if cachedU.size == nU && cachedW.size == nW && cachedResult.nL == nL then
        some (cachedU, cachedW, cachedResult)
      else none
    | none => none

  let (result, allU, allW) ← match cached? with
    | some (cachedU, cachedW, cachedResult) => do
      let t1 ← IO.monoMsNow
      logInfo m!"rsa_predict: [builder] cache hit ({t1 - t0}ms), |U|={nU} |W|={nW} |L|={nL}"
      pure (cachedResult, cachedU, cachedW)
    | none => do
      -- Detect s1Score pattern
      let s1ScoreExpr ← whnf (← mkAppM ``RSA.RSAConfig.s1Score #[cfg])
      let some s1Pattern := detectS1Pattern s1ScoreExpr | return none

      -- Get α
      let αExpr ← mkAppM ``RSA.RSAConfig.α #[cfg]
      let (αRExpr, αBounds) ← reifyToRExpr cache αExpr maxDepth
      unless αBounds.lo == αBounds.hi && αBounds.lo > 0 && αBounds.lo.den == 1 do return none
      let αVal := αBounds.lo

      logInfo m!"rsa_predict: [builder] detected RSA, |U|={nU} |W|={nW} |L|={nL}"

      -- Build the full layer stack
      let result ← buildRSALayers cache cfg allU allW allL s1Pattern (αRExpr, αBounds) αVal

      let t1 ← IO.monoMsNow
      logInfo m!"rsa_predict: [builder] layers built ({t1 - t0}ms)"

      -- Store in persistent cache
      persistentBuildCache.modify fun m => m.insert cfgHash (allU, allW, result)

      pure (result, allU, allW)

  -- Now resolve the specific expressions requested.
  -- After denom cancel, activeLhs/activeRhs can be:
  --   (a) Core.RationalAction.score L1agent u w  (same-utterance)
  --   (b) HMul.hMul (score u₁ w) (totalScore u₂)  (cross-utterance)

  -- Resolve a single score/totalScore expression to its builder RExpr.
  let resolveScoreOrTotal (e : Expr) : MetaM (Option (Expr × MetaBounds)) := do
    let mut current := e
    for _ in List.range 10 do
      let fn := current.getAppFn
      let args := current.getAppArgs
      if fn.isConstOf ``Core.RationalAction.score && args.size ≥ 6 then
        let s := args[4]!  -- stimulus (u for L1)
        let a := args[5]!  -- action (w for L1)
        let mut ui? : Option ℕ := none
        let mut wi? : Option ℕ := none
        for i in List.range nU do
          if ← isDefEq s allU[i]! then ui? := some i; break
        for i in List.range nW do
          if ← isDefEq a allW[i]! then wi? := some i; break
        match ui?, wi? with
        | some ui, some wi => return some result.l1Scores[ui * nW + wi]!
        | _, _ => return none
      if fn.isConstOf ``Core.RationalAction.totalScore && args.size ≥ 5 then
        let s := args[4]!  -- stimulus (u for L1)
        let mut ui? : Option ℕ := none
        for i in List.range nU do
          if ← isDefEq s allU[i]! then ui? := some i; break
        match ui? with
        | some ui => return some result.l1Totals[ui]!
        | none => return none
      if let some e' ← unfoldDefinition? current then
        current := e'.headBeta
      else break
    return none

  -- Resolve an expression: either HMul (cross-product) or direct score/totalScore.
  let resolveExpr (e : Expr) : MetaM (Option (Expr × MetaBounds)) := do
    if isAppOfMin e ``HMul.hMul 6 then
      let mulArgs := e.getAppArgs
      let some l ← resolveScoreOrTotal mulArgs[4]! | return none
      let some r ← resolveScoreOrTotal mulArgs[5]! | return none
      return some (rexprMul l r)
    resolveScoreOrTotal e

  let some lhsResult ← resolveExpr activeLhs | return none
  let some rhsResult ← resolveExpr activeRhs | return none

  -- Populate cache boundsMap entries for DAG dead-branch elimination.
  -- Insert all intermediate RExpr→bounds into the cache.
  -- Key doesn't matter for boundsMap (only rexpr.hash → bounds is used).
  for entry in result.l1Scores do
    cache.modify fun m => m.insert entry.1 entry
  for entry in result.l1Totals do
    cache.modify fun m => m.insert entry.1 entry

  let t2 ← IO.monoMsNow
  logInfo m!"rsa_predict: [builder] resolved expressions ({t2 - t0}ms total)"
  return some (lhsResult.1, lhsResult.2, rhsResult.1, rhsResult.2)

-- ============================================================================
-- Generic L1 Builder (for S2 and other composite goals)
-- ============================================================================

/-- Build L1 and L1_latent RExprs for an RSAConfig by:
    1. Instantiating the s1Score lambda body directly (bypassing S1→S1agent→policy chain)
    2. Reifying each instantiated body via the generic reifier
    3. Assembling S1→L1 layers algebraically

    This avoids the expensive whnf chain through `cfg.S1 l w u →
    (S1agent l).policy w u → RationalAction.policy → iteZero → Finset.sum`.
    Instead, we substitute concrete L0 policy function + args into the s1Score body
    and reify the resulting simple arithmetic expression (ite/exp/log/Finset.sum).

    Seeds the reification cache with L1/L1_latent values so the generic reifier
    finds them immediately when processing S2Utility or similar composite expressions. -/
def buildAndSeedL1 (cache : ReifyCache) (cfg : Expr) : TacticM Unit := do
  let t0 ← IO.monoMsNow

  -- Check persistent build cache (reuse if same config was already built)
  let cfgHash := hash cfg
  let cachedMap ← persistentBuildCache.get
  if cachedMap.contains cfgHash then
    logInfo m!"rsa_predict: [generic-L1] cache hit"
    return

  -- Extract types and enumerate elements
  let cfgType ← whnf (← inferType cfg)
  let cfgArgs := cfgType.getAppArgs
  unless cfgArgs.size ≥ 2 do return
  let U := cfgArgs[0]!
  let W := cfgArgs[1]!
  let L ← whnf (← mkAppM ``RSA.RSAConfig.Latent #[cfg])

  let (_, allU) ← getFiniteElems U
  let (_, allW) ← getFiniteElems W
  let (_, allL) ← getFiniteElems L
  let nU := allU.size
  let nW := allW.size
  let nL := allL.size

  -- Only for models large enough to benefit
  if nL * nU * nW < 500 then return

  logInfo m!"rsa_predict: [generic-L1] building, |U|={nU} |W|={nW} |L|={nL}"

  -- Get s1Score lambda body (whnf once to expose the lambda)
  let s1ScoreLambda ← whnf (← mkAppM ``RSA.RSAConfig.s1Score #[cfg])
  unless s1ScoreLambda.isLambda do
    logInfo m!"rsa_predict: [generic-L1] s1Score is not a lambda, skipping"
    return

  -- Get α as Lean expression (for substitution into s1Score body)
  let αLeanExpr ← whnf (← mkAppM ``RSA.RSAConfig.α #[cfg])

  -- Pre-compute priors via generic reifier (small expressions, fast)
  let mut worldPriors : Array (Expr × MetaBounds) := #[]
  for w in allW do
    worldPriors := worldPriors.push
      (← reifyToRExpr cache (← mkAppM ``RSA.RSAConfig.worldPrior #[cfg, w]) maxDepth)

  let mut latentPriors : Array (Expr × MetaBounds) := Array.mkEmpty (nW * nL)
  for w in allW do
    for l in allL do
      latentPriors := latentPriors.push
        (← reifyToRExpr cache (← mkAppM ``RSA.RSAConfig.latentPrior #[cfg, w, l]) maxDepth)

  let t1 ← IO.monoMsNow

  -- Build S1 scores by instantiating s1Score body for each (l, w, u).
  -- Instead of reifyToRExpr(cfg.S1 l w u) which goes through the slow
  -- S1→S1agent→policy→Finset.sum chain, we:
  -- 1. Get the L0 policy function expression: (L0agent cfg l).policy
  -- 2. Substitute it + concrete α,l,w,u into the s1Score lambda
  -- 3. headBeta to get the body with all args substituted
  -- 4. reifyToRExpr on the body (simple arithmetic, L0 evals cached)
  let mut s1Scores : Array (Expr × MetaBounds) := Array.mkEmpty (nL * nW * nU)
  for l in allL do
    let l0Agent ← mkAppM ``RSA.RSAConfig.L0agent #[cfg, l]
    let l0PolicyFn ← mkAppM ``Core.RationalAction.policy #[l0Agent]
    for w in allW do
      for u in allU do
        let body := s1ScoreLambda
          |>.app l0PolicyFn |>.app αLeanExpr |>.app l |>.app w |>.app u
          |>.headBeta
        s1Scores := s1Scores.push (← reifyToRExpr cache body maxDepth)

  let t2 ← IO.monoMsNow
  logInfo m!"rsa_predict: [generic-L1] S1 cells ({nL*nW*nU}) reified ({t2-t1}ms)"

  -- S1 totals: Σ_u s1Score(l, w, u) for each (l, w)
  let mut s1Totals : Array (Expr × MetaBounds) := Array.mkEmpty (nL * nW)
  for li in List.range nL do
    for wi in List.range nW do
      let items := (List.range nU).toArray.map fun ui =>
        s1Scores[li * nW * nU + wi * nU + ui]!
      s1Totals := s1Totals.push (rexprSum items)

  -- S1 policies: iteZero(total, 0, score/total)
  let mut s1Policies : Array (Expr × MetaBounds) := Array.mkEmpty (nL * nW * nU)
  for li in List.range nL do
    for wi in List.range nW do
      let total := s1Totals[li * nW + wi]!
      for ui in List.range nU do
        s1Policies := s1Policies.push
          (rexprPolicy s1Scores[li * nW * nU + wi * nU + ui]! total)

  -- L1 scores: worldPrior(w) * Σ_l latentPrior(w,l) * S1policy(l,w,u)
  let mut l1Scores : Array (Expr × MetaBounds) := Array.mkEmpty (nU * nW)
  for ui in List.range nU do
    for wi in List.range nW do
      let mut innerTerms : Array (Expr × MetaBounds) := Array.mkEmpty nL
      for li in List.range nL do
        let lp := latentPriors[wi * nL + li]!
        let s1p := s1Policies[li * nW * nU + wi * nU + ui]!
        innerTerms := innerTerms.push (rexprMul lp s1p)
      l1Scores := l1Scores.push (rexprMul worldPriors[wi]! (rexprSum innerTerms))

  -- L1 totals: Σ_w L1score(u, w)
  let mut l1Totals : Array (Expr × MetaBounds) := Array.mkEmpty nU
  for ui in List.range nU do
    let items := (List.range nW).toArray.map fun wi => l1Scores[ui * nW + wi]!
    l1Totals := l1Totals.push (rexprSum items)

  -- Seed cache with L1 policy values: L1(u, w) = iteZero(total, 0, score/total)
  for ui in List.range nU do
    for wi in List.range nW do
      let l1Policy := rexprPolicy l1Scores[ui * nW + wi]! l1Totals[ui]!
      let key ← mkAppM ``RSA.RSAConfig.L1 #[cfg, allU[ui]!, allW[wi]!]
      cache.modify fun m => m.insert key l1Policy

  -- Seed cache with L1_latent policy values
  -- L1_latent score(u, l) = Σ_w worldPrior(w) * latentPrior(w,l) * S1policy(l,w,u)
  -- L1_latent total(u) = same as L1 total (marginal over all l and w)
  for ui in List.range nU do
    for li in List.range nL do
      let mut latentTerms : Array (Expr × MetaBounds) := Array.mkEmpty nW
      for wi in List.range nW do
        let wp := worldPriors[wi]!
        let lp := latentPriors[wi * nL + li]!
        let s1p := s1Policies[li * nW * nU + wi * nU + ui]!
        latentTerms := latentTerms.push (rexprMul wp (rexprMul lp s1p))
      let latentScore := rexprSum latentTerms
      let l1LatentPolicy := rexprPolicy latentScore l1Totals[ui]!
      let key ← mkAppM ``RSA.RSAConfig.L1_latent #[cfg, allU[ui]!, allL[li]!]
      cache.modify fun m => m.insert key l1LatentPolicy

  -- Store in persistent cache to avoid rebuilding for subsequent theorems
  let result : RSABuildResult := { nU, nW, nL, l1Scores, l1Totals }
  persistentBuildCache.modify fun m => m.insert cfgHash (allU, allW, result)

  let t3 ← IO.monoMsNow
  logInfo m!"rsa_predict: [generic-L1] complete ({t3-t0}ms, {nU*nW} L1 + {nU*nL} L1_latent values seeded)"

/-- Scan an expression for RSA.RSAConfig.L1 or L1_latent function heads.
    Returns the config from the first match, or none. -/
private partial def findL1Config (e : Expr) (depth : ℕ := 20) : Option Expr :=
  if depth == 0 then none
  else
    let fn := e.getAppFn
    let args := e.getAppArgs
    -- Direct L1 or L1_latent reference
    if (fn.isConstOf ``RSA.RSAConfig.L1 || fn.isConstOf ``RSA.RSAConfig.L1_latent) then
      -- cfg is the first explicit arg (after implicit type/instance args)
      -- L1: {U} {W} [DecEq U] [Fin U] [DecEq W] [Fin W] cfg u w → cfg at args.size - 3
      if args.size ≥ 3 then some args[args.size - 3]!
      else none
    else
      -- Recurse into sub-expressions
      args.findSome? (findL1Config · (depth - 1))

/-- Pre-seed the reification cache with L1/L1_latent values for RSAConfig
    references found in the expression. Call before reifyToRExpr to avoid
    expensive whnf of nested L1 computations (e.g., in S2Utility). -/
def tryPreseedL1 (cache : ReifyCache) (lhs rhs : Expr) : TacticM Unit := do
  -- whnf both sides to expose L1 references
  let lhs' ← whnf lhs
  let rhs' ← whnf rhs
  -- Find config from either side
  let cfg? := findL1Config lhs' <|> findL1Config rhs'
  let some cfg := cfg? | return
  -- Build and seed
  buildAndSeedL1 cache cfg

end Linglib.Tactics.RSAPredict
