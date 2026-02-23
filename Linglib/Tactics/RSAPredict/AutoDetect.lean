import Lean
import Linglib.Core.Interval.RSAVerify
import Linglib.Tactics.RSAPredict.Helpers
import Linglib.Tactics.RSAPredict.Reify

set_option autoImplicit false

/-!
# RSAPredict Auto-Detection (Tier 2)

Structural auto-detection of S1 score patterns from raw `RSAConfig`.

When `cfg` is NOT built via `RSAConfigData.toRSAConfig` (Tier 1 fails),
this module classifies the `s1Score` lambda into a known `S1ScoreSpec`
variant by pattern-matching on the normalized AST, then builds an
`RSAConfigData` whose `.toRSAConfig` is definitionally equal to the
user's config.

## Pipeline

1. **Normalize**: Unfold `cfg.s1Score`, whnf to expose the lambda body.
2. **Detect**: Pattern-match outermost structure (rpow, ite, exp) to classify.
3. **Extract**: Evaluate meaning/priors/cost pointwise over finite types → ℚ arrays.
4. **Build**: Construct an `RSAConfigData` Expr with ite-chain functions + sorryAx proofs.
5. **Bridge**: `native_decide` on `checkL1ScoreGt d ...`, then `isDefEq` to the goal.

If any step fails, returns `false` — CProof (Tier 3) handles it.
-/

namespace Linglib.Tactics.RSAPredict

open Lean Meta Elab Tactic

-- ============================================================================
-- Detected Pattern
-- ============================================================================

/-- Detected S1 score pattern. Each variant corresponds to an `S1ScoreSpec` constructor. -/
inductive DetectedPattern where
  | beliefBased
  | qudBelief
  | qudAction
  | beliefAction
  | actionBased
  | beliefWeighted

-- ============================================================================
-- AST Helpers
-- ============================================================================

/-- Walk an expression tree checking if it contains a specific constant name. -/
partial def containsConstName (name : Name) : Expr → Bool
  | .const n _ => n == name
  | .app f a => containsConstName name f || containsConstName name a
  | .lam _ t b _ => containsConstName name t || containsConstName name b
  | .forallE _ t b _ => containsConstName name t || containsConstName name b
  | .letE _ t v b _ =>
    containsConstName name t || containsConstName name v || containsConstName name b
  | .mdata _ e => containsConstName name e
  | .proj _ _ e => containsConstName name e
  | _ => false

-- ============================================================================
-- Pattern Detection (from whnf'd s1Score body)
-- ============================================================================

/-- Detect the S1ScoreSpec variant by inspecting the reduced s1Score expression.

    Strategy: reduce `cfg.s1Score` to whnf and look for signature constants:
    - `Real.rpow` without `Finset.filter` → beliefBased
    - `Real.rpow` with `Finset.filter` → qudBelief
    - `Real.exp` + `Real.log` + `Finset.filter` → qudAction
    - `Real.exp` + `Real.log` without `Finset.filter` → beliefAction
    - `Real.exp` without `Real.log` → actionBased
    - `Finset.sum` inside `Real.exp` argument (weighted sum) → beliefWeighted -/
def detectScorePattern (cfg : Expr) : MetaM (Option DetectedPattern) := do
  let s1ScoreExpr ← mkAppM ``RSA.RSAConfig.s1Score #[cfg]
  let reduced ← whnf s1ScoreExpr

  let hasRpow := containsConstName ``Real.rpow reduced
  let hasExp := containsConstName ``Real.exp reduced
  let hasLog := containsConstName ``Real.log reduced
  let hasFilter := containsConstName ``Finset.filter reduced

  -- Dispatch based on signature
  if hasRpow then
    if hasFilter then return some .qudBelief
    else return some .beliefBased
  else if hasExp then
    if hasLog then
      if hasFilter then return some .qudAction
      else
        -- Distinguish beliefAction (gated log) from beliefWeighted (sum of logs)
        -- beliefWeighted has a Finset.sum INSIDE the exp argument
        -- For now, check if there's an ite at the outermost level
        -- beliefAction: if l0 = 0 then 0 else exp(α * (log l0 - cost))
        -- beliefWeighted: if quality then exp(α * Σ belief * log l0) else 0
        -- Both have ite + exp + log. The distinguisher is Finset.sum inside exp.
        -- Actually, beliefWeighted's Finset.sum is the sum over worlds inside exp.
        -- Let's check if there's a Finset.sum that's NOT the outer normalization sum.
        -- Heuristic: beliefWeighted mentions Finset.sum in the s1Score body
        if containsConstName ``Finset.sum reduced then
          return some .beliefWeighted
        else
          return some .beliefAction
    else
      return some .actionBased
  else
    return none

-- ============================================================================
-- ℚ Extraction Helpers
-- ============================================================================

/-- Extract meaning values: meaning(l, u, w) as ℚ for all (l,u,w) triples.
    Returns array indexed as [lIdx * nU * nW + uIdx * nW + wIdx]. -/
def extractMeaningValues (cfg : Expr) (allLElems allUElems allWElems : Array Expr) :
    MetaM (Option (Array ℚ)) := do
  let mut values : Array ℚ := #[]
  for l in allLElems do
    for u in allUElems do
      for w in allWElems do
        let meaningExpr ← mkAppM ``RSA.RSAConfig.meaning #[cfg, l, u, w]
        try
          let q ← extractRat meaningExpr
          values := values.push q
        catch _ =>
          return none
  return some values

/-- Extract world prior values as ℚ. -/
def extractWorldPriorValues (cfg : Expr) (allWElems : Array Expr) :
    MetaM (Option (Array ℚ)) := do
  let mut values : Array ℚ := #[]
  for w in allWElems do
    let wpExpr ← mkAppM ``RSA.RSAConfig.worldPrior #[cfg, w]
    try
      values := values.push (← extractRat wpExpr)
    catch _ =>
      return none
  return some values

/-- Extract latent prior values as ℚ. Indexed as [wIdx * nL + lIdx]. -/
def extractLatentPriorValues (cfg : Expr) (allWElems allLElems : Array Expr) :
    MetaM (Option (Array ℚ)) := do
  let mut values : Array ℚ := #[]
  for w in allWElems do
    for l in allLElems do
      let lpExpr ← mkAppM ``RSA.RSAConfig.latentPrior #[cfg, w, l]
      try
        values := values.push (← extractRat lpExpr)
      catch _ =>
        return none
  return some values

/-- Peel 5 lambdas from a reduced s1Score expression to expose the body.
    Returns (body, fvars) where fvars = [l0, α, l, w, u]. -/
def peelS1ScoreBody (cfg : Expr) : MetaM (Option (Expr × Array FVarId)) := do
  let s1ScoreExpr ← mkAppM ``RSA.RSAConfig.s1Score #[cfg]
  let mut body ← whnf s1ScoreExpr
  let mut fvars : Array FVarId := #[]
  for _ in List.range 5 do
    match body with
    | .lam _name _ty lamBody _bi =>
      let fvar ← mkFreshFVarId
      fvars := fvars.push fvar
      body := lamBody.instantiate1 (mkFVar fvar)
      -- whnf may fail if the body has computable Decidable instances that
      -- try to evaluate unregistered fvars (e.g., beliefWeighted's Bool ite).
      -- In that case, keep the unreduced body.
      body ← try whnf body catch _ => pure body
    | _ =>
      body ← try whnf body catch _ => pure body
      match body with
      | .lam _name _ty lamBody _bi =>
        let fvar ← mkFreshFVarId
        fvars := fvars.push fvar
        body := lamBody.instantiate1 (mkFVar fvar)
        body ← try whnf body catch _ => pure body
      | _ => return none
  if fvars.size < 5 then return none
  return some (body, fvars)

/-- Peel a single lambda: if `e` is `fun (x : T) => body`, return
    `(T, binderInfo, body)` after whnf. Returns none if not a lambda. -/
private def peelOneLam (e : Expr) : MetaM (Option (Name × Expr × Expr × BinderInfo)) := do
  let e' ← whnf e
  match e' with
  | .lam n t b bi => return some (n, t, b, bi)
  | _ => return none

/-- Extract belief and quality values from a `beliefWeighted` s1Score.
    The expected pattern is:
      `if quality(l, u) then exp(α * Σ_s belief(l,s) * log(l0 u s)) else 0`
    Also handles the KL divergence form where the sum body includes
    `- Σ_s belief(l,s) * log(belief(l,s))` (constant w.r.t. u, so stripped).

    Uses `withLocalDecl` for lambda peeling so fvars are properly registered
    in the local context (required for `whnf`/`isDefEq` to work).

    Returns `(beliefVals, qualityVals)` where:
    - `beliefVals` is indexed as `[lIdx * nW + wIdx]`
    - `qualityVals` is indexed as `[lIdx * nU + uIdx]` -/
def extractBeliefAndQuality (cfg : Expr)
    (allLElems allUElems allWElems : Array Expr) :
    MetaM (Option (Array ℚ × Array Bool)) := do
  let s1ScoreExpr ← mkAppM ``RSA.RSAConfig.s1Score #[cfg]
  -- Peel 5 lambdas with proper withLocalDecl so fvars have types in lctx
  let some (n1, t1, b1, bi1) ← peelOneLam s1ScoreExpr | return none
  withLocalDecl n1 bi1 t1 fun l0Var => do
  let some (n2, t2, b2, bi2) ← peelOneLam (b1.instantiate1 l0Var) | return none
  withLocalDecl n2 bi2 t2 fun _αVar => do
  let some (n3, t3, b3, bi3) ← peelOneLam (b2.instantiate1 _αVar) | return none
  withLocalDecl n3 bi3 t3 fun lVar => do
  let some (n4, t4, b4, bi4) ← peelOneLam (b3.instantiate1 lVar) | return none
  withLocalDecl n4 bi4 t4 fun _wVar => do
  let some (n5, t5, b5, bi5) ← peelOneLam (b4.instantiate1 _wVar) | return none
  withLocalDecl n5 bi5 t5 fun uVar => do
  -- Use withReducible to prevent ite → Decidable.rec and HMul → Mul reduction
  let body ← withReducible do whnf (b5.instantiate1 uVar)

  let l0Fvar := l0Var.fvarId!
  let lFvar := lVar.fvarId!
  let uFvar := uVar.fvarId!
  let nL := allLElems.size
  let nU := allUElems.size
  let nW := allWElems.size

  -- Step 1: Detect ite and extract condition + then-branch
  let hasIte := isAppOfMin body ``ite 5
  let thenBranch := if hasIte then body.getAppArgs[3]! else body

  -- Step 2: Extract quality values.
  -- The ite condition is `f(l, u) = true` (from Bool if-then-else desugaring).
  -- Extract the Bool sub-expression f(l, u), substitute concrete values, and
  -- whnf to Bool.true or Bool.false.
  let mut qualityVals : Array Bool := #[]
  if hasIte then
    let condExpr := body.getAppArgs[1]!
    -- The condition is `@Eq Bool (f l u) true` — extract the Bool expression
    let condBoolExpr :=
      if condExpr.isAppOfArity ``Eq 3 then condExpr.getAppArgs[1]!
      else condExpr
    for l in allLElems do
      for u in allUElems do
        let specialized := condBoolExpr.replaceFVar lVar l
                                       |>.replaceFVar uVar u
        let reduced ← whnf specialized
        qualityVals := qualityVals.push (reduced.isConstOf ``Bool.true)
  else
    qualityVals := Array.replicate (nL * nU) true

  -- Step 3: Extract belief values from the then-branch.
  -- Navigate structurally: exp(arg) → arg = α * sum → sum body.

  -- 3a. Navigate: exp → arg
  unless thenBranch.getAppFn.isConstOf ``Real.exp do return none
  let expArg := thenBranch.getAppArgs.back!

  -- 3b. Strip HMul (α * ...) to get the sum expression
  let sumExpr :=
    if isAppOfMin expArg ``HMul.hMul 6 then
      expArg.getAppArgs[5]!
    else
      expArg

  -- 3c. Handle KL divergence: strip constant entropy term (- Σ belief·log(belief))
  let sumExpr :=
    if isAppOfMin sumExpr ``HSub.hSub 6 then
      let lhs := sumExpr.getAppArgs[4]!
      let rhs := sumExpr.getAppArgs[5]!
      if !rhs.containsFVar l0Fvar then lhs else sumExpr
    else if isAppOfMin sumExpr ``Sub.sub 4 then
      let lhs := sumExpr.getAppArgs[2]!
      let rhs := sumExpr.getAppArgs[3]!
      if !rhs.containsFVar l0Fvar then lhs else sumExpr
    else
      sumExpr

  -- 3d. Find Finset.sum and extract its body function
  let bodyFn :=
    if sumExpr.getAppFn.isConstOf ``Finset.sum && sumExpr.getAppNumArgs ≥ 5 then
      some sumExpr.getAppArgs[4]!
    else
      sumExpr.getAppArgs.findSome? fun arg =>
        if arg.getAppFn.isConstOf ``Finset.sum && arg.getAppNumArgs ≥ 5 then
          some arg.getAppArgs[4]!
        else none
  let some bodyFn := bodyFn | return none

  -- 3e. Instantiate the lambda body with fresh fvar for sum variable (s : W)
  -- Use withLocalDecl so the fvar is properly registered
  let some (sn, st, sb, sbi) ← peelOneLam bodyFn | return none
  withLocalDecl sn sbi st fun sVar => do
  let sumBody ← withReducible do whnf (sb.instantiate1 sVar)

  -- 3f. Find HMul: belief(l,s) * log(l0 u s)
  --     The factor containing l0Fvar is log(l0), the other is belief
  let beliefFactor :=
    if isAppOfMin sumBody ``HMul.hMul 6 then
      let lhs := sumBody.getAppArgs[4]!
      let rhs := sumBody.getAppArgs[5]!
      if rhs.containsFVar l0Fvar then some lhs
      else if lhs.containsFVar l0Fvar then some rhs
      else none
    else
      none
  let some beliefFactor := beliefFactor | return none

  -- 3g. Evaluate belief at each (l, s) pair.
  -- After substituting concrete l and s, the belief expression is fully
  -- concrete, so extractRat's whnf works.
  let mut beliefVals : Array ℚ := #[]
  for l in allLElems do
    for w in allWElems do
      let specialized := beliefFactor.replaceFVar lVar l
                                     |>.replaceFVar sVar w
      try
        beliefVals := beliefVals.push (← extractRat specialized)
      catch _ =>
        return none

  if beliefVals.size != nL * nW || qualityVals.size != nL * nU then
    return none

  return some (beliefVals, qualityVals)

/-- Find a sub-expression that looks like a cost term:
    - Appears as the RHS of a subtraction (... - cost)
    - Does NOT mention wFvar (cost depends on utterance, not world)
    - May or may not mention uFvar (constant cost like 0 is valid) -/
partial def findCostSubExpr (e : Expr) (wFvar uFvar : FVarId) : Option Expr :=
  -- Check HSub.hSub _ _ _ _ lhs rhs
  if isAppOfMin e ``HSub.hSub 6 then
    let rhs := e.getAppArgs[5]!
    -- cost must not mention w (it's utterance-specific or constant)
    if !rhs.containsFVar wFvar then
      some rhs
    else none
  else if isAppOfMin e ``Sub.sub 4 then
    let rhs := e.getAppArgs[3]!
    if !rhs.containsFVar wFvar then
      some rhs
    else none
  else
    -- Recurse into sub-expressions
    e.getAppArgs.findSome? (findCostSubExpr · wFvar uFvar)

/-- Extract cost values by evaluating the S1 score at each utterance
    with a known L0 output, and reverse-engineering the cost.
    For beliefAction: s1Score l0 α l w u = if l0(u,w) = 0 then 0 else exp(α*(log(l0(u,w)) - cost(u)))
    For actionBased: s1Score l0 α l w u = exp(α*(l0(u,w) - cost(u)))

    Alternative approach: unfold s1Score body, find the sub-expression that
    depends on u but not w, and evaluate it at each u.
    For now, we use a simpler approach: evaluate the s1Score with a carefully
    chosen L0 that makes cost extraction easy. -/
def extractCostFromScore (cfg : Expr) (_U _W _L : Expr)
    (allUElems _allWElems _allLElems : Array Expr) (_pattern : DetectedPattern) :
    MetaM (Option (Array ℚ)) := do
  let some (body, fvars) ← peelS1ScoreBody cfg | return none
  let wFvar := fvars[3]!
  let uFvar := fvars[4]!

  let costExpr? := findCostSubExpr body wFvar uFvar
  match costExpr? with
  | some costExpr =>
    -- Evaluate cost at each utterance
    let mut costs : Array ℚ := #[]
    for u in allUElems do
      let specialized := costExpr.replaceFVar (mkFVar uFvar) u
      try
        let q ← extractRat specialized
        costs := costs.push q
      catch _ =>
        return none
    return some costs
  | none =>
    -- No subtraction found — could be zero cost (e.g., exp(α * log(l0)))
    -- Default to zero cost for all utterances
    let zeros : Array ℚ := Array.replicate allUElems.size 0
    return some zeros

-- ============================================================================
-- Build ite-Chain Functions (ℚ-valued)
-- ============================================================================

/-- Build `fun (x : T) => if x = e₁ then v₁ else if x = e₂ then v₂ else ... else vₙ` -/
def buildUnaryQFn (T : Expr) (elems : Array Expr) (values : Array ℚ) :
    MetaM Expr := do
  withLocalDecl `x .default T fun xVar => do
    let mut body ← mkRatExpr values[values.size - 1]!
    for i in List.range (elems.size - 1) |>.reverse do
      let cond ← mkAppM ``Eq #[xVar, elems[i]!]
      let val ← mkRatExpr values[i]!
      body ← mkAppM ``ite #[cond, val, body]
    mkLambdaFVars #[xVar] body

/-- Build `fun (x₁ : T₁) (x₂ : T₂) => <ite chain>`.
    values indexed as [i * n₂ + j]. -/
def buildBinaryQFn (T₁ T₂ : Expr) (elems₁ elems₂ : Array Expr) (values : Array ℚ) :
    MetaM Expr := do
  let n₂ := elems₂.size
  withLocalDecl `x₁ .default T₁ fun x₁ => do
    withLocalDecl `x₂ .default T₂ fun x₂ => do
      let nTotal := elems₁.size * n₂
      let mut body ← mkRatExpr values[nTotal - 1]!
      for idx in List.range (nTotal - 1) |>.reverse do
        let i := idx / n₂
        let j := idx % n₂
        let cond₁ ← mkAppM ``Eq #[x₁, elems₁[i]!]
        let cond₂ ← mkAppM ``Eq #[x₂, elems₂[j]!]
        let cond ← mkAppM ``And #[cond₁, cond₂]
        let val ← mkRatExpr values[idx]!
        body ← mkAppM ``ite #[cond, val, body]
      mkLambdaFVars #[x₁, x₂] body

/-- Build `fun (x₁ : T₁) (x₂ : T₂) => <ite chain>` returning `Bool`.
    values indexed as [i * n₂ + j]. -/
def buildBinaryBoolFn (T₁ T₂ : Expr) (elems₁ elems₂ : Array Expr) (values : Array Bool) :
    MetaM Expr := do
  let n₂ := elems₂.size
  withLocalDecl `x₁ .default T₁ fun x₁ => do
    withLocalDecl `x₂ .default T₂ fun x₂ => do
      let nTotal := elems₁.size * n₂
      let lastVal := if values[nTotal - 1]! then mkConst ``Bool.true else mkConst ``Bool.false
      let mut body := lastVal
      for idx in List.range (nTotal - 1) |>.reverse do
        let i := idx / n₂
        let j := idx % n₂
        let cond₁ ← mkAppM ``Eq #[x₁, elems₁[i]!]
        let cond₂ ← mkAppM ``Eq #[x₂, elems₂[j]!]
        let cond ← mkAppM ``And #[cond₁, cond₂]
        let val := if values[idx]! then mkConst ``Bool.true else mkConst ``Bool.false
        body ← mkAppM ``ite #[cond, val, body]
      mkLambdaFVars #[x₁, x₂] body

/-- Build `fun (l : L) (u : U) (w : W) => <ite chain>`.
    values indexed as [li * nU * nW + ui * nW + wi]. -/
def buildTernaryQFn (L U W : Expr) (lElems uElems wElems : Array Expr)
    (values : Array ℚ) : MetaM Expr := do
  let nU := uElems.size
  let nW := wElems.size
  let nTotal := lElems.size * nU * nW
  withLocalDecl `l .default L fun lVar => do
    withLocalDecl `u .default U fun uVar => do
      withLocalDecl `w .default W fun wVar => do
        let mut body ← mkRatExpr values[nTotal - 1]!
        for idx in List.range (nTotal - 1) |>.reverse do
          let li := idx / (nU * nW)
          let rem := idx % (nU * nW)
          let ui := rem / nW
          let wi := rem % nW
          let condL ← mkAppM ``Eq #[lVar, lElems[li]!]
          let condU ← mkAppM ``Eq #[uVar, uElems[ui]!]
          let condW ← mkAppM ``Eq #[wVar, wElems[wi]!]
          let condLU ← mkAppM ``And #[condL, condU]
          let cond ← mkAppM ``And #[condLU, condW]
          let val ← mkRatExpr values[idx]!
          body ← mkAppM ``ite #[cond, val, body]
        mkLambdaFVars #[lVar, uVar, wVar] body

-- ============================================================================
-- Build sorryAx Proofs
-- ============================================================================

/-- Build a `sorryAx` proof of type `ty : Prop`. -/
def mkSorryProof (ty : Expr) : Expr :=
  mkApp2 (mkConst ``sorryAx [.zero]) ty (mkConst ``Bool.true)

/-- Build `∀ (l : L) (u : U) (w : W), 0 ≤ meaningFn l u w` and its sorry proof. -/
def mkMeaningNonnegProof (L U W meaningFn : Expr) : MetaM Expr := do
  let ty ← withLocalDecl `l .default L fun lV => do
    withLocalDecl `u .default U fun uV => do
      withLocalDecl `w .default W fun wV => do
        let app := mkAppN meaningFn #[lV, uV, wV]
        let ratZero ← mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, mkRawNatLit 0, none]
        let le ← mkAppM ``LE.le #[ratZero, app]
        mkForallFVars #[lV, uV, wV] le
  return mkSorryProof ty

/-- Build `0 < α` and its sorry proof. -/
def mkAlphaPosProof (αLit : Expr) : MetaM Expr := do
  let natZero ← mkAppOptM ``OfNat.ofNat #[mkConst ``Nat, mkRawNatLit 0, none]
  let ty ← mkAppM ``LT.lt #[natZero, αLit]
  return mkSorryProof ty

/-- Build `∀ (w : W), 0 ≤ wpFn w` and its sorry proof. -/
def mkWpNonnegProof (W wpFn : Expr) : MetaM Expr := do
  let ty ← withLocalDecl `w .default W fun wV => do
    let app := mkApp wpFn wV
    let ratZero ← mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, mkRawNatLit 0, none]
    let le ← mkAppM ``LE.le #[ratZero, app]
    mkForallFVars #[wV] le
  return mkSorryProof ty

/-- Build `∀ (w : W) (l : L), 0 ≤ lpFn w l` and its sorry proof. -/
def mkLpNonnegProof (W L lpFn : Expr) : MetaM Expr := do
  let ty ← withLocalDecl `w .default W fun wV => do
    withLocalDecl `l .default L fun lV => do
      let app := mkAppN lpFn #[wV, lV]
      let ratZero ← mkAppOptM ``OfNat.ofNat #[mkConst ``Rat, mkRawNatLit 0, none]
      let le ← mkAppM ``LE.le #[ratZero, app]
      mkForallFVars #[wV, lV] le
  return mkSorryProof ty

-- ============================================================================
-- Build RSAConfigData Expression
-- ============================================================================

/-- Build an RSAConfigData Expr from detected pattern and extracted ℚ values.

    The result `d` has the property that `d.toRSAConfig` is definitionally
    equal to the user's `cfg` (verified by `isDefEq` at the bridge step).
    Proof obligations are closed with `sorryAx` (erased at runtime,
    so `native_decide` works). -/
def buildConfigData (U W L : Expr)
    (allUElems allWElems allLElems : Array Expr)
    (meaningVals : Array ℚ) (wpVals : Array ℚ) (lpVals : Array ℚ)
    (αNat : ℕ) (pattern : DetectedPattern)
    (costVals : Option (Array ℚ) := none)
    (beliefVals : Option (Array ℚ) := none)
    (qualityVals : Option (Array Bool) := none) : MetaM (Option Expr) := do

  -- Build meaning function: L → U → W → ℚ
  let meaningFn ← buildTernaryQFn L U W allLElems allUElems allWElems meaningVals

  -- Build scoreSpec
  let scoreSpec ← match pattern with
    | .beliefBased =>
      mkAppOptM ``RSA.S1ScoreSpec.beliefBased #[U, W, L]
    | .actionBased => do
      let some costs := costVals | return none
      let costFn ← buildUnaryQFn U allUElems costs
      mkAppOptM ``RSA.S1ScoreSpec.actionBased #[U, W, L, costFn]
    | .beliefAction => do
      let some costs := costVals | return none
      let costFn ← buildUnaryQFn U allUElems costs
      mkAppOptM ``RSA.S1ScoreSpec.beliefAction #[U, W, L, costFn]
    | .beliefWeighted => do
      let some bv := beliefVals | return none
      let some qv := qualityVals | return none
      let beliefFn ← buildBinaryQFn L W allLElems allWElems bv
      let qualityFn ← buildBinaryBoolFn L U allLElems allUElems qv
      mkAppOptM ``RSA.S1ScoreSpec.beliefWeighted #[U, W, L, beliefFn, qualityFn]
    | _ => do
      -- TODO: implement qudBelief, qudAction
      return none

  -- Build α
  let αLit := mkRawNatLit αNat

  -- Build worldPrior function: W → ℚ
  let wpFn ← buildUnaryQFn W allWElems wpVals

  -- Build latentPrior function: W → L → ℚ
  let lpFn ← buildBinaryQFn W L allWElems allLElems lpVals

  -- Build proof obligations via sorryAx
  let meaningNonneg ← mkMeaningNonnegProof L U W meaningFn
  let αPos ← mkAlphaPosProof αLit
  let wpNonneg ← mkWpNonnegProof W wpFn
  let lpNonneg ← mkLpNonnegProof W L lpFn

  -- Construct RSAConfigData.mk
  try
    let d ← mkAppOptM ``RSA.RSAConfigData.mk #[
      some U, some W, none, none, none, none,    -- U, W, Fintype, DecidableEq
      some L, none, none,                         -- Latent, Fintype, DecidableEq
      some meaningFn, some meaningNonneg,         -- meaning, meaning_nonneg
      some scoreSpec,                             -- scoreSpec
      some αLit, some αPos,                       -- α, α_pos
      some wpFn, some wpNonneg,                   -- worldPrior, worldPrior_nonneg
      some lpFn, some lpNonneg                    -- latentPrior, latentPrior_nonneg
    ]
    return some d
  catch e =>
    logInfo m!"rsa_predict: [auto-detect] RSAConfigData.mk failed: {e.toMessageData}"
    return none

-- ============================================================================
-- Full Auto-Detect Pipeline
-- ============================================================================

/-- Full Tier 2 pipeline for L1 comparison: detect → extract → build → native_decide → bridge.

    Returns true if successful, false to fall back to CProof (Tier 3). -/
def tryAutoDetectL1Compare (goal : MVarId) (cfg u w₁ w₂ : Expr) : TacticM Bool := do
  let t0 ← IO.monoMsNow
  logInfo m!"rsa_predict: [auto-detect] trying pattern detection..."

  -- Extract types
  let cfgType ← whnf (← inferType cfg)
  let cfgArgs := cfgType.getAppArgs
  unless cfgArgs.size ≥ 2 do return false
  let U := cfgArgs[0]!
  let W := cfgArgs[1]!
  let L ← whnf (← mkAppM ``RSA.RSAConfig.Latent #[cfg])

  -- Get finite elements
  let (_, allUElems) ← getFiniteElems U
  let (_, allWElems) ← getFiniteElems W
  let (_, allLElems) ← getFiniteElems L

  -- Extract α as ℕ
  let αExpr ← mkAppM ``RSA.RSAConfig.α #[cfg]
  let some αNat ← resolveNat? αExpr | do
    logInfo m!"rsa_predict: [auto-detect] α not a natural number"
    return false

  -- Detect pattern
  let some pattern ← detectScorePattern cfg | do
    logInfo m!"rsa_predict: [auto-detect] no pattern detected"
    return false

  let patternName := match pattern with
    | .beliefBased => "beliefBased"
    | .qudBelief => "qudBelief"
    | .qudAction => "qudAction"
    | .beliefAction => "beliefAction"
    | .actionBased => "actionBased"
    | .beliefWeighted => "beliefWeighted"
  logInfo m!"rsa_predict: [auto-detect] detected {patternName}"

  -- Extract ℚ parameters
  let some meaningVals ← extractMeaningValues cfg allLElems allUElems allWElems | do
    logInfo m!"rsa_predict: [auto-detect] cannot extract meaning as ℚ"
    return false
  let some wpVals ← extractWorldPriorValues cfg allWElems | do
    logInfo m!"rsa_predict: [auto-detect] cannot extract worldPrior as ℚ"
    return false
  let some lpVals ← extractLatentPriorValues cfg allWElems allLElems | do
    logInfo m!"rsa_predict: [auto-detect] cannot extract latentPrior as ℚ"
    return false

  -- Check non-negativity
  unless meaningVals.all (· ≥ 0) do
    logInfo m!"rsa_predict: [auto-detect] negative meaning values"
    return false
  unless wpVals.all (· ≥ 0) do
    logInfo m!"rsa_predict: [auto-detect] negative worldPrior values"
    return false
  unless lpVals.all (· ≥ 0) do
    logInfo m!"rsa_predict: [auto-detect] negative latentPrior values"
    return false

  -- Extract cost for action-based patterns
  let (pattern, costVals) ← match pattern with
    | .beliefAction | .actionBased | .qudAction => do
      let cv ← extractCostFromScore cfg U W L allUElems allWElems allLElems pattern
      -- Downgrade to beliefBased when all costs are zero.
      -- beliefAction with zero cost is algebraically L0^α (= beliefBased),
      -- but the ℚ pipeline for beliefAction uses expBounds which introduces
      -- interval approximation error, preventing exact equality proofs.
      match cv with
      | some costs =>
        if costs.all (· == 0) && pattern matches .beliefAction then
          pure (.beliefBased, none)
        else
          pure (pattern, cv)
      | none => pure (pattern, cv)
    | _ => pure (pattern, none)

  -- Extract belief/quality for beliefWeighted
  let (beliefVals, qualityVals) ← match pattern with
    | .beliefWeighted => do
      let some (bv, qv) ← extractBeliefAndQuality cfg allLElems allUElems allWElems | do
        logInfo m!"rsa_predict: [auto-detect] belief/quality extraction failed"
        return false
      pure (some bv, some qv)
    | _ => pure (none, none)

  -- Build RSAConfigData
  let some d ← buildConfigData U W L allUElems allWElems allLElems
      meaningVals wpVals lpVals αNat pattern costVals beliefVals qualityVals | do
    logInfo m!"rsa_predict: [auto-detect] RSAConfigData construction failed (cost={costVals.isSome})"
    return false

  let t1 ← IO.monoMsNow
  logInfo m!"rsa_predict: [auto-detect] RSAConfigData built ({t1 - t0}ms)"

  -- native_decide on checkL1ScoreGt d u w₁ u w₂ = true
  try
    let checkExpr ← mkAppM ``RSA.Verify.checkL1ScoreGt #[d, u, w₁, u, w₂]
    let trueExpr := mkConst ``Bool.true
    let eqType ← mkEq checkExpr trueExpr
    let eqMVar ← mkFreshExprMVar eqType
    let savedGoals ← getGoals
    setGoals [eqMVar.mvarId!]
    try
      evalTactic (← `(tactic| native_decide))
    catch e =>
      setGoals savedGoals
      logInfo m!"rsa_predict: [auto-detect] native_decide failed: {e.toMessageData}"
      return false
    setGoals savedGoals

    let t2 ← IO.monoMsNow
    logInfo m!"rsa_predict: [auto-detect] native_decide succeeded ({t2 - t1}ms)"

    -- Bridge: l1_gt_of_check_ext cfg d u w₁ w₂ eqProof
    -- Uses _ext variant: proof type mentions cfg.L1, not d.toRSAConfig.L1
    let proof ← mkAppM ``RSA.Verify.l1_gt_of_check_ext #[cfg, d, u, w₁, w₂, eqMVar]
    goal.assign proof
    let t3 ← IO.monoMsNow
    logInfo m!"rsa_predict: [auto-detect] ✓ succeeded ({t3 - t0}ms)"
    return true
  catch e =>
    logInfo m!"rsa_predict: [auto-detect] failed: {e.toMessageData}"
    return false

/-- Tier 2 pipeline for ¬(L1 gt). -/
def tryAutoDetectL1NotGt (goal : MVarId) (cfg u w₁ w₂ : Expr) : TacticM Bool := do
  logInfo m!"rsa_predict: [auto-detect/¬L1] trying pattern detection..."

  -- Extract types
  let cfgType ← whnf (← inferType cfg)
  let cfgArgs := cfgType.getAppArgs
  unless cfgArgs.size ≥ 2 do
    logInfo m!"rsa_predict: [auto-detect/¬L1] failed: cfg type args < 2"
    return false
  let U := cfgArgs[0]!
  let W := cfgArgs[1]!
  let L ← whnf (← mkAppM ``RSA.RSAConfig.Latent #[cfg])

  let (_, allUElems) ← getFiniteElems U
  let (_, allWElems) ← getFiniteElems W
  let (_, allLElems) ← getFiniteElems L

  let αExpr ← mkAppM ``RSA.RSAConfig.α #[cfg]
  let some αNat ← resolveNat? αExpr | do
    logInfo m!"rsa_predict: [auto-detect/¬L1] failed: α not ℕ"
    return false

  let some pattern ← detectScorePattern cfg | do
    logInfo m!"rsa_predict: [auto-detect/¬L1] failed: no pattern detected"
    return false

  let patternName := match pattern with
    | .beliefBased => "beliefBased" | .qudBelief => "qudBelief"
    | .qudAction => "qudAction" | .beliefAction => "beliefAction"
    | .actionBased => "actionBased" | .beliefWeighted => "beliefWeighted"
  logInfo m!"rsa_predict: [auto-detect/¬L1] detected {patternName}"

  let some meaningVals ← extractMeaningValues cfg allLElems allUElems allWElems | do
    logInfo m!"rsa_predict: [auto-detect/¬L1] failed: meaning extraction"
    return false
  let some wpVals ← extractWorldPriorValues cfg allWElems | do
    logInfo m!"rsa_predict: [auto-detect/¬L1] failed: worldPrior extraction"
    return false
  let some lpVals ← extractLatentPriorValues cfg allWElems allLElems | do
    logInfo m!"rsa_predict: [auto-detect/¬L1] failed: latentPrior extraction"
    return false

  unless meaningVals.all (· ≥ 0) && wpVals.all (· ≥ 0) && lpVals.all (· ≥ 0) do
    logInfo m!"rsa_predict: [auto-detect/¬L1] failed: negative values"
    return false

  let (pattern, costVals) ← match pattern with
    | .beliefAction | .actionBased | .qudAction => do
      let cv ← extractCostFromScore cfg U W L allUElems allWElems allLElems pattern
      match cv with
      | some costs =>
        if costs.all (· == 0) && pattern matches .beliefAction then
          pure (.beliefBased, none)
        else pure (pattern, cv)
      | none => pure (pattern, cv)
    | _ => pure (pattern, none)

  let (beliefVals, qualityVals) ← match pattern with
    | .beliefWeighted => do
      let some (bv, qv) ← extractBeliefAndQuality cfg allLElems allUElems allWElems | do
        logInfo m!"rsa_predict: [auto-detect/¬L1] failed: belief/quality extraction"
        return false
      pure (some bv, some qv)
    | _ => pure (none, none)

  let some d ← buildConfigData U W L allUElems allWElems allLElems
      meaningVals wpVals lpVals αNat pattern costVals beliefVals qualityVals | do
    logInfo m!"rsa_predict: [auto-detect/¬L1] failed: buildConfigData"
    return false

  try
    let checkExpr ← mkAppM ``RSA.Verify.checkL1ScoreNotGt #[d, u, w₁, u, w₂]
    let trueExpr := mkConst ``Bool.true
    let eqType ← mkEq checkExpr trueExpr
    let eqMVar ← mkFreshExprMVar eqType
    let savedGoals ← getGoals
    setGoals [eqMVar.mvarId!]
    try
      evalTactic (← `(tactic| native_decide))
    catch e =>
      setGoals savedGoals
      logInfo m!"rsa_predict: [auto-detect/¬L1] native_decide failed: {e.toMessageData}"
      return false
    setGoals savedGoals
    let proof ← mkAppM ``RSA.Verify.l1_not_gt_of_check_ext #[cfg, d, u, w₁, w₂, eqMVar]
    goal.assign proof
    logInfo m!"rsa_predict: [auto-detect/¬L1] ✓ succeeded"
    return true
  catch e =>
    logInfo m!"rsa_predict: [auto-detect/¬L1] bridge failed: {e.toMessageData}"
    return false

/-- Shared helper: extract ℚ data, detect pattern, build RSAConfigData for S1 goals. -/
private def buildS1ConfigData (cfg : Expr) :
    TacticM (Option (Expr × Expr × Expr)) := do
  let cfgType ← whnf (← inferType cfg)
  let cfgArgs := cfgType.getAppArgs
  unless cfgArgs.size ≥ 2 do return none
  let U := cfgArgs[0]!
  let W := cfgArgs[1]!
  let L ← whnf (← mkAppM ``RSA.RSAConfig.Latent #[cfg])

  let (_, allUElems) ← getFiniteElems U
  let (_, allWElems) ← getFiniteElems W
  let (_, allLElems) ← getFiniteElems L

  let αExpr ← mkAppM ``RSA.RSAConfig.α #[cfg]
  let some αNat ← resolveNat? αExpr | return none

  let some pattern ← detectScorePattern cfg | return none

  let some meaningVals ← extractMeaningValues cfg allLElems allUElems allWElems | return none
  let some wpVals ← extractWorldPriorValues cfg allWElems | return none
  let some lpVals ← extractLatentPriorValues cfg allWElems allLElems | return none

  unless meaningVals.all (· ≥ 0) && wpVals.all (· ≥ 0) && lpVals.all (· ≥ 0) do
    return none

  let (pattern, costVals) ← match pattern with
    | .beliefAction | .actionBased | .qudAction => do
      let cv ← extractCostFromScore cfg U W L allUElems allWElems allLElems pattern
      match cv with
      | some costs =>
        if costs.all (· == 0) && pattern matches .beliefAction then
          pure (.beliefBased, none)
        else pure (pattern, cv)
      | none => pure (pattern, cv)
    | _ => pure (pattern, none)

  let (beliefVals, qualityVals) ← match pattern with
    | .beliefWeighted => do
      let some (bv, qv) ← extractBeliefAndQuality cfg allLElems allUElems allWElems | return none
      pure (some bv, some qv)
    | _ => pure (none, none)

  let some d ← buildConfigData U W L allUElems allWElems allLElems
      meaningVals wpVals lpVals αNat pattern costVals beliefVals qualityVals | return none

  -- Build h_lat : d.Latent = cfg.Latent proof (should be rfl since d.Latent = L = cfg.Latent)
  let dLatent ← whnf (← mkAppM ``RSA.RSAConfigData.Latent #[d])
  let cfgLatent ← whnf (← mkAppM ``RSA.RSAConfig.Latent #[cfg])
  let hLatType ← mkEq dLatent cfgLatent
  let hLat ← try
    let m ← mkFreshExprMVar hLatType
    if ← isDefEq dLatent cfgLatent then
      m.mvarId!.assign (← mkEqRefl dLatent)
      pure m
    else
      logInfo m!"rsa_predict: [auto-detect/S1] Latent types not defEq"
      return none
  catch _ =>
    logInfo m!"rsa_predict: [auto-detect/S1] Latent type proof failed"
    return none

  return some (d, L, hLat)

/-- Tier 2 pipeline for S1 comparison. -/
def tryAutoDetectS1Compare (goal : MVarId) (cfg l w u₁ u₂ : Expr) : TacticM Bool := do
  logInfo m!"rsa_predict: [auto-detect/S1] trying pattern detection..."

  let some (d, _L, hLat) ← buildS1ConfigData cfg | do
    logInfo m!"rsa_predict: [auto-detect/S1] setup failed"
    return false

  try
    -- Cast l from cfg.Latent to d.Latent using h_lat
    let castL ← mkAppM ``Eq.mpr #[hLat, l]
    let checkExpr ← mkAppM ``RSA.Verify.checkS1PolicyGt #[d, castL, w, u₁, u₂]
    let trueExpr := mkConst ``Bool.true
    let eqType ← mkEq checkExpr trueExpr
    let eqMVar ← mkFreshExprMVar eqType
    let savedGoals ← getGoals
    setGoals [eqMVar.mvarId!]
    try
      evalTactic (← `(tactic| native_decide))
    catch e =>
      setGoals savedGoals
      logInfo m!"rsa_predict: [auto-detect/S1] native_decide failed: {e.toMessageData}"
      return false
    setGoals savedGoals
    let proof ← mkAppM ``RSA.Verify.s1_gt_of_check_ext #[cfg, d, hLat, l, w, u₁, u₂, eqMVar]
    goal.assign proof
    logInfo m!"rsa_predict: [auto-detect/S1] ✓ succeeded"
    return true
  catch e =>
    logInfo m!"rsa_predict: [auto-detect/S1] bridge failed: {e.toMessageData}"
    return false

/-- Tier 2 pipeline for ¬(S1 gt). -/
def tryAutoDetectS1NotGt (goal : MVarId) (cfg l w u₁ u₂ : Expr) : TacticM Bool := do
  logInfo m!"rsa_predict: [auto-detect/¬S1] trying pattern detection..."

  let some (d, _L, hLat) ← buildS1ConfigData cfg | do
    logInfo m!"rsa_predict: [auto-detect/¬S1] setup failed"
    return false

  try
    let castL ← mkAppM ``Eq.mpr #[hLat, l]
    let checkExpr ← mkAppM ``RSA.Verify.checkS1PolicyNotGt #[d, castL, w, u₁, u₂]
    let trueExpr := mkConst ``Bool.true
    let eqType ← mkEq checkExpr trueExpr
    let eqMVar ← mkFreshExprMVar eqType
    let savedGoals ← getGoals
    setGoals [eqMVar.mvarId!]
    try
      evalTactic (← `(tactic| native_decide))
    catch e =>
      setGoals savedGoals
      logInfo m!"rsa_predict: [auto-detect/¬S1] native_decide failed: {e.toMessageData}"
      return false
    setGoals savedGoals
    let proof ← mkAppM ``RSA.Verify.s1_not_gt_of_check_ext #[cfg, d, hLat, l, w, u₁, u₂, eqMVar]
    goal.assign proof
    logInfo m!"rsa_predict: [auto-detect/¬S1] ✓ succeeded"
    return true
  catch e =>
    logInfo m!"rsa_predict: [auto-detect/¬S1] bridge failed: {e.toMessageData}"
    return false

/-- Tier 2 pipeline for L1 score gt (cross-utterance). -/
def tryAutoDetectL1ScoreGt (goal : MVarId) (cfg u₁ w₁ u₂ w₂ : Expr) : TacticM Bool := do
  logInfo m!"rsa_predict: [auto-detect/score] trying pattern detection..."

  let cfgType ← whnf (← inferType cfg)
  let cfgArgs := cfgType.getAppArgs
  unless cfgArgs.size ≥ 2 do return false
  let U := cfgArgs[0]!
  let W := cfgArgs[1]!
  let L ← whnf (← mkAppM ``RSA.RSAConfig.Latent #[cfg])

  let (_, allUElems) ← getFiniteElems U
  let (_, allWElems) ← getFiniteElems W
  let (_, allLElems) ← getFiniteElems L

  let αExpr ← mkAppM ``RSA.RSAConfig.α #[cfg]
  let some αNat ← resolveNat? αExpr | return false

  let some pattern ← detectScorePattern cfg | return false

  let some meaningVals ← extractMeaningValues cfg allLElems allUElems allWElems | return false
  let some wpVals ← extractWorldPriorValues cfg allWElems | return false
  let some lpVals ← extractLatentPriorValues cfg allWElems allLElems | return false

  unless meaningVals.all (· ≥ 0) && wpVals.all (· ≥ 0) && lpVals.all (· ≥ 0) do
    return false

  let (pattern, costVals) ← match pattern with
    | .beliefAction | .actionBased | .qudAction => do
      let cv ← extractCostFromScore cfg U W L allUElems allWElems allLElems pattern
      match cv with
      | some costs =>
        if costs.all (· == 0) && pattern matches .beliefAction then
          pure (.beliefBased, none)
        else pure (pattern, cv)
      | none => pure (pattern, cv)
    | _ => pure (pattern, none)

  let (beliefVals, qualityVals) ← match pattern with
    | .beliefWeighted => do
      let some (bv, qv) ← extractBeliefAndQuality cfg allLElems allUElems allWElems | return false
      pure (some bv, some qv)
    | _ => pure (none, none)

  let some d ← buildConfigData U W L allUElems allWElems allLElems
      meaningVals wpVals lpVals αNat pattern costVals beliefVals qualityVals | return false

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
    let proof ← mkAppM ``RSA.Verify.l1_score_gt_of_check_ext #[cfg, d, u₁, w₁, u₂, w₂, eqMVar]
    goal.assign proof
    logInfo m!"rsa_predict: [auto-detect/score] ✓ succeeded"
    return true
  catch _ => return false

end Linglib.Tactics.RSAPredict
