import Lean
import Linglib.Core.Interval.RSAVerify
import Linglib.Core.Interval.ReflectInterval
import Linglib.Tactics.RSAPredict.Helpers
import Linglib.Tactics.RSAPredict.Reify
import Linglib.Tactics.RSAPredict.FinsetExpand

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
2. **Check**: `native_decide` on batched `checkGt`/`checkNotGt` (evalValid + separation).
3. **Assign**: Directly assign `gt_of_checkGt lhsRExpr rhsRExpr hcheck` — the kernel
   verifies `denote(lhsRExpr) ≡ lhsExpr` and `denote(rhsRExpr) ≡ rhsExpr`.

This eliminates the congruence proof tree (O(n) nodes → O(1) proof term) and the
equality bridge (`gt_of_eq_gt_eq`), reducing both reification time and proof term size.
-/

namespace Linglib.Tactics.RSAPredict

open Lean Meta Elab Tactic
open Linglib.Interval

-- ============================================================================
-- Persistent Reification Cache
-- ============================================================================

-- Note: cross-theorem caching via IO.Ref doesn't work because Lean 4
-- elaborates theorems in parallel (IO.Ref is racily shared across threads).
-- Each invocation creates a fresh local cache instead. Within a single theorem,
-- LHS/RHS reification shares sub-expressions via the local cache.

-- ============================================================================
-- Meta-Level DAG Builder
-- ============================================================================

/-- Meta-level DAG state: array of DAGNode Exprs + dedup map keyed on Expr hash.
    Walking the RExpr `Expr` at meta-time avoids the 28M-node tree traversal that
    would happen at `native_decide` time. `Expr.hash` is O(1) (cached in the Expr
    representation), and the reifier returns the same `Expr` object for cached
    sub-expressions, so shared sub-trees dedup immediately. -/
private abbrev DAGMetaState := Array Expr × Std.HashMap UInt64 ℕ

/-- Walk an RExpr `Expr` to build a DAG at meta-time. On cache hit (same
    `Expr.hash`), returns the existing DAG index without recursing — this is
    where the 28.8M → 1,245 reduction happens. -/
private partial def rexprExprToDAGAux (ref : IO.Ref DAGMetaState) (e : Expr) : MetaM ℕ := do
  let key := e.hash
  let (_, seen) ← ref.get
  if let some idx := seen.get? key then return idx

  let fn := e.getAppFn
  let args := e.getAppArgs
  let some name := fn.constName?
    | throwError "rsa_predict: DAG builder: non-const head in RExpr: {fn}"

  let dagNodeExpr ← match name with
    | ``RExpr.nat => pure (mkApp (mkConst ``DAGNode.nat) args[0]!)
    | ``RExpr.ratCast => pure (mkApp (mkConst ``DAGNode.ratCast) args[0]!)
    | ``RExpr.add => do
      pure (mkApp2 (mkConst ``DAGNode.add)
        (mkRawNatLit (← rexprExprToDAGAux ref args[0]!))
        (mkRawNatLit (← rexprExprToDAGAux ref args[1]!)))
    | ``RExpr.mul => do
      pure (mkApp2 (mkConst ``DAGNode.mul)
        (mkRawNatLit (← rexprExprToDAGAux ref args[0]!))
        (mkRawNatLit (← rexprExprToDAGAux ref args[1]!)))
    | ``RExpr.div => do
      pure (mkApp2 (mkConst ``DAGNode.div)
        (mkRawNatLit (← rexprExprToDAGAux ref args[0]!))
        (mkRawNatLit (← rexprExprToDAGAux ref args[1]!)))
    | ``RExpr.neg => do
      pure (mkApp (mkConst ``DAGNode.neg)
        (mkRawNatLit (← rexprExprToDAGAux ref args[0]!)))
    | ``RExpr.sub => do
      pure (mkApp2 (mkConst ``DAGNode.sub)
        (mkRawNatLit (← rexprExprToDAGAux ref args[0]!))
        (mkRawNatLit (← rexprExprToDAGAux ref args[1]!)))
    | ``RExpr.rexp => do
      pure (mkApp (mkConst ``DAGNode.rexp)
        (mkRawNatLit (← rexprExprToDAGAux ref args[0]!)))
    | ``RExpr.rlog => do
      pure (mkApp (mkConst ``DAGNode.rlog)
        (mkRawNatLit (← rexprExprToDAGAux ref args[0]!)))
    | ``RExpr.rpow => do
      pure (mkApp2 (mkConst ``DAGNode.rpow)
        (mkRawNatLit (← rexprExprToDAGAux ref args[0]!))
        args[1]!)  -- exponent is a ℕ literal, not a sub-expression
    | ``RExpr.inv => do
      pure (mkApp (mkConst ``DAGNode.inv)
        (mkRawNatLit (← rexprExprToDAGAux ref args[0]!)))
    | ``RExpr.iteZero => do
      pure (mkApp3 (mkConst ``DAGNode.iteZero)
        (mkRawNatLit (← rexprExprToDAGAux ref args[0]!))
        (mkRawNatLit (← rexprExprToDAGAux ref args[1]!))
        (mkRawNatLit (← rexprExprToDAGAux ref args[2]!)))
    | ``RExpr.expMulLogSub => do
      pure (mkApp3 (mkConst ``DAGNode.expMulLogSub)
        (mkRawNatLit (← rexprExprToDAGAux ref args[0]!))
        (mkRawNatLit (← rexprExprToDAGAux ref args[1]!))
        (mkRawNatLit (← rexprExprToDAGAux ref args[2]!)))
    | _ => throwError "rsa_predict: DAG builder: unknown RExpr constructor: {name}"

  let (dagNodes, seen) ← ref.get
  let idx := dagNodes.size
  ref.set (dagNodes.push dagNodeExpr, seen.insert key idx)
  return idx

/-- Build a Lean `Expr` representing `Array DAGNode` from the DAG node Exprs. -/
private def buildDAGArrayExpr (dagNodes : Array Expr) : Expr :=
  let dagNodeType := mkConst ``DAGNode
  let nil := mkApp (mkConst ``List.nil [Level.zero]) dagNodeType
  let listExpr := dagNodes.foldr
    (fun elem rest => mkApp3 (mkConst ``List.cons [Level.zero]) dagNodeType elem rest)
    nil
  mkApp2 (mkConst ``Array.mk [Level.zero]) dagNodeType listExpr

/-- Build a shared DAG from two RExpr Exprs. The second call inherits the
    dedup state from the first, so cross-side sharing is captured.
    Returns `(dagArrayExpr, lhsIdx, rhsIdx)`. -/
private def buildSharedDAG (lhsRExpr rhsRExpr : Expr) :
    MetaM (Expr × ℕ × ℕ) := do
  let ref ← IO.mkRef ((#[], {}) : DAGMetaState)
  let lhsIdx ← rexprExprToDAGAux ref lhsRExpr
  let rhsIdx ← rexprExprToDAGAux ref rhsRExpr
  let (dagNodes, _) ← ref.get
  return (buildDAGArrayExpr dagNodes, lhsIdx, rhsIdx)

-- ============================================================================
-- Let-Bound RExpr Builder (for fast LCNF compilation in native_decide)
-- ============================================================================

/-- State for building let-bound RExpr expressions. Entries are stored in
    topological order (leaves first). Each entry's value uses `bvar` references
    to earlier entries. -/
private abbrev LetDAGState := Array Expr × Std.HashMap UInt64 ℕ

/-- Walk an RExpr `Expr` to build a let-bound representation. Returns the
    let-DAG index of the expression. Children are processed first, ensuring
    topological order. Shared sub-expressions (by `Expr.hash`) get a single
    let binding, making LCNF compilation O(unique nodes) instead of O(tree). -/
private partial def rexprToLetDAGAux (ref : IO.Ref LetDAGState) (e : Expr) : MetaM ℕ := do
  let key := e.hash
  let (_, seen) ← ref.get
  if let some idx := seen.get? key then return idx

  let fn := e.getAppFn
  let args := e.getAppArgs
  let some name := fn.constName?
    | throwError "rsa_predict: let-DAG builder: non-const head in RExpr: {fn}"

  -- Process children first (may add entries), THEN determine this node's index.
  -- Helper: bvar reference to child index `ci` from depth `d`.
  let mkRef (d ci : ℕ) : Expr := mkBVar (d - ci - 1)

  let value ← match name with
    | ``RExpr.nat | ``RExpr.ratCast => pure e  -- leaf, no children
    | ``RExpr.neg => do
      let ci ← rexprToLetDAGAux ref args[0]!
      let d := (← ref.get).1.size
      pure (mkApp (mkConst ``RExpr.neg) (mkRef d ci))
    | ``RExpr.rexp => do
      let ci ← rexprToLetDAGAux ref args[0]!
      let d := (← ref.get).1.size
      pure (mkApp (mkConst ``RExpr.rexp) (mkRef d ci))
    | ``RExpr.rlog => do
      let ci ← rexprToLetDAGAux ref args[0]!
      let d := (← ref.get).1.size
      pure (mkApp (mkConst ``RExpr.rlog) (mkRef d ci))
    | ``RExpr.inv => do
      let ci ← rexprToLetDAGAux ref args[0]!
      let d := (← ref.get).1.size
      pure (mkApp (mkConst ``RExpr.inv) (mkRef d ci))
    | ``RExpr.add => do
      let ai ← rexprToLetDAGAux ref args[0]!
      let bi ← rexprToLetDAGAux ref args[1]!
      let d := (← ref.get).1.size
      pure (mkApp2 (mkConst ``RExpr.add) (mkRef d ai) (mkRef d bi))
    | ``RExpr.mul => do
      let ai ← rexprToLetDAGAux ref args[0]!
      let bi ← rexprToLetDAGAux ref args[1]!
      let d := (← ref.get).1.size
      pure (mkApp2 (mkConst ``RExpr.mul) (mkRef d ai) (mkRef d bi))
    | ``RExpr.div => do
      let ai ← rexprToLetDAGAux ref args[0]!
      let bi ← rexprToLetDAGAux ref args[1]!
      let d := (← ref.get).1.size
      pure (mkApp2 (mkConst ``RExpr.div) (mkRef d ai) (mkRef d bi))
    | ``RExpr.sub => do
      let ai ← rexprToLetDAGAux ref args[0]!
      let bi ← rexprToLetDAGAux ref args[1]!
      let d := (← ref.get).1.size
      pure (mkApp2 (mkConst ``RExpr.sub) (mkRef d ai) (mkRef d bi))
    | ``RExpr.rpow => do
      let ai ← rexprToLetDAGAux ref args[0]!
      let d := (← ref.get).1.size
      pure (mkApp2 (mkConst ``RExpr.rpow) (mkRef d ai) args[1]!)  -- ℕ exponent literal
    | ``RExpr.iteZero => do
      let ci ← rexprToLetDAGAux ref args[0]!
      let ti ← rexprToLetDAGAux ref args[1]!
      let ei ← rexprToLetDAGAux ref args[2]!
      let d := (← ref.get).1.size
      pure (mkApp3 (mkConst ``RExpr.iteZero) (mkRef d ci) (mkRef d ti) (mkRef d ei))
    | ``RExpr.expMulLogSub => do
      let ai ← rexprToLetDAGAux ref args[0]!
      let xi ← rexprToLetDAGAux ref args[1]!
      let ci ← rexprToLetDAGAux ref args[2]!
      let d := (← ref.get).1.size
      pure (mkApp3 (mkConst ``RExpr.expMulLogSub) (mkRef d ai) (mkRef d xi) (mkRef d ci))
    | _ => throwError "rsa_predict: let-DAG builder: unknown RExpr: {name}"

  let (entries, seen) ← ref.get
  let idx := entries.size
  ref.set (entries.push value, seen.insert key idx)
  return idx

/-- Build a let-bound `checkFn lhs rhs` expression from two RExpr Exprs.
    The result is wrapped in nested `Expr.letE` bindings so that LCNF sees
    ~1K nodes (O(unique sub-expressions)) instead of ~28M (O(tree)).
    Kernel verification is still efficient: zeta-reduction preserves Expr
    sharing via `instantiate1`, so `denote` reduction is O(unique nodes). -/
private def buildLetBoundCheck (checkFnName : Name) (lhsRExpr rhsRExpr : Expr) :
    MetaM Expr := do
  let ref ← IO.mkRef ((#[], {}) : LetDAGState)
  let lhsIdx ← rexprToLetDAGAux ref lhsRExpr
  let rhsIdx ← rexprToLetDAGAux ref rhsRExpr
  let (entries, _) ← ref.get
  let n := entries.size
  -- Body: checkFn (bvar lhsOffset) (bvar rhsOffset)
  let body := mkApp2 (mkConst checkFnName)
    (mkBVar (n - lhsIdx - 1)) (mkBVar (n - rhsIdx - 1))
  -- Wrap in nested letE (outermost = entry 0, innermost = entry n-1)
  let rexprType := mkConst ``RExpr
  let mut result := body
  for i in [:n] do
    let j := n - 1 - i  -- build from innermost to outermost
    result := Expr.letE `r rexprType entries[j]! result false
  return result

-- ============================================================================
-- Direct RExpr Pipeline
-- ============================================================================

/-- Direct RExpr reification for `lhs > rhs` goals.
    Reifies both sides to RExpr, wraps in let-bindings for fast LCNF compilation
    (O(unique nodes) instead of O(tree nodes)), then runs `native_decide` on the
    compact `checkGtOpt`. When Finset.sum is encountered during reification,
    builds bridge proofs: Finset.sum Finset.univ f = (l.map f).sum, so the kernel
    verifies denote(rexpr) ≡ (l.map f).sum (fast) instead of ≡ Finset.sum (slow). -/
def tryDirectRExprCompare (goal : MVarId) (lhsExpr rhsExpr : Expr) : TacticM Bool := do
  let t0 ← IO.monoMsNow

  -- Phase 1: Reify both sides. The reifier records Finset.sum sites it encounters.
  let localCache ← IO.mkRef ({} : ReifyCacheData)
  let (lhsRExpr, lhsBounds) ← reifyToRExpr localCache lhsExpr maxDepth
  let (rhsRExpr, rhsBounds) ← reifyToRExpr localCache rhsExpr maxDepth

  unless lhsBounds.lo > rhsBounds.hi do
    logInfo m!"rsa_predict: [direct] bounds don't separate (lhs=[{lhsBounds.lo}, {lhsBounds.hi}] rhs=[{rhsBounds.lo}, {rhsBounds.hi}])"
    return false

  -- Phase 2: Build bridge proofs for Finset.sum sites found during reification.
  let finsetSites := (← localCache.get).finsetSumSites
  let useBridge := finsetSites.size > 0

  let (lhsExpandProof?, rhsExpandProof?) ← if useBridge then do
    let lhsP? ← expandFinsetSums lhsExpr
    let rhsP? ← expandFinsetSums rhsExpr
    pure (lhsP?.2, rhsP?.2)
  else
    pure (none, none)

  try
    -- Phase 3: Prove via native_decide on let-bound checkGtOpt.
    let letCheckExpr ← buildLetBoundCheck ``RExpr.checkGtOpt lhsRExpr rhsRExpr
    let letCheckType ← mkEq letCheckExpr (mkConst ``Bool.true)
    let hcheck ← nativeDecideProof letCheckType

    -- Phase 4: Build proof term.
    let h_gt := mkApp3 (mkConst ``RExpr.gt_of_checkGtOpt) lhsRExpr rhsRExpr hcheck

    if lhsExpandProof?.isSome || rhsExpandProof?.isSome then
      let h_lhs := lhsExpandProof?.getD (← mkAppM ``Eq.refl #[lhsExpr])
      let h_rhs := rhsExpandProof?.getD (← mkAppM ``Eq.refl #[rhsExpr])
      let proof ← mkAppM ``gt_of_eq_gt_eq #[h_lhs, h_rhs, h_gt]
      goal.assign proof
    else
      goal.assign h_gt

    let t3 ← IO.monoMsNow
    logInfo m!"rsa_predict: [direct] proved ({t3 - t0}ms)"
    return true
  catch e =>
    logInfo m!"rsa_predict: [direct] failed: {e.toMessageData}"
    return false

/-- Direct RExpr reification for `not (lhs > rhs)` goals.
    Assigns proofs directly — the kernel verifies denote ≡ original. -/
def tryDirectRExprNotGt (goal : MVarId) (lhsExpr rhsExpr : Expr) : TacticM Bool := do
  let t0 ← IO.monoMsNow
  let localCache ← IO.mkRef ({} : ReifyCacheData)
  let (lhsRExpr, lhsBounds) ← reifyToRExpr localCache lhsExpr maxDepth
  let (rhsRExpr, rhsBounds) ← reifyToRExpr localCache rhsExpr maxDepth

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
      logInfo m!"rsa_predict: [direct/not-gt] proved via structural equality ({t2 - t0}ms)"
      return true

    -- Exact ℚ evaluation path
    let exactCheckExpr ← mkAppM ``RExpr.checkExactNotGt #[lhsRExpr, rhsRExpr]
    let exactCheckType ← mkEq exactCheckExpr (mkConst ``Bool.true)
    if let some hexact ← try? (nativeDecideProof exactCheckType) then
      let proof := mkApp3 (mkConst ``RExpr.not_gt_of_checkExactNotGt)
        lhsRExpr rhsRExpr hexact
      goal.assign proof
      let t2 ← IO.monoMsNow
      logInfo m!"rsa_predict: [direct/not-gt] proved via exact ℚ ({t2 - t0}ms)"
      return true

    -- Semantic equality path
    let semCheckExpr ← mkAppM ``RExpr.checkSemanticEq #[lhsRExpr, rhsRExpr]
    let semCheckType ← mkEq semCheckExpr (mkConst ``Bool.true)
    if let some hsem ← try? (nativeDecideProof semCheckType) then
      let proof := mkApp3 (mkConst ``RExpr.not_gt_of_checkSemanticEq)
        lhsRExpr rhsRExpr hsem
      goal.assign proof
      let t2 ← IO.monoMsNow
      logInfo m!"rsa_predict: [direct/not-gt] proved via semantic equality ({t2 - t0}ms)"
      return true

    -- Interval separation path
    unless lhsBounds.hi ≤ rhsBounds.lo do
      return false

    let letCheckExpr ← buildLetBoundCheck ``RExpr.checkNotGtOpt lhsRExpr rhsRExpr
    let letCheckType ← mkEq letCheckExpr (mkConst ``Bool.true)
    let hcheck ← nativeDecideProof letCheckType

    let proof := mkApp3 (mkConst ``RExpr.not_gt_of_checkNotGtOpt)
      lhsRExpr rhsRExpr hcheck
    goal.assign proof
    let t3 ← IO.monoMsNow
    logInfo m!"rsa_predict: [direct/not-gt] proved ({t3 - t0}ms)"
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
  let localCache ← IO.mkRef ({} : ReifyCacheData)
  let (lhsRExpr, _) ← reifyToRExpr localCache lhsExpr maxDepth
  let (rhsRExpr, _) ← reifyToRExpr localCache rhsExpr maxDepth

  try
    -- Fast path: structurally equal RExpr → congrArg denote
    let eqType ← mkEq lhsRExpr rhsRExpr
    if let some heq ← try? (nativeDecideProof eqType) then
      let denoteFn := mkConst ``RExpr.denote
      let proof ← mkAppM ``congrArg #[denoteFn, heq]
      goal.assign proof
      let t2 ← IO.monoMsNow
      logInfo m!"rsa_predict: [direct/eq] proved via structural equality ({t2 - t0}ms)"
      return true

    -- Exact ℚ evaluation path
    let checkExpr ← mkAppM ``RExpr.checkExactEq #[lhsRExpr, rhsRExpr]
    let checkType ← mkEq checkExpr (mkConst ``Bool.true)
    if let some hcheck ← try? (nativeDecideProof checkType) then
      let proof := mkApp3 (mkConst ``RExpr.eq_of_checkExactEq) lhsRExpr rhsRExpr hcheck
      goal.assign proof
      let t2 ← IO.monoMsNow
      logInfo m!"rsa_predict: [direct/eq] proved via exact ℚ ({t2 - t0}ms)"
      return true

    -- Semantic equality path
    let semCheckExpr ← mkAppM ``RExpr.checkSemanticEq #[lhsRExpr, rhsRExpr]
    let semCheckType ← mkEq semCheckExpr (mkConst ``Bool.true)
    if let some hsem ← try? (nativeDecideProof semCheckType) then
      let proof := mkApp3 (mkConst ``RExpr.eq_of_checkSemanticEq) lhsRExpr rhsRExpr hsem
      goal.assign proof
      let t2 ← IO.monoMsNow
      logInfo m!"rsa_predict: [direct/eq] proved via semantic equality ({t2 - t0}ms)"
      return true

    return false
  catch e =>
    logInfo m!"rsa_predict: [direct/eq] failed: {e.toMessageData}"
    return false

-- ============================================================================
-- Reflection-Based Proof Builders (unified direct RExpr strategy)
-- ============================================================================

/-- Try to prove `cfg.L1 u w1 > cfg.L1 u w2` via direct RExpr reification.
    Returns true if successful, false to fall back to CProof. -/
def tryReflectL1Compare (goal : MVarId) (cfg u w₁ w₂ : Expr) : TacticM Bool := do
  let lhs ← mkAppM ``RSA.RSAConfig.L1 #[cfg, u, w₁]
  let rhs ← mkAppM ``RSA.RSAConfig.L1 #[cfg, u, w₂]
  tryDirectRExprCompare goal lhs rhs

/-- Try to prove `cfg.L1agent.score u1 w1 > cfg.L1agent.score u2 w2` via reflection.
    Used for marginal/cross-utterance comparisons at the score level. -/
def tryReflectL1ScoreGt (goal : MVarId) (cfg u₁ w₁ u₂ w₂ : Expr) : TacticM Bool := do
  let l1agent ← mkAppM ``RSA.RSAConfig.L1agent #[cfg]
  let lhs ← mkAppM ``Core.RationalAction.score #[l1agent, u₁, w₁]
  let rhs ← mkAppM ``Core.RationalAction.score #[l1agent, u₂, w₂]
  tryDirectRExprCompare goal lhs rhs

/-- Try to prove `not (cfg.L1 u w1 > cfg.L1 u w2)` via reflection. -/
def tryReflectL1NotGt (goal : MVarId) (cfg u w₁ w₂ : Expr) : TacticM Bool := do
  let lhs ← mkAppM ``RSA.RSAConfig.L1 #[cfg, u, w₁]
  let rhs ← mkAppM ``RSA.RSAConfig.L1 #[cfg, u, w₂]
  tryDirectRExprNotGt goal lhs rhs

/-- Try to prove `cfg.S1 l w u1 > cfg.S1 l w u2` via reflection. -/
def tryReflectS1Compare (goal : MVarId) (cfg l w u₁ u₂ : Expr) : TacticM Bool := do
  let lhs ← mkAppM ``RSA.RSAConfig.S1 #[cfg, l, w, u₁]
  let rhs ← mkAppM ``RSA.RSAConfig.S1 #[cfg, l, w, u₂]
  tryDirectRExprCompare goal lhs rhs

/-- Try to prove `not (cfg.S1 l w u1 > cfg.S1 l w u2)` via reflection. -/
def tryReflectS1NotGt (goal : MVarId) (cfg l w u₁ u₂ : Expr) : TacticM Bool := do
  let lhs ← mkAppM ``RSA.RSAConfig.S1 #[cfg, l, w, u₁]
  let rhs ← mkAppM ``RSA.RSAConfig.S1 #[cfg, l, w, u₂]
  tryDirectRExprNotGt goal lhs rhs

end Linglib.Tactics.RSAPredict
