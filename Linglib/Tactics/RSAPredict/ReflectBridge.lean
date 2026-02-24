import Lean
import Linglib.Core.Interval.RSAVerify
import Linglib.Core.Interval.ReflectInterval
import Linglib.Tactics.RSAPredict.Helpers
import Linglib.Tactics.RSAPredict.Reify

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

/-- Module-scope reification cache shared across all `rsa_predict` invocations
    within a file. The first theorem pays the full reification cost; subsequent
    theorems for the same model get cache hits on shared sub-expressions
    (L0 policies, S1 scores, belief distributions, etc.). -/
initialize persistentReifyCache : IO.Ref (Std.HashMap UInt64 (Expr × MetaBounds)) ←
  IO.mkRef ∅

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

/-- Direct RExpr reification for `lhs > rhs` goals.
    Builds a shared DAG at meta-time from the RExpr `Expr` structure,
    then runs `native_decide` on the compact `checkGtDAG` (O(unique nodes)
    instead of O(tree nodes)). Falls back to tree-based `checkGtOpt`
    if DAG construction fails. -/
def tryDirectRExprCompare (goal : MVarId) (lhsExpr rhsExpr : Expr) : TacticM Bool := do
  let t0 ← IO.monoMsNow
  let cacheBefore ← persistentReifyCache.get
  let (lhsRExpr, lhsBounds) ← reifyToRExpr persistentReifyCache lhsExpr maxDepth
  let (rhsRExpr, rhsBounds) ← reifyToRExpr persistentReifyCache rhsExpr maxDepth

  unless lhsBounds.lo > rhsBounds.hi do
    logInfo m!"rsa_predict: [direct] bounds don't separate"
    return false

  let cacheAfter ← persistentReifyCache.get
  let t1 ← IO.monoMsNow
  logInfo m!"rsa_predict: [direct] reified ({t1 - t0}ms, cache {cacheBefore.size}→{cacheAfter.size})"

  try
    -- Build shared DAG at meta-time (O(unique sub-expressions), not O(tree nodes))
    let (dagArrayExpr, lhsIdx, rhsIdx) ← buildSharedDAG lhsRExpr rhsRExpr
    let t1b ← IO.monoMsNow
    logInfo m!"rsa_predict: [direct] DAG built ({t1b - t1}ms)"

    -- native_decide on checkGtDAG: evaluates only ~1K unique DAG nodes
    let checkExpr := mkApp3 (mkConst ``checkGtDAG) dagArrayExpr
      (mkRawNatLit lhsIdx) (mkRawNatLit rhsIdx)
    let checkType ← mkEq checkExpr (mkConst ``Bool.true)
    let hcheck ← nativeDecideProof checkType

    let t2 ← IO.monoMsNow
    logInfo m!"rsa_predict: [direct] native_decide ({t2 - t1b}ms)"

    -- gt_of_checkGtDAG : (lhs rhs : RExpr) → (dag : Array DAGNode) → (li ri : ℕ) →
    --   checkGtDAG dag li ri = true → lhs.denote > rhs.denote
    let proof := mkAppN (mkConst ``gt_of_checkGtDAG)
      #[lhsRExpr, rhsRExpr, dagArrayExpr, mkRawNatLit lhsIdx, mkRawNatLit rhsIdx, hcheck]
    goal.assign proof

    let t3 ← IO.monoMsNow
    logInfo m!"rsa_predict: [direct] assigned ({t3 - t0}ms)"
    return true
  catch e =>
    -- Fallback to tree-based checkGtOpt (for small models or DAG builder failures)
    logInfo m!"rsa_predict: [direct] DAG path failed: {e.toMessageData}, trying tree fallback"
    try
      let checkExpr ← mkAppM ``RExpr.checkGtOpt #[lhsRExpr, rhsRExpr]
      let checkType ← mkEq checkExpr (mkConst ``Bool.true)
      let hcheck ← nativeDecideProof checkType
      let proof := mkApp3 (mkConst ``RExpr.gt_of_checkGtOpt) lhsRExpr rhsRExpr hcheck
      goal.assign proof
      let t3 ← IO.monoMsNow
      logInfo m!"rsa_predict: [direct] assigned via tree fallback ({t3 - t0}ms)"
      return true
    catch e2 =>
      logInfo m!"rsa_predict: [direct] tree fallback also failed: {e2.toMessageData}"
      return false

/-- Direct RExpr reification for `not (lhs > rhs)` goals.
    Assigns proofs directly — the kernel verifies denote ≡ original. -/
def tryDirectRExprNotGt (goal : MVarId) (lhsExpr rhsExpr : Expr) : TacticM Bool := do
  let t0 ← IO.monoMsNow
  let (lhsRExpr, lhsBounds) ← reifyToRExpr persistentReifyCache lhsExpr maxDepth
  let (rhsRExpr, rhsBounds) ← reifyToRExpr persistentReifyCache rhsExpr maxDepth

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

    -- Exact ℚ evaluation path: for pure arithmetic RExpr (no exp/log),
    -- evaluate both to exact ℚ and check ¬(>).
    let exactCheckExpr ← mkAppM ``RExpr.checkExactNotGt #[lhsRExpr, rhsRExpr]
    let exactCheckType ← mkEq exactCheckExpr (mkConst ``Bool.true)
    if let some hexact ← try? (nativeDecideProof exactCheckType) then
      let proof := mkApp3 (mkConst ``RExpr.not_gt_of_checkExactNotGt)
        lhsRExpr rhsRExpr hexact
      goal.assign proof
      let t2 ← IO.monoMsNow
      logInfo m!"rsa_predict: [direct/not-gt] assigned via exact ℚ ({t2 - t0}ms)"
      return true

    -- Interval separation path: need lhs.eval.hi ≤ rhs.eval.lo
    unless lhsBounds.hi ≤ rhsBounds.lo do
      logInfo m!"rsa_predict: [direct/not-gt] bounds don't prove le, exact ℚ not available"
      return false

    -- Try DAG-based interval check first
    let dagOk ← try
      let (dagArrayExpr, lhsIdx, rhsIdx) ← buildSharedDAG lhsRExpr rhsRExpr
      let checkExpr := mkApp3 (mkConst ``checkNotGtDAG) dagArrayExpr
        (mkRawNatLit lhsIdx) (mkRawNatLit rhsIdx)
      let checkType ← mkEq checkExpr (mkConst ``Bool.true)
      let hcheck ← nativeDecideProof checkType
      let proof := mkAppN (mkConst ``not_gt_of_checkNotGtDAG)
        #[lhsRExpr, rhsRExpr, dagArrayExpr, mkRawNatLit lhsIdx, mkRawNatLit rhsIdx, hcheck]
      goal.assign proof
      let t2 ← IO.monoMsNow
      logInfo m!"rsa_predict: [direct/not-gt] assigned via DAG interval ({t2 - t0}ms)"
      pure true
    catch _ => pure false
    if dagOk then return true

    -- Fallback to tree-based checkNotGtOpt
    let checkExpr ← mkAppM ``RExpr.checkNotGtOpt #[lhsRExpr, rhsRExpr]
    let checkType ← mkEq checkExpr (mkConst ``Bool.true)
    let hcheck ← nativeDecideProof checkType
    let proof := mkApp3 (mkConst ``RExpr.not_gt_of_checkNotGtOpt)
      lhsRExpr rhsRExpr hcheck
    goal.assign proof
    let t2 ← IO.monoMsNow
    logInfo m!"rsa_predict: [direct/not-gt] assigned via interval fallback ({t2 - t0}ms)"
    return true
  catch e =>
    logInfo m!"rsa_predict: [direct/not-gt] failed: {e.toMessageData}"
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
