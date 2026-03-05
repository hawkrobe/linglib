import Lean
import Linglib.Tactics.RSAPredict.Helpers

set_option autoImplicit false

/-!
# Finset.sum Expansion for RSA Predict

Transforms `Finset.sum Finset.univ f` into `(l.map f).sum` where `l` is a concrete
list of all elements. The kernel can efficiently reduce `List.map`/`List.sum` via
simple iota-reduction (O(n) pattern matches), whereas `Finset.sum` goes through
`Multiset`/`Quotient` infrastructure that the kernel cannot efficiently handle.

## Architecture

The expansion happens BEFORE reification. For each `Finset.sum` in the goal expression:
1. Enumerate elements of the finite type → concrete list `l`
2. Prove `l.Nodup` and `l.toFinset = Finset.univ` via `native_decide`
3. Apply bridge theorem: `∑ x, f x = (l.map f).sum`
4. Use `kabstract` + `congrArg` to propagate the equality through the expression context

After expansion, the reifier processes `(l.map f).sum`, which the kernel reduces
to `f a₀ + (f a₁ + (... + 0))` via simple `List.map`/`List.sum` pattern matching.
-/

namespace Linglib.Tactics.RSAPredict

open Lean Meta Elab Tactic

-- ============================================================================
-- Bridge Theorems
-- ============================================================================

/-- Bridge: `Finset.sum` over `Finset.univ` equals `List.sum` of mapped list.
    Uses Mathlib's `List.sum_toFinset` (additive version of `List.prod_toFinset`). -/
theorem finset_sum_eq_list_map_sum {ι : Type} {M : Type} [AddCommMonoid M]
    [DecidableEq ι] [Fintype ι]
    (l : List ι) (f : ι → M) (h_nd : l.Nodup) (h_eq : l.toFinset = Finset.univ) :
    Finset.sum Finset.univ f = (l.map f).sum := by
  rw [← h_eq]
  exact List.sum_toFinset f h_nd

/-- Bridge for GT comparisons through equalities. -/
theorem gt_of_eq_gt_eq {a b c d : ℝ} (hac : a = c) (hbd : b = d) (h : c > d) :
    a > b :=
  hac ▸ hbd ▸ h

/-- Bridge for not-GT comparisons through equalities. -/
theorem not_gt_of_eq_not_gt_eq {a b c d : ℝ} (hac : a = c) (hbd : b = d)
    (h : ¬(c > d)) : ¬(a > b) :=
  hac ▸ hbd ▸ h

/-- Bridge for equality comparisons through equalities. -/
theorem eq_of_eq_eq_eq {a b c d : ℝ} (hac : a = c) (hbd : b = d) (h : c = d) :
    a = b :=
  hac ▸ hbd ▸ h

-- ============================================================================
-- Native Decide Helper
-- ============================================================================

/-- Prove a Prop via `native_decide`. Returns the proof term. -/
def nativeDecideProof (propType : Expr) : TacticM Expr := do
  let mvar ← mkFreshExprMVar propType
  let savedGoals ← getGoals
  setGoals [mvar.mvarId!]
  evalTactic (← `(tactic| native_decide))
  setGoals savedGoals
  return mvar

-- ============================================================================
-- Single Finset.sum Expansion
-- ============================================================================

/-- Expand a single `Finset.sum Finset.univ f` to `(l.map f).sum`.
    Returns `(expandedExpr, eqProof)` where `eqProof : sumExpr = expandedExpr`. -/
def expandOneFinsetSum (sumExpr : Expr) : TacticM (Expr × Expr) := do
  let args := sumExpr.getAppArgs
  -- Finset.sum args: [ι, M, instAddCommMonoid, s, f]
  let ι := args[0]!
  let f := args[4]!

  -- Enumerate elements of ι
  let (listExpr, _elems) ← getFiniteElems ι

  -- Build (l.map f).sum
  let mappedList ← mkAppM ``List.map #[f, listExpr]
  let expandedSum ← mkAppM ``List.sum #[mappedList]

  -- Prove l.Nodup via native_decide
  let nodupProp ← mkAppM ``List.Nodup #[listExpr]
  let h_nd ← nativeDecideProof nodupProp

  -- Prove l.toFinset = Finset.univ via native_decide
  let toFinsetExpr ← mkAppM ``List.toFinset #[listExpr]
  let univExpr ← mkAppOptM ``Finset.univ #[ι, none]
  let eqProp ← mkEq toFinsetExpr univExpr
  let h_eq ← nativeDecideProof eqProp

  -- Apply bridge theorem
  let proof ← mkAppM ``finset_sum_eq_list_map_sum #[listExpr, f, h_nd, h_eq]

  return (expandedSum, proof)

-- ============================================================================
-- Recursive Expansion
-- ============================================================================

/-- Check if an expression is `Finset.sum s f` where `s` is `Finset.univ`. -/
private def isFinsetSumUniv (e : Expr) : MetaM Bool := do
  if !(e.getAppFn.isConstOf ``Finset.sum && e.getAppNumArgs ≥ 5) then return false
  let s := e.getAppArgs[3]!
  let sW ← withReducible (whnf s)
  return sW.getAppFn.isConstOf ``Finset.univ

/-- Collect all `Finset.sum Finset.univ f` subexpressions in `e` that have no
    loose bound variables (i.e., are self-contained). Returns them in bottom-up
    order (leaves first). -/
private partial def collectFinsetSums (e : Expr) : MetaM (Array Expr) := do
  let ref ← IO.mkRef (#[] : Array Expr)
  go ref e
  ref.get
where
  go (ref : IO.Ref (Array Expr)) (e : Expr) : MetaM Unit := do
    -- Recurse into application arguments
    for arg in e.getAppArgs do
      go ref arg
    -- Check if this is a Finset.sum Finset.univ (with no loose bvars)
    if !e.hasLooseBVars then
      if ← isFinsetSumUniv e then
        ref.modify fun arr => arr.push e

/-- Expand all `Finset.sum Finset.univ` occurrences in an expression.
    Uses `kabstract` + `congrArg` to propagate equality through the context.
    Returns `(expandedExpr, eqProof?)` where `eqProof : e = expandedExpr`. -/
def expandFinsetSums (e : Expr) : TacticM (Expr × Option Expr) := do
  let sums ← collectFinsetSums e
  if sums.isEmpty then return (e, none)

  let mut current := e
  let mut totalProof? : Option Expr := none

  for sumExpr in sums do
    -- Check if this sum still appears in current (it might have been
    -- inside a previously expanded sum and already replaced).
    -- Use a two-pass approach: first check containment, then replace.
    let found := Option.isSome <| current.find? fun sub => sub.equal sumExpr
    if !found then continue
    -- Replace the sum occurrence with bvar 0 to build abstraction body
    let body := current.replace fun sub =>
      if sub.equal sumExpr then some (mkBVar 0) else none

    -- Expand this sum
    let result ← try
      let (expandedSum, h_sum) ← expandOneFinsetSum sumExpr

      -- Build congruence: current = current[sumExpr ↦ expandedSum]
      let sumType ← inferType sumExpr
      let ctx := Expr.lam `z sumType body BinderInfo.default
      let h_step ← mkAppM ``congrArg #[ctx, h_sum]

      -- Update current expression
      let newCurrent := body.instantiate1 expandedSum
      pure (some (newCurrent, h_step))
    catch _ =>
      pure none

    if let some (newCurrent, h_step) := result then
      current := newCurrent
      totalProof? ← match totalProof? with
        | none => pure (some h_step)
        | some h_prev => do
          let composed ← mkAppM ``Eq.trans #[h_prev, h_step]
          pure (some composed)

  return (current, totalProof?)

end Linglib.Tactics.RSAPredict
