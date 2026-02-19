import Lean

/-!
# nonneg_of_forall tactic

Closes `0 ≤ f a₁ + f a₂ + ⋯ + f aₙ` given `∀ x, 0 ≤ f x` in context.

Decomposes sums via `add_nonneg` (and products via `mul_nonneg`), then
closes leaf goals by applying forall-quantified non-negativity hypotheses
from the local context.

Typical usage at `RSAConfig.qud` call sites:
```
qudProject_nonneg := by
  intro q f w hf; cases q <;> simp [myProject] <;> nonneg_of_forall
```
-/

open Lean Meta Elab Tactic

/-- Decompose `0 ≤ a + b` or `0 ≤ a * b` goals, then close leaves
    by applying hypotheses from the local context. -/
private partial def nonnegCore (goals : List MVarId) : TacticM Unit := do
  match goals with
  | [] => return
  | goal :: rest =>
    if ← goal.isAssigned then
      nonnegCore rest
      return
    -- Try add_nonneg: 0 ≤ a + b ← 0 ≤ a ∧ 0 ≤ b
    let tryAdd ← try
      let gs ← goal.apply (← mkConstWithFreshMVarLevels `add_nonneg)
      pure (some gs)
    catch _ => pure none
    match tryAdd with
    | some gs => nonnegCore (gs ++ rest); return
    | none => pure ()
    -- Try mul_nonneg: 0 ≤ a * b ← 0 ≤ a ∧ 0 ≤ b
    let tryMul ← try
      let gs ← goal.apply (← mkConstWithFreshMVarLevels `mul_nonneg)
      pure (some gs)
    catch _ => pure none
    match tryMul with
    | some gs => nonnegCore (gs ++ rest); return
    | none => pure ()
    -- Leaf: try each local hypothesis via apply (handles ∀ x, 0 ≤ f x)
    let ctx ← goal.withContext getLCtx
    let mut closed := false
    for decl in ctx do
      if closed then break
      if decl.isAuxDecl then continue
      try
        let gs ← goal.apply decl.toExpr
        if gs.isEmpty then closed := true
      catch _ => continue
    if !closed then
      throwTacticEx `nonneg_of_forall goal "cannot close leaf goal"
    nonnegCore rest

/-- Close `0 ≤ f a₁ + f a₂ + ⋯ + f aₙ` given `∀ x, 0 ≤ f x` in context.

Decomposes sums via `add_nonneg` (and products via `mul_nonneg`), then
closes leaf goals by applying forall-quantified non-negativity hypotheses
from the local context. -/
elab "nonneg_of_forall" : tactic => do
  let goals ← getGoals
  nonnegCore goals
  setGoals []
