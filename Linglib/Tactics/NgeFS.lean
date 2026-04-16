import Linglib.Core.Scales.EpistemicScale.FinsetBridge
import Lean.Elab.Tactic

/-!
# Automation for ¬ge and ¬geFS derivations

The `nge_close` tactic automatically derives negated ordering facts
(`¬sys.ge A B`) from hypotheses in the local context. It handles compositions
of monotonicity, transitivity, and positivity lemmas up to depth 3, with
backtracking over hypothesis assignments.

## Supported patterns

* **0-step**: direct `assumption`
* **1-step**: `nge_of_mono_right_set`, `nge_of_mono_left_set`,
  `nge_of_trans_left_set`, `nge_of_trans_right_set`, `nge_via_hpos_set`
* **2-step**: compositions like `mono_right ∘ trans_left`, etc.
* **3-step**: `mono_right ∘ trans_left ∘ trans_left`, etc.

Subset obligations (`C ⊆ B`) on Sets are closed by
`intro x hx; fin_cases x <;> simp_all`. On Finsets, by `decide`.
-/

open Core.Scale
open Lean Elab Tactic Meta

namespace Tactics.NgeFS

variable {n : ℕ}

/-- Variant of `ngeFS_of_mono_right` without autoParam, suitable for `apply`. -/
theorem ngeFS_of_mono_right' (sys : EpistemicSystemFA (Fin n))
    {A C B : Finset (Fin n)}
    (hng : ¬sys.geFS A C) (h : C ⊆ B) :
    ¬sys.geFS A B := ngeFS_of_mono_right sys B hng h

/-- Variant of `ngeFS_of_mono_left` without autoParam, suitable for `apply`. -/
theorem ngeFS_of_mono_left' (sys : EpistemicSystemFA (Fin n))
    {C B A : Finset (Fin n)}
    (hng : ¬sys.geFS C B) (h : A ⊆ C) :
    ¬sys.geFS A B := ngeFS_of_mono_left sys A hng h

/-- Check if an expression is a negation (¬P or P → False). -/
private def isNeg (e : Expr) : Bool :=
  e.isAppOf ``Not || match e with
    | .forallE _ _ (.const ``False _) _ => true
    | _ => false

/-- Try a tactic on goal `g`, succeeding only if all resulting goals close. -/
private def tryTac (g : MVarId) (tac : TacticM Unit) : TacticM Bool := do
  let s ← saveState
  try
    setGoals [g]
    tac
    let remaining ← getGoals
    let mut allDone := true
    for rg in remaining do
      if !(← rg.isAssigned) then allDone := false; break
    if allDone then return true
    restoreState s; return false
  catch _ => restoreState s; return false

/-- Try closing a single goal with assumption, decide, fin_cases, or trans. -/
private def closeOne (g : MVarId) : TacticM Bool := do
  if ← g.isAssigned then return true
  -- assumption
  if ← tryTac g (evalTactic (← `(tactic| assumption))) then return true
  -- decide (Finset subsets, etc.)
  if ← tryTac g (evalTactic (← `(tactic| decide))) then return true
  -- Set subset: intro x hx; fin_cases x <;> simp_all
  if ← tryTac g (evalTactic (← `(tactic| (intro x hx; fin_cases x <;> simp_all)))) then
    return true
  -- Set diff: ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff]
  if ← tryTac g (evalTactic (← `(tactic|
      (ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff])))) then
    return true
  -- geFS_trans for composed positive geFS goals
  if ← tryTac g (evalTactic (← `(tactic|
      (apply EpistemicSystemFA.geFS_trans <;> assumption)))) then
    return true
  -- ge trans for composed positive ge goals
  if ← tryTac g (evalTactic (← `(tactic|
      (apply EpistemicSystemFA.trans <;> assumption)))) then
    return true
  -- Try applying a universal hypothesis (e.g., hpos : ∀ i, ¬ge ∅ {i})
  let s ← saveState
  try
    setGoals [g]
    evalTactic (← `(tactic| (apply ‹_›)))
    let remaining ← getGoals
    let mut ok := true
    for rg in remaining do
      if ← rg.isAssigned then continue
      setGoals [rg]
      try evalTactic (← `(tactic| decide)); continue
      catch _ => try evalTactic (← `(tactic| (fin_cases ‹_› <;> simp_all))); continue
      catch _ => ok := false; break
    if ok then return true
    restoreState s
  catch _ => restoreState s
  return false

/-- Try closing all remaining goals. -/
private def closeAll : TacticM Bool := do
  for g in (← getGoals) do
    if ← g.isAssigned then continue
    if !(← closeOne g) then return false
  return true

/-- Try `apply lem`, then close subgoals. First tries closing everything
    directly (handles via_hpos where decide determines metavars first).
    Falls back to: for the ¬-type subgoal, try each hypothesis with
    backtracking, then close remaining with closeAll. -/
private def tryLem (lem : Name) : TacticM Bool := do
  let goal ← getMainGoal
  let lctx ← goal.withContext getLCtx
  let s ← saveState
  try
    let subgoals ← goal.apply (← mkConstWithFreshMVarLevels lem)
    setGoals subgoals
    -- Fast path: try closing everything directly (decide first, then others)
    let s1 ← saveState
    -- First pass: close decidable/computable goals to determine metavariables
    -- Skip goals whose types contain unresolved metavars (they need other goals
    -- to be solved first to determine their metavars)
    for g in subgoals do
      if ← g.isAssigned then continue
      let gType ← instantiateMVars (← g.getType)
      if gType.hasExprMVar then continue
      setGoals [g]
      let sg ← saveState
      try evalTactic (← `(tactic| decide)); continue catch _ => restoreState sg
      try
        evalTactic (← `(tactic|
          (ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff])))
        -- Verify all resulting goals are fully closed (ext/fin_cases/simp can
        -- partially close goals without throwing, leaving metavar holes)
        let mut allClosed := true
        for rg in (← getGoals) do
          if !(← rg.isAssigned) then allClosed := false; break
        if allClosed then continue
        restoreState sg
      catch _ => restoreState sg
    -- Second pass: close remaining goals
    setGoals subgoals
    if ← closeAll then return true
    restoreState s1
    -- Slow path: find neg subgoal, try hypotheses with backtracking
    let mut negGoal : Option MVarId := none
    for g in subgoals do
      if ← g.isAssigned then continue
      let t ← instantiateMVars (← g.getType)
      if isNeg t || isNeg (← whnf t) then
        negGoal := some g
        break
    if let some ng := negGoal then
      -- Collect hypotheses into array for iteration
      let mut hyps : Array LocalDecl := #[]
      for decl in lctx do
        if decl.isAuxDecl then continue
        hyps := hyps.push decl
      for decl in hyps do
        let s2 ← saveState
        try
          -- Compute type fresh each iteration (avoids stale metavar state)
          let ngType ← instantiateMVars (← ng.getType)
          if ← isDefEq ngType decl.type then
            ng.assign decl.toExpr
            let remaining := subgoals.filter (· != ng)
            -- First pass: close equality/decidable goals to determine metavars
            for rg in remaining do
              if ← rg.isAssigned then continue
              let rgType ← instantiateMVars (← rg.getType)
              if rgType.hasExprMVar then continue
              setGoals [rg]
              let srg ← saveState
              try evalTactic (← `(tactic| decide)); continue catch _ => restoreState srg
              try
                evalTactic (← `(tactic|
                  (ext x; fin_cases x <;> simp [Set.mem_diff, Set.mem_insert_iff])))
                -- Verify all resulting goals are fully closed
                let mut allClosed := true
                for rg2 in (← getGoals) do
                  if !(← rg2.isAssigned) then allClosed := false; break
                if allClosed then continue
                restoreState srg
              catch _ => restoreState srg
            setGoals remaining
            if ← closeAll then return true
          restoreState s2
        catch _ => restoreState s2
      restoreState s; return false
    else
      if ← closeAll then return true
      restoreState s; return false
  catch _ => restoreState s; return false

/-- 2-step: apply outer, then tryLem inner on the neg subgoal.
    First tries inner directly (handles cases where inner determines metavars).
    Falls back to backtracking over hypotheses for pos subgoals with metavars,
    which determines outer metavars before running inner. -/
private def try2 (outer inner : Name) : TacticM Bool := do
  let goal ← getMainGoal
  let lctx ← goal.withContext getLCtx
  let s ← saveState
  try
    -- Try 1: original approach (inner determines metavars via backtracking)
    let outerGoals ← goal.apply (← mkConstWithFreshMVarLevels outer)
    for g in outerGoals do
      if ← g.isAssigned then continue
      let t ← instantiateMVars (← g.getType)
      if isNeg t || isNeg (← whnf t) then
        setGoals [g]
        if ← tryLem inner then
          let remaining := outerGoals.filter (· != g)
          setGoals remaining
          if ← closeAll then return true
    restoreState s
    -- Try 2: determine outer pos metavars first via hypothesis backtracking
    let outerGoals2 ← goal.apply (← mkConstWithFreshMVarLevels outer)
    let mut negGoal : Option MVarId := none
    let mut posGoals : Array MVarId := #[]
    for g in outerGoals2 do
      if ← g.isAssigned then continue
      let t ← instantiateMVars (← g.getType)
      if isNeg t || isNeg (← whnf t) then
        if negGoal.isNone then negGoal := some g
      else
        posGoals := posGoals.push g
    if let some ng := negGoal then
      -- Find first pos goal with unresolved metavars
      let mut metaPosGoal : Option MVarId := none
      for pg in posGoals do
        if ← pg.isAssigned then continue
        let pgType ← instantiateMVars (← pg.getType)
        if pgType.hasExprMVar then
          metaPosGoal := some pg
          break
      if let some mpg := metaPosGoal then
        let mut hyps : Array LocalDecl := #[]
        for decl in lctx do
          if decl.isAuxDecl then continue
          hyps := hyps.push decl
        for decl in hyps do
          let s2 ← saveState
          try
            let mpgType ← instantiateMVars (← mpg.getType)
            if ← isDefEq mpgType decl.type then
              mpg.assign decl.toExpr
              setGoals [ng]
              if ← tryLem inner then
                let remaining := outerGoals2.filter (· != ng)
                setGoals remaining
                if ← closeAll then return true
            restoreState s2
          catch _ => restoreState s2
    restoreState s; return false
  catch _ => restoreState s; return false

/-- 3-step: outer ∘ (middle ∘ inner) on the neg subgoal. -/
private def try3 (outer middle inner : Name) : TacticM Bool := do
  let goal ← getMainGoal
  let s ← saveState
  try
    let outerGoals ← goal.apply (← mkConstWithFreshMVarLevels outer)
    for g in outerGoals do
      if ← g.isAssigned then continue
      let t ← instantiateMVars (← g.getType)
      if isNeg t || isNeg (← whnf t) then
        setGoals [g]
        if ← try2 middle inner then
          let remaining := outerGoals.filter (· != g)
          setGoals remaining
          if ← closeAll then return true
    restoreState s; return false
  catch _ => restoreState s; return false

/-- All 1-step lemma names (Finset + Set variants). -/
private def lemmas1 : List Name :=
  [``Tactics.NgeFS.ngeFS_of_mono_right', ``Tactics.NgeFS.ngeFS_of_mono_left',
   ``ngeFS_of_trans_left, ``ngeFS_of_trans_right,
   ``ngeFS_via_hpos,
   ``nge_of_mono_right_set, ``nge_of_mono_left_set,
   ``nge_of_trans_left_set, ``nge_of_trans_right_set,
   ``nge_via_hpos_set,
   ``nge_of_additive_mp,
   ``nge_via_hpos_all]

/-- All 2-step (outer, inner) combinations. -/
private def lemmas2 : List (Name × Name) :=
  -- Finset combos
  [(``Tactics.NgeFS.ngeFS_of_mono_right', ``ngeFS_of_trans_left),
   (``Tactics.NgeFS.ngeFS_of_mono_right', ``ngeFS_of_trans_right),
   (``Tactics.NgeFS.ngeFS_of_mono_right', ``Tactics.NgeFS.ngeFS_of_mono_right'),
   (``Tactics.NgeFS.ngeFS_of_mono_right', ``Tactics.NgeFS.ngeFS_of_mono_left'),
   (``Tactics.NgeFS.ngeFS_of_mono_left', ``Tactics.NgeFS.ngeFS_of_mono_left'),
   (``Tactics.NgeFS.ngeFS_of_mono_left', ``ngeFS_of_trans_left),
   (``Tactics.NgeFS.ngeFS_of_mono_left', ``ngeFS_of_trans_right),
   -- Set combos
   (``nge_of_mono_right_set, ``nge_of_trans_left_set),
   (``nge_of_mono_right_set, ``nge_of_trans_right_set),
   (``nge_of_mono_right_set, ``nge_of_mono_right_set),
   (``nge_of_mono_right_set, ``nge_of_mono_left_set),
   (``nge_of_mono_left_set, ``nge_of_mono_left_set),
   (``nge_of_mono_left_set, ``nge_of_trans_left_set),
   (``nge_of_mono_left_set, ``nge_of_trans_right_set),
   -- Trans-trans combos (singleton chains)
   (``nge_of_trans_left_set, ``nge_of_trans_left_set),
   (``nge_of_trans_left_set, ``nge_of_trans_right_set),
   (``nge_of_trans_right_set, ``nge_of_trans_left_set),
   (``nge_of_trans_right_set, ``nge_of_trans_right_set),
   -- Additive combos
   (``nge_of_trans_left_set, ``nge_via_hpos_set),
   (``nge_of_trans_right_set, ``nge_via_hpos_set),
   (``nge_of_trans_left_set, ``nge_via_hpos_all),
   (``nge_of_trans_right_set, ``nge_via_hpos_all),
   (``nge_of_trans_left_set, ``nge_of_additive_mp),
   (``nge_of_trans_right_set, ``nge_of_additive_mp),
   (``nge_of_mono_right_set, ``nge_of_additive_trans_left),
   (``nge_of_mono_left_set, ``nge_of_additive_trans_left),
   (``nge_of_mono_right_set, ``nge_via_hpos_set),
   (``nge_of_mono_left_set, ``nge_via_hpos_set),
   (``nge_of_mono_right_set, ``nge_via_hpos_all),
   (``nge_of_mono_left_set, ``nge_via_hpos_all)]

/-- All 3-step (outer, middle, inner) combinations. -/
private def lemmas3 : List (Name × Name × Name) :=
  -- Finset combos
  [(``Tactics.NgeFS.ngeFS_of_mono_right', ``ngeFS_of_trans_left, ``ngeFS_of_trans_left),
   (``Tactics.NgeFS.ngeFS_of_mono_right', ``ngeFS_of_trans_left, ``ngeFS_of_trans_right),
   (``Tactics.NgeFS.ngeFS_of_mono_right', ``Tactics.NgeFS.ngeFS_of_mono_right', ``ngeFS_of_trans_left),
   (``Tactics.NgeFS.ngeFS_of_mono_right', ``Tactics.NgeFS.ngeFS_of_mono_left', ``ngeFS_of_trans_left),
   (``Tactics.NgeFS.ngeFS_of_mono_left', ``ngeFS_of_trans_left, ``ngeFS_of_trans_left),
   (``Tactics.NgeFS.ngeFS_of_mono_left', ``ngeFS_of_trans_left, ``ngeFS_of_trans_right),
   -- Set combos
   (``nge_of_mono_right_set, ``nge_of_trans_left_set, ``nge_of_trans_left_set),
   (``nge_of_mono_right_set, ``nge_of_trans_left_set, ``nge_of_trans_right_set),
   (``nge_of_mono_right_set, ``nge_of_mono_right_set, ``nge_of_trans_left_set),
   (``nge_of_mono_right_set, ``nge_of_mono_left_set, ``nge_of_trans_left_set),
   (``nge_of_mono_left_set, ``nge_of_trans_left_set, ``nge_of_trans_left_set),
   (``nge_of_mono_left_set, ``nge_of_trans_left_set, ``nge_of_trans_right_set)]

end Tactics.NgeFS

/-- Automatically derive `¬sys.ge A B` or `¬sys.geFS A B` from hypotheses
    via compositions of monotonicity, transitivity, and positivity lemmas
    (up to depth 3). Works with both Set-typed and Finset-typed goals. -/
elab "nge_close" : tactic => do
  let goal ← getMainGoal
  let otherGoals := (← getGoals).filter (· != goal)
  setGoals [goal]
  -- 0-step
  try goal.assumption; setGoals otherGoals; return catch _ => pure ()
  -- 1-step
  for lem in Tactics.NgeFS.lemmas1 do
    if ← Tactics.NgeFS.tryLem lem then setGoals otherGoals; return
  -- 2-step
  for (o, i) in Tactics.NgeFS.lemmas2 do
    if ← Tactics.NgeFS.try2 o i then setGoals otherGoals; return
  -- 3-step
  for (o, m, i) in Tactics.NgeFS.lemmas3 do
    if ← Tactics.NgeFS.try3 o m i then setGoals otherGoals; return
  throwError "nge_close: no pattern matched"

/-- Close `∀ pair ∈ pairs, ¬sys.ge ↑pair.1 ↑pair.2` goals by iterating over
    list membership, substituting each pair, normalizing Finset→Set coercions,
    and closing by `assumption`. Used in the `hlt` argument of
    `cancellation_from_pairs`.

    Strategy: intro a single pair variable (not destructured), normalize
    membership to `pair = v₁ ∨ pair = v₂ ∨ ...` via `simp`, then peel
    disjuncts with `rcases h | hmem`. Each `subst h` substitutes the whole
    pair, after which `simp` reduces Prod projections via iota and normalizes
    `Finset.coe`, and `assumption` matches a hypothesis. Sequential (not `<;>`)
    composition ensures each `subst`+close block targets only the first goal
    from `rcases`. The final bare equality is handled after `repeat`. -/
macro "hlt_assumption" : tactic =>
  `(tactic|
    (intro pair hmem
     simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
     repeat (
       rcases hmem with h | hmem
       subst h
       simp only [Finset.coe_insert, Finset.coe_singleton]
       assumption)
     subst hmem
     simp only [Finset.coe_insert, Finset.coe_singleton]
     assumption))

/-- Derive `¬ge A B` via trans+additive+hpos: find a hypothesis `ge C A` in context
    where `C ⊆ B` and `B\C` nonempty. Tries each ge hypothesis × witness pair. -/
elab "nge_overlap" : tactic => do
  let goal ← getMainGoal
  let hyps ← goal.withContext do
    let lctx ← getLCtx
    let mut hyps : Array Name := #[]
    for decl in lctx do
      if decl.isAuxDecl then continue
      hyps := hyps.push decl.userName
    return hyps
  for name in hyps do
    for j in ([0, 1, 2, 3] : List Nat) do
      let hId : TSyntax `term := ⟨mkIdent name⟩
      let jLit : TSyntax `num := ⟨Syntax.mkNumLit s!"{j}"⟩
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine nge_of_trans_overlap ‹_› ‹_› $hId ?_ ?_))
        evalTactic (← `(tactic|
          ext x; fin_cases x <;>
            simp [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]))
        evalTactic (← `(tactic|
          refine ⟨⟨$jLit, ?_⟩, ?_⟩))
        evalTactic (← `(tactic| omega))
        evalTactic (← `(tactic|
          simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff]))
        evalTactic (← `(tactic| omega))
        return
      catch _ => restoreState s
  throwError "nge_overlap: no ge hypothesis found with C ⊆ B and B\\C nonempty"

/-- Extract a natural number from an `OfNat.ofNat` expression. -/
private def extractOfNat (e : Expr) : Option Nat :=
  if e.isAppOf ``OfNat.ofNat then
    let args := e.getAppArgs
    if h : args.size > 1 then
      match args[1] with
      | .lit (.natVal n) => some n
      | _ => none
    else none
  else none

/-- Extract elements from a `Set (Fin n)` expression built with
    `Insert.insert` and `Singleton.singleton`. -/
private partial def extractSetElems (e : Expr) : List Nat :=
  if e.isAppOf ``Insert.insert then
    let args := e.getAppArgs
    if h : args.size > 4 then
      match extractOfNat args[3] with
      | some n => n :: extractSetElems args[4]
      | none => []
    else []
  else if e.isAppOf ``Singleton.singleton then
    let args := e.getAppArgs
    if h : args.size > 3 then
      match extractOfNat args[3] with
      | some n => [n]
      | none => []
    else []
  else []

/-- Extract (A_elems, B_elems) from a goal of the form `¬sys.ge A B`. -/
private def extractGoalSets (goalType : Expr) : Option (List Nat × List Nat) :=
  if goalType.isAppOf ``Not then
    let inner := goalType.appArg!
    if inner.getAppNumArgs ≥ 2 then
      let B := inner.appArg!
      let A := inner.appFn!.appArg!
      some (extractSetElems A, extractSetElems B)
    else none
  else none

/-- Extract (D_elems, E_elems) from a hypothesis type `sys.ge D E`. -/
private def extractGeHypSets (ty : Expr) : Option (List Nat × List Nat) :=
  if ty.getAppNumArgs ≥ 2 then
    let E := ty.appArg!
    let D := ty.appFn!.appArg!
    -- Verify the head is ge-like (not a ¬ or other connective)
    if ty.isAppOf ``Not then none
    else some (extractSetElems D, extractSetElems E)
  else none

/-- Extract (D_elems, E_elems) from a hypothesis type `¬sys.ge D E`. -/
private def extractNgeHypSets (ty : Expr) : Option (List Nat × List Nat) :=
  if ty.isAppOf ``Not then
    let inner := ty.appArg!
    if inner.getAppNumArgs ≥ 2 then
      let E := inner.appArg!
      let D := inner.appFn!.appArg!
      some (extractSetElems D, extractSetElems E)
    else none
  else none

/-- Build syntax for a `Set (Fin 4)` from a list of Nat elements. -/
private def mkSetSyntax (elems : List Nat) : CoreM (TSyntax `term) := do
  match elems with
  | [] => `((∅ : Set (Fin 4)))
  | [a] =>
    let aLit : TSyntax `num := ⟨Syntax.mkNumLit s!"{a}"⟩
    `(({($aLit : Fin 4)} : Set (Fin 4)))
  | a :: rest => do
    let aLit : TSyntax `num := ⟨Syntax.mkNumLit s!"{a}"⟩
    let inner ← mkSetSyntax rest
    `(Insert.insert ($aLit : Fin 4) $inner)

/-- List difference (elements of xs not in ys). -/
private def listDiff (xs ys : List Nat) : List Nat :=
  xs.filter (· ∉ ys)

/-- Derive `¬ge A B` via double additive: find hypotheses `ge D1 E1` and `¬ge D2 E2`
    in context such that `nge_of_double_additive` applies with computed bridge set C.
    C is computed as D1 ∪ (A \ E1), then verified against D2, E2, B. -/
elab "nge_double_additive" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let some (aElems, bElems) := extractGoalSets goalType
    | throwError "nge_double_additive: goal is not ¬sys.ge A B"
  -- Collect ge and ¬ge hypotheses with their set elements
  let (geHyps, ngeHyps) ← goal.withContext do
    let lctx ← getLCtx
    let mut geHyps : Array (Name × List Nat × List Nat) := #[]
    let mut ngeHyps : Array (Name × List Nat × List Nat) := #[]
    for decl in lctx do
      if decl.isAuxDecl then continue
      let ty ← instantiateMVars decl.type
      match extractGeHypSets ty with
      | some (d, e) => if !d.isEmpty && !e.isEmpty then
          geHyps := geHyps.push (decl.userName, d, e)
      | none => pure ()
      match extractNgeHypSets ty with
      | some (d, e) => if !d.isEmpty && !e.isEmpty then
          ngeHyps := ngeHyps.push (decl.userName, d, e)
      | none => pure ()
    return (geHyps, ngeHyps)
  -- For each ge hypothesis, compute C and check if a matching ¬ge exists
  for (geName, d1Elems, e1Elems) in geHyps do
    -- C = D1 ∪ (A \ E1)
    let cElems := (d1Elems ++ listDiff aElems e1Elems).eraseDups
    -- Verify C \ A = D1 and A \ C = E1
    let cDiffA := listDiff cElems aElems
    let aDiffC := listDiff aElems cElems
    if cDiffA.length != d1Elems.length then continue
    if aDiffC.length != e1Elems.length then continue
    if !d1Elems.all (· ∈ cDiffA) then continue
    if !e1Elems.all (· ∈ aDiffC) then continue
    -- Compute what we need from the ¬ge side
    let d2Needed := listDiff cElems bElems
    let e2Needed := listDiff bElems cElems
    -- Search for matching ¬ge hypothesis
    for (ngeName, d2Elems, e2Elems) in ngeHyps do
      if d2Elems.length != d2Needed.length then continue
      if e2Elems.length != e2Needed.length then continue
      if !d2Needed.all (· ∈ d2Elems) then continue
      if !e2Needed.all (· ∈ e2Elems) then continue
      -- Found a match! Build C syntax and apply
      let cSyn ← mkSetSyntax cElems
      let geId : TSyntax `term := ⟨mkIdent geName⟩
      let ngeId : TSyntax `term := ⟨mkIdent ngeName⟩
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine @nge_of_double_additive _ ‹_› _ _ $cSyn _ _ _ _
            $geId ?_ ?_ $ngeId ?_ ?_))
        evalTactic (← `(tactic|
          all_goals (ext x; fin_cases x <;>
            simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff,
              Fin.ext_iff] <;> omega)))
        return
      catch _ => restoreState s
  throwError "nge_double_additive: no matching ge/¬ge hypothesis pair found"

/-- Derive `ge B A` via one additive step + one trans step, or two additive steps.
    Mirrors `nge_double_additive` but for positive ge facts:
    1. One additive + trans: find singleton ge {d} {e} with d ∈ B, e ∉ B,
       compute C = (B\{d})∪{e}, and check if ge C A is in context.
    2. Double additive: as above, then also check if ge (C\A) (A\C) is in context. -/
elab "ge_via_additive" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  -- Extract ge B A from goal (NOT negated)
  let some (bElems, aElems) := extractGeHypSets goalType
    | throwError "ge_via_additive: goal is not sys.ge B A"
  -- Collect all ge hypotheses
  let geHyps ← goal.withContext do
    let lctx ← getLCtx
    let mut hyps : Array (Name × List Nat × List Nat) := #[]
    for decl in lctx do
      if decl.isAuxDecl then continue
      let ty ← instantiateMVars decl.type
      match extractGeHypSets ty with
      | some (d, e) => if !d.isEmpty && !e.isEmpty then
          hyps := hyps.push (decl.userName, d, e)
      | none => pure ()
    return hyps
  -- Pattern 1: one additive + trans with ge hypothesis
  for (singletonName, dElems, eElems) in geHyps do
    if dElems.length != 1 || eElems.length != 1 then continue
    let d := dElems.head!
    let e := eElems.head!
    if !bElems.any (· == d) then continue  -- d must be in B
    if bElems.any (· == e) then continue   -- e must not be in B
    -- C = (B \ {d}) ∪ {e}
    let cElems := (bElems.filter (· != d) ++ [e]).eraseDups
    -- Check if ge C A is directly in context
    for (caName, caD, caE) in geHyps do
      if caD.length != cElems.length || caE.length != aElems.length then continue
      if !cElems.all (· ∈ caD) || !caD.all (· ∈ cElems) then continue
      if !aElems.all (· ∈ caE) || !caE.all (· ∈ aElems) then continue
      -- Found match! Apply ge_of_additive_trans
      let cSyn ← mkSetSyntax cElems
      let sId : TSyntax `term := ⟨mkIdent singletonName⟩
      let caId : TSyntax `term := ⟨mkIdent caName⟩
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine @ge_of_additive_trans _ ‹_› _ $cSyn _ _ _ $sId ?_ ?_ $caId))
        evalTactic (← `(tactic|
          all_goals (ext x; fin_cases x <;>
            simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff,
              Fin.ext_iff] <;> omega)))
        return
      catch _ => restoreState s
  -- Pattern 2: double additive
  for (s1Name, d1Elems, e1Elems) in geHyps do
    if d1Elems.length != 1 || e1Elems.length != 1 then continue
    let d1 := d1Elems.head!
    let e1 := e1Elems.head!
    if !bElems.any (· == d1) then continue
    if bElems.any (· == e1) then continue
    let cElems := (bElems.filter (· != d1) ++ [e1]).eraseDups
    -- C\A and A\C
    let cMinusA := cElems.filter (· ∉ aElems)
    let aMinusC := aElems.filter (· ∉ cElems)
    -- Look for singleton ge matching C\A → A\C
    for (s2Name, d2Elems, e2Elems) in geHyps do
      if d2Elems.length != cMinusA.length || e2Elems.length != aMinusC.length then continue
      if !cMinusA.all (· ∈ d2Elems) || !d2Elems.all (· ∈ cMinusA) then continue
      if !aMinusC.all (· ∈ e2Elems) || !e2Elems.all (· ∈ aMinusC) then continue
      let cSyn ← mkSetSyntax cElems
      let s1Id : TSyntax `term := ⟨mkIdent s1Name⟩
      let s2Id : TSyntax `term := ⟨mkIdent s2Name⟩
      let s ← saveState
      try
        evalTactic (← `(tactic|
          refine @ge_of_double_additive_pos _ ‹_› _ $cSyn _ _ _ _ _
            $s1Id ?_ ?_ $s2Id ?_ ?_))
        evalTactic (← `(tactic|
          all_goals (ext x; fin_cases x <;>
            simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff,
              Fin.ext_iff] <;> omega)))
        return
      catch _ => restoreState s
  throwError "ge_via_additive: no pattern matched"

/-- Saturate context with transitively-derived singleton ge facts.
    Collects all singleton `ge {i} {j}` hypotheses, then derives all
    transitive consequences `ge {i} {k}` via `sys.trans`. Two rounds
    for chains up to length 4. -/
elab "saturate_singleton_ge" : tactic => do
  let initGoal ← getMainGoal
  let sysName ← initGoal.withContext do
    let lctx ← getLCtx
    for decl in lctx do
      if decl.isAuxDecl then continue
      let ty ← instantiateMVars decl.type
      if ty.isAppOfArity ``EpistemicSystemFA 1 then
        return decl.userName
    throwError "saturate_singleton_ge: no EpistemicSystemFA found"
  let sysId : TSyntax `term := ⟨mkIdent sysName⟩
  -- Two rounds to saturate chains of length up to 4
  for _ in [0, 1] do
    -- Collect singleton ge hypotheses from current context
    let goal ← getMainGoal
    let geHyps ← goal.withContext do
      let lctx ← getLCtx
      let mut hyps : Array (Name × List Nat × List Nat) := #[]
      for decl in lctx do
        if decl.isAuxDecl then continue
        let ty ← instantiateMVars decl.type
        match extractGeHypSets ty with
        | some (d, e) =>
          if d.length == 1 && e.length == 1 then
            hyps := hyps.push (decl.userName, d, e)
        | none => pure ()
      return hyps
    -- Try all pairs of singleton ge hypotheses
    let mut counter : Nat := 0
    for (h1Name, d1, _) in geHyps do
      for (h2Name, _, e2) in geHyps do
        let h1Id : TSyntax `term := ⟨mkIdent h1Name⟩
        let h2Id : TSyntax `term := ⟨mkIdent h2Name⟩
        let freshName := Name.mkSimple s!"_hge_{d1.head!}_{e2.head!}_{counter}"
        let freshId : TSyntax `ident := ⟨mkIdent freshName⟩
        let s ← saveState
        try
          evalTactic (← `(tactic|
            have $freshId := ($sysId).trans _ _ _ $h1Id $h2Id))
          counter := counter + 1
        catch _ => restoreState s

/-- Like `hlt_assumption` but falls back to `nge_close` when `assumption` fails.
    Used in the `hlt` argument of `cancellation_from_pairs` when not all ¬ge
    facts are pre-computed in the context. Processes each pair via rcases,
    closing each ¬ge goal via assumption, nge_double_additive, nge_close,
    or nge_overlap. -/
macro "hlt_nge_close" : tactic =>
  `(tactic|
    (intro pair hmem
     simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
     repeat (
       rcases hmem with h | hmem
       subst h
       simp only [Finset.coe_insert, Finset.coe_singleton]
       first | assumption | nge_double_additive | nge_close | nge_overlap)
     try (subst hmem
          simp only [Finset.coe_insert, Finset.coe_singleton]
          first | assumption | nge_double_additive | nge_close | nge_overlap)))

/-- Close `∀ pair ∈ eq_pairs, sys.ge ↑pair.1 ↑pair.2 → sys.ge ↑pair.2 ↑pair.1`
    goals (the `heq` argument of `cancellation_from_pairs`). Like `hlt_assumption`
    but with an `intro _` step to discharge the antecedent before `assumption`. -/
macro "hge_assumption" : tactic =>
  `(tactic|
    (intro pair hmem
     simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
     repeat (
       rcases hmem with h | hmem
       subst h
       simp only [Finset.coe_insert, Finset.coe_singleton]
       intro _
       assumption)
     subst hmem
     simp only [Finset.coe_insert, Finset.coe_singleton]
     intro _
     assumption))

/-- Like `hge_assumption` but derives ge facts via transitivity when `assumption`
    fails. Handles eq_pairs where the reverse direction needs transitive closure.

    Uses an elab tactic to find the `EpistemicSystemFA` hypothesis by type and
    apply `.trans` using its actual FVar name, avoiding macro hygiene issues. -/
elab "hge_trans" : tactic => do
  let goal ← getMainGoal
  let sysName ← goal.withContext do
    let lctx ← getLCtx
    for decl in lctx do
      if decl.isAuxDecl then continue
      let ty ← instantiateMVars decl.type
      if ty.isAppOfArity ``EpistemicSystemFA 1 then
        return decl.userName
    throwError "hge_trans: no EpistemicSystemFA hypothesis found"
  let sysId : TSyntax `term := ⟨mkIdent sysName⟩
  evalTactic (← `(tactic|
    (intro pair hmem
     simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
     repeat' (
       first
       | (rcases hmem with h | hmem
          subst h
          simp only [Finset.coe_insert, Finset.coe_singleton]
          intro _
          first | assumption
                | (apply ($sysId).trans <;> assumption))
       | (subst hmem
          simp only [Finset.coe_insert, Finset.coe_singleton]
          intro _
          first | assumption
                | (apply ($sysId).trans <;> assumption))))))

