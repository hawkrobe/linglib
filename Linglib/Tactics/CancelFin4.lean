import Linglib.Core.Scales.EpistemicScale.CancellationHelpers
import Linglib.Tactics.NgeFS

/-!
# Cancellation tactics for EpistemicSystemFA (Fin 4)

- `cancel_fin4`: packages `cancellation_from_pairs` with explicit pair lists
- `solve_cancellation`: auto-computes lt_pairs and eq_pairs from integer weights,
  pre-derives all ¬ge facts via a multi-pass fixpoint loop, then applies
  `cancellation_from_pairs`
-/

open Core.Scale

-- ══════════════════════════════════════════════════════════════
-- § 1. cancel_fin4: macro with explicit pair lists
-- ══════════════════════════════════════════════════════════════

open Lean in
/-- Convenience macro for calling `cancellation_from_pairs` with standard proof
    obligations. Takes weight vector, lt_pairs list, and eq_pairs list.
    Use `lt_pairs` and `eq_pairs` keywords to separate arguments. -/
macro "cancel_fin4" ws:term "lt_pairs" lt:term "eq_pairs" eq:term : tactic => do
  let cfp := mkIdent ``cancellation_from_pairs
  `(tactic|
    exact $cfp ‹_› $ws
      (by intro i; fin_cases i <;> norm_num)
      (by simp [Fin.sum_univ_four]; norm_num)
      ‹_›
      $lt (by native_decide)
      (by hlt_nge_close)
      $eq (by native_decide)
      (by hge_assumption))

-- ══════════════════════════════════════════════════════════════
-- § 2. solve_cancellation: auto-compute pairs from weights
-- ══════════════════════════════════════════════════════════════

/-- Weight sum for elements selected by a bitmask over {0,1,2,3}. -/
private def scWeightSum (w0 w1 w2 w3 : Nat) (mask : Nat) : Nat :=
  (if mask % 2 == 1 then w0 else 0) +
  (if mask / 2 % 2 == 1 then w1 else 0) +
  (if mask / 4 % 2 == 1 then w2 else 0) +
  (if mask / 8 % 2 == 1 then w3 else 0)

/-- Elements selected by a bitmask, as a sorted list of indices. -/
private def scBitmaskElts (mask : Nat) : List Nat :=
  (if mask % 2 == 1 then [0] else []) ++
  (if mask / 2 % 2 == 1 then [1] else []) ++
  (if mask / 4 % 2 == 1 then [2] else []) ++
  (if mask / 8 % 2 == 1 then [3] else [])

/-- Check if two bitmasks select disjoint subsets. -/
private def scDisjoint (a b : Nat) : Bool :=
  !(a % 2 == 1 && b % 2 == 1) &&
  !(a / 2 % 2 == 1 && b / 2 % 2 == 1) &&
  !(a / 4 % 2 == 1 && b / 4 % 2 == 1) &&
  !(a / 8 % 2 == 1 && b / 8 % 2 == 1)

/-- Classify all nonempty disjoint subset pairs by weight sum comparison.
    Returns (lt_pairs, eq_pairs) where lt_pairs has pairs (A, B) with
    sum_A < sum_B, and eq_pairs has pairs with sum_A = sum_B. -/
private def scClassifyPairs (w0 w1 w2 w3 : Nat) :
    List (List Nat × List Nat) × List (List Nat × List Nat) := Id.run do
  let masks := List.range 15 |>.map (· + 1)
  let mut lt : Array (List Nat × List Nat) := #[]
  let mut eq : Array (List Nat × List Nat) := #[]
  for a in masks do
    for b in masks do
      if scDisjoint a b then
        let sA := scWeightSum w0 w1 w2 w3 a
        let sB := scWeightSum w0 w1 w2 w3 b
        if sA < sB then
          lt := lt.push (scBitmaskElts a, scBitmaskElts b)
        else if sA == sB then
          eq := eq.push (scBitmaskElts a, scBitmaskElts b)
  (lt.toList, eq.toList)

open Lean in
/-- Build Finset (Fin 4) syntax from element indices. -/
private def scMkFinsetSyn (elts : List Nat) : MacroM (TSyntax `term) := do
  let mkN (n : Nat) : TSyntax `term := ⟨Syntax.mkNumLit s!"{n}"⟩
  let fin4 := mkIdent ``Fin
  match elts with
  | [] => Macro.throwError "scMkFinsetSyn: empty element list"
  | [a] => `((Singleton.singleton ($(mkN a) : $fin4 4) : Finset ($fin4 4)))
  | _ =>
    let last := elts.getLast!
    let mut acc ← `((Singleton.singleton ($(mkN last) : $fin4 4) : Finset ($fin4 4)))
    for e in elts.dropLast.reverse do
      acc ← `(Insert.insert ($(mkN e) : $fin4 4) $acc)
    return acc

open Lean in
/-- Build Set (Fin 4) syntax from element indices. -/
private def scMkSetSyn : List Nat → MacroM (TSyntax `term)
  | [] => `((∅ : Set (Fin 4)))
  | [a] =>
    let mkN := (⟨Syntax.mkNumLit s!"{a}"⟩ : TSyntax `term)
    `(({($mkN : Fin 4)} : Set (Fin 4)))
  | a :: rest => do
    let mkN := (⟨Syntax.mkNumLit s!"{a}"⟩ : TSyntax `term)
    let inner ← scMkSetSyn rest
    `(Insert.insert ($mkN : Fin 4) $inner)

open Lean in
/-- Build `[(A₁, B₁), ...]` list syntax from classified pairs. -/
private def scMkPairListSyn (pairs : List (List Nat × List Nat)) :
    MacroM (TSyntax `term) := do
  let pairsSyn ← pairs.mapM fun (a, b) => do
    let aSyn ← scMkFinsetSyn a
    let bSyn ← scMkFinsetSyn b
    `(($aSyn, $bSyn))
  let arr := pairsSyn.toArray
  `([$[$arr],*])


open Lean Lean.Elab Lean.Elab.Tactic in
/-- Auto-compute cancellation from integer weights. Usage: `solve_cancellation 7 6 3 2`.
    The weights are relative proportions — internally normalized to sum to 1.
    Saturates the proof context with singleton transitive closure and totality
    resolutions, then derives all ¬ge facts via `hlt_nge_close`. -/
elab "solve_cancellation" n0:num n1:num n2:num n3:num : tactic => do
  let w0 := n0.getNat
  let w1 := n1.getNat
  let w2 := n2.getNat
  let w3 := n3.getNat
  let total := w0 + w1 + w2 + w3
  let (ltPairs, eqPairs) := scClassifyPairs w0 w1 w2 w3
  -- Apply cancellation_from_pairs
  let mkR (n : Nat) : MacroM (TSyntax `term) := do
    let num := Syntax.mkNumLit s!"{n}"
    let den := Syntax.mkNumLit s!"{total}"
    `(($num : ℚ) / $den)
  let r0 ← liftMacroM (mkR w0)
  let r1 ← liftMacroM (mkR w1)
  let r2 ← liftMacroM (mkR w2)
  let r3 ← liftMacroM (mkR w3)
  let wsSyn ← `(![$r0, $r1, $r2, $r3])
  let ltSyn ← liftMacroM (scMkPairListSyn ltPairs)
  let eqSyn ← liftMacroM (scMkPairListSyn eqPairs)
  let cfp := mkIdent ``cancellation_from_pairs
  -- Find the EpistemicSystemFA hypothesis name
  let sysName ← do
    let goal ← getMainGoal
    goal.withContext do
      let lctx ← getLCtx
      for decl in lctx do
        if decl.isAuxDecl then continue
        let ty ← instantiateMVars decl.type
        if ty.isAppOfArity ``EpistemicSystemFA 1 then
          return decl.userName
      throwError "solve_cancellation: no EpistemicSystemFA found"
  let sysId : TSyntax `term := ⟨mkIdent sysName⟩
  -- Pre-derive transitive singleton ge facts (e.g., h03 from h01+h12+h23)
  evalTactic (← `(tactic| saturate_singleton_ge))
  -- Pre-derive all ¬ge facts for lt_pairs so hlt_assumption can close them
  for (aElts, bElts) in ltPairs do
    let aSyn ← liftMacroM (scMkSetSyn aElts)
    let bSyn ← liftMacroM (scMkSetSyn bElts)
    let aStr := String.join (aElts.map toString)
    let bStr := String.join (bElts.map toString)
    let freshId : TSyntax `ident :=
      ⟨mkIdent (Name.mkSimple s!"_nge_{aStr}_{bStr}")⟩
    let s ← saveState
    try
      evalTactic (← `(tactic|
        have $freshId : ¬($sysId).ge $aSyn $bSyn := by
          first | assumption | nge_double_additive | nge_close | nge_overlap))
    catch _ => restoreState s
  -- Pre-derive eq_pair reverse ge facts so heq can be closed by assumption
  for (aElts, bElts) in eqPairs do
    let aSyn ← liftMacroM (scMkSetSyn aElts)
    let bSyn ← liftMacroM (scMkSetSyn bElts)
    let aStr := String.join (aElts.map toString)
    let bStr := String.join (bElts.map toString)
    let freshId : TSyntax `ident :=
      ⟨mkIdent (Name.mkSimple s!"_geq_{aStr}_{bStr}")⟩
    let s ← saveState
    try
      evalTactic (← `(tactic|
        have $freshId : ($sysId).ge $aSyn $bSyn := by
          first | assumption
                | (apply EpistemicSystemFA.trans ‹_› <;> assumption)
                | ge_via_additive))
    catch _ => restoreState s
  -- Apply cancellation_from_pairs (all ge/¬ge facts now in context)
  if eqPairs.isEmpty then
    evalTactic (← `(tactic|
      exact $cfp ‹_› $wsSyn
        (by intro i; fin_cases i <;> norm_num)
        (by simp [Fin.sum_univ_four]; norm_num)
        ‹_›
        $ltSyn (by native_decide)
        (by hlt_assumption)
        $eqSyn (by native_decide)
        (by intro _ hmem; cases hmem)))
  else
    evalTactic (← `(tactic|
      exact $cfp ‹_› $wsSyn
        (by intro i; fin_cases i <;> norm_num)
        (by simp [Fin.sum_univ_four]; norm_num)
        ‹_›
        $ltSyn (by native_decide)
        (by hlt_assumption)
        $eqSyn (by native_decide)
        (by hge_trans)))
