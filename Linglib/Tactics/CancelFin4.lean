import Linglib.Core.Scales.EpistemicScale.CancellationHelpers
import Linglib.Tactics.NgeFS

/-!
# Cancellation tactics for EpistemicSystemFA (Fin 4)

- `cancel_fin4`: packages `cancellation_from_pairs` with explicit pair lists
- `solve_cancellation`: auto-computes lt_pairs and eq_pairs from integer weights,
  derives all ¬ge/ge facts via deterministic meta-level strategy selection,
  then applies `cancellation_from_pairs`
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

-- ══════════════════════════════════════════════════════════════
-- § 3. Meta-level helpers for deterministic proof construction
-- ══════════════════════════════════════════════════════════════

/-- Set difference on element lists. -/
private def scElDiff (a b : List Nat) : List Nat := a.filter (· ∉ b)

/-- Subset check on element lists. -/
private def scElSubset (a b : List Nat) : Bool := a.all (· ∈ b)

/-- Set equality on element lists (order-independent). -/
private def scElEq (a b : List Nat) : Bool := scElSubset a b && scElSubset b a

/-- Normalize element list (sort for consistent keys). -/
private def scNorm (l : List Nat) : List Nat := l.mergeSort (· ≤ ·)

/-- Extract a natural number from an `OfNat.ofNat` expression. -/
private def scExtractOfNat (e : Lean.Expr) : Option Nat :=
  if e.isAppOf ``OfNat.ofNat then
    let args := e.getAppArgs
    if h : args.size > 1 then
      match args[1] with
      | .lit (.natVal n) => some n
      | _ => none
    else none
  else none

/-- Extract elements from a `Set (Fin n)` expression. -/
private partial def scExtractSetElems (e : Lean.Expr) : List Nat :=
  if e.isAppOf ``Insert.insert then
    let args := e.getAppArgs
    if h : args.size > 4 then
      match scExtractOfNat args[3] with
      | some n => n :: scExtractSetElems args[4]
      | none => []
    else []
  else if e.isAppOf ``Singleton.singleton then
    let args := e.getAppArgs
    if h : args.size > 3 then
      match scExtractOfNat args[3] with
      | some n => [n]
      | none => []
    else []
  else []

/-- Extract (A_elems, B_elems) from `sys.ge A B`. -/
private def scExtractGe (ty : Lean.Expr) : Option (List Nat × List Nat) :=
  if ty.isAppOf ``Not then none
  else if ty.getAppNumArgs ≥ 2 then
    let B := ty.appArg!
    let D := ty.appFn!.appArg!
    some (scExtractSetElems D, scExtractSetElems B)
  else none

/-- Extract (A_elems, B_elems) from `¬sys.ge A B`. -/
private def scExtractNge (ty : Lean.Expr) : Option (List Nat × List Nat) :=
  if ty.isAppOf ``Not then
    let inner := ty.appArg!
    if inner.getAppNumArgs ≥ 2 then
      let B := inner.appArg!
      let D := inner.appFn!.appArg!
      some (scExtractSetElems D, scExtractSetElems B)
    else none
  else none

/-- Database of known ge/¬ge facts. -/
private structure FactDB where
  ge  : Array (List Nat × List Nat × Lean.Name) := #[]
  nge : Array (List Nat × List Nat × Lean.Name) := #[]

private def FactDB.findGe (db : FactDB) (a b : List Nat) : Option Lean.Name :=
  db.ge.findSome? fun (a', b', n) =>
    if scElEq a' a && scElEq b' b then some n else none

private def FactDB.findNge (db : FactDB) (a b : List Nat) : Option Lean.Name :=
  db.nge.findSome? fun (a', b', n) =>
    if scElEq a' a && scElEq b' b then some n else none

-- ══════════════════════════════════════════════════════════════
-- § 4. Deterministic ¬ge derivation
-- ══════════════════════════════════════════════════════════════

/-- Prove a Set (Fin 4) diff equality by reducing to Finset sdiff (decidable). -/
elab "sc_sdiff" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    (simp only [← Finset.coe_insert, ← Finset.coe_singleton, ← Finset.coe_empty,
       ← Finset.coe_sdiff]; first | rfl | (congr 1; decide))))

/-- Prove a Set.Nonempty goal by exhibiting a computed witness. -/
elab "sc_nonempty " n:num : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    exact ⟨⟨$n, by omega⟩,
      by simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, Fin.ext_iff]; omega⟩))

open Lean Lean.Elab Lean.Elab.Tactic in
/-- Try to derive ¬ge A B from known facts using deterministic strategies.
    Returns updated FactDB on success. -/
private def deriveNge (aE bE : List Nat) (db : FactDB) (sysId : TSyntax `term)
    (cnt : Nat) : TacticM (Option (FactDB × Nat)) := do
  -- Already known
  if db.findNge aE bE |>.isSome then return some (db, cnt)
  let aStr := String.join (aE.map toString)
  let bStr := String.join (bE.map toString)
  let mkFresh (tag : String) : Lean.Name := Name.mkSimple s!"_nge_{tag}_{aStr}_{bStr}_{cnt}"
  let aSyn ← liftMacroM (scMkSetSyn aE)
  let bSyn ← liftMacroM (scMkSetSyn bE)
  -- Strategy 1: hpos (A ⊆ B proper subset)
  if scElSubset aE bE then
    let diff := scElDiff bE aE
    if !diff.isEmpty then
      let wLit : TSyntax `num := ⟨Syntax.mkNumLit s!"{diff.head!}"⟩
      let name := mkFresh "hp"
      let freshId : TSyntax `ident := ⟨mkIdent name⟩
      let s ← saveState
      try
        evalTactic (← `(tactic|
          have $freshId : ¬($sysId).ge $aSyn $bSyn := by
            refine nge_via_hpos_all ‹_› ‹_› ?_ ?_
            · sc_sdiff
            · sc_nonempty $wLit))
        return some ({ db with nge := db.nge.push (aE, bE, name) }, cnt + 1)
      catch _ => restoreState s
  -- Strategy 2: additive reduction (¬ge (A\B) (B\A) known)
  let aDiffB := scNorm (scElDiff aE bE)
  let bDiffA := scNorm (scElDiff bE aE)
  if !aDiffB.isEmpty && !bDiffA.isEmpty then
    if let some ngeH := db.findNge aDiffB bDiffA then
      let name := mkFresh "am"
      let freshId : TSyntax `ident := ⟨mkIdent name⟩
      let ngeId : TSyntax `term := ⟨mkIdent ngeH⟩
      let s ← saveState
      try
        evalTactic (← `(tactic|
          have $freshId : ¬($sysId).ge $aSyn $bSyn := by
            refine nge_of_additive_mp ‹_› $ngeId ?_ ?_ <;> sc_sdiff))
        return some ({ db with nge := db.nge.push (aE, bE, name) }, cnt + 1)
      catch _ => restoreState s
  -- Strategy 3: mono_left (¬ge C B known, A ⊆ C, A ≠ C)
  for (cE, bE', ngeH) in db.nge do
    if !scElEq bE' bE then continue
    if !scElSubset aE cE then continue
    if scElEq aE cE then continue
    let name := mkFresh "ml"
    let freshId : TSyntax `ident := ⟨mkIdent name⟩
    let ngeId : TSyntax `term := ⟨mkIdent ngeH⟩
    let s ← saveState
    try
      evalTactic (← `(tactic|
        have $freshId : ¬($sysId).ge $aSyn $bSyn := by
          refine nge_of_mono_left_set ‹_› $ngeId ?_
          intro x hx; fin_cases x <;> simp_all))
      return some ({ db with nge := db.nge.push (aE, bE, name) }, cnt + 1)
    catch _ => restoreState s
  -- Strategy 4: mono_right (¬ge A C known, C ⊆ B, C ≠ B)
  for (aE', cE, ngeH) in db.nge do
    if !scElEq aE' aE then continue
    if !scElSubset cE bE then continue
    if scElEq cE bE then continue
    let name := mkFresh "mr"
    let freshId : TSyntax `ident := ⟨mkIdent name⟩
    let ngeId : TSyntax `term := ⟨mkIdent ngeH⟩
    let s ← saveState
    try
      evalTactic (← `(tactic|
        have $freshId : ¬($sysId).ge $aSyn $bSyn := by
          refine nge_of_mono_right_set ‹_› $ngeId ?_
          intro x hx; fin_cases x <;> simp_all))
      return some ({ db with nge := db.nge.push (aE, bE, name) }, cnt + 1)
    catch _ => restoreState s
  -- Strategy 5: trans_right (¬ge A C known, ge B C known)
  for (aE', cE, ngeH) in db.nge do
    if !scElEq aE' aE then continue
    if let some geH := db.findGe bE cE then
      let name := mkFresh "tr"
      let freshId : TSyntax `ident := ⟨mkIdent name⟩
      let ngeId : TSyntax `term := ⟨mkIdent ngeH⟩
      let geId : TSyntax `term := ⟨mkIdent geH⟩
      let s ← saveState
      try
        evalTactic (← `(tactic|
          have $freshId : ¬($sysId).ge $aSyn $bSyn :=
            nge_of_trans_right_set ‹_› $ngeId $geId))
        return some ({ db with nge := db.nge.push (aE, bE, name) }, cnt + 1)
      catch _ => restoreState s
  -- Strategy 6: trans_left (¬ge C B known, ge C A known)
  for (cE, bE', ngeH) in db.nge do
    if !scElEq bE' bE then continue
    if let some geH := db.findGe cE aE then
      let name := mkFresh "tl"
      let freshId : TSyntax `ident := ⟨mkIdent name⟩
      let ngeId : TSyntax `term := ⟨mkIdent ngeH⟩
      let geId : TSyntax `term := ⟨mkIdent geH⟩
      let s ← saveState
      try
        evalTactic (← `(tactic|
          have $freshId : ¬($sysId).ge $aSyn $bSyn :=
            nge_of_trans_left_set ‹_› $ngeId $geId))
        return some ({ db with nge := db.nge.push (aE, bE, name) }, cnt + 1)
      catch _ => restoreState s
  -- Strategy 7: trans_overlap (ge C A known, C ⊆ B, B\C nonempty)
  for (cE, aE', geH) in db.ge do
    if !scElEq aE' aE then continue
    if !scElSubset cE bE then continue
    let bDiffC := scElDiff bE cE
    if bDiffC.isEmpty then continue
    let wLit : TSyntax `num := ⟨Syntax.mkNumLit s!"{bDiffC.head!}"⟩
    let name := mkFresh "to"
    let freshId : TSyntax `ident := ⟨mkIdent name⟩
    let geId : TSyntax `term := ⟨mkIdent geH⟩
    let s ← saveState
    try
      evalTactic (← `(tactic|
        have $freshId : ¬($sysId).ge $aSyn $bSyn := by
          refine nge_of_trans_overlap ‹_› ‹_› $geId ?_ ?_
          · sc_sdiff
          · sc_nonempty $wLit))
      return some ({ db with nge := db.nge.push (aE, bE, name) }, cnt + 1)
    catch _ => restoreState s
  -- Strategy 8: trans_superset (ge B C known, A ⊆ C, C\A nonempty)
  for (bE', cE, geH) in db.ge do
    if !scElEq bE' bE then continue
    if !scElSubset aE cE then continue
    let cDiffA := scElDiff cE aE
    if cDiffA.isEmpty then continue
    let wLit : TSyntax `num := ⟨Syntax.mkNumLit s!"{cDiffA.head!}"⟩
    let name := mkFresh "ts"
    let freshId : TSyntax `ident := ⟨mkIdent name⟩
    let geId : TSyntax `term := ⟨mkIdent geH⟩
    let s ← saveState
    try
      evalTactic (← `(tactic|
        have $freshId : ¬($sysId).ge $aSyn $bSyn := by
          refine nge_of_trans_superset ‹_› ‹_› $geId ?_ ?_
          · sc_sdiff
          · sc_nonempty $wLit))
      return some ({ db with nge := db.nge.push (aE, bE, name) }, cnt + 1)
    catch _ => restoreState s
  -- Strategy 9: double_additive (bridge C)
  for (d1E, e1E, geH) in db.ge do
    -- C = D1 ∪ (A \ E1)
    let cE := scNorm ((d1E ++ scElDiff aE e1E).eraseDups)
    -- Verify C\A = D1, A\C = E1
    if !scElEq (scNorm (scElDiff cE aE)) (scNorm d1E) then continue
    if !scElEq (scNorm (scElDiff aE cE)) (scNorm e1E) then continue
    -- Need ¬ge (C\B) (B\C)
    let cDiffB := scNorm (scElDiff cE bE)
    let bDiffC := scNorm (scElDiff bE cE)
    if let some ngeH := db.findNge cDiffB bDiffC then
      let cSyn ← liftMacroM (scMkSetSyn cE)
      let name := mkFresh "da"
      let freshId : TSyntax `ident := ⟨mkIdent name⟩
      let geId : TSyntax `term := ⟨mkIdent geH⟩
      let ngeId : TSyntax `term := ⟨mkIdent ngeH⟩
      let s ← saveState
      try
        evalTactic (← `(tactic|
          have $freshId : ¬($sysId).ge $aSyn $bSyn := by
            refine @nge_of_double_additive _ ‹_› _ _ $cSyn _ _ _ _
              $geId ?_ ?_ $ngeId ?_ ?_ <;> sc_sdiff))
        return some ({ db with nge := db.nge.push (aE, bE, name) }, cnt + 1)
      catch _ => restoreState s
  -- Strategy 10: additive then trans_right
  -- ¬ge (A\X) (X\A) known, ge B X known → ¬ge A X (additive) → ¬ge A B (trans)
  for (dE, eE, ngeH) in db.nge do
    let xE := scNorm ((scElDiff aE dE ++ eE).eraseDups)
    if !scElEq (scNorm (scElDiff aE xE)) (scNorm dE) then continue
    if !scElEq (scNorm (scElDiff xE aE)) (scNorm eE) then continue
    if scElEq xE bE then continue  -- would be strategy 2
    if let some geH := db.findGe bE xE then
      let xSyn ← liftMacroM (scMkSetSyn xE)
      let intermName := Name.mkSimple s!"_nge_atr1_{aStr}_{cnt}"
      let intermId : TSyntax `ident := ⟨mkIdent intermName⟩
      let name := mkFresh "atr"
      let freshId : TSyntax `ident := ⟨mkIdent name⟩
      let ngeId : TSyntax `term := ⟨mkIdent ngeH⟩
      let geId : TSyntax `term := ⟨mkIdent geH⟩
      let s ← saveState
      try
        evalTactic (← `(tactic|
          have $intermId : ¬($sysId).ge $aSyn $xSyn := by
            refine nge_of_additive_mp ‹_› $ngeId ?_ ?_ <;> sc_sdiff))
        evalTactic (← `(tactic|
          have $freshId : ¬($sysId).ge $aSyn $bSyn :=
            nge_of_trans_right_set ‹_› $intermId $geId))
        return some ({ db with nge := db.nge.push (aE, bE, name) }, cnt + 1)
      catch _ => restoreState s
  -- Strategy 11: additive then trans_left
  -- ¬ge (X\B) (B\X) known, ge X A known → ¬ge X B (additive) → ¬ge A B (trans)
  for (dE, eE, ngeH) in db.nge do
    let xE := scNorm ((scElDiff bE eE ++ dE).eraseDups)
    if !scElEq (scNorm (scElDiff xE bE)) (scNorm dE) then continue
    if !scElEq (scNorm (scElDiff bE xE)) (scNorm eE) then continue
    if scElEq xE aE then continue  -- would be strategy 2
    if let some geH := db.findGe xE aE then
      let xSyn ← liftMacroM (scMkSetSyn xE)
      let intermName := Name.mkSimple s!"_nge_atl1_{bStr}_{cnt}"
      let intermId : TSyntax `ident := ⟨mkIdent intermName⟩
      let name := mkFresh "atl"
      let freshId : TSyntax `ident := ⟨mkIdent name⟩
      let ngeId : TSyntax `term := ⟨mkIdent ngeH⟩
      let geId : TSyntax `term := ⟨mkIdent geH⟩
      let s ← saveState
      try
        evalTactic (← `(tactic|
          have $intermId : ¬($sysId).ge $xSyn $bSyn := by
            refine nge_of_additive_mp ‹_› $ngeId ?_ ?_ <;> sc_sdiff))
        evalTactic (← `(tactic|
          have $freshId : ¬($sysId).ge $aSyn $bSyn :=
            nge_of_trans_left_set ‹_› $intermId $geId))
        return some ({ db with nge := db.nge.push (aE, bE, name) }, cnt + 1)
      catch _ => restoreState s
  return none

-- ══════════════════════════════════════════════════════════════
-- § 5. Deterministic ge derivation
-- ══════════════════════════════════════════════════════════════

open Lean Lean.Elab Lean.Elab.Tactic in
/-- Try to derive ge A B from known facts. Returns updated FactDB on success. -/
private def deriveGe (aE bE : List Nat) (db : FactDB) (sysId : TSyntax `term)
    (cnt : Nat) : TacticM (Option (FactDB × Nat)) := do
  if db.findGe aE bE |>.isSome then return some (db, cnt)
  let aStr := String.join (aE.map toString)
  let bStr := String.join (bE.map toString)
  let aSyn ← liftMacroM (scMkSetSyn aE)
  let bSyn ← liftMacroM (scMkSetSyn bE)
  -- Strategy 1: trans (ge A C and ge C B both known)
  for (aE', cE, geH1) in db.ge do
    if !scElEq aE' aE then continue
    if let some geH2 := db.findGe cE bE then
      let name := Name.mkSimple s!"_ge_t_{aStr}_{bStr}_{cnt}"
      let freshId : TSyntax `ident := ⟨mkIdent name⟩
      let ge1Id : TSyntax `term := ⟨mkIdent geH1⟩
      let ge2Id : TSyntax `term := ⟨mkIdent geH2⟩
      let s ← saveState
      try
        evalTactic (← `(tactic|
          have $freshId : ($sysId).ge $aSyn $bSyn :=
            ($sysId).trans _ _ _ $ge1Id $ge2Id))
        return some ({ db with ge := db.ge.push (aE, bE, name) }, cnt + 1)
      catch _ => restoreState s
  -- Strategy 2: additive_trans (ge (A\C) (C\A) and ge C B)
  for (d1E, e1E, geH1) in db.ge do
    -- C = (A \ D1) ∪ E1
    let cE := scNorm ((scElDiff aE d1E ++ e1E).eraseDups)
    if !scElEq (scNorm (scElDiff aE cE)) (scNorm d1E) then continue
    if !scElEq (scNorm (scElDiff cE aE)) (scNorm e1E) then continue
    if let some geH2 := db.findGe cE bE then
      let cSyn ← liftMacroM (scMkSetSyn cE)
      let name := Name.mkSimple s!"_ge_at_{aStr}_{bStr}_{cnt}"
      let freshId : TSyntax `ident := ⟨mkIdent name⟩
      let ge1Id : TSyntax `term := ⟨mkIdent geH1⟩
      let ge2Id : TSyntax `term := ⟨mkIdent geH2⟩
      let s ← saveState
      try
        evalTactic (← `(tactic|
          have $freshId : ($sysId).ge $aSyn $bSyn := by
            refine @ge_of_additive_trans _ ‹_› _ $cSyn _ _ _
              $ge1Id ?_ ?_ $ge2Id <;> sc_sdiff))
        return some ({ db with ge := db.ge.push (aE, bE, name) }, cnt + 1)
      catch _ => restoreState s
  -- Strategy 3: double_additive_pos (bridge C)
  for (d1E, e1E, geH1) in db.ge do
    let cE := scNorm ((scElDiff aE d1E ++ e1E).eraseDups)
    if !scElEq (scNorm (scElDiff aE cE)) (scNorm d1E) then continue
    if !scElEq (scNorm (scElDiff cE aE)) (scNorm e1E) then continue
    let cDiffB := scNorm (scElDiff cE bE)
    let bDiffC := scNorm (scElDiff bE cE)
    if let some geH2 := db.findGe cDiffB bDiffC then
      let cSyn ← liftMacroM (scMkSetSyn cE)
      let name := Name.mkSimple s!"_ge_da_{aStr}_{bStr}_{cnt}"
      let freshId : TSyntax `ident := ⟨mkIdent name⟩
      let ge1Id : TSyntax `term := ⟨mkIdent geH1⟩
      let ge2Id : TSyntax `term := ⟨mkIdent geH2⟩
      let s ← saveState
      try
        evalTactic (← `(tactic|
          have $freshId : ($sysId).ge $aSyn $bSyn := by
            refine @ge_of_double_additive_pos _ ‹_› _ $cSyn _ _ _ _ _
              $ge1Id ?_ ?_ $ge2Id ?_ ?_ <;> sc_sdiff))
        return some ({ db with ge := db.ge.push (aE, bE, name) }, cnt + 1)
      catch _ => restoreState s
  return none

-- ══════════════════════════════════════════════════════════════
-- § 6. solve_cancellation: main entry point
-- ══════════════════════════════════════════════════════════════

open Lean Lean.Elab Lean.Elab.Tactic in
/-- Auto-compute cancellation from integer weights. Usage: `solve_cancellation 7 6 3 2`.
    Derives all ¬ge/ge facts via deterministic meta-level strategy selection
    (no backtracking search), then applies `cancellation_from_pairs`. -/
elab "solve_cancellation" n0:num n1:num n2:num n3:num : tactic => do
  let w0 := n0.getNat
  let w1 := n1.getNat
  let w2 := n2.getNat
  let w3 := n3.getNat
  let total := w0 + w1 + w2 + w3
  let (ltPairs, eqPairs) := scClassifyPairs w0 w1 w2 w3
  -- Build weight vector syntax
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
  -- Find sys hypothesis
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
  -- Phase 1: Collect known ge/¬ge facts from context
  let mut db : FactDB := {}
  let goal ← getMainGoal
  let (geFacts, ngeFacts) ← goal.withContext do
    let lctx ← getLCtx
    let mut geFacts : Array (List Nat × List Nat × Lean.Name) := #[]
    let mut ngeFacts : Array (List Nat × List Nat × Lean.Name) := #[]
    for decl in lctx do
      if decl.isAuxDecl then continue
      let ty ← instantiateMVars decl.type
      match scExtractGe ty with
      | some (d, e) =>
        if !d.isEmpty || !e.isEmpty then
          geFacts := geFacts.push (d, e, decl.userName)
      | none => pure ()
      match scExtractNge ty with
      | some (d, e) =>
        if !d.isEmpty || !e.isEmpty then
          ngeFacts := ngeFacts.push (d, e, decl.userName)
      | none => pure ()
    return (geFacts, ngeFacts)
  db := { ge := geFacts, nge := ngeFacts }
  -- Phase 2: Transitive closure of singleton ge facts (2 rounds)
  for _ in [0, 1] do
    let singleGe := db.ge.filter fun (d, e, _) => d.length == 1 && e.length == 1
    for (d1, e1, h1Name) in singleGe do
      for (d2, e2, h2Name) in singleGe do
        if e1.head! != d2.head! then continue  -- chain: d1→e1=d2→e2
        if d1.head! == e2.head! then continue   -- trivial
        if db.findGe d1 e2 |>.isSome then continue
        let h1Id : TSyntax `term := ⟨mkIdent h1Name⟩
        let h2Id : TSyntax `term := ⟨mkIdent h2Name⟩
        let freshName := Name.mkSimple s!"_hge_t_{d1.head!}_{e2.head!}"
        let freshId : TSyntax `ident := ⟨mkIdent freshName⟩
        let s ← saveState
        try
          evalTactic (← `(tactic|
            have $freshId := ($sysId).trans _ _ _ $h1Id $h2Id))
          db := { db with ge := db.ge.push (d1, e2, freshName) }
        catch _ => restoreState s
  -- Phase 3: Derive ¬ge facts for lt_pairs (multi-pass fixpoint)
  let mut cnt : Nat := 0
  for _ in [0, 1, 2, 3] do  -- up to 4 rounds
    let mut progress := false
    for (aElts, bElts) in ltPairs do
      if db.findNge aElts bElts |>.isSome then continue
      match ← deriveNge aElts bElts db sysId cnt with
      | some (db', cnt') => db := db'; cnt := cnt'; progress := true
      | none => pure ()
    if !progress then break
  -- Phase 4: Derive ge facts for eq_pairs (multi-pass)
  for _ in [0, 1, 2] do
    let mut progress := false
    for (aElts, bElts) in eqPairs do
      if db.findGe aElts bElts |>.isSome then continue
      match ← deriveGe aElts bElts db sysId cnt with
      | some (db', cnt') => db := db'; cnt := cnt'; progress := true
      | none => pure ()
    if !progress then break
  -- Phase 5: Apply cancellation_from_pairs
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
