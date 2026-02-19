import Lean
import Linglib.Core.Interval.QInterval
import Linglib.Core.Interval.PadeExp
import Linglib.Core.Interval.RpowInterval

set_option autoImplicit false

/-!
# RSADecide — Verified Predictions via Interval Arithmetic

The `rsa_decide` tactic proves ℝ comparison goals by:
1. Reifying both sides into `QInterval` computations (computable ℚ)
2. Evaluating the intervals
3. Checking separation (decidable on ℚ)
4. Assembling the proof via `gt_of_separated`

For ℚ or decidable goals, dispatches directly to `native_decide`.
-/

namespace Linglib.Tactics

open Lean Meta Elab Tactic
open Linglib.Interval

-- ============================================================================
-- ReifyResult
-- ============================================================================

/-- Result of reifying an ℝ expression into interval arithmetic. -/
private structure RResult where
  /-- QInterval expression (Lean Expr of type QInterval). -/
  interval : Expr
  /-- Proof that interval.containsReal(original_expr). -/
  proof : Expr
  /-- Evaluated lower bound (tracked in MetaM, not kernel). -/
  lo : ℚ
  /-- Evaluated upper bound. -/
  hi : ℚ

-- ============================================================================
-- Expr Inspection Helpers
-- ============================================================================

/-- Extract a natural number from `@OfNat.ofNat T n inst`. -/
private def getOfNat? (e : Expr) : Option ℕ := do
  guard (e.isAppOfArity ``OfNat.ofNat 3)
  e.appFn!.appArg!.rawNatLit?

/-- Extract a natural number from `@Nat.cast T inst n`. -/
private def getNatCast? (e : Expr) : Option ℕ := do
  guard (e.isAppOfArity ``Nat.cast 3)
  e.getAppArgs[2]!.rawNatLit?

/-- Extract a natural number from either `@OfNat.ofNat T n inst` or `@Nat.cast T inst n`. -/
private def getNat? (e : Expr) : Option ℕ :=
  getOfNat? e <|> getNatCast? e

/-- Try to extract a natural number from an expression, unfolding/reducing as needed.
    Handles `cfg.α` → `1`, `@Nat.cast ℝ _ (cfg.α)` → `@Nat.cast ℝ _ 1`,
    and internal forms like `Real.one✝` (via isDefEq against small naturals). -/
private def resolveNat? (e : Expr) : MetaM (Option ℕ) := do
  if let some n := getNat? e then return some n
  let e' ← whnf e
  if let some n := getNat? e' then return some n
  -- If Nat.cast T _ n, try reducing the inner ℕ expression
  if e'.isAppOfArity ``Nat.cast 3 then
    let inner ← whnf e'.getAppArgs[2]!
    return inner.rawNatLit?
  -- Check if defeq to a small natural number (handles Real.one✝ etc.)
  let eType ← inferType e'
  if eType.isConstOf ``Real then
    for n in ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : List ℕ) do
      let nE := mkRawNatLit n
      let target ← mkAppOptM ``OfNat.ofNat #[mkConst ``Real, nE, none]
      let isEq ← withNewMCtxDepth do
        try isDefEq e' target catch _ => return false
      if isEq then return some n
  return none

/-- Check if an expression is an application of a given constant with at least `n` args. -/
private def isAppOfMin (e : Expr) (name : Name) (minArgs : ℕ) : Bool :=
  e.getAppFn.isConstOf name && e.getAppNumArgs ≥ minArgs

-- ============================================================================
-- QInterval Construction Helpers
-- ============================================================================

/-- Construct `@Nat.cast ℚ _ n` — definitionally equal to `(n : ℚ)`.
    Using Nat.cast ensures the proof term aligns with ℝ's `OfNat` instance,
    which is defined as `Nat.cast n`. -/
private def mkNatCastRat (n : ℕ) : MetaM Expr :=
  mkAppOptM ``Nat.cast #[mkConst ``Rat, none, mkRawNatLit n]

/-- Construct `(0 : ℚ)`. -/
private def mkRatZero : MetaM Expr := mkNatCastRat 0

/-- Construct `QInterval.lo I`. -/
private def mkLo (I : Expr) : MetaM Expr := mkAppM ``QInterval.lo #[I]

/-- Construct `QInterval.hi I`. -/
private def mkHi (I : Expr) : MetaM Expr := mkAppM ``QInterval.hi #[I]

-- ============================================================================
-- The Reifier
-- ============================================================================

private def maxReifyDepth : ℕ := 200

/-- Core reifier: ℝ expression → QInterval + containment proof.

Recognized patterns:
- Natural literals: `@OfNat.ofNat ℝ n _` → `exact (n : ℚ)`
- Addition: `HAdd.hAdd` or `Add.add` → `add`
- Multiplication (nonneg): `HMul.hMul` or `Mul.mul` → `mulNonneg`
- Division (nonneg/pos): `HDiv.hDiv` or `Div.div` → `divPos`
- Negation: `Neg.neg` → `neg`
- Subtraction: `HSub.hSub` or `Sub.sub` → `sub`
- Real.rpow with natural exponent → `rpowNat`
- If-then-else: `if x = 0 then a else b` → branch selection
- Unknown: try `unfoldDefinition?`, then `whnf` -/
private partial def reifyCore (e : Expr) (depth : ℕ) : MetaM RResult := do
  if depth == 0 then
    throwError "rsa_decide: max reification depth on: {← ppExpr e}"

  -- Match BEFORE whnf to catch HAdd, HMul, etc. before they unfold to Real internals.

  -- Natural literal: @OfNat.ofNat ℝ n _
  if let some n := getOfNat? e then
    let q : ℚ := n
    let nE := mkRawNatLit n
    let qE ← mkNatCastRat n
    let interval ← mkAppM ``QInterval.exact #[qE]
    let proof ← mkAppM ``QInterval.exact_natCast_containsReal #[nE]
    return { interval, proof, lo := q, hi := q }

  let fn := e.getAppFn
  let args := e.getAppArgs

  -- Addition: @HAdd.hAdd ℝ ℝ ℝ _ a b (6 args)
  if isAppOfMin e ``HAdd.hAdd 6 then
    let ra ← reifyCore args[4]! (depth - 1)
    let rb ← reifyCore args[5]! (depth - 1)
    let interval ← mkAppM ``QInterval.add #[ra.interval, rb.interval]
    let proof ← mkAppM ``QInterval.add_containsReal #[ra.proof, rb.proof]
    return { interval, proof, lo := ra.lo + rb.lo, hi := ra.hi + rb.hi }

  -- Addition: @Add.add ℝ _ a b (4 args) — from whnf/reduce
  if isAppOfMin e ``Add.add 4 then
    let ra ← reifyCore args[2]! (depth - 1)
    let rb ← reifyCore args[3]! (depth - 1)
    let interval ← mkAppM ``QInterval.add #[ra.interval, rb.interval]
    let proof ← mkAppM ``QInterval.add_containsReal #[ra.proof, rb.proof]
    return { interval, proof, lo := ra.lo + rb.lo, hi := ra.hi + rb.hi }

  -- Multiplication: @HMul.hMul ℝ ℝ ℝ _ a b (6 args)
  if isAppOfMin e ``HMul.hMul 6 then
    let ra ← reifyCore args[4]! (depth - 1)
    let rb ← reifyCore args[5]! (depth - 1)
    if ra.lo ≥ 0 && rb.lo ≥ 0 then
      let z ← mkRatZero
      let ha ← mkDecideProof (← mkAppM ``LE.le #[z, ← mkLo ra.interval])
      let hb ← mkDecideProof (← mkAppM ``LE.le #[z, ← mkLo rb.interval])
      let interval ← mkAppM ``QInterval.mulNonneg #[ra.interval, rb.interval, ha, hb]
      let proof ← mkAppM ``QInterval.mulNonneg_containsReal #[ha, hb, ra.proof, rb.proof]
      return { interval, proof, lo := ra.lo * rb.lo, hi := ra.hi * rb.hi }
    else
      throwError "rsa_decide: multiplication with negative intervals not supported"

  -- Multiplication: @Mul.mul ℝ _ a b (4 args) — from whnf/reduce
  if isAppOfMin e ``Mul.mul 4 then
    let ra ← reifyCore args[2]! (depth - 1)
    let rb ← reifyCore args[3]! (depth - 1)
    if ra.lo ≥ 0 && rb.lo ≥ 0 then
      let z ← mkRatZero
      let ha ← mkDecideProof (← mkAppM ``LE.le #[z, ← mkLo ra.interval])
      let hb ← mkDecideProof (← mkAppM ``LE.le #[z, ← mkLo rb.interval])
      let interval ← mkAppM ``QInterval.mulNonneg #[ra.interval, rb.interval, ha, hb]
      let proof ← mkAppM ``QInterval.mulNonneg_containsReal #[ha, hb, ra.proof, rb.proof]
      return { interval, proof, lo := ra.lo * rb.lo, hi := ra.hi * rb.hi }
    else
      throwError "rsa_decide: multiplication with negative intervals not supported"

  -- Division: @HDiv.hDiv ℝ ℝ ℝ _ a b (6 args)
  if isAppOfMin e ``HDiv.hDiv 6 then
    let ra ← reifyCore args[4]! (depth - 1)
    let rb ← reifyCore args[5]! (depth - 1)
    if ra.lo ≥ 0 && rb.lo > 0 then
      let z ← mkRatZero
      let ha ← mkDecideProof (← mkAppM ``LE.le #[z, ← mkLo ra.interval])
      let hb ← mkDecideProof (← mkAppM ``LT.lt #[z, ← mkLo rb.interval])
      let interval ← mkAppM ``QInterval.divPos #[ra.interval, rb.interval, ha, hb]
      let proof ← mkAppM ``QInterval.divPos_containsReal #[ha, hb, ra.proof, rb.proof]
      return { interval, proof, lo := ra.lo / rb.hi, hi := ra.hi / rb.lo }
    else
      throwError "rsa_decide: division requires nonneg numerator and positive denominator"

  -- Division: @Div.div ℝ _ a b (4 args) — from whnf/reduce
  if isAppOfMin e ``Div.div 4 then
    let ra ← reifyCore args[2]! (depth - 1)
    let rb ← reifyCore args[3]! (depth - 1)
    if ra.lo ≥ 0 && rb.lo > 0 then
      let z ← mkRatZero
      let ha ← mkDecideProof (← mkAppM ``LE.le #[z, ← mkLo ra.interval])
      let hb ← mkDecideProof (← mkAppM ``LT.lt #[z, ← mkLo rb.interval])
      let interval ← mkAppM ``QInterval.divPos #[ra.interval, rb.interval, ha, hb]
      let proof ← mkAppM ``QInterval.divPos_containsReal #[ha, hb, ra.proof, rb.proof]
      return { interval, proof, lo := ra.lo / rb.hi, hi := ra.hi / rb.lo }
    else
      throwError "rsa_decide: division requires nonneg numerator and positive denominator"

  -- Negation: @Neg.neg ℝ _ a
  if isAppOfMin e ``Neg.neg 3 then
    let ra ← reifyCore args[2]! (depth - 1)
    let interval ← mkAppM ``QInterval.neg #[ra.interval]
    let proof ← mkAppM ``QInterval.neg_containsReal #[ra.proof]
    return { interval, proof, lo := -ra.hi, hi := -ra.lo }

  -- Subtraction: @HSub.hSub ℝ ℝ ℝ _ a b (6 args)
  if isAppOfMin e ``HSub.hSub 6 then
    let ra ← reifyCore args[4]! (depth - 1)
    let rb ← reifyCore args[5]! (depth - 1)
    let interval ← mkAppM ``QInterval.sub #[ra.interval, rb.interval]
    let proof ← mkAppM ``QInterval.sub_containsReal #[ra.proof, rb.proof]
    return { interval, proof, lo := ra.lo - rb.hi, hi := ra.hi - rb.lo }

  -- Subtraction: @Sub.sub ℝ _ a b (4 args) — from whnf/reduce
  if isAppOfMin e ``Sub.sub 4 then
    let ra ← reifyCore args[2]! (depth - 1)
    let rb ← reifyCore args[3]! (depth - 1)
    let interval ← mkAppM ``QInterval.sub #[ra.interval, rb.interval]
    let proof ← mkAppM ``QInterval.sub_containsReal #[ra.proof, rb.proof]
    return { interval, proof, lo := ra.lo - rb.hi, hi := ra.hi - rb.lo }

  -- Real.rpow: @Real.rpow base exp
  if fn.isConstOf ``Real.rpow && args.size ≥ 2 then
    let base := args[0]!
    let exp := args[1]!
    -- Check if exponent is a natural number (possibly after unfolding cfg.α etc.)
    if let some n ← resolveNat? exp then
      let rb ← reifyCore base (depth - 1)
      if n == 0 then
        -- rpow x 0 = 1
        let interval := ← mkAppM ``Linglib.Interval.rpowZero #[]
        let proof ← mkAppM ``Linglib.Interval.rpowZero_containsReal #[base]
        return { interval, proof, lo := 1, hi := 1 }
      else if n == 1 then
        -- rpow x 1 = x (for nonneg x)
        if rb.lo ≥ 0 then
          let z ← mkRatZero
          let ha ← mkDecideProof (← mkAppM ``LE.le #[z, ← mkLo rb.interval])
          let proof ← mkAppM ``Linglib.Interval.rpowOne_containsReal #[ha, rb.proof]
          return { rb with proof }
        else
          throwError "rsa_decide: rpow with negative base not supported"
      else
        -- rpow x n for n ≥ 2
        if rb.lo ≥ 0 then
          let z ← mkRatZero
          let ha ← mkDecideProof (← mkAppM ``LE.le #[z, ← mkLo rb.interval])
          let nE := mkRawNatLit n
          let interval ← mkAppM ``Linglib.Interval.rpowNat #[rb.interval, nE, ha]
          let proof ← mkAppM ``Linglib.Interval.rpowNat_containsReal #[ha, rb.proof]
          return { interval, proof, lo := rb.lo ^ n, hi := rb.hi ^ n }
        else
          throwError "rsa_decide: rpow with negative base not supported"
    -- Non-natural exponent: try unfolding rpow
    if let some e' ← unfoldDefinition? e then
      return ← reifyCore e' (depth - 1)
    throwError "rsa_decide: rpow with non-natural exponent not supported"

  -- If-then-else: @ite ℝ cond dec thenBr elseBr
  if fn.isConstOf ``ite && args.size ≥ 5 then
    let cond := args[1]!
    let thenBr := args[3]!
    let elseBr := args[4]!
    -- Check if cond is `@Eq ℝ x 0` (no whnf — preserves OfNat structure)
    if cond.isAppOfArity ``Eq 3 then
      let cArgs := cond.getAppArgs
      let lhsC := cArgs[1]!
      let rhsC := cArgs[2]!
      if let some 0 := getOfNat? rhsC then
        -- Condition: lhsC = 0
        let rl ← reifyCore lhsC (depth - 1)
        if rl.lo > 0 then
          -- lhsC > 0 → lhsC ≠ 0 → condition false → take else branch
          let z ← mkRatZero
          let hlo ← mkDecideProof (← mkAppM ``LT.lt #[z, ← mkLo rl.interval])
          let hpos ← mkAppM ``QInterval.pos_of_lo_pos #[rl.proof, hlo]
          let hne ← mkAppM ``ne_of_gt #[hpos]
          let rElse ← reifyCore elseBr (depth - 1)
          -- x (thenBr) is implicit and can't be inferred bottom-up; provide explicitly
          let proof ← mkAppOptM ``QInterval.ite_neg_containsReal
            #[none, none, none, some thenBr, none, some hne, some rElse.proof]
          return { rElse with proof }
        else if rl.lo == 0 && rl.hi == 0 then
          -- lhsC = 0 → condition true → take then branch
          -- TODO: construct equality proof
          throwError "rsa_decide: ite with zero totalScore not yet supported"
        else
          throwError "rsa_decide: cannot determine ite (interval [{rl.lo}, {rl.hi}])"
    -- Unrecognized condition shape
    throwError "rsa_decide: unsupported ite condition: {← ppExpr cond}"

  -- Fast-path for summation forms: whnf directly to skip the
  -- Finset.sum → Multiset.sum → Quot.lift → List.foldr unfold chain.
  -- Saves ~3-5 depth per sum element (critical for models with |W| ≥ 10).
  let fnName := fn.constName?
  if fnName == some ``Finset.sum ||
     fnName == some ``Multiset.sum ||
     fnName == some ``Multiset.fold ||
     fnName == some ``List.foldr ||
     fnName == some ``List.foldl ||
     fnName == some ``List.sum ||
     fnName == some ``Quot.lift then
    let e' ← whnf e
    if !e.equal e' then
      return ← reifyCore e' (depth - 1)

  -- Default: try unfolding one definition.
  -- headBeta after unfolding: struct projection unfold produces lambdas
  -- (e.g., `(fun l0 α w u => rpow ...) arg1 arg2 ...`). Without headBeta,
  -- the lambda head falls through to whnf which over-reduces (e.g., rpow → NNReal).
  if let some e' ← unfoldDefinition? e then
    return ← reifyCore e'.headBeta (depth - 1)

  -- Secondary fallback: whnf (handles Quot.lift from Finset.sum, etc.)
  let e' ← whnf e
  if !e.equal e' then
    return ← reifyCore e' (depth - 1)

  -- Tertiary fallback: detect internal numeric literals (Real.zero✝, Real.one✝, etc.)
  -- After whnf, OfNat instances may reduce to internal implementation names.
  let eType ← inferType e
  if eType.isConstOf ``Real then
    for n in ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : List ℕ) do
      let nE := mkRawNatLit n
      let target ← mkAppOptM ``OfNat.ofNat #[mkConst ``Real, nE, none]
      let isEq ← withNewMCtxDepth do
        try isDefEq e target catch _ => return false
      if isEq then
        let q : ℚ := n
        let qE ← mkNatCastRat n
        let interval ← mkAppM ``QInterval.exact #[qE]
        let proof ← mkAppM ``QInterval.exact_natCast_containsReal #[nE]
        return { interval, proof, lo := q, hi := q }

  -- Quaternary fallback: detect internal binary operations (Real.add✝, Real.mul✝, etc.)
  -- After whnf reduces Quot.lift/List.foldr, the + on ℝ becomes its internal implementation
  -- (a private name). We detect these by checking isDefEq against HAdd.hAdd/HMul.hMul/HDiv.hDiv.
  if args.size ≥ 2 then
    let a := args[args.size - 2]!
    let b := args[args.size - 1]!
    -- Addition
    let isAdd ← withNewMCtxDepth do
      try isDefEq e (← mkAppM ``HAdd.hAdd #[a, b]) catch _ => return false
    if isAdd then
      let ra ← reifyCore a (depth - 1)
      let rb ← reifyCore b (depth - 1)
      let interval ← mkAppM ``QInterval.add #[ra.interval, rb.interval]
      let proof ← mkAppM ``QInterval.add_containsReal #[ra.proof, rb.proof]
      return { interval, proof, lo := ra.lo + rb.lo, hi := ra.hi + rb.hi }
    -- Multiplication
    let isMul ← withNewMCtxDepth do
      try isDefEq e (← mkAppM ``HMul.hMul #[a, b]) catch _ => return false
    if isMul then
      let ra ← reifyCore a (depth - 1)
      let rb ← reifyCore b (depth - 1)
      if ra.lo ≥ 0 && rb.lo ≥ 0 then
        let z ← mkRatZero
        let ha ← mkDecideProof (← mkAppM ``LE.le #[z, ← mkLo ra.interval])
        let hb ← mkDecideProof (← mkAppM ``LE.le #[z, ← mkLo rb.interval])
        let interval ← mkAppM ``QInterval.mulNonneg #[ra.interval, rb.interval, ha, hb]
        let proof ← mkAppM ``QInterval.mulNonneg_containsReal #[ha, hb, ra.proof, rb.proof]
        return { interval, proof, lo := ra.lo * rb.lo, hi := ra.hi * rb.hi }
      else
        throwError "rsa_decide: multiplication with negative intervals not supported"
    -- Division
    let isDiv ← withNewMCtxDepth do
      try isDefEq e (← mkAppM ``HDiv.hDiv #[a, b]) catch _ => return false
    if isDiv then
      let ra ← reifyCore a (depth - 1)
      let rb ← reifyCore b (depth - 1)
      if ra.lo ≥ 0 && rb.lo > 0 then
        let z ← mkRatZero
        let ha ← mkDecideProof (← mkAppM ``LE.le #[z, ← mkLo ra.interval])
        let hb ← mkDecideProof (← mkAppM ``LT.lt #[z, ← mkLo rb.interval])
        let interval ← mkAppM ``QInterval.divPos #[ra.interval, rb.interval, ha, hb]
        let proof ← mkAppM ``QInterval.divPos_containsReal #[ha, hb, ra.proof, rb.proof]
        return { interval, proof, lo := ra.lo / rb.hi, hi := ra.hi / rb.lo }
      else
        throwError "rsa_decide: division requires nonneg numerator and positive denominator"

  -- Detect Real.rpow via isDefEq with metavariables.
  -- Handles NNReal internal forms like `(toNNReal(x) ^ y).val` (from unfolded rpow).
  let eType ← inferType e
  if eType.isConstOf ``Real then
    let rpowMatch ← withNewMCtxDepth do
      try
        let baseM ← mkFreshExprMVar (mkConst ``Real)
        let expM ← mkFreshExprMVar (mkConst ``Real)
        let rpowE ← mkAppM ``Real.rpow #[baseM, expM]
        if ← isDefEq e rpowE then
          let base ← instantiateMVars baseM
          let exp ← instantiateMVars expM
          return some (base, exp)
        else return none
      catch _ => return none
    if let some (base, exp) := rpowMatch then
      if let some n ← resolveNat? exp then
        let rb ← reifyCore base (depth - 1)
        if n == 0 then
          let interval ← mkAppM ``Linglib.Interval.rpowZero #[]
          let proof ← mkAppM ``Linglib.Interval.rpowZero_containsReal #[base]
          return { interval, proof, lo := 1, hi := 1 }
        else if n == 1 then
          if rb.lo ≥ 0 then
            let z ← mkRatZero
            let ha ← mkDecideProof (← mkAppM ``LE.le #[z, ← mkLo rb.interval])
            let proof ← mkAppM ``Linglib.Interval.rpowOne_containsReal #[ha, rb.proof]
            return { rb with proof }
          else
            throwError "rsa_decide: rpow with negative base not supported"
        else
          if rb.lo ≥ 0 then
            let z ← mkRatZero
            let ha ← mkDecideProof (← mkAppM ``LE.le #[z, ← mkLo rb.interval])
            let nE := mkRawNatLit n
            let interval ← mkAppM ``Linglib.Interval.rpowNat #[rb.interval, nE, ha]
            let proof ← mkAppM ``Linglib.Interval.rpowNat_containsReal #[ha, rb.proof]
            return { interval, proof, lo := rb.lo ^ n, hi := rb.hi ^ n }
          else
            throwError "rsa_decide: rpow with negative base not supported"

  throwError "rsa_decide: cannot reify: {← ppExpr e}"

/-- Reify an ℝ expression. -/
private def reify (e : Expr) : MetaM RResult := reifyCore e maxReifyDepth

-- ============================================================================
-- Main Tactic
-- ============================================================================

/-- Assign a proof to a goal, bridging cast mismatches via `exact_mod_cast`.
    The reifier produces proofs involving `@Nat.cast ℝ _ n`, but goals may use
    `@OfNat.ofNat ℝ n _` (not definitionally equal for n = 0, 1).
    `exact_mod_cast` normalizes these casts automatically. -/
private def assignProof (goal : MVarId) (proof : Expr) : TacticM Unit := do
  let proofType ← inferType proof
  let goalType ← goal.getType
  if ← isDefEq proofType goalType then
    goal.assign proof
  else
    -- Bridge cast mismatch: introduce proof as hypothesis, close with cast normalization.
    -- assumption_mod_cast handles simple cases (Nat.cast n vs OfNat.ofNat n).
    -- norm_cast handles deeper mismatches (e.g., inside Real.rpow arguments).
    let goalWithH ← goal.assert `h_rsa proofType proof
    let (_, finalGoal) ← goalWithH.intro1
    setGoals [finalGoal]
    try evalTactic (← `(tactic| assumption_mod_cast))
    catch _ =>
      try evalTactic (← `(tactic| push_cast at *; assumption))
      catch _ => evalTactic (← `(tactic| norm_cast at *; assumption))

/-- `rsa_decide` proves ℝ comparison goals via interval arithmetic.
    For decidable goals (ℚ, Bool, Fin), dispatches to `native_decide`. -/
elab "rsa_decide" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType

  -- Try native_decide first (handles ℚ, Bool, finite types)
  try
    evalTactic (← `(tactic| native_decide))
    return
  catch _ => pure ()

  let fn := goalType.getAppFn
  let args := goalType.getAppArgs

  -- GT.gt: lhs > rhs
  if fn.isConstOf ``GT.gt && args.size ≥ 4 then
    let lhs := args[2]!
    let rhs := args[3]!
    let rl ← reify lhs
    let rr ← reify rhs
    if rr.hi < rl.lo then
      let sepProp ← mkAppM ``LT.lt #[← mkHi rr.interval, ← mkLo rl.interval]
      let sepProof ← mkDecideProof sepProp
      let proof ← mkAppM ``QInterval.gt_of_separated #[rl.proof, rr.proof, sepProof]
      assignProof goal proof
      return
    else
      throwError "rsa_decide: no separation for >:\n  lhs ∈ [{rl.lo}, {rl.hi}]\n  rhs ∈ [{rr.lo}, {rr.hi}]"

  -- GE.ge: lhs ≥ rhs
  if fn.isConstOf ``GE.ge && args.size ≥ 4 then
    let lhs := args[2]!
    let rhs := args[3]!
    let rl ← reify lhs
    let rr ← reify rhs
    if rr.hi ≤ rl.lo then
      let sepProp ← mkAppM ``LE.le #[← mkHi rr.interval, ← mkLo rl.interval]
      let sepProof ← mkDecideProof sepProp
      let proof ← mkAppM ``QInterval.ge_of_le_lo #[rl.proof, rr.proof, sepProof]
      assignProof goal proof
      return
    else
      throwError "rsa_decide: no separation for ≥:\n  lhs ∈ [{rl.lo}, {rl.hi}]\n  rhs ∈ [{rr.lo}, {rr.hi}]"

  -- Eq: lhs = rhs (prove via ≥ both ways → le_antisymm)
  if fn.isConstOf ``Eq && args.size ≥ 3 then
    let lhs := args[1]!
    let rhs := args[2]!
    let rl ← reify lhs
    let rr ← reify rhs
    if rr.hi ≤ rl.lo && rl.hi ≤ rr.lo then
      -- lhs ≥ rhs
      let geProp1 ← mkAppM ``LE.le #[← mkHi rr.interval, ← mkLo rl.interval]
      let geProof1 ← mkDecideProof geProp1
      let hge1 ← mkAppM ``QInterval.ge_of_le_lo #[rl.proof, rr.proof, geProof1]
      -- rhs ≥ lhs
      let geProp2 ← mkAppM ``LE.le #[← mkHi rl.interval, ← mkLo rr.interval]
      let geProof2 ← mkDecideProof geProp2
      let hge2 ← mkAppM ``QInterval.ge_of_le_lo #[rr.proof, rl.proof, geProof2]
      -- le_antisymm : a ≤ b → b ≤ a → a = b
      let proof ← mkAppM ``le_antisymm #[hge2, hge1]
      assignProof goal proof
      return
    else
      throwError "rsa_decide: no separation for =:\n  lhs ∈ [{rl.lo}, {rl.hi}]\n  rhs ∈ [{rr.lo}, {rr.hi}]"

  throwError "rsa_decide: unsupported goal: {← ppExpr goalType}"

end Linglib.Tactics
