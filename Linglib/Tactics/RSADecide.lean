import Lean
import Linglib.Core.Interval.QInterval
import Linglib.Core.Interval.PadeExp
import Linglib.Core.Interval.RpowInterval
import Linglib.Core.Interval.LogInterval
import Linglib.Core.Interval.ReflectInterval
import Linglib.Core.RationalAction

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

/-- Evaluate log(q) at meta level for q > 0. -/
private def evalLogPoint (q : ℚ) : ℚ × ℚ :=
  if h : 0 < q then
    let I := Linglib.Interval.logPoint q h
    (I.lo, I.hi)
  else (0, 0)

-- ============================================================================
-- Zero Short-Circuit Helpers
-- ============================================================================

/-- Build a zero result for x * y when x is known to be zero. -/
private def mkZeroMulResult (ra : RResult) (rhsExpr : Expr) : MetaM RResult := do
  let hlo ← mkDecideProof (← mkAppM ``Eq #[← mkLo ra.interval, ← mkNatCastRat 0])
  let hhi ← mkDecideProof (← mkAppM ``Eq #[← mkHi ra.interval, ← mkNatCastRat 0])
  let zeroE ← mkNatCastRat 0
  let interval ← mkAppM ``QInterval.exact #[zeroE]
  let proof ← mkAppOptM ``QInterval.zero_mul_containsReal
    #[none, none, some rhsExpr, some ra.proof, some hlo, some hhi]
  return { interval, proof, lo := 0, hi := 0 }

/-- Build a zero result for x / y when x is known to be zero. -/
private def mkZeroDivResult (ra : RResult) (rhsExpr : Expr) : MetaM RResult := do
  let hlo ← mkDecideProof (← mkAppM ``Eq #[← mkLo ra.interval, ← mkNatCastRat 0])
  let hhi ← mkDecideProof (← mkAppM ``Eq #[← mkHi ra.interval, ← mkNatCastRat 0])
  let zeroE ← mkNatCastRat 0
  let interval ← mkAppM ``QInterval.exact #[zeroE]
  let proof ← mkAppOptM ``QInterval.zero_div_containsReal
    #[none, none, some rhsExpr, some ra.proof, some hlo, some hhi]
  return { interval, proof, lo := 0, hi := 0 }

/-- Build a zero result for x * y when y is known to be zero. -/
private def mkMulZeroResult (lhsExpr : Expr) (rb : RResult) : MetaM RResult := do
  let hlo ← mkDecideProof (← mkAppM ``Eq #[← mkLo rb.interval, ← mkNatCastRat 0])
  let hhi ← mkDecideProof (← mkAppM ``Eq #[← mkHi rb.interval, ← mkNatCastRat 0])
  let zeroE ← mkNatCastRat 0
  let interval ← mkAppM ``QInterval.exact #[zeroE]
  let proof ← mkAppOptM ``QInterval.mul_zero_containsReal
    #[none, some lhsExpr, none, some rb.proof, some hlo, some hhi]
  return { interval, proof, lo := 0, hi := 0 }

-- ============================================================================
-- The Reifier
-- ============================================================================

private def maxReifyDepth : ℕ := 200

/-- Core reifier: ℝ expression → QInterval + containment proof.

Recognized patterns:
- Natural literals: `@OfNat.ofNat ℝ n _` → `exact (n : ℚ)`
- Addition: `HAdd.hAdd` or `Add.add` → `add`
- Multiplication: `HMul.hMul` or `Mul.mul` → `mulNonneg` (both nonneg) or `mul` (general)
- Division (nonneg/pos): `HDiv.hDiv` or `Div.div` → `divPos`
- Negation: `Neg.neg` → `neg`
- Subtraction: `HSub.hSub` or `Sub.sub` → `sub`
- Real.rpow with natural exponent → `rpowNat`
- Real.exp → `expInterval`
- Real.log (positive interval) → `logInterval`
- If-then-else: `if x = 0 then a else b` → branch selection
- Unknown: try `unfoldDefinition?`, then `whnf` -/
private partial def reifyCore (e : Expr) (depth : ℕ) : MetaM RResult := do
  if depth == 0 then
    throwError "rsa_decide: max reification depth on: {← ppExpr e}"

  -- Match BEFORE whnf to catch HAdd, HMul, etc. before they unfold to Real internals.

  -- Natural literal: @OfNat.ofNat ℝ n _
  -- Use exact_zero/one_containsReal for n=0,1 to avoid Nat.cast vs OfNat.ofNat
  -- mismatch (Nat.cast 1 = 0 + 1 ≢ OfNat.ofNat 1 = One.one in Lean 4).
  if let some n := getOfNat? e then
    let q : ℚ := n
    let nE := mkRawNatLit n
    let qE ← mkNatCastRat n
    let interval ← mkAppM ``QInterval.exact #[qE]
    let proof ← match n with
      | 0 => mkAppM ``QInterval.exact_zero_containsReal #[]
      | 1 => mkAppM ``QInterval.exact_one_containsReal #[]
      | _ => mkAppM ``QInterval.exact_natCast_containsReal #[nE]
    return { interval, proof, lo := q, hi := q }

  -- Let binding: substitute the bound value into the body before whnf.
  -- This prevents whnf from reducing `let x := v in if x = 0 then ...`
  -- all the way to Decidable.rec, letting the ite handler catch it instead.
  if e.isLet then
    return ← reifyCore (e.letBody!.instantiate1 e.letValue!) (depth - 1)

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
    -- Zero short-circuit: 0 * y = 0
    if ra.lo == 0 && ra.hi == 0 then
      return ← mkZeroMulResult ra args[5]!
    let rb ← reifyCore args[5]! (depth - 1)
    -- Zero short-circuit: x * 0 = 0
    if rb.lo == 0 && rb.hi == 0 then
      return ← mkMulZeroResult args[4]! rb
    if ra.lo ≥ 0 && rb.lo ≥ 0 then
      let z ← mkRatZero
      let ha ← mkDecideProof (← mkAppM ``LE.le #[z, ← mkLo ra.interval])
      let hb ← mkDecideProof (← mkAppM ``LE.le #[z, ← mkLo rb.interval])
      let interval ← mkAppM ``QInterval.mulNonneg #[ra.interval, rb.interval, ha, hb]
      let proof ← mkAppM ``QInterval.mulNonneg_containsReal #[ha, hb, ra.proof, rb.proof]
      return { interval, proof, lo := ra.lo * rb.lo, hi := ra.hi * rb.hi }
    else
      -- General multiplication: 4-corner method
      let interval ← mkAppM ``QInterval.mul #[ra.interval, rb.interval]
      let proof ← mkAppM ``QInterval.mul_containsReal #[ra.proof, rb.proof]
      let c00 := ra.lo * rb.lo; let c01 := ra.lo * rb.hi
      let c10 := ra.hi * rb.lo; let c11 := ra.hi * rb.hi
      let lo := min (min c00 c01) (min c10 c11)
      let hi := max (max c00 c01) (max c10 c11)
      return { interval, proof, lo, hi }

  -- Multiplication: @Mul.mul ℝ _ a b (4 args) — from whnf/reduce
  if isAppOfMin e ``Mul.mul 4 then
    let ra ← reifyCore args[2]! (depth - 1)
    if ra.lo == 0 && ra.hi == 0 then
      return ← mkZeroMulResult ra args[3]!
    let rb ← reifyCore args[3]! (depth - 1)
    if rb.lo == 0 && rb.hi == 0 then
      return ← mkMulZeroResult args[2]! rb
    if ra.lo ≥ 0 && rb.lo ≥ 0 then
      let z ← mkRatZero
      let ha ← mkDecideProof (← mkAppM ``LE.le #[z, ← mkLo ra.interval])
      let hb ← mkDecideProof (← mkAppM ``LE.le #[z, ← mkLo rb.interval])
      let interval ← mkAppM ``QInterval.mulNonneg #[ra.interval, rb.interval, ha, hb]
      let proof ← mkAppM ``QInterval.mulNonneg_containsReal #[ha, hb, ra.proof, rb.proof]
      return { interval, proof, lo := ra.lo * rb.lo, hi := ra.hi * rb.hi }
    else
      -- General multiplication: 4-corner method
      let interval ← mkAppM ``QInterval.mul #[ra.interval, rb.interval]
      let proof ← mkAppM ``QInterval.mul_containsReal #[ra.proof, rb.proof]
      let c00 := ra.lo * rb.lo; let c01 := ra.lo * rb.hi
      let c10 := ra.hi * rb.lo; let c11 := ra.hi * rb.hi
      let lo := min (min c00 c01) (min c10 c11)
      let hi := max (max c00 c01) (max c10 c11)
      return { interval, proof, lo, hi }

  -- Division: @HDiv.hDiv ℝ ℝ ℝ _ a b (6 args)
  if isAppOfMin e ``HDiv.hDiv 6 then
    let ra ← reifyCore args[4]! (depth - 1)
    if ra.lo == 0 && ra.hi == 0 then
      return ← mkZeroDivResult ra args[5]!
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
    if ra.lo == 0 && ra.hi == 0 then
      return ← mkZeroDivResult ra args[3]!
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

  -- Real.exp: @Real.exp x
  if fn.isConstOf ``Real.exp && args.size ≥ 1 then
    let arg := args[0]!
    let ra ← reifyCore arg (depth - 1)
    let interval ← mkAppM ``Linglib.Interval.expInterval #[ra.interval]
    let proof ← mkAppM ``Linglib.Interval.expInterval_containsReal #[ra.proof]
    let elo := (Linglib.Interval.expPoint ra.lo).lo
    let ehi := (Linglib.Interval.expPoint ra.hi).hi
    return { interval, proof, lo := elo, hi := ehi }

  -- Real.log: @Real.log x
  if fn.isConstOf ``Real.log && args.size ≥ 1 then
    let arg := args[0]!
    let ra ← reifyCore arg (depth - 1)
    if ra.lo > 0 then
      let z ← mkRatZero
      let hlo ← mkDecideProof (← mkAppM ``LT.lt #[z, ← mkLo ra.interval])
      let interval ← mkAppM ``Linglib.Interval.logInterval #[ra.interval, hlo]
      let proof ← mkAppM ``Linglib.Interval.logInterval_containsReal #[hlo, ra.proof]
      let llo := (evalLogPoint ra.lo).1
      let lhi := (evalLogPoint ra.hi).2
      return { interval, proof, lo := llo, hi := lhi }
    else
      throwError "rsa_decide: log of non-positive interval [{ra.lo}, {ra.hi}]"

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
          let proof ← mkAppOptM ``QInterval.ite_neg_containsReal
            #[none, none, none, some thenBr, none, some hne, some rElse.proof]
          return { rElse with proof }
        else if rl.lo == 0 && rl.hi == 0 then
          -- lhsC = 0 → condition true → take then branch
          let hlo ← mkDecideProof (← mkAppM ``Eq #[← mkLo rl.interval, ← mkNatCastRat 0])
          let hhi ← mkDecideProof (← mkAppM ``Eq #[← mkHi rl.interval, ← mkNatCastRat 0])
          let heq ← mkAppM ``QInterval.eq_zero_of_bounds #[rl.proof, hlo, hhi]
          let rThen ← reifyCore thenBr (depth - 1)
          let proof ← mkAppOptM ``QInterval.ite_pos_containsReal
            #[none, none, none, none, some elseBr, some heq, some rThen.proof]
          return { rThen with proof }
        else
          throwError "rsa_decide: cannot determine ite (interval [{rl.lo}, {rl.hi}])"
    -- Other conditions (Bool, decidable): try whnf to evaluate the branch
    let e' ← whnf e
    if !e.equal e' then
      return ← reifyCore e' (depth - 1)
    throwError "rsa_decide: unsupported ite condition: {← ppExpr cond}"

  -- Decidable.rec: catches ite that was reduced to its definition by whnf.
  -- @Decidable.rec {p} {motive} (isFalse : ¬p → T) (isTrue : p → T) (inst)
  -- isFalse = else branch, isTrue = then branch (reversed from ite order).
  if fn.isConstOf ``Decidable.rec && args.size ≥ 5 then
    let prop := args[0]!
    let isFalseBr := args[2]!
    let isTrueBr := args[3]!
    let inst := args[4]!
    if prop.isAppOfArity ``Eq 3 then
      let propArgs := prop.getAppArgs
      let lhsC := propArgs[1]!
      let rhsC := propArgs[2]!
      if let some 0 := getOfNat? rhsC then
        let rl ← reifyCore lhsC (depth - 1)
        -- Cast the proof to reference the original lhsC (same reason as ite handler)
        let expectedType ← mkAppM ``QInterval.containsReal #[rl.interval, lhsC]
        let rl_proof ← mkExpectedTypeHint rl.proof expectedType
        if rl.lo > 0 then
          -- lhsC > 0 → condition false → take isFalse branch (the else branch)
          let z ← mkRatZero
          let hlo ← mkDecideProof (← mkAppM ``LT.lt #[z, ← mkLo rl.interval])
          let hpos ← mkAppM ``QInterval.pos_of_lo_pos #[rl_proof, hlo]
          let hne ← mkAppM ``ne_of_gt #[hpos]
          -- Apply isFalseBr to hne to get else body, beta-reduce
          let elseBody := (Expr.app isFalseBr hne).headBeta
          let rElse ← reifyCore elseBody (depth - 1)
          -- Use decidable_rec_neg_containsReal via mkAppN (bypass meta-level type
          -- checking for the interval and proof arguments)
          let proof := mkAppN (mkConst ``QInterval.decidable_rec_neg_containsReal [])
            #[prop, inst, rElse.interval, isFalseBr, isTrueBr, hne, rElse.proof]
          return { rElse with proof }
        else if rl.lo == 0 && rl.hi == 0 then
          -- lhsC = 0 → condition true → take isTrue branch (the then branch)
          let hlo ← mkDecideProof (← mkAppM ``Eq #[← mkLo rl.interval, ← mkNatCastRat 0])
          let hhi ← mkDecideProof (← mkAppM ``Eq #[← mkHi rl.interval, ← mkNatCastRat 0])
          let heq ← mkAppM ``QInterval.eq_zero_of_bounds #[rl_proof, hlo, hhi]
          -- Apply isTrueBr to heq to get then body, beta-reduce
          let thenBody := (Expr.app isTrueBr heq).headBeta
          let rThen ← reifyCore thenBody (depth - 1)
          -- Use decidable_rec_pos_containsReal via mkAppN (same reason as above)
          let proof := mkAppN (mkConst ``QInterval.decidable_rec_pos_containsReal [])
            #[prop, inst, rThen.interval, isFalseBr, isTrueBr, heq, rThen.proof]
          return { rThen with proof }

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
        let proof ← match n with
          | 0 => mkAppM ``QInterval.exact_zero_containsReal #[]
          | 1 => mkAppM ``QInterval.exact_one_containsReal #[]
          | _ => mkAppM ``QInterval.exact_natCast_containsReal #[nE]
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
      if ra.lo == 0 && ra.hi == 0 then
        return ← mkZeroMulResult ra b
      let rb ← reifyCore b (depth - 1)
      if rb.lo == 0 && rb.hi == 0 then
        return ← mkMulZeroResult a rb
      if ra.lo ≥ 0 && rb.lo ≥ 0 then
        let z ← mkRatZero
        let ha ← mkDecideProof (← mkAppM ``LE.le #[z, ← mkLo ra.interval])
        let hb ← mkDecideProof (← mkAppM ``LE.le #[z, ← mkLo rb.interval])
        let interval ← mkAppM ``QInterval.mulNonneg #[ra.interval, rb.interval, ha, hb]
        let proof ← mkAppM ``QInterval.mulNonneg_containsReal #[ha, hb, ra.proof, rb.proof]
        return { interval, proof, lo := ra.lo * rb.lo, hi := ra.hi * rb.hi }
      else
        let interval ← mkAppM ``QInterval.mul #[ra.interval, rb.interval]
        let proof ← mkAppM ``QInterval.mul_containsReal #[ra.proof, rb.proof]
        let c00 := ra.lo * rb.lo; let c01 := ra.lo * rb.hi
        let c10 := ra.hi * rb.lo; let c11 := ra.hi * rb.hi
        let lo := min (min c00 c01) (min c10 c11)
        let hi := max (max c00 c01) (max c10 c11)
        return { interval, proof, lo, hi }
    -- Division
    let isDiv ← withNewMCtxDepth do
      try isDefEq e (← mkAppM ``HDiv.hDiv #[a, b]) catch _ => return false
    if isDiv then
      let ra ← reifyCore a (depth - 1)
      if ra.lo == 0 && ra.hi == 0 then
        return ← mkZeroDivResult ra b
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

  -- Detect Real.exp / Real.log via isDefEq with metavariables.
  -- Handles internal forms after whnf reduction.
  let eType ← inferType e
  if eType.isConstOf ``Real then
    -- Real.exp
    let expMatch ← withNewMCtxDepth do
      try
        let argM ← mkFreshExprMVar (mkConst ``Real)
        let expE ← mkAppM ``Real.exp #[argM]
        if ← isDefEq e expE then
          return some (← instantiateMVars argM)
        else return none
      catch _ => return none
    if let some arg := expMatch then
      let ra ← reifyCore arg (depth - 1)
      let interval ← mkAppM ``Linglib.Interval.expInterval #[ra.interval]
      let proof ← mkAppM ``Linglib.Interval.expInterval_containsReal #[ra.proof]
      let elo := (Linglib.Interval.expPoint ra.lo).lo
      let ehi := (Linglib.Interval.expPoint ra.hi).hi
      return { interval, proof, lo := elo, hi := ehi }
    -- Real.log
    let logMatch ← withNewMCtxDepth do
      try
        let argM ← mkFreshExprMVar (mkConst ``Real)
        let logE ← mkAppM ``Real.log #[argM]
        if ← isDefEq e logE then
          return some (← instantiateMVars argM)
        else return none
      catch _ => return none
    if let some arg := logMatch then
      let ra ← reifyCore arg (depth - 1)
      if ra.lo > 0 then
        let z ← mkRatZero
        let hlo ← mkDecideProof (← mkAppM ``LT.lt #[z, ← mkLo ra.interval])
        let interval ← mkAppM ``Linglib.Interval.logInterval #[ra.interval, hlo]
        let proof ← mkAppM ``Linglib.Interval.logInterval_containsReal #[hlo, ra.proof]
        let llo := (evalLogPoint ra.lo).1
        let lhi := (evalLogPoint ra.hi).2
        return { interval, proof, lo := llo, hi := lhi }
      else
        throwError "rsa_decide: log of non-positive interval [{ra.lo}, {ra.hi}]"
    -- Inv.inv: x⁻¹ (appears after whnf as private Real.inv'✝)
    let invMatch ← withNewMCtxDepth do
      try
        let argM ← mkFreshExprMVar (mkConst ``Real)
        let invE ← mkAppM ``Inv.inv #[argM]
        if ← isDefEq e invE then
          return some (← instantiateMVars argM)
        else return none
      catch _ => return none
    if let some arg := invMatch then
      let ra ← reifyCore arg (depth - 1)
      if ra.lo > 0 then
        let z ← mkRatZero
        let hlo ← mkDecideProof (← mkAppM ``LT.lt #[z, ← mkLo ra.interval])
        let interval ← mkAppM ``QInterval.invPos #[ra.interval, hlo]
        let proof ← mkAppM ``QInterval.invPos_containsReal #[hlo, ra.proof]
        return { interval, proof, lo := 1 / ra.hi, hi := 1 / ra.lo }
      else
        throwError "rsa_decide: inverse of non-positive interval [{ra.lo}, {ra.hi}]"

  -- Detect Real.rpow via isDefEq with metavariables.
  -- Handles NNReal internal forms like `(toNNReal(x) ^ y).val` (from unfolded rpow).
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
-- Reflection-Based Reifier (RExpr)
-- ============================================================================

/-- Result of reifying an ℝ expression into an RExpr value. -/
private structure RExprResult where
  /-- RExpr expression (Lean Expr of type RExpr). -/
  rexpr : Expr
  /-- Evaluated lower bound (tracked in MetaM for early separation check). -/
  lo : ℚ
  /-- Evaluated upper bound. -/
  hi : ℚ

/-- Build RExpr.nat n -/
private def mkRExprNat (n : ℕ) : MetaM Expr :=
  mkAppM ``RExpr.nat #[mkRawNatLit n]

/-- Build RExpr.add a b -/
private def mkRExprAdd (a b : Expr) : MetaM Expr :=
  mkAppM ``RExpr.add #[a, b]

/-- Build RExpr.mul a b -/
private def mkRExprMul (a b : Expr) : MetaM Expr :=
  mkAppM ``RExpr.mul #[a, b]

/-- Build RExpr.div a b -/
private def mkRExprDiv (a b : Expr) : MetaM Expr :=
  mkAppM ``RExpr.div #[a, b]

/-- Build RExpr.neg a -/
private def mkRExprNeg (a : Expr) : MetaM Expr :=
  mkAppM ``RExpr.neg #[a]

/-- Build RExpr.sub a b -/
private def mkRExprSub (a b : Expr) : MetaM Expr :=
  mkAppM ``RExpr.sub #[a, b]

/-- Build RExpr.rexp a -/
private def mkRExprExp (a : Expr) : MetaM Expr :=
  mkAppM ``RExpr.rexp #[a]

/-- Build RExpr.rlog a -/
private def mkRExprLog (a : Expr) : MetaM Expr :=
  mkAppM ``RExpr.rlog #[a]

/-- Build RExpr.rpow a n -/
private def mkRExprRpow (a : Expr) (n : ℕ) : MetaM Expr :=
  mkAppM ``RExpr.rpow #[a, mkRawNatLit n]

/-- Build RExpr.inv a -/
private def mkRExprInv (a : Expr) : MetaM Expr :=
  mkAppM ``RExpr.inv #[a]

/-- Build RExpr.iteZero cond thenBr elseBr -/
private def mkRExprIteZero (c t e : Expr) : MetaM Expr :=
  mkAppM ``RExpr.iteZero #[c, t, e]

/-- Meta-level interval evaluation (mirrors RExpr.eval for early checks). -/
private def metaEvalMul (a b : RExprResult) : ℚ × ℚ :=
  if a.lo == 0 && a.hi == 0 then (0, 0)
  else if b.lo == 0 && b.hi == 0 then (0, 0)
  else if a.lo ≥ 0 && b.lo ≥ 0 then (a.lo * b.lo, a.hi * b.hi)
  else
    let c00 := a.lo * b.lo; let c01 := a.lo * b.hi
    let c10 := a.hi * b.lo; let c11 := a.hi * b.hi
    (min (min c00 c01) (min c10 c11), max (max c00 c01) (max c10 c11))

/-- Core reflection reifier: ℝ expression → RExpr + meta-level bounds.

Mirrors `reifyCore` but produces `RExpr` constructors (data) instead of
`QInterval` proof terms. The result is used with `RExpr.gt_of_eval_separated`
and `native_decide` for kernel-efficient verification. -/
private partial def reifyRExprCore (e : Expr) (depth : ℕ) : MetaM RExprResult := do
  if depth == 0 then
    throwError "rsa_decide [reflect]: max reification depth on: {← ppExpr e}"

  -- Let binding: substitute
  if e.isLet then
    return ← reifyRExprCore (e.letBody!.instantiate1 e.letValue!) (depth - 1)

  -- Natural literal: @OfNat.ofNat ℝ n _
  if let some n := getOfNat? e then
    let rexpr ← mkRExprNat n
    return { rexpr, lo := n, hi := n }

  let fn := e.getAppFn
  let args := e.getAppArgs

  -- Addition: @HAdd.hAdd ℝ ℝ ℝ _ a b
  if isAppOfMin e ``HAdd.hAdd 6 then
    let ra ← reifyRExprCore args[4]! (depth - 1)
    let rb ← reifyRExprCore args[5]! (depth - 1)
    let rexpr ← mkRExprAdd ra.rexpr rb.rexpr
    return { rexpr, lo := ra.lo + rb.lo, hi := ra.hi + rb.hi }

  -- Addition: @Add.add ℝ _ a b
  if isAppOfMin e ``Add.add 4 then
    let ra ← reifyRExprCore args[2]! (depth - 1)
    let rb ← reifyRExprCore args[3]! (depth - 1)
    let rexpr ← mkRExprAdd ra.rexpr rb.rexpr
    return { rexpr, lo := ra.lo + rb.lo, hi := ra.hi + rb.hi }

  -- Multiplication: @HMul.hMul ℝ ℝ ℝ _ a b
  if isAppOfMin e ``HMul.hMul 6 then
    let ra ← reifyRExprCore args[4]! (depth - 1)
    if ra.lo == 0 && ra.hi == 0 then
      let rb_rexpr ← reifyRExprCore args[5]! (depth - 1)
      let rexpr ← mkRExprMul ra.rexpr rb_rexpr.rexpr
      return { rexpr, lo := 0, hi := 0 }
    let rb ← reifyRExprCore args[5]! (depth - 1)
    let rexpr ← mkRExprMul ra.rexpr rb.rexpr
    let (lo, hi) := metaEvalMul ra rb
    return { rexpr, lo, hi }

  -- Multiplication: @Mul.mul ℝ _ a b
  if isAppOfMin e ``Mul.mul 4 then
    let ra ← reifyRExprCore args[2]! (depth - 1)
    if ra.lo == 0 && ra.hi == 0 then
      let rb_rexpr ← reifyRExprCore args[3]! (depth - 1)
      let rexpr ← mkRExprMul ra.rexpr rb_rexpr.rexpr
      return { rexpr, lo := 0, hi := 0 }
    let rb ← reifyRExprCore args[3]! (depth - 1)
    let rexpr ← mkRExprMul ra.rexpr rb.rexpr
    let (lo, hi) := metaEvalMul ra rb
    return { rexpr, lo, hi }

  -- Division: @HDiv.hDiv ℝ ℝ ℝ _ a b
  if isAppOfMin e ``HDiv.hDiv 6 then
    let ra ← reifyRExprCore args[4]! (depth - 1)
    if ra.lo == 0 && ra.hi == 0 then
      let rb_rexpr ← reifyRExprCore args[5]! (depth - 1)
      let rexpr ← mkRExprDiv ra.rexpr rb_rexpr.rexpr
      return { rexpr, lo := 0, hi := 0 }
    let rb ← reifyRExprCore args[5]! (depth - 1)
    let rexpr ← mkRExprDiv ra.rexpr rb.rexpr
    if ra.lo ≥ 0 && rb.lo > 0 then
      return { rexpr, lo := ra.lo / rb.hi, hi := ra.hi / rb.lo }
    return { rexpr, lo := -1, hi := 1 }  -- conservative

  -- Division: @Div.div ℝ _ a b
  if isAppOfMin e ``Div.div 4 then
    let ra ← reifyRExprCore args[2]! (depth - 1)
    if ra.lo == 0 && ra.hi == 0 then
      let rb_rexpr ← reifyRExprCore args[3]! (depth - 1)
      let rexpr ← mkRExprDiv ra.rexpr rb_rexpr.rexpr
      return { rexpr, lo := 0, hi := 0 }
    let rb ← reifyRExprCore args[3]! (depth - 1)
    let rexpr ← mkRExprDiv ra.rexpr rb.rexpr
    if ra.lo ≥ 0 && rb.lo > 0 then
      return { rexpr, lo := ra.lo / rb.hi, hi := ra.hi / rb.lo }
    return { rexpr, lo := -1, hi := 1 }

  -- Negation: @Neg.neg ℝ _ a
  if isAppOfMin e ``Neg.neg 3 then
    let ra ← reifyRExprCore args[2]! (depth - 1)
    let rexpr ← mkRExprNeg ra.rexpr
    return { rexpr, lo := -ra.hi, hi := -ra.lo }

  -- Subtraction: @HSub.hSub ℝ ℝ ℝ _ a b
  if isAppOfMin e ``HSub.hSub 6 then
    let ra ← reifyRExprCore args[4]! (depth - 1)
    let rb ← reifyRExprCore args[5]! (depth - 1)
    let rexpr ← mkRExprSub ra.rexpr rb.rexpr
    return { rexpr, lo := ra.lo - rb.hi, hi := ra.hi - rb.lo }

  -- Subtraction: @Sub.sub ℝ _ a b
  if isAppOfMin e ``Sub.sub 4 then
    let ra ← reifyRExprCore args[2]! (depth - 1)
    let rb ← reifyRExprCore args[3]! (depth - 1)
    let rexpr ← mkRExprSub ra.rexpr rb.rexpr
    return { rexpr, lo := ra.lo - rb.hi, hi := ra.hi - rb.lo }

  -- Real.rpow: @Real.rpow base exp
  if fn.isConstOf ``Real.rpow && args.size ≥ 2 then
    let base := args[0]!
    let exp := args[1]!
    if let some n ← resolveNat? exp then
      let rb ← reifyRExprCore base (depth - 1)
      let rexpr ← mkRExprRpow rb.rexpr n
      if n == 0 then return { rexpr, lo := 1, hi := 1 }
      if rb.lo ≥ 0 then return { rexpr, lo := rb.lo ^ n, hi := rb.hi ^ n }
      return { rexpr, lo := 0, hi := max (rb.lo.num.natAbs ^ n) (rb.hi ^ n) }
    if let some e' ← unfoldDefinition? e then
      return ← reifyRExprCore e' (depth - 1)
    throwError "rsa_decide [reflect]: rpow with non-natural exponent"

  -- Real.exp
  if fn.isConstOf ``Real.exp && args.size ≥ 1 then
    let ra ← reifyRExprCore args[0]! (depth - 1)
    let rexpr ← mkRExprExp ra.rexpr
    let elo := (Linglib.Interval.expPoint ra.lo).lo
    let ehi := (Linglib.Interval.expPoint ra.hi).hi
    return { rexpr, lo := elo, hi := ehi }

  -- Real.log
  if fn.isConstOf ``Real.log && args.size ≥ 1 then
    let ra ← reifyRExprCore args[0]! (depth - 1)
    let rexpr ← mkRExprLog ra.rexpr
    if ra.lo > 0 then
      let llo := (evalLogPoint ra.lo).1
      let lhi := (evalLogPoint ra.hi).2
      return { rexpr, lo := llo, hi := lhi }
    else
      return { rexpr, lo := -1000, hi := 1000 }

  -- If-then-else: @ite ℝ cond dec thenBr elseBr
  if fn.isConstOf ``ite && args.size ≥ 5 then
    let cond := args[1]!
    let thenBr := args[3]!
    let elseBr := args[4]!
    if cond.isAppOfArity ``Eq 3 then
      let cArgs := cond.getAppArgs
      let lhsC := cArgs[1]!
      let rhsC := cArgs[2]!
      if let some 0 := getOfNat? rhsC then
        let rl ← reifyRExprCore lhsC (depth - 1)
        if rl.lo > 0 then
          -- cond is false (x ≠ 0) → else branch
          let re ← reifyRExprCore elseBr (depth - 1)
          let rexpr ← mkRExprIteZero rl.rexpr (← mkRExprNat 0) re.rexpr
          -- Note: iteZero uses cond as first arg, then=second, else=third.
          -- When cond > 0, eval takes the else branch.
          return { rexpr := rexpr, lo := re.lo, hi := re.hi }
        else if rl.lo == 0 && rl.hi == 0 then
          -- cond is true (x = 0) → then branch
          let rt ← reifyRExprCore thenBr (depth - 1)
          let rexpr ← mkRExprIteZero rl.rexpr rt.rexpr (← mkRExprNat 0)
          return { rexpr := rexpr, lo := rt.lo, hi := rt.hi }
        else
          throwError "rsa_decide [reflect]: cannot decide ite (interval [{rl.lo}, {rl.hi}])"
    -- Other conditions: try whnf
    let e' ← whnf e
    if !e.equal e' then
      return ← reifyRExprCore e' (depth - 1)
    throwError "rsa_decide [reflect]: unsupported ite condition: {← ppExpr cond}"

  -- Decidable.rec (from whnf'd ite)
  if fn.isConstOf ``Decidable.rec && args.size ≥ 5 then
    let prop := args[0]!
    let isFalseBr := args[2]!
    let isTrueBr := args[3]!
    if prop.isAppOfArity ``Eq 3 then
      let propArgs := prop.getAppArgs
      let lhsC := propArgs[1]!
      let rhsC := propArgs[2]!
      if let some 0 := getOfNat? rhsC then
        let rl ← reifyRExprCore lhsC (depth - 1)
        if rl.lo > 0 then
          -- x ≠ 0 → isFalse branch (= else)
          -- Use mkSorry for the dummy proof: only needed to beta-reduce the lambda,
          -- not part of the final proof term (which uses RExpr.iteZero + native_decide)
          let negProp ← mkAppM ``Not #[prop]
          let dummyProof := mkApp2 (mkConst ``sorryAx [levelZero]) negProp (toExpr true)
          let elseBody := (Expr.app isFalseBr dummyProof).headBeta
          let re ← reifyRExprCore elseBody (depth - 1)
          let rexpr ← mkRExprIteZero rl.rexpr (← mkRExprNat 0) re.rexpr
          return { rexpr := rexpr, lo := re.lo, hi := re.hi }
        else if rl.lo == 0 && rl.hi == 0 then
          -- x = 0 → isTrue branch (= then)
          let dummyProof := mkApp2 (mkConst ``sorryAx [levelZero]) prop (toExpr true)
          let thenBody := (Expr.app isTrueBr dummyProof).headBeta
          let rt ← reifyRExprCore thenBody (depth - 1)
          let rexpr ← mkRExprIteZero rl.rexpr rt.rexpr (← mkRExprNat 0)
          return { rexpr := rexpr, lo := rt.lo, hi := rt.hi }

  -- Fast-path for summation forms
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
      return ← reifyRExprCore e' (depth - 1)

  -- Default: try unfolding one definition
  if let some e' ← unfoldDefinition? e then
    return ← reifyRExprCore e'.headBeta (depth - 1)

  -- whnf fallback
  let e' ← whnf e
  if !e.equal e' then
    return ← reifyRExprCore e' (depth - 1)

  -- Tertiary: detect numeric literals via isDefEq
  let eType ← inferType e
  if eType.isConstOf ``Real then
    for n in ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : List ℕ) do
      let nE := mkRawNatLit n
      let target ← mkAppOptM ``OfNat.ofNat #[mkConst ``Real, nE, none]
      let isEq ← withNewMCtxDepth do
        try isDefEq e target catch _ => return false
      if isEq then
        let rexpr ← mkRExprNat n
        return { rexpr, lo := n, hi := n }

  -- Quaternary: detect binary ops via isDefEq
  if args.size ≥ 2 then
    let a := args[args.size - 2]!
    let b := args[args.size - 1]!
    let isAdd ← withNewMCtxDepth do
      try isDefEq e (← mkAppM ``HAdd.hAdd #[a, b]) catch _ => return false
    if isAdd then
      let ra ← reifyRExprCore a (depth - 1)
      let rb ← reifyRExprCore b (depth - 1)
      let rexpr ← mkRExprAdd ra.rexpr rb.rexpr
      return { rexpr, lo := ra.lo + rb.lo, hi := ra.hi + rb.hi }
    let isMul ← withNewMCtxDepth do
      try isDefEq e (← mkAppM ``HMul.hMul #[a, b]) catch _ => return false
    if isMul then
      let ra ← reifyRExprCore a (depth - 1)
      let rb ← reifyRExprCore b (depth - 1)
      let rexpr ← mkRExprMul ra.rexpr rb.rexpr
      let (lo, hi) := metaEvalMul ra rb
      return { rexpr, lo, hi }
    let isDiv ← withNewMCtxDepth do
      try isDefEq e (← mkAppM ``HDiv.hDiv #[a, b]) catch _ => return false
    if isDiv then
      let ra ← reifyRExprCore a (depth - 1)
      let rb ← reifyRExprCore b (depth - 1)
      let rexpr ← mkRExprDiv ra.rexpr rb.rexpr
      if ra.lo ≥ 0 && rb.lo > 0 then
        return { rexpr, lo := ra.lo / rb.hi, hi := ra.hi / rb.lo }
      return { rexpr, lo := -1, hi := 1 }

  -- Detect exp/log/inv/rpow via isDefEq
  if eType.isConstOf ``Real then
    let expMatch ← withNewMCtxDepth do
      try
        let argM ← mkFreshExprMVar (mkConst ``Real)
        if ← isDefEq e (← mkAppM ``Real.exp #[argM]) then
          return some (← instantiateMVars argM)
        else return none
      catch _ => return none
    if let some arg := expMatch then
      let ra ← reifyRExprCore arg (depth - 1)
      let rexpr ← mkRExprExp ra.rexpr
      let elo := (Linglib.Interval.expPoint ra.lo).lo
      let ehi := (Linglib.Interval.expPoint ra.hi).hi
      return { rexpr, lo := elo, hi := ehi }
    let logMatch ← withNewMCtxDepth do
      try
        let argM ← mkFreshExprMVar (mkConst ``Real)
        if ← isDefEq e (← mkAppM ``Real.log #[argM]) then
          return some (← instantiateMVars argM)
        else return none
      catch _ => return none
    if let some arg := logMatch then
      let ra ← reifyRExprCore arg (depth - 1)
      let rexpr ← mkRExprLog ra.rexpr
      if ra.lo > 0 then
        return { rexpr, lo := (evalLogPoint ra.lo).1, hi := (evalLogPoint ra.hi).2 }
      return { rexpr, lo := -1000, hi := 1000 }
    let invMatch ← withNewMCtxDepth do
      try
        let argM ← mkFreshExprMVar (mkConst ``Real)
        if ← isDefEq e (← mkAppM ``Inv.inv #[argM]) then
          return some (← instantiateMVars argM)
        else return none
      catch _ => return none
    if let some arg := invMatch then
      let ra ← reifyRExprCore arg (depth - 1)
      let rexpr ← mkRExprInv ra.rexpr
      if ra.lo > 0 then
        return { rexpr, lo := 1 / ra.hi, hi := 1 / ra.lo }
      return { rexpr, lo := -1, hi := 1 }

  if eType.isConstOf ``Real then
    let rpowMatch ← withNewMCtxDepth do
      try
        let baseM ← mkFreshExprMVar (mkConst ``Real)
        let expM ← mkFreshExprMVar (mkConst ``Real)
        if ← isDefEq e (← mkAppM ``Real.rpow #[baseM, expM]) then
          return some (← instantiateMVars baseM, ← instantiateMVars expM)
        else return none
      catch _ => return none
    if let some (base, exp) := rpowMatch then
      if let some n ← resolveNat? exp then
        let rb ← reifyRExprCore base (depth - 1)
        let rexpr ← mkRExprRpow rb.rexpr n
        if n == 0 then return { rexpr, lo := 1, hi := 1 }
        if rb.lo ≥ 0 then return { rexpr, lo := rb.lo ^ n, hi := rb.hi ^ n }
        return { rexpr, lo := 0, hi := 1 }

  throwError "rsa_decide [reflect]: cannot reify: {← ppExpr e}"

/-- Reify an ℝ expression into an RExpr. -/
private def reifyRExpr (e : Expr) : MetaM RExprResult := reifyRExprCore e maxReifyDepth

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

/-- Try to extract (ra, s, a) from an expression that unfolds to
    `RationalAction.policy ra s a`. Unfolds up to 5 levels. -/
private def extractPolicy? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let mut current := e
  for _ in List.range 5 do
    let fn := current.getAppFn
    let args := current.getAppArgs
    if fn.isConstOf ``Core.RationalAction.policy && args.size ≥ 6 then
      return some (args[3]!, args[4]!, args[5]!)  -- ra, s, a
    if let some e' ← unfoldDefinition? current then
      current := e'.headBeta
    else break
  return none

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

    -- Primary path: proof by reflection via RExpr + native_decide.
    -- Reifies both sides into RExpr values, then:
    --   1. native_decide evaluates the interval separation in compiled code
    --   2. Kernel verifies only eval_sound + native_decide (no Nat.cast reductions)
    try
      let rl ← reifyRExpr lhs
      let rr ← reifyRExpr rhs
      logInfo m!"rsa_decide [reflect]: meta-level bounds: lhs ∈ [{rl.lo}, {rl.hi}], rhs ∈ [{rr.lo}, {rr.hi}]"
      -- Build separation type: rhs.eval.hi < lhs.eval.lo
      let rhsEval ← mkAppM ``RExpr.eval #[rr.rexpr]
      let lhsEval ← mkAppM ``RExpr.eval #[rl.rexpr]
      let sepType ← mkAppM ``LT.lt
        #[← mkAppM ``QInterval.hi #[rhsEval],
          ← mkAppM ``QInterval.lo #[lhsEval]]
      -- Create metavar for separation proof and close with native_decide
      let sepMVar ← mkFreshExprMVar sepType
      let savedGoals ← getGoals
      setGoals [sepMVar.mvarId!]
      evalTactic (← `(tactic| native_decide))
      setGoals savedGoals
      -- Prove evalValid for both sides via native_decide
      let boolTrue := mkConst ``Bool.true
      let lhsValidType ← mkAppM ``Eq
        #[← mkAppM ``RExpr.evalValid #[rl.rexpr], boolTrue]
      let lhsValidMVar ← mkFreshExprMVar lhsValidType
      let savedGoals2 ← getGoals
      setGoals [lhsValidMVar.mvarId!]
      evalTactic (← `(tactic| native_decide))
      setGoals savedGoals2
      let rhsValidType ← mkAppM ``Eq
        #[← mkAppM ``RExpr.evalValid #[rr.rexpr], boolTrue]
      let rhsValidMVar ← mkFreshExprMVar rhsValidType
      let savedGoals3 ← getGoals
      setGoals [rhsValidMVar.mvarId!]
      evalTactic (← `(tactic| native_decide))
      setGoals savedGoals3
      -- Build full proof: gt_of_eval_separated lhs rhs hlv hrv sep
      let proof ← mkAppM ``Linglib.Interval.RExpr.gt_of_eval_separated
        #[rl.rexpr, rr.rexpr, lhsValidMVar, rhsValidMVar, sepMVar]
      -- Assign proof. RExpr.denote uses Nat.cast while goals use OfNat.ofNat;
      -- unfold denote first, then bridge the cast mismatch.
      let proofType ← inferType proof
      let goalType ← goal.getType
      if ← isDefEq proofType goalType then
        goal.assign proof
      else
        let goalWithH ← goal.assert `h_rsa proofType proof
        let (_, finalGoal) ← goalWithH.intro1
        setGoals [finalGoal]
        evalTactic (← `(tactic| simp only [Linglib.Interval.RExpr.denote] at *))
        evalTactic (← `(tactic| assumption_mod_cast))
      return
    catch e =>
      logInfo m!"rsa_decide [reflect]: reflection failed ({e.toMessageData}), trying standard path"

    -- Fallback: old Expr-based approach
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
