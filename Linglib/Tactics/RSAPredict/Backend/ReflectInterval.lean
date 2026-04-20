import Linglib.Tactics.RSAPredict.Backend.QInterval
import Linglib.Tactics.RSAPredict.Backend.PadeExp
import Linglib.Tactics.RSAPredict.Backend.LogInterval
import Linglib.Tactics.RSAPredict.Backend.RpowInterval
import Linglib.Tactics.RSAPredict.Backend.SqrtInterval

set_option autoImplicit false

/-!
# ReflectInterval — Proof by Reflection for Interval Arithmetic

Defines a reified expression type `RExpr` with:
- `RExpr.denote : RExpr → ℝ` — the real-valued denotation
- `RExpr.eval : RExpr → QInterval` — computable interval evaluation
- `RExpr.eval_sound` — soundness (under `evalValid` precondition)

The `rsa_decide` tactic reifies ℝ expressions into `RExpr` values, then:
1. `native_decide` checks `evalValid` (always true for RSA expressions)
2. `native_decide` evaluates `(rhs.eval).hi < (lhs.eval).lo` in compiled code
3. The kernel verifies only `eval_sound` applications + `native_decide`

This eliminates the 5M+ `Nat.cast` kernel reductions from the old Expr-based approach.
-/

namespace Interval

open Interval.QInterval

-- ============================================================================
-- RExpr: Reified Arithmetic Expressions
-- ============================================================================

/-- Reified arithmetic expression over ℝ.

Each constructor corresponds to an operation the `rsa_decide` tactic can reify.
The `denote` function maps back to ℝ; the `eval` function computes a `QInterval`
bounding the value. -/
inductive RExpr where
  | nat : ℕ → RExpr
  /-- ℚ→ℝ cast leaf. `denote` produces `↑q : ℝ` via `Rat.cast`, matching
      goal expressions that originated from ℚ→ℝ coercions (e.g., `↑(prior h)`).
      Using `nat` for these would produce `Nat.cast n` which is not definitionally
      equal to `Rat.cast (n : ℚ)` in the kernel. -/
  | ratCast : ℚ → RExpr
  | add : RExpr → RExpr → RExpr
  | mul : RExpr → RExpr → RExpr
  | div : RExpr → RExpr → RExpr
  | neg : RExpr → RExpr
  | sub : RExpr → RExpr → RExpr
  | rexp : RExpr → RExpr
  | rlog : RExpr → RExpr
  | rpow : RExpr → ℕ → RExpr
  | inv : RExpr → RExpr
  /-- `iteZero cond thenBr elseBr` = if cond.denote = 0 then thenBr else elseBr -/
  | iteZero : RExpr → RExpr → RExpr → RExpr
  /-- `expMulLogSub α x c` = exp(α * (log(x) - c)).
      `eval` uses algebraic identity x^α * exp(-α*c) when α is a concrete natural,
      avoiding Padé log+exp calls that produce enormous rationals. -/
  | expMulLogSub : RExpr → RExpr → RExpr → RExpr
  /-- `rsqrt x` = √x (Real.sqrt). `denote` uses `Real.sqrt`, `eval` uses
      `sqrtInterval` (= exp(log/2)) for positive intervals, exact 0 for [0,0]. -/
  | rsqrt : RExpr → RExpr
  deriving Repr, Inhabited, DecidableEq

-- ============================================================================
-- Denotation: RExpr → ℝ
-- ============================================================================

/-- Map a reified expression to its real value. Noncomputable (uses Real.exp, etc.). -/
noncomputable def RExpr.denote : RExpr → ℝ
  | .nat 0 => (0 : ℝ)
  | .nat 1 => (1 : ℝ)
  | .nat n => (n : ℝ)  -- Nat.cast n
  | .ratCast q => (↑q : ℝ)  -- Rat.cast q
  | .add a b => a.denote + b.denote
  | .mul a b => a.denote * b.denote
  | .div a b => a.denote / b.denote
  | .neg a => -a.denote
  | .sub a b => a.denote - b.denote
  | .rexp a => Real.exp a.denote
  | .rlog a => Real.log a.denote
  | .rpow a 0 => Real.rpow a.denote (0 : ℝ)
  | .rpow a 1 => Real.rpow a.denote (1 : ℝ)
  | .rpow a n => Real.rpow a.denote n  -- Nat.cast n
  | .inv a => a.denote⁻¹
  | .iteZero c t e => if c.denote = 0 then t.denote else e.denote
  | .expMulLogSub α x cost => Real.exp (α.denote * (Real.log x.denote - cost.denote))
  | .rsqrt a => Real.sqrt a.denote

-- ============================================================================
-- Evaluation: RExpr → QInterval (computable)
-- ============================================================================

/-- Coarsen an interval to bounded precision. Applied after each eval step
    to prevent rational number explosion from Padé exp/log. -/
private abbrev c (I : QInterval) : QInterval := I.coarsen

/-- Evaluate a reified expression to a bounding QInterval. Fully computable.
    Every compound operation is coarsened to bounded-precision rationals. -/
def RExpr.eval : RExpr → QInterval
  | .nat n => QInterval.exact n
  | .ratCast q => QInterval.exact q
  | .add a b => c ((a.eval).add (b.eval))
  | .mul a b =>
    let ra := a.eval
    let rb := b.eval
    -- Zero short-circuit
    if ra.lo == 0 && ra.hi == 0 then QInterval.exact 0
    else if rb.lo == 0 && rb.hi == 0 then QInterval.exact 0
    -- Nonneg fast path
    else if h₁ : 0 ≤ ra.lo then
      if h₂ : 0 ≤ rb.lo then c (ra.mulNonneg rb h₁ h₂)
      else c (ra.mul rb)
    else c (ra.mul rb)
  | .div a b =>
    let ra := a.eval
    let rb := b.eval
    if ra.lo == 0 && ra.hi == 0 then QInterval.exact 0
    else if h₁ : 0 ≤ ra.lo then
      if h₂ : 0 < rb.lo then c (ra.divPos rb h₁ h₂)
      else ⟨-1, 1, by norm_num⟩  -- fallback (guarded by evalValid)
    else ⟨-1, 1, by norm_num⟩
  | .neg a => (a.eval).neg
  | .sub a b => c ((a.eval).sub (b.eval))
  | .rexp a => c (expInterval (a.eval))
  | .rlog a =>
    let ra := a.eval
    if h : 0 < ra.lo then c (logInterval ra h)
    else if ra.lo == 0 && ra.hi == 0 then QInterval.exact 0  -- log(0) = 0 in Lean
    else ⟨-1000, 1000, by norm_num⟩  -- fallback (guarded by evalValid)
  | .rpow a n =>
    let ra := a.eval
    if n == 0 then Interval.rpowZero
    else if h : 0 ≤ ra.lo then c (Interval.rpowNat ra n h)
    else ⟨0, 1, by norm_num⟩  -- fallback (guarded by evalValid)
  | .inv a =>
    let ra := a.eval
    if h : 0 < ra.lo then c (ra.invPos h)
    else ⟨-1, 1, by norm_num⟩  -- fallback (guarded by evalValid)
  | .iteZero c' t e =>
    let rc := c'.eval
    if rc.lo == 0 && rc.hi == 0 then t.eval    -- cond = 0 → then branch
    else if h : (0 : ℚ) < rc.lo then e.eval      -- cond > 0 → else branch
    else  -- can't decide: take union of both branches
      let rt := t.eval
      let re := e.eval
      ⟨min rt.lo re.lo, max rt.hi re.hi,
       le_trans (min_le_left _ _) (le_trans rt.valid (le_max_left _ _))⟩
  | .expMulLogSub α x cost =>
    let rα := α.eval
    let rx := x.eval
    let rc := cost.eval
    if hx : 0 < rx.lo then
      -- α is a concrete non-negative integer? Use algebraic identity.
      if rα.lo == rα.hi && rα.lo.den == 1 && decide (0 ≤ rα.lo.num) then
        let n := rα.lo.num.toNat
        -- x^n (no Padé needed)
        let xpow :=
          if n == 0 then QInterval.exact 1
          else if n == 1 then rx
          else Interval.rpowNat rx n (le_of_lt hx)
        -- exp(-α * c): at most one Padé call per unique cost value
        let negαc := (rα.mul rc).neg
        let expFactor := c (expInterval negαc)
        -- x^n * exp(-α*c)
        if h₁ : 0 ≤ xpow.lo then
          if h₂ : 0 ≤ expFactor.lo then c (xpow.mulNonneg expFactor h₁ h₂)
          else c (xpow.mul expFactor)
        else c (xpow.mul expFactor)
      else
        -- Non-integer α: standard log + exp computation
        let logx := c (logInterval rx hx)
        let diff := c (logx.sub rc)
        let prod := c (rα.mul diff)
        c (expInterval prod)
    else ⟨0, 1, by norm_num⟩
  | .rsqrt a =>
    let ra := a.eval
    if h : 0 < ra.lo then c (sqrtInterval ra h)
    else if ra.lo == 0 && ra.hi == 0 then QInterval.exact 0  -- sqrt(0) = 0
    else ⟨0, 1, by norm_num⟩  -- fallback (guarded by evalValid)

-- ============================================================================
-- Validity: eval avoids unsound fallback branches
-- ============================================================================

/-- Whether `eval` avoids unsound fallback branches.

The fallback intervals in `eval` (e.g., `⟨-1, 1⟩` for division with non-positive
denominator) are hard-coded constants that do not soundly bound the result for
arbitrary inputs. `evalValid` returns `true` exactly when no such fallback is
reached — i.e., every division has a positive denominator, every log/inv has a
positive argument, and every rpow has a nonneg base (or zero exponent).

In practice, `rsa_decide` only builds `RExpr` values from RSA computations
(positive probabilities, positive denominators), so `evalValid` is always `true`.
The tactic verifies this via `native_decide` as a precondition. -/
def RExpr.evalValid : RExpr → Bool
  | .nat _ => true
  | .ratCast _ => true
  | .add a b => a.evalValid && b.evalValid
  | .mul a b => a.evalValid && b.evalValid
  | .div a b =>
    a.evalValid && b.evalValid &&
    ((a.eval.lo == 0 && a.eval.hi == 0) ||
     (decide (0 ≤ a.eval.lo) && decide (0 < b.eval.lo)))
  | .neg a => a.evalValid
  | .sub a b => a.evalValid && b.evalValid
  | .rexp a => a.evalValid
  | .rlog a => a.evalValid && (decide (0 < a.eval.lo) ||
    (a.eval.lo == 0 && a.eval.hi == 0))  -- log(0) = 0 in Lean
  | .rpow a n => a.evalValid && (n == 0 || decide (0 ≤ a.eval.lo))
  | .inv a => a.evalValid && decide (0 < a.eval.lo)
  | .iteZero c t e =>
    c.evalValid &&
    (let rc := c.eval
     if rc.lo = 0 ∧ rc.hi = 0 then t.evalValid
     else if (0 : ℚ) < rc.lo then e.evalValid
     else t.evalValid && e.evalValid)
  | .expMulLogSub α x cost =>
    α.evalValid && x.evalValid && cost.evalValid && decide (0 < x.eval.lo)
  | .rsqrt a => a.evalValid && (decide (0 < a.eval.lo) ||
    (a.eval.lo == 0 && a.eval.hi == 0))  -- sqrt(0) = 0

-- ============================================================================
-- tryExtractLogProduct: pattern-match sum-of-integer-logs
-- ============================================================================

/-- Extract `(xᵢ, bᵢ)` pairs from a sum-of-weighted-logs `RExpr`.
    Returns `none` if the expression doesn't match the pattern `Σ bᵢ · log(xᵢ)`.
    Coefficients `bᵢ` are rational (not just integer), enabling exact evaluation
    when log arguments coincide and coefficients sum to an integer (e.g.,
    `1/3 · log(x) + 1/3 · log(x) + 1/3 · log(x)` → `x^1` exactly). -/
def RExpr.tryExtractLogProduct : RExpr → Option (List (RExpr × ℚ))
  | .mul coeff (.rlog x) =>
    let iv := coeff.eval
    if iv.lo == iv.hi && decide (0 ≤ iv.lo) then
      let b := iv.lo
      if b == 0 then some []  -- zero coefficient, skip the log
      else some [(x, b)]
    else none
  | .rlog x => some [(x, 1)]
  | .add a b => do
    let la ← a.tryExtractLogProduct
    let lb ← b.tryExtractLogProduct
    some (la ++ lb)
  | other =>
    -- Maybe the whole thing evaluates to zero (e.g. iteZero returning 0)
    let iv := other.eval
    if iv.lo == 0 && iv.hi == 0 then some []
    else none

-- ============================================================================
-- evalBoth: Merged eval + evalValid (single-pass, no redundant computation)
-- ============================================================================

/-- Merged eval + evalValid in a single traversal. Returns `(interval, valid)`.
    This eliminates the redundant `eval` calls that `evalValid` makes on
    subexpressions — each node computes its interval exactly once.
    Uses a flat pair instead of `Option` to avoid heap allocation overhead
    in compiled code. -/
def RExpr.evalBoth : RExpr → QInterval × Bool
  | .nat n => (QInterval.exact n, true)
  | .ratCast q => (QInterval.exact q, true)
  | .add a b =>
    let (ra, va) := a.evalBoth
    let (rb, vb) := b.evalBoth
    (c (ra.add rb), va && vb)
  | .mul a b =>
    let (ra, va) := a.evalBoth
    let (rb, vb) := b.evalBoth
    let v := va && vb
    if ra.lo == 0 && ra.hi == 0 then (QInterval.exact 0, v)
    else if rb.lo == 0 && rb.hi == 0 then (QInterval.exact 0, v)
    else if h₁ : 0 ≤ ra.lo then
      if h₂ : 0 ≤ rb.lo then (c (ra.mulNonneg rb h₁ h₂), v)
      else (c (ra.mul rb), v)
    else (c (ra.mul rb), v)
  | .div a b =>
    let (ra, va) := a.evalBoth
    let (rb, vb) := b.evalBoth
    if ra.lo == 0 && ra.hi == 0 then (QInterval.exact 0, va && vb)
    else if h₁ : 0 ≤ ra.lo then
      if h₂ : 0 < rb.lo then (c (ra.divPos rb h₁ h₂), va && vb)
      else (⟨-1, 1, by norm_num⟩, false)
    else (⟨-1, 1, by norm_num⟩, false)
  | .neg a =>
    let (ra, va) := a.evalBoth
    (ra.neg, va)
  | .sub a b =>
    let (ra, va) := a.evalBoth
    let (rb, vb) := b.evalBoth
    (c (ra.sub rb), va && vb)
  | .rexp a =>
    let (ra, va) := a.evalBoth
    (c (expInterval ra), va)
  | .rlog a =>
    let (ra, va) := a.evalBoth
    if h : 0 < ra.lo then (c (logInterval ra h), va)
    else if ra.lo == 0 && ra.hi == 0 then (QInterval.exact 0, va)
    else (⟨-1000, 1000, by norm_num⟩, false)
  | .rpow a n =>
    let (ra, va) := a.evalBoth
    if n == 0 then (Interval.rpowZero, va)
    else if h : 0 ≤ ra.lo then (c (Interval.rpowNat ra n h), va)
    else (⟨0, 1, by norm_num⟩, false)
  | .inv a =>
    let (ra, va) := a.evalBoth
    if h : 0 < ra.lo then (c (ra.invPos h), va)
    else (⟨-1, 1, by norm_num⟩, false)
  | .iteZero c' t e =>
    let (rc, vc) := c'.evalBoth
    if rc.lo == 0 && rc.hi == 0 then
      let (rt, vt) := t.evalBoth
      (rt, vc && vt)
    else if h : (0 : ℚ) < rc.lo then
      let (re, ve) := e.evalBoth
      (re, vc && ve)
    else
      let (rt, vt) := t.evalBoth
      let (re, ve) := e.evalBoth
      (⟨min rt.lo re.lo, max rt.hi re.hi,
       le_trans (min_le_left _ _) (le_trans rt.valid (le_max_left _ _))⟩,
       vc && vt && ve)
  | .expMulLogSub α x cost =>
    let (rα, vα) := α.evalBoth
    let (rx, vx) := x.evalBoth
    let (rc, vc) := cost.evalBoth
    let vbase := vα && vx && vc
    if hx : 0 < rx.lo then
      if rα.lo == rα.hi && rα.lo.den == 1 && decide (0 ≤ rα.lo.num) then
        let n := rα.lo.num.toNat
        let xpow :=
          if n == 0 then QInterval.exact 1
          else if n == 1 then rx
          else Interval.rpowNat rx n (le_of_lt hx)
        let negαc := (rα.mul rc).neg
        let expFactor := c (expInterval negαc)
        if h₁ : 0 ≤ xpow.lo then
          if h₂ : 0 ≤ expFactor.lo then (c (xpow.mulNonneg expFactor h₁ h₂), vbase)
          else (c (xpow.mul expFactor), vbase)
        else (c (xpow.mul expFactor), vbase)
      else
        let logx := c (logInterval rx hx)
        let diff := c (logx.sub rc)
        let prod := c (rα.mul diff)
        (c (expInterval prod), vbase)
    else (⟨0, 1, by norm_num⟩, false)
  | .rsqrt a =>
    let (ra, va) := a.evalBoth
    if h : 0 < ra.lo then (c (sqrtInterval ra h), va)
    else if ra.lo == 0 && ra.hi == 0 then (QInterval.exact 0, va)
    else (⟨0, 1, by norm_num⟩, false)

-- ============================================================================
-- Shared helpers for eval_sound and evalBoth_sound
-- ============================================================================

/-- Helper: the three-branch mul pattern always contains v1 * v2. -/
private theorem mul_branch_containsReal {a b : QInterval} {v1 v2 : ℝ}
    (h1 : a.containsReal v1) (h2 : b.containsReal v2) :
    (if h₁ : 0 ≤ a.lo then
       if h₂ : 0 ≤ b.lo then c (a.mulNonneg b h₁ h₂)
       else c (a.mul b)
     else c (a.mul b)).containsReal (v1 * v2) := by
  split
  · rename_i h₁; split
    · rename_i h₂
      exact QInterval.coarsen_containsReal _ (QInterval.mulNonneg_containsReal h₁ h₂ h1 h2)
    · exact QInterval.coarsen_containsReal _ (QInterval.mul_containsReal h1 h2)
  · exact QInterval.coarsen_containsReal _ (QInterval.mul_containsReal h1 h2)

/-- Key lemma: if interval proves x = 0, then x = 0. -/
private theorem interval_eq_zero {I : QInterval} {x : ℝ}
    (hx : I.containsReal x) (hlo : I.lo = 0) (hhi : I.hi = 0) : x = 0 :=
  QInterval.eq_zero_of_bounds hx (by simp [hlo]) (by simp [hhi])

/-- Key lemma: if interval proves x > 0, then x > 0. -/
private theorem interval_pos {I : QInterval} {x : ℝ}
    (hx : I.containsReal x) (hlo : 0 < I.lo) : 0 < x :=
  lt_of_lt_of_le (by exact_mod_cast hlo) hx.1

/-- rpow denote reduces to rpow for all n, bridging the 3-pattern match. -/
private theorem rpow_denote_eq (a : RExpr) (n : ℕ) :
    (a.rpow n).denote = a.denote ^ (↑n : ℝ) := by
  cases n with
  | zero => exact congr_arg (Real.rpow a.denote) Nat.cast_zero.symm
  | succ m => cases m with
    | zero => exact congr_arg (Real.rpow a.denote) Nat.cast_one.symm
    | succ _ => rfl

-- ============================================================================
-- evalBoth soundness
-- ============================================================================

set_option maxHeartbeats 800000 in
/-- Soundness of the merged eval+validity check. If `evalBoth` returns
    `(I, true)`, then `I` contains the real denotation. This mirrors
    `eval_sound` but avoids the redundant subexpression evaluation that
    plagues the separate `evalValid` + `eval` approach. -/
theorem RExpr.evalBoth_sound : ∀ (e : RExpr),
    e.evalBoth.2 = true → e.evalBoth.1.containsReal e.denote := by
  intro e
  induction e with
  | nat n =>
    intro _
    match n with
    | 0 => exact QInterval.exact_zero_containsReal
    | 1 => exact QInterval.exact_one_containsReal
    | n + 2 => exact QInterval.exact_natCast_containsReal (n + 2)
  | ratCast q =>
    intro _; exact QInterval.exact_containsReal q
  | add a b iha ihb =>
    intro hv; dsimp only [evalBoth] at hv ⊢; simp only [Bool.and_eq_true] at hv
    exact QInterval.coarsen_containsReal _
      (QInterval.add_containsReal (iha hv.1) (ihb hv.2))
  | mul a b iha ihb =>
    intro hv; dsimp only [evalBoth, denote] at hv ⊢
    split_ifs at hv ⊢ with h1 h2 h3 h4 <;>
      simp only [Bool.and_eq_true] at hv <;>
      try exact absurd rfl hv
    · simp only [Bool.and_eq_true, beq_iff_eq] at h1
      exact QInterval.zero_mul_containsReal (iha hv.1) h1.1 h1.2
    · simp only [Bool.and_eq_true, beq_iff_eq] at h2
      exact QInterval.mul_zero_containsReal (ihb hv.2) h2.1 h2.2
    · exact QInterval.coarsen_containsReal _
        (QInterval.mulNonneg_containsReal h3 h4 (iha hv.1) (ihb hv.2))
    · exact QInterval.coarsen_containsReal _
        (QInterval.mul_containsReal (iha hv.1) (ihb hv.2))
    · exact QInterval.coarsen_containsReal _
        (QInterval.mul_containsReal (iha hv.1) (ihb hv.2))
  | div a b iha ihb =>
    intro hv; dsimp only [evalBoth, denote] at hv ⊢
    split_ifs at hv ⊢ with h1 h2 h3 <;>
      simp only [Bool.and_eq_true] at hv <;>
      try exact absurd rfl hv
    · simp only [Bool.and_eq_true, beq_iff_eq] at h1
      exact QInterval.zero_div_containsReal (iha hv.1) h1.1 h1.2
    · exact QInterval.coarsen_containsReal _
        (QInterval.divPos_containsReal h2 h3 (iha hv.1) (ihb hv.2))
  | neg a iha =>
    intro hv; exact QInterval.neg_containsReal (iha hv)
  | sub a b iha ihb =>
    intro hv; dsimp only [evalBoth] at hv ⊢; simp only [Bool.and_eq_true] at hv
    exact QInterval.coarsen_containsReal _
      (QInterval.sub_containsReal (iha hv.1) (ihb hv.2))
  | rexp a iha =>
    intro hv
    exact QInterval.coarsen_containsReal _ (expInterval_containsReal (iha hv))
  | rlog a iha =>
    intro hv; dsimp only [evalBoth, denote] at hv ⊢
    split_ifs at hv ⊢ with h1 h2 <;>
      try exact absurd rfl hv
    · exact QInterval.coarsen_containsReal _ (logInterval_containsReal h1 (iha hv))
    · simp only [Bool.and_eq_true, beq_iff_eq] at h2
      have haz := interval_eq_zero (iha hv) h2.1 h2.2
      rw [haz, Real.log_zero]
      exact_mod_cast QInterval.exact_containsReal (0 : ℚ)
  | rpow a n iha =>
    intro hv; dsimp only [evalBoth] at hv ⊢
    split_ifs at hv ⊢ with h1 h2 <;>
      try exact absurd rfl hv
    · have h1' : n = 0 := by simpa [beq_iff_eq] using h1
      subst h1'; exact rpowZero_containsReal a.denote
    · rw [rpow_denote_eq]
      exact QInterval.coarsen_containsReal _ (rpowNat_containsReal h2 (iha hv))
  | inv a iha =>
    intro hv; dsimp only [evalBoth, denote] at hv ⊢
    split_ifs at hv ⊢ with h1
    · exact QInterval.coarsen_containsReal _ (QInterval.invPos_containsReal h1 (iha hv))
  | iteZero c' t e ihc iht ihe =>
    intro hv; dsimp only [evalBoth] at hv ⊢
    split_ifs at hv ⊢ with h1 h2 <;>
      simp only [Bool.and_eq_true] at hv <;>
      try exact absurd rfl hv
    · -- c = [0,0] → cond = 0 → then branch
      simp only [Bool.and_eq_true, beq_iff_eq] at h1
      have hzero := interval_eq_zero (ihc hv.1) h1.1 h1.2
      unfold denote; simp [hzero]; exact iht hv.2
    · -- 0 < c.lo → cond > 0 → else branch
      have hcond_pos := interval_pos (ihc hv.1) h2
      unfold denote; simp [ne_of_gt hcond_pos]; exact ihe hv.2
    · -- can't decide: union covers both branches
      unfold denote
      simp only [QInterval.containsReal]
      split
      · constructor
        · exact le_trans (by exact_mod_cast min_le_left _ _) (iht hv.1.2).1
        · exact le_trans (iht hv.1.2).2 (by exact_mod_cast le_max_left _ _)
      · constructor
        · exact le_trans (by exact_mod_cast min_le_right _ _) (ihe hv.2).1
        · exact le_trans (ihe hv.2).2 (by exact_mod_cast le_max_right _ _)
  | expMulLogSub α x cost ihα ihx ihc =>
    intro hv; dsimp only [evalBoth, denote] at hv ⊢
    split_ifs at hv ⊢ with hx hint <;>
      simp only [Bool.and_eq_true] at hv <;>
      try exact absurd rfl hv
    all_goals have ha := ihα hv.1.1
    all_goals have hxx := ihx hv.1.2
    all_goals have hc := ihc hv.2
    all_goals have hx_pos : 0 < denote x := interval_pos hxx hx
    -- Non-integer path
    all_goals first
    | exact QInterval.coarsen_containsReal _ (expInterval_containsReal
        (QInterval.coarsen_containsReal _ (QInterval.mul_containsReal ha
          (QInterval.coarsen_containsReal _ (QInterval.sub_containsReal
            (QInterval.coarsen_containsReal _ (logInterval_containsReal hx hxx)) hc)))))
    | -- Integer path: algebraic identity exp(α*(log x - c)) = x^n * exp(-αc)
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hint
      obtain ⟨⟨hαeq, hαden⟩, hαnn⟩ := hint
      have hαval : denote α = ↑(α.evalBoth.1).lo := le_antisymm (hαeq ▸ ha.2) ha.1
      have hαq : (α.evalBoth.1).lo = (↑((α.evalBoth.1).lo.num.toNat) : ℚ) := by
        have h1 := Rat.num_div_den (α.evalBoth.1).lo
        rw [hαden] at h1; simp at h1
        rw [← h1]; exact_mod_cast (Int.toNat_of_nonneg hαnn).symm
      have hαr : denote α = (↑((α.evalBoth.1).lo.num.toNat) : ℝ) := by
        rw [hαval, hαq]; push_cast; rfl
      have hident : Real.exp (denote α * (Real.log (denote x) - denote cost))
          = (denote x) ^ ((α.evalBoth.1).lo.num.toNat : ℝ) *
            Real.exp (-(denote α * denote cost)) := by
        rw [hαr]
        have key : ((α.evalBoth.1).lo.num.toNat : ℝ) *
                   (Real.log (denote x) - denote cost) =
                   Real.log (denote x) * ((α.evalBoth.1).lo.num.toNat : ℝ) +
                   (-(((α.evalBoth.1).lo.num.toNat : ℝ) * denote cost)) := by ring
        rw [key, Real.exp_add]; congr 1
        exact (Real.rpow_def_of_pos hx_pos ((α.evalBoth.1).lo.num.toNat : ℝ)).symm
      rw [hident]
      have h_expF : (QInterval.coarsen (expInterval ((α.evalBoth.1).mul (cost.evalBoth.1)).neg)).containsReal
          (Real.exp (-(denote α * denote cost))) :=
        QInterval.coarsen_containsReal _ (expInterval_containsReal
          (QInterval.neg_containsReal (QInterval.mul_containsReal ha hc)))
      first
      | -- rpowNat × mulNonneg
        exact QInterval.coarsen_containsReal _ (QInterval.mulNonneg_containsReal ‹_› ‹_›
          (rpowNat_containsReal (le_of_lt hx) hxx) h_expF)
      | -- rpowNat × mul
        exact QInterval.coarsen_containsReal _ (QInterval.mul_containsReal
          (rpowNat_containsReal (le_of_lt hx) hxx) h_expF)
      | -- n=1 × mulNonneg
        have h_n1 : α.evalBoth.1.lo.num.toNat = 1 := beq_iff_eq.mp (by assumption)
        have h_xpow : x.evalBoth.1.containsReal
            (denote x ^ ((α.evalBoth.1).lo.num.toNat : ℝ)) := by
          rw [show ((α.evalBoth.1).lo.num.toNat : ℝ) = 1 from by exact_mod_cast h_n1]
          rw [Real.rpow_one]; exact hxx
        exact QInterval.coarsen_containsReal _ (QInterval.mulNonneg_containsReal ‹_› ‹_› h_xpow h_expF)
      | -- n=1 × mul
        have h_n1 : α.evalBoth.1.lo.num.toNat = 1 := beq_iff_eq.mp (by assumption)
        have h_xpow : x.evalBoth.1.containsReal
            (denote x ^ ((α.evalBoth.1).lo.num.toNat : ℝ)) := by
          rw [show ((α.evalBoth.1).lo.num.toNat : ℝ) = 1 from by exact_mod_cast h_n1]
          rw [Real.rpow_one]; exact hxx
        exact QInterval.coarsen_containsReal _ (QInterval.mul_containsReal h_xpow h_expF)
      | -- n=0 × mulNonneg
        have h_n0 : α.evalBoth.1.lo.num.toNat = 0 := beq_iff_eq.mp (by assumption)
        have h_xpow : (QInterval.exact 1).containsReal
            (denote x ^ ((α.evalBoth.1).lo.num.toNat : ℝ)) := by
          rw [show ((α.evalBoth.1).lo.num.toNat : ℝ) = 0 from by exact_mod_cast h_n0]
          rw [Real.rpow_zero]; exact_mod_cast QInterval.exact_containsReal 1
        exact QInterval.coarsen_containsReal _ (QInterval.mulNonneg_containsReal ‹_› ‹_› h_xpow h_expF)
      | -- n=0 × mul
        have h_n0 : α.evalBoth.1.lo.num.toNat = 0 := beq_iff_eq.mp (by assumption)
        have h_xpow : (QInterval.exact 1).containsReal
            (denote x ^ ((α.evalBoth.1).lo.num.toNat : ℝ)) := by
          rw [show ((α.evalBoth.1).lo.num.toNat : ℝ) = 0 from by exact_mod_cast h_n0]
          rw [Real.rpow_zero]; exact_mod_cast QInterval.exact_containsReal 1
        exact QInterval.coarsen_containsReal _ (QInterval.mul_containsReal h_xpow h_expF)
  | rsqrt a iha =>
    intro hv; dsimp only [evalBoth, denote] at hv ⊢
    split_ifs at hv ⊢ with h1 h2 <;>
      try exact absurd rfl hv
    · exact QInterval.coarsen_containsReal _ (sqrtInterval_containsReal h1 (iha hv))
    · simp only [Bool.and_eq_true, beq_iff_eq] at h2
      have haz := interval_eq_zero (iha hv) h2.1 h2.2
      rw [haz, Real.sqrt_zero]
      exact_mod_cast QInterval.exact_containsReal (0 : ℚ)

-- ============================================================================
-- Soundness: eval_sound
-- ============================================================================

set_option maxHeartbeats 800000 in
/-- Soundness of interval evaluation by reflection.

Every well-formed `RExpr` (one where `evalValid = true`) evaluates to a
`QInterval` that contains the real denotation. The `evalValid` precondition
excludes expressions with degenerate operations (division by non-positive,
log of non-positive, etc.) whose fallback intervals are unsound. -/
theorem RExpr.eval_sound : ∀ (e : RExpr), e.evalValid = true →
    (e.eval).containsReal e.denote
  | .nat n => by
    intro _
    match n with
    | 0 => exact QInterval.exact_zero_containsReal
    | 1 => exact QInterval.exact_one_containsReal
    | n + 2 =>
      simp only [eval, denote]
      exact QInterval.exact_natCast_containsReal (n + 2)
  | .ratCast q => by
    intro _; simp only [eval, denote]
    exact QInterval.exact_containsReal q
  | .add a b => by
    intro hv
    simp only [evalValid, Bool.and_eq_true] at hv
    simp only [eval, denote]
    exact QInterval.coarsen_containsReal _ (QInterval.add_containsReal (eval_sound a hv.1) (eval_sound b hv.2))
  | .mul a b => by
    intro hv
    simp only [evalValid, Bool.and_eq_true] at hv
    simp only [eval, denote]
    have iha := eval_sound a hv.1
    have ihb := eval_sound b hv.2
    split
    · -- ra.lo == 0 && ra.hi == 0
      rename_i h
      simp [beq_iff_eq] at h
      exact QInterval.zero_mul_containsReal iha h.1 h.2
    · split
      · -- rb.lo == 0 && rb.hi == 0
        rename_i _ h
        simp [beq_iff_eq] at h
        exact QInterval.mul_zero_containsReal ihb h.1 h.2
      · split
        · -- 0 ≤ ra.lo
          split
          · -- 0 ≤ rb.lo
            exact QInterval.coarsen_containsReal _ (QInterval.mulNonneg_containsReal ‹_› ‹_› iha ihb)
          · exact QInterval.coarsen_containsReal _ (QInterval.mul_containsReal iha ihb)
        · exact QInterval.coarsen_containsReal _ (QInterval.mul_containsReal iha ihb)
  | .div a b => by
    intro hv
    have hva : a.evalValid = true := by
      simp only [evalValid, Bool.and_eq_true] at hv; exact hv.1.1
    have hvb : b.evalValid = true := by
      simp only [evalValid, Bool.and_eq_true] at hv; exact hv.1.2
    simp only [eval, denote]
    have iha := eval_sound a hva
    have ihb := eval_sound b hvb
    split
    · rename_i h; simp [beq_iff_eq] at h
      exact QInterval.zero_div_containsReal iha h.1 h.2
    · split
      · split
        · exact QInterval.coarsen_containsReal _ (QInterval.divPos_containsReal ‹_› ‹_› iha ihb)
        · exfalso; simp_all [evalValid]
      · exfalso; simp_all [evalValid]
  | .neg a => by
    intro hv
    simp only [evalValid] at hv
    simp only [eval, denote]
    exact QInterval.neg_containsReal (eval_sound a hv)
  | .sub a b => by
    intro hv
    simp only [evalValid, Bool.and_eq_true] at hv
    simp only [eval, denote]
    exact QInterval.coarsen_containsReal _ (QInterval.sub_containsReal (eval_sound a hv.1) (eval_sound b hv.2))
  | .rexp a => by
    intro hv
    simp only [evalValid] at hv
    simp only [eval, denote]
    exact QInterval.coarsen_containsReal _ (expInterval_containsReal (eval_sound a hv))
  | .rlog a => by
    intro hv
    simp only [evalValid, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
               decide_eq_true_eq] at hv
    simp only [eval, denote]
    have iha := eval_sound a hv.1
    split
    · exact QInterval.coarsen_containsReal _ (logInterval_containsReal ‹_› iha)
    · split
      · -- log(0) = 0: a.eval = [0, 0] means a.denote = 0
        rename_i hnotpos hzero
        simp only [Bool.and_eq_true, beq_iff_eq] at hzero
        have haz := interval_eq_zero iha hzero.1 hzero.2
        rw [haz, Real.log_zero]
        have := QInterval.exact_containsReal (0 : ℚ)
        simp [Rat.cast_zero] at this
        exact this
      · -- fallback: contradiction with evalValid
        rename_i hnotpos hnotzero
        exfalso
        rcases hv.2 with hpos | hboth
        · exact hnotpos hpos
        · simp only [Bool.and_eq_true, beq_iff_eq] at hboth hnotzero
          exact hnotzero hboth
  | .rpow a 0 => by
    intro _; simp only [eval, denote]
    exact rpowZero_containsReal a.denote
  | .rpow a 1 => by
    intro hv
    simp only [evalValid, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
               decide_eq_true_eq] at hv
    have iha := eval_sound a hv.1
    simp only [eval, denote]
    split
    · rename_i h; simp at h
    · split
      · rename_i hlo
        have h := rpowNat_containsReal (n := 1) hlo iha
        simp only [Nat.cast_one] at h
        exact QInterval.coarsen_containsReal _ h
      · exact absurd (hv.2.resolve_left (by decide)) ‹_›
  | .rpow a (n + 2) => by
    intro hv
    simp only [evalValid, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
               decide_eq_true_eq] at hv
    have iha := eval_sound a hv.1
    simp only [eval, denote]
    split
    · rename_i h; simp at h
    · split
      · exact QInterval.coarsen_containsReal _ (rpowNat_containsReal ‹_› iha)
      · exact absurd (hv.2.resolve_left (by omega)) ‹_›
  | .inv a => by
    intro hv
    simp only [evalValid, Bool.and_eq_true, decide_eq_true_eq] at hv
    simp only [eval, denote]
    have iha := eval_sound a hv.1
    split
    · exact QInterval.coarsen_containsReal _ (QInterval.invPos_containsReal ‹_› iha)
    · exact absurd hv.2 ‹_›
  | .iteZero c t e => by
    intro hv
    -- Extract c.evalValid and the branch-conditional validity
    have hvc : c.evalValid = true := by
      simp only [evalValid, Bool.and_eq_true] at hv; exact hv.1
    have hbv : (if c.eval.lo = 0 ∧ c.eval.hi = 0 then t.evalValid
                else if (0 : ℚ) < c.eval.lo then e.evalValid
                else t.evalValid && e.evalValid) = true := by
      simp only [evalValid, Bool.and_eq_true] at hv; exact hv.2
    have ihc := eval_sound c hvc
    simp only [eval, denote]
    split
    · -- rc.lo == 0 && rc.hi == 0 → cond = 0 → then branch
      rename_i heq; simp [beq_iff_eq] at heq
      rw [if_pos heq] at hbv
      have hzero := interval_eq_zero ihc heq.1 heq.2
      simp [hzero]; exact eval_sound t hbv
    · split
      · -- 0 < rc.lo → cond > 0 → cond ≠ 0 → else branch
        rename_i hne hpos
        have hpne : ¬(c.eval.lo = 0 ∧ c.eval.hi = 0) := by
          intro ⟨hlo, _⟩; linarith
        rw [if_neg hpne, if_pos hpos] at hbv
        have hcond_pos := interval_pos ihc hpos
        simp [ne_of_gt hcond_pos]; exact eval_sound e hbv
      · -- can't decide: union covers both branches
        rename_i hne hle
        have hpne : ¬(c.eval.lo = 0 ∧ c.eval.hi = 0) := by
          simp [beq_iff_eq, Bool.and_eq_true] at hne
          intro ⟨a, b⟩; exact hne a b
        rw [if_neg hpne, if_neg hle] at hbv
        simp only [Bool.and_eq_true] at hbv
        obtain ⟨hvt, hve⟩ := hbv
        simp only [QInterval.containsReal]
        split
        · constructor
          · exact le_trans (by exact_mod_cast min_le_left _ _) (eval_sound t hvt).1
          · exact le_trans (eval_sound t hvt).2 (by exact_mod_cast le_max_left _ _)
        · constructor
          · exact le_trans (by exact_mod_cast min_le_right _ _) (eval_sound e hve).1
          · exact le_trans (eval_sound e hve).2 (by exact_mod_cast le_max_right _ _)
  | .expMulLogSub α x cost => by
    intro hv
    simp only [evalValid, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨⟨hva, hvx⟩, hvc⟩, hxpos⟩ := hv
    have ihα := eval_sound α hva
    have ihx := eval_sound x hvx
    have ihc := eval_sound cost hvc
    simp only [eval, denote]
    split
    · rename_i hx
      split
      · -- Integer α path: α is a non-negative integer
        rename_i hint
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hint
        obtain ⟨⟨hαeq, hαden⟩, hαnn⟩ := hint
        have hx_pos : 0 < denote x := interval_pos ihx hx
        have hαval : denote α = ↑(eval α).lo :=
          le_antisymm (hαeq ▸ ihα.2) ihα.1
        have hαq : (eval α).lo = (↑((eval α).lo.num.toNat) : ℚ) := by
          have h1 := Rat.num_div_den (eval α).lo
          rw [hαden] at h1; simp at h1
          rw [← h1]; exact_mod_cast (Int.toNat_of_nonneg hαnn).symm
        have hαr : denote α = (↑((eval α).lo.num.toNat) : ℝ) := by
          rw [hαval, hαq]; push_cast; rfl
        have hident : Real.exp (denote α * (Real.log (denote x) - denote cost))
            = (denote x) ^ ((eval α).lo.num.toNat : ℝ) *
              Real.exp (-(denote α * denote cost)) := by
          rw [hαr]
          have key : ((eval α).lo.num.toNat : ℝ) *
                     (Real.log (denote x) - denote cost) =
                     Real.log (denote x) * ((eval α).lo.num.toNat : ℝ) +
                     (-(((eval α).lo.num.toNat : ℝ) * denote cost)) := by ring
          rw [key, Real.exp_add]
          congr 1
          exact (Real.rpow_def_of_pos hx_pos ((eval α).lo.num.toNat : ℝ)).symm
        rw [hident]
        have h_expF : (c (expInterval ((eval α).mul (eval cost)).neg)).containsReal
            (Real.exp (-(denote α * denote cost))) :=
          QInterval.coarsen_containsReal _ (expInterval_containsReal
            (QInterval.neg_containsReal (QInterval.mul_containsReal ihα ihc)))
        have h_xpow : ((if (eval α).lo.num.toNat == 0 then QInterval.exact 1
                        else if (eval α).lo.num.toNat == 1 then eval x
                        else rpowNat (eval x) ((eval α).lo.num.toNat) (le_of_lt hx)
                       ) : QInterval).containsReal
                       ((denote x) ^ ((eval α).lo.num.toNat : ℝ)) := by
          split
          · rename_i hn0; simp only [beq_iff_eq] at hn0
            have h0 : ((eval α).lo.num.toNat : ℝ) = 0 := by exact_mod_cast hn0
            rw [h0, Real.rpow_zero]
            exact_mod_cast QInterval.exact_containsReal 1
          · split
            · rename_i _ hn1; simp [beq_iff_eq] at hn1
              simp only [hn1, Nat.cast_one]; rw [Real.rpow_one]; exact ihx
            · exact rpowNat_containsReal (le_of_lt hx) ihx
        exact mul_branch_containsReal h_xpow h_expF
      · -- Non-integer α path
        exact QInterval.coarsen_containsReal _ (expInterval_containsReal
          (QInterval.coarsen_containsReal _ (QInterval.mul_containsReal ihα
            (QInterval.coarsen_containsReal _ (QInterval.sub_containsReal
              (QInterval.coarsen_containsReal _ (logInterval_containsReal hx ihx)) ihc)))))
    · exact absurd hxpos ‹_›
  | .rsqrt a => by
    intro hv
    simp only [evalValid, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
               decide_eq_true_eq] at hv
    have iha := eval_sound a hv.1
    simp only [eval, denote]
    split
    · exact QInterval.coarsen_containsReal _ (sqrtInterval_containsReal ‹_› iha)
    · split
      · rename_i _ hzero
        simp only [Bool.and_eq_true, beq_iff_eq] at hzero
        have haz := interval_eq_zero iha hzero.1 hzero.2
        rw [haz, Real.sqrt_zero]
        exact_mod_cast QInterval.exact_containsReal (0 : ℚ)
      · -- fallback: contradiction with evalValid
        rename_i hnotpos hnotzero
        exfalso
        rcases hv.2 with hpos | hboth
        · exact hnotpos hpos
        · simp only [Bool.and_eq_true, beq_iff_eq] at hboth hnotzero
          exact hnotzero hboth

-- ============================================================================
-- Separation theorem for reflected expressions
-- ============================================================================

/-- If interval evaluation proves separation, the denotations are ordered.
    Requires `evalValid` for both sides to ensure the intervals are sound. -/
theorem RExpr.gt_of_eval_separated (lhs rhs : RExpr)
    (hlv : lhs.evalValid = true) (hrv : rhs.evalValid = true)
    (h : rhs.eval.hi < lhs.eval.lo) :
    lhs.denote > rhs.denote :=
  QInterval.gt_of_separated (eval_sound lhs hlv) (eval_sound rhs hrv) h

/-- Decidable separation check (for native_decide). -/
instance (lhs rhs : RExpr) : Decidable (rhs.eval.hi < lhs.eval.lo) :=
  inferInstance  -- ℚ comparison is decidable

/-- Non-separation for ¬(>) goals. -/
theorem RExpr.not_gt_of_eval_bounded (lhs rhs : RExpr)
    (hlv : lhs.evalValid = true) (hrv : rhs.evalValid = true)
    (h : lhs.eval.hi ≤ rhs.eval.lo) :
    ¬(lhs.denote > rhs.denote) :=
  not_lt.mpr (QInterval.le_of_separated (eval_sound lhs hlv) (eval_sound rhs hrv) h)

instance (lhs rhs : RExpr) : Decidable (lhs.eval.hi ≤ rhs.eval.lo) :=
  inferInstance

-- ============================================================================
-- evalRexpOpt: exp-log rewrite optimization
-- ============================================================================

/-- Group `(x_rexpr, coeff)` pairs by exact value of the log argument,
    summing coefficients within each group. Uses `eval` point intervals
    to identify equal arguments (if `eval` gives a point `[q, q]`, the
    argument is exact). Entries with non-exact arguments are kept as
    singletons. Returns `(x_rexpr, total_coeff)` pairs. -/
private def groupLogFactors (factors : List (RExpr × ℚ)) :
    List (RExpr × ℚ) :=
  factors.foldl (init := ([] : List (RExpr × ℚ))) fun acc (x, b) =>
    let xIv := x.eval
    if xIv.lo == xIv.hi then
      -- Exact value — try to merge with existing group
      let q := xIv.lo
      let (found, acc') := acc.foldl (init := (false, [])) fun (found, result) (gExpr, gCoeff) =>
        if !found then
          let gIv := gExpr.eval
          if gIv.lo == gIv.hi && gIv.lo == q then
            (true, (gExpr, gCoeff + b) :: result)
          else
            (found, (gExpr, gCoeff) :: result)
        else
          (found, (gExpr, gCoeff) :: result)
      if found then acc'.reverse
      else acc ++ [(x, b)]
    else
      acc ++ [(x, b)]

private theorem nat_denote (n : ℕ) : (RExpr.nat n).denote = (↑n : ℝ) := by
  match n with
  | 0 => exact_mod_cast RExpr.denote.eq_1
  | 1 => exact_mod_cast RExpr.denote.eq_2
  | n + 2 => exact RExpr.denote.eq_3 _ (by omega) (by omega)

/-- Optimized evaluation for `rexp` nodes: recursively decomposes the inner
    expression using exp identities:
    - exp(a + b) = exp(a) · exp(b) — splits sums
    - exp(n · log(x)) = x^n when n ∈ ℕ, x > 0 — exact power
    - exp(n · body) = exp(body)^n when n ∈ ℕ — factors out nat multiplier
    - exp(other) via Padé — fallback -/
def RExpr.evalRexpOpt : RExpr → QInterval × Bool
  | .add a b =>
    let (ra, va) := a.evalRexpOpt
    let (rb, vb) := b.evalRexpOpt
    let v := va && vb
    if h₁ : 0 ≤ ra.lo then
      if h₂ : 0 ≤ rb.lo then (c (ra.mulNonneg rb h₁ h₂), v)
      else (c (ra.mul rb), v)
    else (c (ra.mul rb), v)
  | .mul (.nat α) (.rlog x) =>
    let (xiv, xv) := x.evalBoth
    if α == 0 then (QInterval.exact 1, xv)
    else if h : 0 < xiv.lo then
      (c (Interval.rpowNat xiv α (le_of_lt h)), xv)
    else
      let (iv, valid) := RExpr.evalBoth (.mul (.nat α) (.rlog x))
      (c (expInterval iv), valid)
  | .mul (.nat α) body =>
    if α == 0 then (QInterval.exact 1, true)
    else if α == 1 then body.evalRexpOpt
    else
      let (base, bv) := body.evalRexpOpt
      if h : 0 ≤ base.lo then
        (c (Interval.rpowNat base α h), bv)
      else
        let (iv, valid) := RExpr.evalBoth (.mul (.nat α) body)
        (c (expInterval iv), valid)
  | other =>
    let (iv, valid) := other.evalBoth
    (c (expInterval iv), valid)

-- ============================================================================
-- evalBothOpt: evalBoth with exp-log product rewrite at .rexp nodes
-- ============================================================================

/-- Like `evalBoth` but intercepts `.rexp` nodes to use the exp-log product
    rewrite via `evalRexpOpt`. All other cases are identical to `evalBoth`.
    `evalRexpOpt` itself calls `evalBoth` (not `evalBothOpt`) for leaf
    sub-expressions, avoiding mutual recursion — this is correct because
    `.rexp` nodes don't nest inside each other in RSA expression trees. -/
def RExpr.evalBothOpt : RExpr → QInterval × Bool
  | .nat n => (QInterval.exact n, true)
  | .ratCast q => (QInterval.exact q, true)
  | .add a b =>
    let (ra, va) := a.evalBothOpt
    let (rb, vb) := b.evalBothOpt
    (c (ra.add rb), va && vb)
  | .mul a b =>
    let (ra, va) := a.evalBothOpt
    if ra.lo == 0 && ra.hi == 0 then (QInterval.exact 0, va)
    else
      let (rb, vb) := b.evalBothOpt
      let v := va && vb
      if rb.lo == 0 && rb.hi == 0 then (QInterval.exact 0, v)
      else if h₁ : 0 ≤ ra.lo then
        if h₂ : 0 ≤ rb.lo then (c (ra.mulNonneg rb h₁ h₂), v)
        else (c (ra.mul rb), v)
      else (c (ra.mul rb), v)
  | .div a b =>
    let (ra, va) := a.evalBothOpt
    let (rb, vb) := b.evalBothOpt
    if ra.lo == 0 && ra.hi == 0 then (QInterval.exact 0, va && vb)
    else if h₁ : 0 ≤ ra.lo then
      if h₂ : 0 < rb.lo then (c (ra.divPos rb h₁ h₂), va && vb)
      else (⟨-1, 1, by norm_num⟩, false)
    else (⟨-1, 1, by norm_num⟩, false)
  | .neg a =>
    let (ra, va) := a.evalBothOpt
    (ra.neg, va)
  | .sub a b =>
    let (ra, va) := a.evalBothOpt
    let (rb, vb) := b.evalBothOpt
    (c (ra.sub rb), va && vb)
  | .rexp a => a.evalRexpOpt  -- use exp-log product rewrite
  | .rlog a =>
    let (ra, va) := a.evalBothOpt
    if h : 0 < ra.lo then (c (logInterval ra h), va)
    else if ra.lo == 0 && ra.hi == 0 then (QInterval.exact 0, va)
    else (⟨-1000, 1000, by norm_num⟩, false)
  | .rpow a n =>
    let (ra, va) := a.evalBothOpt
    if n == 0 then (Interval.rpowZero, va)
    else if h : 0 ≤ ra.lo then (c (Interval.rpowNat ra n h), va)
    else (⟨0, 1, by norm_num⟩, false)
  | .inv a =>
    let (ra, va) := a.evalBothOpt
    if h : 0 < ra.lo then (c (ra.invPos h), va)
    else (⟨-1, 1, by norm_num⟩, false)
  | .iteZero c' t e =>
    let (rc, vc) := c'.evalBothOpt
    if rc.lo == 0 && rc.hi == 0 then
      let (rt, vt) := t.evalBothOpt
      (rt, vc && vt)
    else if h : (0 : ℚ) < rc.lo then
      let (re, ve) := e.evalBothOpt
      (re, vc && ve)
    else
      let (rt, vt) := t.evalBothOpt
      let (re, ve) := e.evalBothOpt
      (⟨min rt.lo re.lo, max rt.hi re.hi,
       le_trans (min_le_left _ _) (le_trans rt.valid (le_max_left _ _))⟩,
       vc && vt && ve)
  | .expMulLogSub α x cost =>
    let (rα, vα) := α.evalBothOpt
    let (rx, vx) := x.evalBothOpt
    let (rc, vc) := cost.evalBothOpt
    let vbase := vα && vx && vc
    if hx : 0 < rx.lo then
      if rα.lo == rα.hi && rα.lo.den == 1 && decide (0 ≤ rα.lo.num) then
        let n := rα.lo.num.toNat
        let xpow :=
          if n == 0 then QInterval.exact 1
          else if n == 1 then rx
          else Interval.rpowNat rx n (le_of_lt hx)
        let negαc := (rα.mul rc).neg
        let expFactor := c (expInterval negαc)
        if h₁ : 0 ≤ xpow.lo then
          if h₂ : 0 ≤ expFactor.lo then (c (xpow.mulNonneg expFactor h₁ h₂), vbase)
          else (c (xpow.mul expFactor), vbase)
        else (c (xpow.mul expFactor), vbase)
      else
        let logx := c (logInterval rx hx)
        let diff := c (logx.sub rc)
        let prod := c (rα.mul diff)
        (c (expInterval prod), vbase)
    else (⟨0, 1, by norm_num⟩, false)
  | .rsqrt a =>
    let (ra, va) := a.evalBothOpt
    if h : 0 < ra.lo then (c (sqrtInterval ra h), va)
    else if ra.lo == 0 && ra.hi == 0 then (QInterval.exact 0, va)
    else (⟨0, 1, by norm_num⟩, false)

-- `unfold evalRexpOpt` expands exactly one level when the scrutinee has a
-- specific constructor head, leaving recursive `evalRexpOpt` calls opaque.
-- For `.mul (.nat α) body` where body is generic, we `cases body` first.
set_option maxHeartbeats 3200000 in
private theorem evalRexpOpt_sound : ∀ (inner : RExpr),
    inner.evalRexpOpt.2 = true → inner.evalRexpOpt.1.containsReal (Real.exp inner.denote)
  -- ══════════════════════════════════════════════════════════════════════
  -- Case 1: exp(a + b) = exp(a) · exp(b)
  -- ══════════════════════════════════════════════════════════════════════
  | .add a b => fun hv => by
    unfold RExpr.evalRexpOpt at hv ⊢
    rcases ha : a.evalRexpOpt with ⟨ra, va⟩
    rcases hb : b.evalRexpOpt with ⟨rb, vb⟩
    simp only [ha, hb] at hv ⊢
    split_ifs at hv ⊢ with h1 h2
    all_goals simp only [Bool.and_eq_true] at hv
    all_goals (
      have iha := evalRexpOpt_sound a (by rw [ha]; exact hv.1)
      have ihb := evalRexpOpt_sound b (by rw [hb]; exact hv.2)
      rw [ha] at iha; rw [hb] at ihb
      simp only [RExpr.denote.eq_5, Real.exp_add])
    · exact QInterval.coarsen_containsReal _
        (QInterval.mulNonneg_containsReal h1 h2 iha ihb)
    · exact QInterval.coarsen_containsReal _
        (QInterval.mul_containsReal iha ihb)
    · exact QInterval.coarsen_containsReal _
        (QInterval.mul_containsReal iha ihb)
  -- ══════════════════════════════════════════════════════════════════════
  -- Case 2: exp(α · log(x)) = x^α  (when x > 0)
  -- ══════════════════════════════════════════════════════════════════════
  | .mul (.nat α) (.rlog x) => fun hv => by
    unfold RExpr.evalRexpOpt at hv ⊢
    rcases hx : x.evalBoth with ⟨xiv, xv⟩
    simp only [hx] at hv ⊢
    split_ifs at hv ⊢ with h0 hpos
    · -- α = 0: exp(0 · log x) = exp(0) = 1
      simp only [beq_iff_eq] at h0; subst h0
      simp only [RExpr.denote.eq_6, RExpr.denote.eq_11, RExpr.denote.eq_1, zero_mul, Real.exp_zero]
      exact_mod_cast QInterval.exact_containsReal (1 : ℚ)
    · -- α ≠ 0, xiv.lo > 0: exp(α·log x) = x^α via rpow
      have hxval : xiv.containsReal x.denote := by
        have h := RExpr.evalBoth_sound x; rw [hx] at h; exact h hv
      have hxpos : 0 < x.denote := interval_pos hxval hpos
      rw [RExpr.denote.eq_6, RExpr.denote.eq_11, nat_denote, mul_comm,
          ← Real.rpow_def_of_pos hxpos]
      exact QInterval.coarsen_containsReal _ (rpowNat_containsReal (le_of_lt hpos) hxval)
    · -- fallback: evalBoth + expInterval
      rcases he : ((RExpr.nat α).mul (.rlog x)).evalBoth with ⟨iv, valid⟩
      simp only [he] at hv ⊢
      have hv' : ((RExpr.nat α).mul (.rlog x)).evalBoth.2 = true := by rw [he]; exact hv
      have heb := RExpr.evalBoth_sound _ hv'; rw [he] at heb
      exact QInterval.coarsen_containsReal _ (expInterval_containsReal heb)
  -- ══════════════════════════════════════════════════════════════════════
  -- Case 3: exp(α · body) — use `split` to decompose the match on body
  -- ══════════════════════════════════════════════════════════════════════
  | .mul (.nat α) body => fun hv => by
    unfold RExpr.evalRexpOpt at hv ⊢
    -- `unfold` produces the full match on (.nat α).mul body; `split` decomposes it
    split at *
    · -- .add case: contradictory (mul ≠ add)
      rename_i heq; exact absurd heq (by simp)
    · -- .mul (.nat _) (.rlog x) subcase (overlap with case 2)
      rename_i _x α' x' heq
      simp only [RExpr.mul.injEq, RExpr.nat.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      -- Same proof as case 2: exp(α·log x) = x^α
      rcases hx : x'.evalBoth with ⟨xiv, xv⟩
      simp only [hx] at hv ⊢
      split_ifs at hv ⊢ with h0 hpos
      · simp only [beq_iff_eq] at h0; subst h0
        simp only [RExpr.denote.eq_6, RExpr.denote.eq_11, RExpr.denote.eq_1,
                    zero_mul, Real.exp_zero]
        exact_mod_cast QInterval.exact_containsReal (1 : ℚ)
      · have hxval : xiv.containsReal x'.denote := by
          have h := RExpr.evalBoth_sound x'; rw [hx] at h; exact h hv
        rw [RExpr.denote.eq_6, RExpr.denote.eq_11, nat_denote, mul_comm,
            ← Real.rpow_def_of_pos (interval_pos hxval hpos)]
        exact QInterval.coarsen_containsReal _ (rpowNat_containsReal (le_of_lt hpos) hxval)
      · rcases he : ((RExpr.nat α).mul (.rlog x')).evalBoth with ⟨iv, valid⟩
        simp only [he] at hv ⊢
        have hv' : ((RExpr.nat α).mul (.rlog x')).evalBoth.2 = true := by rw [he]; exact hv
        have heb := RExpr.evalBoth_sound _ hv'; rw [he] at heb
        exact QInterval.coarsen_containsReal _ (expInterval_containsReal heb)
    · -- .mul (.nat α) body subcase (body ≠ .rlog)
      rename_i _x α' body' _hnotlog heq
      simp only [RExpr.mul.injEq, RExpr.nat.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      -- Now: if/then/else on α for non-rlog body
      split_ifs at hv ⊢ with h0 h1
      · -- α = 0: exp(0 · body) = 1
        simp only [beq_iff_eq] at h0; subst h0
        simp only [RExpr.denote.eq_6, RExpr.denote.eq_1, zero_mul, Real.exp_zero]
        exact_mod_cast QInterval.exact_containsReal (1 : ℚ)
      · -- α = 1: exp(1 · body) = exp(body), delegate to IH
        simp only [beq_iff_eq] at h1
        have h1n : α = 1 := by omega
        subst h1n
        have hden : Real.exp ((RExpr.mul (.nat 1) body).denote) = Real.exp body.denote := by
          congr 1; simp only [RExpr.denote.eq_6, nat_denote, Nat.cast_one, one_mul]
        rw [hden]
        exact evalRexpOpt_sound _ hv
      · -- α ≥ 2: exp(α · body) = exp(body)^α
        rcases hb : body.evalRexpOpt with ⟨base, bv⟩
        simp only [hb] at hv ⊢
        split_ifs at hv ⊢ with hnn
        · -- rpowNat path: base.lo ≥ 0
          have ihb := evalRexpOpt_sound body (by rw [hb]; exact hv)
          rw [hb] at ihb
          have hden : Real.exp ((RExpr.mul (.nat α) body).denote) =
              Real.exp body.denote ^ (↑α : ℝ) := by
            rw [RExpr.denote.eq_6, nat_denote, Real.exp_nat_mul, ← Real.rpow_natCast]
          rw [hden]
          exact QInterval.coarsen_containsReal _ (rpowNat_containsReal hnn ihb)
        · -- fallback: evalBoth + expInterval
          rcases he : ((RExpr.nat α).mul body).evalBoth with ⟨iv, valid⟩
          simp only [he] at hv ⊢
          have hv' : ((RExpr.nat α).mul body).evalBoth.2 = true := by rw [he]; exact hv
          have heb := RExpr.evalBoth_sound _ hv'; rw [he] at heb
          exact QInterval.coarsen_containsReal _ (expInterval_containsReal heb)
    · -- catch-all: contradictory (mul (.nat α) body matches case 3)
      rename_i heq; exact absurd heq (by simp)
  -- ══════════════════════════════════════════════════════════════════════
  -- Case 4: catch-all — evalBoth + expInterval fallback
  -- ══════════════════════════════════════════════════════════════════════
  | .nat _ | .ratCast _ | .div _ _ | .neg _ | .sub _ _ | .rexp _
  | .rlog _ | .rpow _ _ | .inv _ | .iteZero _ _ _ | .expMulLogSub _ _ _
  | .rsqrt _
  | .mul (.ratCast _) _ | .mul (.add _ _) _ | .mul (.mul _ _) _
  | .mul (.div _ _) _ | .mul (.neg _) _ | .mul (.sub _ _) _
  | .mul (.rexp _) _ | .mul (.rlog _) _ | .mul (.rpow _ _) _
  | .mul (.inv _) _ | .mul (.iteZero _ _ _) _ | .mul (.expMulLogSub _ _ _) _
  | .mul (.rsqrt _) _ => fun hv => by
    unfold RExpr.evalRexpOpt at hv ⊢
    exact QInterval.coarsen_containsReal _
      (expInterval_containsReal (RExpr.evalBoth_sound _ hv))

set_option maxHeartbeats 800000 in
/-- Soundness of evalBothOpt. Mirrors `evalBoth_sound` — all cases except
    `.rexp` are structurally identical; `.rexp` delegates to `evalRexpOpt`
    which needs separate soundness reasoning. -/
theorem RExpr.evalBothOpt_sound : ∀ (e : RExpr),
    e.evalBothOpt.2 = true → e.evalBothOpt.1.containsReal e.denote := by
  intro e
  induction e with
  | nat n =>
    intro _
    match n with
    | 0 => exact QInterval.exact_zero_containsReal
    | 1 => exact QInterval.exact_one_containsReal
    | n + 2 => exact QInterval.exact_natCast_containsReal (n + 2)
  | ratCast q =>
    intro _; exact QInterval.exact_containsReal q
  | add a b iha ihb =>
    intro hv; dsimp only [evalBothOpt] at hv ⊢; simp only [Bool.and_eq_true] at hv
    exact QInterval.coarsen_containsReal _
      (QInterval.add_containsReal (iha hv.1) (ihb hv.2))
  | mul a b iha ihb =>
    intro hv; dsimp only [evalBothOpt, denote] at hv ⊢
    split_ifs at hv ⊢ with h1 h2 h3 h4 <;>
      simp only [Bool.and_eq_true] at hv <;>
      try exact absurd rfl hv
    · simp only [Bool.and_eq_true, beq_iff_eq] at h1
      exact QInterval.zero_mul_containsReal (iha hv) h1.1 h1.2
    · simp only [Bool.and_eq_true, beq_iff_eq] at h2
      exact QInterval.mul_zero_containsReal (ihb hv.2) h2.1 h2.2
    · exact QInterval.coarsen_containsReal _
        (QInterval.mulNonneg_containsReal h3 h4 (iha hv.1) (ihb hv.2))
    · exact QInterval.coarsen_containsReal _
        (QInterval.mul_containsReal (iha hv.1) (ihb hv.2))
    · exact QInterval.coarsen_containsReal _
        (QInterval.mul_containsReal (iha hv.1) (ihb hv.2))
  | div a b iha ihb =>
    intro hv; dsimp only [evalBothOpt, denote] at hv ⊢
    split_ifs at hv ⊢ with h1 h2 h3 <;>
      simp only [Bool.and_eq_true] at hv <;>
      try exact absurd rfl hv
    · simp only [Bool.and_eq_true, beq_iff_eq] at h1
      exact QInterval.zero_div_containsReal (iha hv.1) h1.1 h1.2
    · exact QInterval.coarsen_containsReal _
        (QInterval.divPos_containsReal h2 h3 (iha hv.1) (ihb hv.2))
  | neg a iha =>
    intro hv; exact QInterval.neg_containsReal (iha hv)
  | sub a b iha ihb =>
    intro hv; dsimp only [evalBothOpt] at hv ⊢; simp only [Bool.and_eq_true] at hv
    exact QInterval.coarsen_containsReal _
      (QInterval.sub_containsReal (iha hv.1) (ihb hv.2))
  | rexp a _iha =>
    intro hv; exact evalRexpOpt_sound a hv
  | rlog a iha =>
    intro hv; dsimp only [evalBothOpt, denote] at hv ⊢
    split_ifs at hv ⊢ with h1 h2 <;>
      try exact absurd rfl hv
    · exact QInterval.coarsen_containsReal _ (logInterval_containsReal h1 (iha hv))
    · simp only [Bool.and_eq_true, beq_iff_eq] at h2
      have haz := interval_eq_zero (iha hv) h2.1 h2.2
      rw [haz, Real.log_zero]
      exact_mod_cast QInterval.exact_containsReal (0 : ℚ)
  | rpow a n iha =>
    intro hv; dsimp only [evalBothOpt] at hv ⊢
    split_ifs at hv ⊢ with h1 h2 <;>
      try exact absurd rfl hv
    · have h1' : n = 0 := by simpa [beq_iff_eq] using h1
      subst h1'; exact rpowZero_containsReal a.denote
    · rw [rpow_denote_eq]
      exact QInterval.coarsen_containsReal _ (rpowNat_containsReal h2 (iha hv))
  | inv a iha =>
    intro hv; dsimp only [evalBothOpt, denote] at hv ⊢
    split_ifs at hv ⊢ with h1
    · exact QInterval.coarsen_containsReal _ (QInterval.invPos_containsReal h1 (iha hv))
  | iteZero c' t e ihc iht ihe =>
    intro hv; dsimp only [evalBothOpt] at hv ⊢
    split_ifs at hv ⊢ with h1 h2 <;>
      simp only [Bool.and_eq_true] at hv <;>
      try exact absurd rfl hv
    · -- c = [0,0] → cond = 0 → then branch
      simp only [Bool.and_eq_true, beq_iff_eq] at h1
      have hzero := interval_eq_zero (ihc hv.1) h1.1 h1.2
      unfold denote; simp [hzero]; exact iht hv.2
    · -- 0 < c.lo → cond > 0 → else branch
      have hcond_pos := interval_pos (ihc hv.1) h2
      unfold denote; simp [ne_of_gt hcond_pos]; exact ihe hv.2
    · -- can't decide: union covers both branches
      unfold denote
      simp only [QInterval.containsReal]
      split
      · constructor
        · exact le_trans (by exact_mod_cast min_le_left _ _) (iht hv.1.2).1
        · exact le_trans (iht hv.1.2).2 (by exact_mod_cast le_max_left _ _)
      · constructor
        · exact le_trans (by exact_mod_cast min_le_right _ _) (ihe hv.2).1
        · exact le_trans (ihe hv.2).2 (by exact_mod_cast le_max_right _ _)
  | expMulLogSub α x cost ihα ihx ihc =>
    intro hv; dsimp only [evalBothOpt, denote] at hv ⊢
    split_ifs at hv ⊢ with hx hint <;>
      simp only [Bool.and_eq_true] at hv <;>
      try exact absurd rfl hv
    all_goals have ha := ihα hv.1.1
    all_goals have hxx := ihx hv.1.2
    all_goals have hc := ihc hv.2
    all_goals have hx_pos : 0 < denote x := interval_pos hxx hx
    -- Non-integer path
    all_goals first
    | exact QInterval.coarsen_containsReal _ (expInterval_containsReal
        (QInterval.coarsen_containsReal _ (QInterval.mul_containsReal ha
          (QInterval.coarsen_containsReal _ (QInterval.sub_containsReal
            (QInterval.coarsen_containsReal _ (logInterval_containsReal hx hxx)) hc)))))
    | -- Integer path: algebraic identity exp(α*(log x - c)) = x^n * exp(-αc)
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hint
      obtain ⟨⟨hαeq, hαden⟩, hαnn⟩ := hint
      have hαval : denote α = ↑(α.evalBothOpt.1).lo := le_antisymm (hαeq ▸ ha.2) ha.1
      have hαq : (α.evalBothOpt.1).lo = (↑((α.evalBothOpt.1).lo.num.toNat) : ℚ) := by
        have h1 := Rat.num_div_den (α.evalBothOpt.1).lo
        rw [hαden] at h1; simp at h1
        rw [← h1]; exact_mod_cast (Int.toNat_of_nonneg hαnn).symm
      have hαr : denote α = (↑((α.evalBothOpt.1).lo.num.toNat) : ℝ) := by
        rw [hαval, hαq]; push_cast; rfl
      have hident : Real.exp (denote α * (Real.log (denote x) - denote cost))
          = (denote x) ^ ((α.evalBothOpt.1).lo.num.toNat : ℝ) *
            Real.exp (-(denote α * denote cost)) := by
        rw [hαr]
        have key : ((α.evalBothOpt.1).lo.num.toNat : ℝ) *
                   (Real.log (denote x) - denote cost) =
                   Real.log (denote x) * ((α.evalBothOpt.1).lo.num.toNat : ℝ) +
                   (-(((α.evalBothOpt.1).lo.num.toNat : ℝ) * denote cost)) := by ring
        rw [key, Real.exp_add]; congr 1
        exact (Real.rpow_def_of_pos hx_pos ((α.evalBothOpt.1).lo.num.toNat : ℝ)).symm
      rw [hident]
      have h_expF : (QInterval.coarsen (expInterval ((α.evalBothOpt.1).mul (cost.evalBothOpt.1)).neg)).containsReal
          (Real.exp (-(denote α * denote cost))) :=
        QInterval.coarsen_containsReal _ (expInterval_containsReal
          (QInterval.neg_containsReal (QInterval.mul_containsReal ha hc)))
      first
      | -- rpowNat × mulNonneg
        exact QInterval.coarsen_containsReal _ (QInterval.mulNonneg_containsReal ‹_› ‹_›
          (rpowNat_containsReal (le_of_lt hx) hxx) h_expF)
      | -- rpowNat × mul
        exact QInterval.coarsen_containsReal _ (QInterval.mul_containsReal
          (rpowNat_containsReal (le_of_lt hx) hxx) h_expF)
      | -- n=1 × mulNonneg
        have h_n1 : α.evalBothOpt.1.lo.num.toNat = 1 := beq_iff_eq.mp (by assumption)
        have h_xpow : x.evalBothOpt.1.containsReal
            (denote x ^ ((α.evalBothOpt.1).lo.num.toNat : ℝ)) := by
          rw [show ((α.evalBothOpt.1).lo.num.toNat : ℝ) = 1 from by exact_mod_cast h_n1]
          rw [Real.rpow_one]; exact hxx
        exact QInterval.coarsen_containsReal _ (QInterval.mulNonneg_containsReal ‹_› ‹_› h_xpow h_expF)
      | -- n=1 × mul
        have h_n1 : α.evalBothOpt.1.lo.num.toNat = 1 := beq_iff_eq.mp (by assumption)
        have h_xpow : x.evalBothOpt.1.containsReal
            (denote x ^ ((α.evalBothOpt.1).lo.num.toNat : ℝ)) := by
          rw [show ((α.evalBothOpt.1).lo.num.toNat : ℝ) = 1 from by exact_mod_cast h_n1]
          rw [Real.rpow_one]; exact hxx
        exact QInterval.coarsen_containsReal _ (QInterval.mul_containsReal h_xpow h_expF)
      | -- n=0 × mulNonneg
        have h_n0 : α.evalBothOpt.1.lo.num.toNat = 0 := beq_iff_eq.mp (by assumption)
        have h_xpow : (QInterval.exact 1).containsReal
            (denote x ^ ((α.evalBothOpt.1).lo.num.toNat : ℝ)) := by
          rw [show ((α.evalBothOpt.1).lo.num.toNat : ℝ) = 0 from by exact_mod_cast h_n0]
          rw [Real.rpow_zero]; exact_mod_cast QInterval.exact_containsReal 1
        exact QInterval.coarsen_containsReal _ (QInterval.mulNonneg_containsReal ‹_› ‹_› h_xpow h_expF)
      | -- n=0 × mul
        have h_n0 : α.evalBothOpt.1.lo.num.toNat = 0 := beq_iff_eq.mp (by assumption)
        have h_xpow : (QInterval.exact 1).containsReal
            (denote x ^ ((α.evalBothOpt.1).lo.num.toNat : ℝ)) := by
          rw [show ((α.evalBothOpt.1).lo.num.toNat : ℝ) = 0 from by exact_mod_cast h_n0]
          rw [Real.rpow_zero]; exact_mod_cast QInterval.exact_containsReal 1
        exact QInterval.coarsen_containsReal _ (QInterval.mul_containsReal h_xpow h_expF)
  | rsqrt a iha =>
    intro hv; dsimp only [evalBothOpt, denote] at hv ⊢
    split_ifs at hv ⊢ with h1 h2 <;>
      try exact absurd rfl hv
    · exact QInterval.coarsen_containsReal _ (sqrtInterval_containsReal h1 (iha hv))
    · simp only [Bool.and_eq_true, beq_iff_eq] at h2
      have haz := interval_eq_zero (iha hv) h2.1 h2.2
      rw [haz, Real.sqrt_zero]
      exact_mod_cast QInterval.exact_containsReal (0 : ℚ)

/-- Combined check: eval + validity + separation in a single pass via `evalBoth`.
    Each subexpression is evaluated exactly once. -/
def RExpr.checkGt (lhs rhs : RExpr) : Bool :=
  let (li, lv) := lhs.evalBoth
  let (ri, rv) := rhs.evalBoth
  lv && rv && decide (ri.hi < li.lo)

/-- If checkGt succeeds, the denotations are ordered. -/
theorem RExpr.gt_of_checkGt (lhs rhs : RExpr) (h : lhs.checkGt rhs = true) :
    lhs.denote > rhs.denote := by
  simp only [checkGt, Bool.and_eq_true, decide_eq_true_eq] at h
  exact QInterval.gt_of_separated (evalBoth_sound lhs h.1.1) (evalBoth_sound rhs h.1.2) h.2

/-- Combined check for ¬(>): eval + validity + upper bound in a single pass. -/
def RExpr.checkNotGt (lhs rhs : RExpr) : Bool :=
  let (li, lv) := lhs.evalBoth
  let (ri, rv) := rhs.evalBoth
  lv && rv && decide (li.hi ≤ ri.lo)

/-- If checkNotGt succeeds, ¬(lhs > rhs). -/
theorem RExpr.not_gt_of_checkNotGt (lhs rhs : RExpr) (h : lhs.checkNotGt rhs = true) :
    ¬(lhs.denote > rhs.denote) := by
  simp only [checkNotGt, Bool.and_eq_true, decide_eq_true_eq] at h
  exact not_lt.mpr (QInterval.le_of_separated (evalBoth_sound lhs h.1.1) (evalBoth_sound rhs h.1.2) h.2)

-- ============================================================================
-- RExpr normalization: dead-branch elimination for iteZero/mul
-- ============================================================================

/-- Check if an RExpr is provably zero via interval arithmetic. -/
def RExpr.isZero (e : RExpr) : Bool :=
  let (iv, valid) := e.evalBothOpt
  valid && iv.lo == 0 && iv.hi == 0

/-- Check if an RExpr is provably positive via interval arithmetic. -/
def RExpr.isPos (e : RExpr) : Bool :=
  let (iv, valid) := e.evalBothOpt
  valid && decide (0 < iv.lo)

/-- If `isZero` succeeds, the denotation is 0. -/
theorem RExpr.denote_eq_zero (e : RExpr) (h : e.isZero = true) : e.denote = 0 := by
  simp only [isZero, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hv, hlo⟩, hhi⟩ := h
  have hmem := evalBothOpt_sound e hv
  simp only [QInterval.containsReal] at hmem
  rw [hlo, hhi] at hmem
  simp only [Rat.cast_zero] at hmem
  linarith [hmem.1, hmem.2]

/-- If `isPos` succeeds, the denotation is nonzero. -/
theorem RExpr.denote_ne_zero (e : RExpr) (h : e.isPos = true) : e.denote ≠ 0 := by
  simp only [isPos, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hv, hlo⟩ := h
  have hmem := evalBothOpt_sound e hv
  simp only [QInterval.containsReal] at hmem
  have hlo_real : (0 : ℝ) < ↑e.evalBothOpt.1.lo := by exact_mod_cast hlo
  intro heq; linarith [hmem.1]

/-- Normalize an RExpr by:
    1. Resolving `iteZero` with constant conditions (dead-branch elimination)
    2. Eliminating `mul` with provably-zero operands
    3. Rewriting `rexp(mul(α, sub(rlog(x), c)))` → `expMulLogSub(α, x, c)`
    All transformations preserve denotation. Dead-branch elimination is
    critical for proving ¬(>) on symmetric models, where two expressions
    become structurally identical after resolving iteZero branches. -/
def RExpr.normalize : RExpr → RExpr
  | .rexp (.mul α (.sub (.rlog x) cost)) =>
    .expMulLogSub α.normalize x.normalize cost.normalize
  | .nat n => .nat n
  | .ratCast q => .ratCast q
  | .add a b => .add a.normalize b.normalize
  | .mul a b =>
    let na := a.normalize
    let nb := b.normalize
    if na.isZero then .nat 0
    else if nb.isZero then .nat 0
    else .mul na nb
  | .div a b => .div a.normalize b.normalize
  | .neg a => .neg a.normalize
  | .sub a b => .sub a.normalize b.normalize
  | .rexp a => .rexp a.normalize
  | .rlog (.rexp inner) => inner.normalize  -- log(exp(x)) = x
  | .rlog a => .rlog a.normalize
  | .rpow a n => .rpow a.normalize n
  | .inv a => .inv a.normalize
  | .iteZero c t e =>
    let nc := c.normalize
    if nc.isZero then t.normalize
    else if nc.isPos then e.normalize
    else .iteZero nc t.normalize e.normalize
  | .rsqrt a => .rsqrt a.normalize
  | .expMulLogSub α x cost =>
    .expMulLogSub α.normalize x.normalize cost.normalize

/-- Normalization preserves denotation. -/
def RExpr.normalize_denote : ∀ (e : RExpr), e.normalize.denote = e.denote
  | .nat _ | .ratCast _ => rfl
  | .add a b => congrArg₂ (· + ·) a.normalize_denote b.normalize_denote
  | .mul a b => by
    simp only [normalize]
    split_ifs with h1 h2
    · -- a.normalize is zero
      simp only [denote]
      rw [← a.normalize_denote, a.normalize.denote_eq_zero h1, zero_mul]
    · -- b.normalize is zero
      simp only [denote]
      rw [← b.normalize_denote, b.normalize.denote_eq_zero h2, mul_zero]
    · exact congrArg₂ (· * ·) a.normalize_denote b.normalize_denote
  | .div a b => congrArg₂ (· / ·) a.normalize_denote b.normalize_denote
  | .neg a => congrArg (- ·) a.normalize_denote
  | .sub a b => congrArg₂ (· - ·) a.normalize_denote b.normalize_denote
  | .rlog (.rexp inner) => by
    simp only [normalize, denote, Real.log_exp]; exact inner.normalize_denote
  | .rlog (.nat n) => congrArg Real.log (normalize_denote (.nat n))
  | .rlog (.ratCast q) => congrArg Real.log (normalize_denote (.ratCast q))
  | .rlog (.add a b) => congrArg Real.log (normalize_denote (.add a b))
  | .rlog (.mul a b) => congrArg Real.log (normalize_denote (.mul a b))
  | .rlog (.div a b) => congrArg Real.log (normalize_denote (.div a b))
  | .rlog (.neg a) => congrArg Real.log (normalize_denote (.neg a))
  | .rlog (.sub a b) => congrArg Real.log (normalize_denote (.sub a b))
  | .rlog (.rlog a) => congrArg Real.log (normalize_denote (.rlog a))
  | .rlog (.rpow a n) => congrArg Real.log (normalize_denote (.rpow a n))
  | .rlog (.inv a) => congrArg Real.log (normalize_denote (.inv a))
  | .rlog (.iteZero a b c) => congrArg Real.log (normalize_denote (.iteZero a b c))
  | .rlog (.expMulLogSub a b c) => congrArg Real.log (normalize_denote (.expMulLogSub a b c))
  | .rlog (.rsqrt a) => congrArg Real.log (normalize_denote (.rsqrt a))
  | .rpow a 0 => congrArg (Real.rpow · 0) a.normalize_denote
  | .rpow a 1 => congrArg (Real.rpow · 1) a.normalize_denote
  | .rpow a (n + 2) => congrArg (Real.rpow · ↑(n + 2)) a.normalize_denote
  | .inv a => congrArg (·⁻¹) a.normalize_denote
  | .iteZero c t e => by
    simp only [normalize]
    split_ifs with h1 h2
    · -- c.normalize is zero → c.denote = 0 → then branch
      have hc : c.denote = 0 := by rw [← c.normalize_denote]; exact c.normalize.denote_eq_zero h1
      simp only [denote, hc, ↓reduceIte]
      exact t.normalize_denote
    · -- c.normalize is positive → c.denote ≠ 0 → else branch
      have hc : c.denote ≠ 0 := by
        rw [← c.normalize_denote]; exact c.normalize.denote_ne_zero h2
      simp only [denote, if_neg hc]
      exact e.normalize_denote
    · -- unknown → keep iteZero
      simp only [denote, c.normalize_denote, t.normalize_denote, e.normalize_denote]
  | .rsqrt a => congrArg Real.sqrt a.normalize_denote
  | .expMulLogSub α x cost =>
    congrArg Real.exp (congrArg₂ (· * ·) α.normalize_denote
      (congrArg₂ (· - ·) (congrArg Real.log x.normalize_denote) cost.normalize_denote))
  | .rexp (.rsqrt a) => congrArg Real.exp (normalize_denote (.rsqrt a))
  | .rexp (.mul α (.sub (.rsqrt x) cost)) => congrArg Real.exp (normalize_denote _)
  | .rexp (.mul a (.rsqrt b)) => congrArg Real.exp (normalize_denote (.mul a (.rsqrt b)))
  | .rexp (.mul α (.sub (.rlog x) cost)) =>
    congrArg Real.exp (congrArg₂ (· * ·) α.normalize_denote
      (congrArg₂ (· - ·) (congrArg Real.log x.normalize_denote) cost.normalize_denote))
  | .rexp (.nat n) => congrArg Real.exp (normalize_denote (.nat n))
  | .rexp (.ratCast q) => congrArg Real.exp (normalize_denote (.ratCast q))
  | .rexp (.add a b) => congrArg Real.exp (normalize_denote (.add a b))
  | .rexp (.mul a (.nat n)) => congrArg Real.exp (normalize_denote (.mul a (.nat n)))
  | .rexp (.mul a (.ratCast q)) => congrArg Real.exp (normalize_denote (.mul a (.ratCast q)))
  | .rexp (.mul a (.add b c)) => congrArg Real.exp (normalize_denote (.mul a (.add b c)))
  | .rexp (.mul a (.mul b c)) => congrArg Real.exp (normalize_denote (.mul a (.mul b c)))
  | .rexp (.mul a (.div b c)) => congrArg Real.exp (normalize_denote (.mul a (.div b c)))
  | .rexp (.mul a (.neg b)) => congrArg Real.exp (normalize_denote (.mul a (.neg b)))
  | .rexp (.mul a (.sub (.nat _) c)) => congrArg Real.exp (normalize_denote _)
  | .rexp (.mul a (.sub (.ratCast _) c)) => congrArg Real.exp (normalize_denote _)
  | .rexp (.mul a (.sub (.add _ _) c)) => congrArg Real.exp (normalize_denote _)
  | .rexp (.mul a (.sub (.mul _ _) c)) => congrArg Real.exp (normalize_denote _)
  | .rexp (.mul a (.sub (.div _ _) c)) => congrArg Real.exp (normalize_denote _)
  | .rexp (.mul a (.sub (.neg _) c)) => congrArg Real.exp (normalize_denote _)
  | .rexp (.mul a (.sub (.sub _ _) c)) => congrArg Real.exp (normalize_denote _)
  | .rexp (.mul a (.sub (.rexp _) c)) => congrArg Real.exp (normalize_denote _)
  | .rexp (.mul a (.sub (.rpow _ _) c)) => congrArg Real.exp (normalize_denote _)
  | .rexp (.mul a (.sub (.inv _) c)) => congrArg Real.exp (normalize_denote _)
  | .rexp (.mul a (.sub (.iteZero _ _ _) c)) => congrArg Real.exp (normalize_denote _)
  | .rexp (.mul a (.sub (.expMulLogSub _ _ _) c)) => congrArg Real.exp (normalize_denote _)
  | .rexp (.mul a (.rexp b)) => congrArg Real.exp (normalize_denote (.mul a (.rexp b)))
  | .rexp (.mul a (.rlog b)) => congrArg Real.exp (normalize_denote (.mul a (.rlog b)))
  | .rexp (.mul a (.rpow b n)) => congrArg Real.exp (normalize_denote (.mul a (.rpow b n)))
  | .rexp (.mul a (.inv b)) => congrArg Real.exp (normalize_denote (.mul a (.inv b)))
  | .rexp (.mul a (.iteZero b c d)) => congrArg Real.exp (normalize_denote (.mul a (.iteZero b c d)))
  | .rexp (.mul a (.expMulLogSub b c d)) => congrArg Real.exp (normalize_denote (.mul a (.expMulLogSub b c d)))
  | .rexp (.div a b) => congrArg Real.exp (normalize_denote (.div a b))
  | .rexp (.neg a) => congrArg Real.exp (normalize_denote (.neg a))
  | .rexp (.sub a b) => congrArg Real.exp (normalize_denote (.sub a b))
  | .rexp (.rexp a) => congrArg Real.exp (normalize_denote (.rexp a))
  | .rexp (.rlog a) => congrArg Real.exp (normalize_denote (.rlog a))
  | .rexp (.rpow a n) => congrArg Real.exp (normalize_denote (.rpow a n))
  | .rexp (.inv a) => congrArg Real.exp (normalize_denote (.inv a))
  | .rexp (.iteZero a b c) => congrArg Real.exp (normalize_denote (.iteZero a b c))
  | .rexp (.expMulLogSub a b c) => congrArg Real.exp (normalize_denote (.expMulLogSub a b c))

/-- If two RExprs normalize to the same tree, their denotations are equal,
    so neither is greater than the other. -/
theorem RExpr.not_gt_of_normalize_eq (lhs rhs : RExpr)
    (h : lhs.normalize = rhs.normalize) : ¬(lhs.denote > rhs.denote) := by
  have h1 : lhs.denote = rhs.denote := by
    rw [← normalize_denote lhs, ← normalize_denote rhs, h]
  rw [h1]; exact lt_irrefl _

/-- Tree-based comparison using `evalBothOpt`.
    Used by `rsa_predict` for sorry-free soundness proofs. -/
def RExpr.checkGtOpt (lhs rhs : RExpr) : Bool :=
  let (l_iv, l_valid) := lhs.normalize.evalBothOpt
  let (r_iv, r_valid) := rhs.normalize.evalBothOpt
  l_valid && r_valid && decide (r_iv.hi < l_iv.lo)

/-- Tree-based comparison for ¬(>). -/
def RExpr.checkNotGtOpt (lhs rhs : RExpr) : Bool :=
  let (l_iv, l_valid) := lhs.normalize.evalBothOpt
  let (r_iv, r_valid) := rhs.normalize.evalBothOpt
  l_valid && r_valid && decide (l_iv.hi ≤ r_iv.lo)

/-- If `checkGtOpt` succeeds, the denotations are ordered. -/
theorem RExpr.gt_of_checkGtOpt (lhs rhs : RExpr)
    (h : lhs.checkGtOpt rhs = true) : lhs.denote > rhs.denote := by
  simp only [checkGtOpt, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [← lhs.normalize_denote, ← rhs.normalize_denote]
  exact QInterval.gt_of_separated (evalBothOpt_sound _ h.1.1) (evalBothOpt_sound _ h.1.2) h.2

/-- If `checkNotGtOpt` succeeds, ¬(lhs > rhs). -/
theorem RExpr.not_gt_of_checkNotGtOpt (lhs rhs : RExpr)
    (h : lhs.checkNotGtOpt rhs = true) : ¬(lhs.denote > rhs.denote) := by
  simp only [checkNotGtOpt, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [← lhs.normalize_denote, ← rhs.normalize_denote]
  exact not_lt.mpr (QInterval.le_of_separated (evalBothOpt_sound _ h.1.1) (evalBothOpt_sound _ h.1.2) h.2)

-- ============================================================================
-- Memoized evaluation (for large trees with shared sub-expressions)
-- ============================================================================

/-- Memoized `evalBothOpt` using pointer-based identity for O(unique-node)
    evaluation of trees with structural sharing. Falls through to
    `evalRexpOpt` for `.rexp` nodes (which internally uses `evalBoth`
    on small sub-expressions — no memoization needed there). -/
private unsafe def RExpr.evalBothOptCached (e : @& RExpr)
    (cache : IO.Ref (Std.HashMap USize (QInterval × Bool))) : BaseIO (QInterval × Bool) := do
  let addr := ptrAddrUnsafe e
  if let some cached := (← cache.get)[addr]? then return cached
  let result ← match e with
    | .nat n => pure (QInterval.exact n, true)
    | .ratCast q => pure (QInterval.exact q, true)
    | .add a b => do
      let (ra, va) ← a.evalBothOptCached cache
      let (rb, vb) ← b.evalBothOptCached cache
      pure (c (ra.add rb), va && vb)
    | .mul a b => do
      let (ra, va) ← a.evalBothOptCached cache
      if ra.lo == 0 && ra.hi == 0 then pure (QInterval.exact 0, va)
      else do
        let (rb, vb) ← b.evalBothOptCached cache
        let v := va && vb
        if rb.lo == 0 && rb.hi == 0 then pure (QInterval.exact 0, v)
        else if h₁ : 0 ≤ ra.lo then
          if h₂ : 0 ≤ rb.lo then pure (c (ra.mulNonneg rb h₁ h₂), v)
          else pure (c (ra.mul rb), v)
        else pure (c (ra.mul rb), v)
    | .div a b => do
      let (ra, va) ← a.evalBothOptCached cache
      let (rb, vb) ← b.evalBothOptCached cache
      if ra.lo == 0 && ra.hi == 0 then pure (QInterval.exact 0, va && vb)
      else if h₁ : 0 ≤ ra.lo then
        if h₂ : 0 < rb.lo then pure (c (ra.divPos rb h₁ h₂), va && vb)
        else pure (⟨-1, 1, by norm_num⟩, false)
      else pure (⟨-1, 1, by norm_num⟩, false)
    | .neg a => do
      let (ra, va) ← a.evalBothOptCached cache
      pure (ra.neg, va)
    | .sub a b => do
      let (ra, va) ← a.evalBothOptCached cache
      let (rb, vb) ← b.evalBothOptCached cache
      pure (c (ra.sub rb), va && vb)
    | .rsqrt a => do
      let (ra, va) ← a.evalBothOptCached cache
      if h : 0 < ra.lo then pure (c (sqrtInterval ra h), va)
      else if ra.lo == 0 && ra.hi == 0 then pure (QInterval.exact 0, va)
      else pure (⟨0, 1, by norm_num⟩, false)
    | .rexp a => pure a.evalRexpOpt  -- delegate to factor optimization
    | .rlog a => do
      let (ra, va) ← a.evalBothOptCached cache
      if h : 0 < ra.lo then pure (c (logInterval ra h), va)
      else if ra.lo == 0 && ra.hi == 0 then pure (QInterval.exact 0, va)
      else pure (⟨-1000, 1000, by norm_num⟩, false)
    | .rpow a n => do
      let (ra, va) ← a.evalBothOptCached cache
      if n == 0 then pure (Interval.rpowZero, va)
      else if h : 0 ≤ ra.lo then pure (c (Interval.rpowNat ra n h), va)
      else pure (⟨0, 1, by norm_num⟩, false)
    | .inv a => do
      let (ra, va) ← a.evalBothOptCached cache
      if h : 0 < ra.lo then pure (c (ra.invPos h), va)
      else pure (⟨-1, 1, by norm_num⟩, false)
    | .iteZero c' t e => do
      let (rc, vc) ← c'.evalBothOptCached cache
      if rc.lo == 0 && rc.hi == 0 then do
        let (rt, vt) ← t.evalBothOptCached cache
        pure (rt, vc && vt)
      else if h : (0 : ℚ) < rc.lo then do
        let (re, ve) ← e.evalBothOptCached cache
        pure (re, vc && ve)
      else do
        let (rt, vt) ← t.evalBothOptCached cache
        let (re, ve) ← e.evalBothOptCached cache
        pure (⟨min rt.lo re.lo, max rt.hi re.hi,
         le_trans (min_le_left _ _) (le_trans rt.valid (le_max_left _ _))⟩,
         vc && vt && ve)
    | .expMulLogSub α x cost => do
      let (rα, vα) ← α.evalBothOptCached cache
      let (rx, vx) ← x.evalBothOptCached cache
      let (rc, vc) ← cost.evalBothOptCached cache
      let vbase := vα && vx && vc
      if hx : 0 < rx.lo then
        if rα.lo == rα.hi && rα.lo.den == 1 && decide (0 ≤ rα.lo.num) then
          let n := rα.lo.num.toNat
          let xpow :=
            if n == 0 then QInterval.exact 1
            else if n == 1 then rx
            else Interval.rpowNat rx n (le_of_lt hx)
          let negαc := (rα.mul rc).neg
          let expFactor := c (expInterval negαc)
          if h₁ : 0 ≤ xpow.lo then
            if h₂ : 0 ≤ expFactor.lo then pure (c (xpow.mulNonneg expFactor h₁ h₂), vbase)
            else pure (c (xpow.mul expFactor), vbase)
          else pure (c (xpow.mul expFactor), vbase)
        else
          let logx := c (logInterval rx hx)
          let diff := c (logx.sub rc)
          let prod := c (rα.mul diff)
          pure (c (expInterval prod), vbase)
      else pure (⟨0, 1, by norm_num⟩, false)
  cache.modify (·.insert addr result)
  return result

-- Note: the cached implementations do NOT call .normalize because normalize
-- allocates a fresh tree, destroying pointer sharing that evalBothOptCached
-- relies on for O(unique-node) memoization via ptrAddrUnsafe. The reference
-- implementations (checkGtOpt/checkNotGtOpt) normalize for kernel soundness;
-- the cached versions are strictly more conservative (may miss some true results
-- but never return a wrong true).
private unsafe def RExpr.checkGtOptCachedImpl (lhs rhs : RExpr) : Bool :=
  unsafeBaseIO do
    let cache ← IO.mkRef (∅ : Std.HashMap USize (QInterval × Bool))
    let (l_iv, l_valid) ← lhs.evalBothOptCached cache
    let (r_iv, r_valid) ← rhs.evalBothOptCached cache
    return (l_valid && r_valid && decide (r_iv.hi < l_iv.lo))

private unsafe def RExpr.checkNotGtOptCachedImpl (lhs rhs : RExpr) : Bool :=
  unsafeBaseIO do
    let cache ← IO.mkRef (∅ : Std.HashMap USize (QInterval × Bool))
    let (l_iv, l_valid) ← lhs.evalBothOptCached cache
    let (r_iv, r_valid) ← rhs.evalBothOptCached cache
    return (l_valid && r_valid && decide (l_iv.hi ≤ r_iv.lo))

/-- Memoized gt check. The `@[implemented_by]` annotation makes `native_decide`
    use the fast memoized implementation while the reference implementation
    (identical to `checkGtOpt`) is used for kernel verification. -/
@[implemented_by RExpr.checkGtOptCachedImpl]
def RExpr.checkGtOptMemo (lhs rhs : RExpr) : Bool :=
  lhs.checkGtOpt rhs

@[implemented_by RExpr.checkNotGtOptCachedImpl]
def RExpr.checkNotGtOptMemo (lhs rhs : RExpr) : Bool :=
  lhs.checkNotGtOpt rhs

theorem RExpr.gt_of_checkGtOptMemo (lhs rhs : RExpr)
    (h : lhs.checkGtOptMemo rhs = true) : lhs.denote > rhs.denote :=
  gt_of_checkGtOpt lhs rhs h

theorem RExpr.not_gt_of_checkNotGtOptMemo (lhs rhs : RExpr)
    (h : lhs.checkNotGtOptMemo rhs = true) : ¬(lhs.denote > rhs.denote) :=
  not_gt_of_checkNotGtOpt lhs rhs h

-- ============================================================================
-- Exact exp evaluation via log factor grouping
-- ============================================================================

/-- Evaluate a simple rational expression (no exp/log/expMulLogSub).
    Used by log factor collection to evaluate coefficients and bases,
    avoiding mutual recursion with `evalExact`. -/
private def RExpr.asRat : RExpr → Option ℚ
  | .nat n => some n
  | .ratCast q => some q
  | .add a b => do return (← a.asRat) + (← b.asRat)
  | .mul a b => do return (← a.asRat) * (← b.asRat)
  | .div a b => do let vb ← b.asRat; guard (vb ≠ 0); return (← a.asRat) / vb
  | .sub a b => do return (← a.asRat) - (← b.asRat)
  | .neg a => do return -(← a.asRat)
  | .inv a => do let va ← a.asRat; guard (va ≠ 0); return 1 / va
  | .rpow a n => do let va ← a.asRat; guard (0 ≤ va); return va ^ n
  | .iteZero c t e => do let vc ← c.asRat; if vc = 0 then t.asRat else e.asRat
  | .rexp _ | .rlog _ | .rsqrt _ | .expMulLogSub _ _ _ => none

set_option maxHeartbeats 400000 in
private theorem RExpr.asRat_sound (e : RExpr) (q : ℚ)
    (h : e.asRat = some q) : e.denote = (q : ℝ) := by
  induction e generalizing q with
  | nat n =>
    simp [asRat] at h
    cases n with
    | zero => unfold denote; simp [← h]
    | succ m => cases m with
      | zero => unfold denote; simp [← h]
      | succ k => unfold denote; rw [← h]; push_cast; rfl
  | ratCast q' => simp [asRat] at h; subst h; rfl
  | add a b iha ihb =>
    cases ha : a.asRat with
    | none => simp [asRat, ha] at h
    | some va =>
      cases hb : b.asRat with
      | none => simp [asRat, ha, hb] at h
      | some vb =>
        have hq : q = va + vb := by simp [asRat, ha, hb] at h; exact h.symm
        subst hq; unfold denote; rw [iha va ha, ihb vb hb]; push_cast; ring
  | mul a b iha ihb =>
    cases ha : a.asRat with
    | none => simp [asRat, ha] at h
    | some va =>
      cases hb : b.asRat with
      | none => simp [asRat, ha, hb] at h
      | some vb =>
        have hq : q = va * vb := by simp [asRat, ha, hb] at h; exact h.symm
        subst hq; unfold denote; rw [iha va ha, ihb vb hb]; push_cast; ring
  | div a b iha ihb =>
    cases hb : b.asRat with
    | none => simp [asRat, hb] at h
    | some vb =>
      by_cases hvb : vb = 0
      · simp [asRat, hb, hvb] at h
      · cases ha : a.asRat with
        | none => simp [asRat, ha, hb] at h
        | some va =>
          have hq : q = va / vb := by simp [asRat, ha, hb, hvb] at h; exact h.symm
          subst hq; unfold denote; rw [iha va ha, ihb vb hb]; push_cast; ring
  | neg a iha =>
    cases ha : a.asRat with
    | none => simp [asRat, ha] at h
    | some va =>
      have hq : q = -va := by simp [asRat, ha] at h; exact h.symm
      subst hq; unfold denote; rw [iha va ha]; push_cast; ring
  | sub a b iha ihb =>
    cases ha : a.asRat with
    | none => simp [asRat, ha] at h
    | some va =>
      cases hb : b.asRat with
      | none => simp [asRat, ha, hb] at h
      | some vb =>
        have hq : q = va - vb := by simp [asRat, ha, hb] at h; exact h.symm
        subst hq; unfold denote; rw [iha va ha, ihb vb hb]; push_cast; ring
  | inv a iha =>
    cases ha : a.asRat with
    | none => simp [asRat, ha] at h
    | some va =>
      by_cases hva : va = 0
      · simp [asRat, ha, hva] at h
      · have hq : q = va⁻¹ := by simp [asRat, ha, hva] at h; exact h.symm
        subst hq; unfold denote; rw [iha va ha]; push_cast; rfl
  | rpow a n iha =>
    cases ha : a.asRat with
    | none => simp [asRat, ha] at h
    | some va =>
      by_cases hva : 0 ≤ va
      · have hq : q = va ^ n := by simp [asRat, ha, hva] at h; exact h.symm
        subst hq; rw [rpow_denote_eq, iha va ha, Real.rpow_natCast]; push_cast; ring
      · simp [asRat, ha, hva] at h
  | iteZero c t e ihc iht ihe =>
    cases hc : c.asRat with
    | none => simp [asRat, hc] at h
    | some vc =>
      unfold denote
      by_cases hvc : vc = 0
      · have hcd : c.denote = 0 := by rw [ihc vc hc, hvc]; simp
        simp [hcd]
        exact iht q (by simp [asRat, hc, hvc] at h; exact h)
      · have hcd : c.denote ≠ 0 := by rw [ihc vc hc]; exact_mod_cast hvc
        simp [hcd]
        exact ihe q (by simp [asRat, hc, hvc] at h; exact h)
  | rexp _ | rlog _ | rsqrt _ | expMulLogSub _ _ _ => simp [asRat] at h

/-- Weighted log sum interpretation: Σ cᵢ · log(xvᵢ). -/
private noncomputable def logFactorSum (fs : List (ℚ × ℚ)) : ℝ :=
  (fs.map fun p => (↑p.2 : ℝ) * Real.log (↑p.1 : ℝ)).sum

/-- Insert-or-merge into grouped factor list: if `base` already exists as a key,
    add `coeff` to the existing coefficient; otherwise append a new entry. -/
private def addLogFactor : List (ℚ × ℚ) → ℚ → ℚ → List (ℚ × ℚ)
  | [], base, coeff => [(base, coeff)]
  | (k, v) :: rest, base, coeff =>
    if k == base then (k, v + coeff) :: rest
    else (k, v) :: addLogFactor rest base coeff

private theorem addLogFactor_sound (acc : List (ℚ × ℚ)) (base coeff : ℚ) :
    logFactorSum (addLogFactor acc base coeff) =
    logFactorSum acc + (↑coeff : ℝ) * Real.log (↑base : ℝ) := by
  induction acc with
  | nil => simp [addLogFactor, logFactorSum]
  | cons hd tl ih =>
    obtain ⟨k, v⟩ := hd
    simp only [addLogFactor]
    split
    · rename_i heq
      simp only [beq_iff_eq] at heq; subst heq
      simp only [logFactorSum, List.map_cons, List.sum_cons]
      push_cast; ring
    · simp only [logFactorSum, List.map_cons, List.sum_cons] at ih ⊢
      linarith

private theorem foldl_addLogFactor_sound (acc extras : List (ℚ × ℚ)) :
    logFactorSum (extras.foldl (fun a p => addLogFactor a p.1 p.2) acc) =
    logFactorSum acc + logFactorSum extras := by
  induction extras generalizing acc with
  | nil => simp [logFactorSum]
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [ih, addLogFactor_sound]
    simp only [logFactorSum, List.map_cons, List.sum_cons]
    ring

private theorem logFactorSum_map_scale (c : ℚ) (fs : List (ℚ × ℚ)) :
    logFactorSum (fs.map (fun p => (p.1, c * p.2))) =
    (↑c : ℝ) * logFactorSum fs := by
  induction fs with
  | nil => simp [logFactorSum]
  | cons hd tl ih =>
    simp only [logFactorSum, List.map_cons, List.map, List.sum_cons] at ih ⊢
    rw [ih]; push_cast; ring

/-- Collect (base_value, coefficient) pairs from a sum-of-weighted-logs
    expression, grouping by exact base value during collection. -/
private def collectAndGroupLogFactors : RExpr → Option (List (ℚ × ℚ))
  | .add a b => do
    let la ← collectAndGroupLogFactors a
    let lb ← collectAndGroupLogFactors b
    return lb.foldl (fun acc p => addLogFactor acc p.1 p.2) la
  | .mul coeff (.rlog x) => do return [(← x.asRat, ← coeff.asRat)]
  | .mul coeff body => do
    let c ← coeff.asRat
    let factors ← collectAndGroupLogFactors body
    return factors.map (fun p => (p.1, c * p.2))
  | .rlog x => do return [(← x.asRat, 1)]
  | other => do guard ((← other.asRat) == 0); return []

private theorem logFactorSum_cons (xv c : ℚ) (rest : List (ℚ × ℚ)) :
    logFactorSum ((xv, c) :: rest) =
    (↑c : ℝ) * Real.log (↑xv : ℝ) + logFactorSum rest := by
  simp [logFactorSum]

private theorem collectLogFactors_asRat_zero {e : RExpr} {fs : List (ℚ × ℚ)}
    (h : (do let v ← e.asRat; guard ((v == 0) = true);
             pure ([] : List (ℚ × ℚ))) = some fs) :
    e.denote = logFactorSum fs := by
  cases hasRat : e.asRat with
  | none => simp [hasRat] at h
  | some v =>
    simp only [hasRat] at h
    by_cases hv0 : v = 0
    · subst hv0; simp at h; subst h
      rw [RExpr.asRat_sound _ _ hasRat]
      simp [logFactorSum]
    · exfalso; revert h; simp [hv0, beq_iff_eq, guard]

private theorem collectLogFactors_mul_body {a b : RExpr} {fs : List (ℚ × ℚ)}
    (h : (do let c ← a.asRat
             let factors ← collectAndGroupLogFactors b
             return factors.map (fun p => (p.1, c * p.2))) = some fs)
    (ihb : ∀ fs, collectAndGroupLogFactors b = some fs → b.denote = logFactorSum fs) :
    (RExpr.mul a b).denote = logFactorSum fs := by
  cases hc : a.asRat with
  | none => simp [hc] at h
  | some c =>
    cases hfact : collectAndGroupLogFactors b with
    | none => simp [hc, hfact] at h
    | some factors =>
      simp [hc, hfact] at h; subst h
      simp only [RExpr.denote]
      rw [RExpr.asRat_sound _ _ hc, ihb factors hfact, logFactorSum_map_scale]

set_option maxHeartbeats 800000 in
private def collectAndGroupLogFactors_sound :
    ∀ (e : RExpr) (fs : List (ℚ × ℚ)),
    collectAndGroupLogFactors e = some fs →
    e.denote = logFactorSum fs
  | .add a b, fs, h => by
    simp only [collectAndGroupLogFactors] at h
    cases hla : collectAndGroupLogFactors a with
    | none => simp [hla] at h
    | some la =>
      cases hlb : collectAndGroupLogFactors b with
      | none => simp [hla, hlb] at h
      | some lb =>
        simp [hla, hlb] at h; subst h
        simp only [RExpr.denote]
        rw [collectAndGroupLogFactors_sound a la hla,
            collectAndGroupLogFactors_sound b lb hlb,
            foldl_addLogFactor_sound]
  | .mul a b, fs, h => by
    cases b with
    | rlog x =>
      simp only [collectAndGroupLogFactors] at h
      cases hxv : x.asRat with
      | none => simp [hxv] at h
      | some xv =>
        cases hcv : a.asRat with
        | none => simp [hxv, hcv] at h
        | some cv =>
          simp [hxv, hcv] at h; subst h
          simp only [RExpr.denote]
          rw [RExpr.asRat_sound _ _ hcv, RExpr.asRat_sound _ _ hxv]
          simp [logFactorSum]
    | _ =>
      exact collectLogFactors_mul_body h
        (fun fs h => collectAndGroupLogFactors_sound _ fs h)
  | .rlog x, fs, h => by
    simp only [collectAndGroupLogFactors] at h
    cases hxv : x.asRat with
    | none => simp [hxv] at h
    | some xv =>
      simp [hxv] at h; subst h
      simp only [RExpr.denote]
      rw [RExpr.asRat_sound _ _ hxv]
      simp [logFactorSum]
  | .nat _, fs, h | .ratCast _, fs, h | .div _ _, fs, h | .neg _, fs, h
  | .sub _ _, fs, h | .rexp _, fs, h | .rsqrt _, fs, h | .rpow _ _, fs, h | .inv _, fs, h
  | .iteZero _ _ _, fs, h | .expMulLogSub _ _ _, fs, h => by
    simp only [collectAndGroupLogFactors] at h
    exact collectLogFactors_asRat_zero h

/-- Compute ∏ᵢ xvᵢ^nᵢ from grouped factor list, where each coefficient
    must be a non-negative integer and each base must be positive. -/
private def evalGroupedProduct : List (ℚ × ℚ) → Option ℚ
  | [] => some 1
  | (xv, c) :: rest =>
    if c == 0 then evalGroupedProduct rest
    else if c.den == 1 && decide (0 ≤ c.num) && decide ((0 : ℚ) < xv) then do
      return xv ^ c.num.toNat * (← evalGroupedProduct rest)
    else none

private theorem rat_den_one_cast (c : ℚ) (hden : c.den = 1) (hnum : 0 ≤ c.num) :
    (↑c : ℝ) = ↑(c.num.toNat : ℕ) := by
  have h1 := (Rat.num_div_den c).symm
  have : (↑c : ℝ) = (↑c.num : ℝ) / (↑(c.den : ℕ) : ℝ) := by exact_mod_cast h1
  rw [this, hden, Nat.cast_one, div_one]
  exact_mod_cast (Int.toNat_of_nonneg hnum).symm

set_option maxHeartbeats 800000 in
private theorem evalGroupedProduct_sound (gs : List (ℚ × ℚ)) (q : ℚ)
    (h : evalGroupedProduct gs = some q) :
    Real.exp (logFactorSum gs) = (↑q : ℝ) := by
  induction gs generalizing q with
  | nil =>
    simp [evalGroupedProduct] at h; subst h
    simp [logFactorSum, Real.exp_zero]
  | cons p rest ih =>
    obtain ⟨xv, c⟩ := p
    simp only [evalGroupedProduct] at h
    split_ifs at h with hc hcond
    · -- c == 0
      simp only [beq_iff_eq] at hc
      have : logFactorSum ((xv, c) :: rest) = logFactorSum rest := by
        rw [logFactorSum_cons, hc, Rat.cast_zero, zero_mul, zero_add]
      rw [this]; exact ih q h
    · -- natural coeff with positive base
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
      obtain ⟨⟨hden, hnum⟩, hxv_pos⟩ := hcond
      cases hrest : evalGroupedProduct rest with
      | none => simp [hrest] at h
      | some restQ =>
        simp [hrest] at h; subst h
        rw [logFactorSum_cons, Real.exp_add, ih restQ hrest]
        -- Show: exp(c * log(xv)) = xv ^ c.num.toNat
        have hxv_pos_real : (0 : ℝ) < (↑xv : ℝ) := by exact_mod_cast hxv_pos
        rw [rat_den_one_cast c hden hnum, Real.exp_nat_mul,
            Real.exp_log hxv_pos_real]
        push_cast; ring

/-- Evaluate exp(body) exactly when body decomposes as a sum of coeff * log(base)
    terms where grouped coefficients are non-negative integers and bases are
    positive rationals. Returns the exact ℚ value of exp(body). -/
private def evalExpExact (body : RExpr) : Option ℚ := do
  let factors ← collectAndGroupLogFactors body
  evalGroupedProduct factors

private theorem evalExpExact_sound (body : RExpr) (q : ℚ)
    (h : evalExpExact body = some q) :
    Real.exp body.denote = (↑q : ℝ) := by
  simp only [evalExpExact] at h
  cases hf : collectAndGroupLogFactors body with
  | none => simp [hf] at h
  | some factors =>
    simp [hf] at h
    rw [collectAndGroupLogFactors_sound body factors hf]
    exact evalGroupedProduct_sound factors q h

-- ============================================================================
-- Exact ℚ evaluation (for ¬(>) goals where intervals overlap)
-- ============================================================================

/-- Evaluate an RExpr to an exact ℚ value, if possible.
    Handles exp nodes via log factor grouping (e.g., exp(1/2·log(x) + 1/2·log(x))
    groups to exp(1·log(x)) = x). Returns `none` for log, expMulLogSub, or when
    log factor coefficients don't sum to natural numbers.
    Used for `¬(>)` goals where interval arithmetic is too imprecise. -/
def RExpr.evalExact : RExpr → Option ℚ
  | .nat n => some n
  | .ratCast q => some q
  | .add a b => do return (← a.evalExact) + (← b.evalExact)
  | .mul a b => do return (← a.evalExact) * (← b.evalExact)
  | .div a b => do
    let vb ← b.evalExact
    guard (vb ≠ 0)
    return (← a.evalExact) / vb
  | .sub a b => do return (← a.evalExact) - (← b.evalExact)
  | .neg a => do return -(← a.evalExact)
  | .inv a => do
    let va ← a.evalExact
    guard (va ≠ 0)
    return 1 / va
  | .rpow a n => do
    let va ← a.evalExact
    guard (0 ≤ va)
    return va ^ n
  | .iteZero c t e => do
    let vc ← c.evalExact
    if vc = 0 then t.evalExact else e.evalExact
  | .rexp body => evalExpExact body
  | .rlog _ => none
  | .rsqrt _ => none
  | .expMulLogSub _ _ _ => none

set_option maxHeartbeats 400000 in
/-- Soundness: if evalExact returns q, then denote = (q : ℝ). -/
theorem RExpr.evalExact_sound (e : RExpr) (q : ℚ)
    (h : e.evalExact = some q) : e.denote = (q : ℝ) := by
  induction e generalizing q with
  | nat n =>
    simp [evalExact] at h
    cases n with
    | zero => unfold denote; simp [← h]
    | succ m => cases m with
      | zero => unfold denote; simp [← h]
      | succ k => unfold denote; rw [← h]; push_cast; rfl
  | ratCast q' => simp [evalExact] at h; subst h; rfl
  | add a b iha ihb =>
    cases ha : a.evalExact with
    | none => simp [evalExact, ha] at h
    | some va =>
      cases hb : b.evalExact with
      | none => simp [evalExact, ha, hb] at h
      | some vb =>
        have hq : q = va + vb := by simp [evalExact, ha, hb] at h; exact h.symm
        subst hq; unfold denote; rw [iha va ha, ihb vb hb]; push_cast; ring
  | mul a b iha ihb =>
    cases ha : a.evalExact with
    | none => simp [evalExact, ha] at h
    | some va =>
      cases hb : b.evalExact with
      | none => simp [evalExact, ha, hb] at h
      | some vb =>
        have hq : q = va * vb := by simp [evalExact, ha, hb] at h; exact h.symm
        subst hq; unfold denote; rw [iha va ha, ihb vb hb]; push_cast; ring
  | div a b iha ihb =>
    cases hb : b.evalExact with
    | none => simp [evalExact, hb] at h
    | some vb =>
      by_cases hvb : vb = 0
      · simp [evalExact, hb, hvb] at h
      · cases ha : a.evalExact with
        | none => simp [evalExact, ha, hb] at h
        | some va =>
          have hq : q = va / vb := by simp [evalExact, ha, hb, hvb] at h; exact h.symm
          subst hq; unfold denote; rw [iha va ha, ihb vb hb]; push_cast; ring
  | neg a iha =>
    cases ha : a.evalExact with
    | none => simp [evalExact, ha] at h
    | some va =>
      have hq : q = -va := by simp [evalExact, ha] at h; exact h.symm
      subst hq; unfold denote; rw [iha va ha]; push_cast; ring
  | sub a b iha ihb =>
    cases ha : a.evalExact with
    | none => simp [evalExact, ha] at h
    | some va =>
      cases hb : b.evalExact with
      | none => simp [evalExact, ha, hb] at h
      | some vb =>
        have hq : q = va - vb := by simp [evalExact, ha, hb] at h; exact h.symm
        subst hq; unfold denote; rw [iha va ha, ihb vb hb]; push_cast; ring
  | inv a iha =>
    cases ha : a.evalExact with
    | none => simp [evalExact, ha] at h
    | some va =>
      by_cases hva : va = 0
      · simp [evalExact, ha, hva] at h
      · have hq : q = va⁻¹ := by simp [evalExact, ha, hva] at h; exact h.symm
        subst hq; unfold denote; rw [iha va ha]; push_cast; rfl
  | rpow a n iha =>
    cases ha : a.evalExact with
    | none => simp [evalExact, ha] at h
    | some va =>
      by_cases hva : 0 ≤ va
      · have hq : q = va ^ n := by simp [evalExact, ha, hva] at h; exact h.symm
        subst hq; rw [rpow_denote_eq, iha va ha, Real.rpow_natCast]; push_cast; ring
      · simp [evalExact, ha, hva] at h
  | iteZero c t e ihc iht ihe =>
    cases hc : c.evalExact with
    | none => simp [evalExact, hc] at h
    | some vc =>
      unfold denote
      by_cases hvc : vc = 0
      · have hcd : c.denote = 0 := by rw [ihc vc hc, hvc]; simp
        simp [hcd]
        exact iht q (by simp [evalExact, hc, hvc] at h; exact h)
      · have hcd : c.denote ≠ 0 := by rw [ihc vc hc]; exact_mod_cast hvc
        simp [hcd]
        exact ihe q (by simp [evalExact, hc, hvc] at h; exact h)
  | rexp body _ =>
    simp only [evalExact] at h
    unfold denote
    exact evalExpExact_sound body q h
  | rlog _ => simp [evalExact] at h
  | rsqrt _ => simp [evalExact] at h
  | expMulLogSub _ _ _ => simp [evalExact] at h

/-- If both sides have the same exact ℚ value, ¬(lhs > rhs). -/
def RExpr.checkExactNotGt (lhs rhs : RExpr) : Bool :=
  match lhs.evalExact, rhs.evalExact with
  | some q₁, some q₂ => decide (¬(q₁ > q₂))
  | _, _ => false

/-- Soundness of exact ¬(>) check. -/
theorem RExpr.not_gt_of_checkExactNotGt (lhs rhs : RExpr)
    (h : lhs.checkExactNotGt rhs = true) :
    ¬(lhs.denote > rhs.denote) := by
  unfold checkExactNotGt at h
  split at h
  · rename_i q₁ q₂ hq₁ hq₂
    simp only [decide_eq_true_eq] at h
    rw [evalExact_sound lhs q₁ hq₁, evalExact_sound rhs q₂ hq₂]
    exact_mod_cast h
  · exact absurd h (by simp)

/-- If lhs evaluates to a strictly greater ℚ than rhs, lhs.denote > rhs.denote. -/
def RExpr.checkExactGt (lhs rhs : RExpr) : Bool :=
  match lhs.evalExact, rhs.evalExact with
  | some q₁, some q₂ => decide (q₁ > q₂)
  | _, _ => false

/-- Soundness of exact (>) check. -/
theorem RExpr.gt_of_checkExactGt (lhs rhs : RExpr)
    (h : lhs.checkExactGt rhs = true) :
    lhs.denote > rhs.denote := by
  unfold checkExactGt at h
  split at h
  · rename_i q₁ q₂ hq₁ hq₂
    simp only [decide_eq_true_eq] at h
    rw [evalExact_sound lhs q₁ hq₁, evalExact_sound rhs q₂ hq₂]
    exact_mod_cast h
  · exact absurd h (by simp)

/-- Check exact equality: both sides evaluate to the same ℚ. -/
def RExpr.checkExactEq (lhs rhs : RExpr) : Bool :=
  match lhs.evalExact, rhs.evalExact with
  | some q₁, some q₂ => q₁ == q₂
  | _, _ => false

/-- Soundness of exact equality check. -/
theorem RExpr.eq_of_checkExactEq (lhs rhs : RExpr)
    (h : lhs.checkExactEq rhs = true) :
    lhs.denote = rhs.denote := by
  unfold checkExactEq at h
  split at h
  · rename_i q₁ q₂ hq₁ hq₂
    simp only [beq_iff_eq] at h
    rw [evalExact_sound lhs q₁ hq₁, evalExact_sound rhs q₂ hq₂, h]
  · exact absurd h (by simp)

/-- Semantic equality: walk two RExpr trees in parallel, using evalExact at each
    node when possible. Handles exp/log cases where evalExact returns none by
    checking structural match and recursing into children. This enables proving
    `exp(log(1/(0+1+1))) = exp(log(1/(1+0+1)))` — the exp/log match structurally,
    and the arithmetic children both evalExact to 1/2. -/
def RExpr.checkSemanticEq (a b : RExpr) : Bool :=
  -- Try exact evaluation at this node
  match a.evalExact, b.evalExact with
  | some q₁, some q₂ => q₁ == q₂
  | _, _ =>
    -- Structural match with recursive semantic check on children
    match a, b with
    | .nat n₁, .nat n₂ => n₁ == n₂
    | .add a₁ a₂, .add b₁ b₂ => a₁.checkSemanticEq b₁ && a₂.checkSemanticEq b₂
    | .mul a₁ a₂, .mul b₁ b₂ => a₁.checkSemanticEq b₁ && a₂.checkSemanticEq b₂
    | .div a₁ a₂, .div b₁ b₂ => a₁.checkSemanticEq b₁ && a₂.checkSemanticEq b₂
    | .sub a₁ a₂, .sub b₁ b₂ => a₁.checkSemanticEq b₁ && a₂.checkSemanticEq b₂
    | .neg a₁, .neg b₁ => a₁.checkSemanticEq b₁
    | .inv a₁, .inv b₁ => a₁.checkSemanticEq b₁
    | .rpow a₁ n₁, .rpow b₁ n₂ => a₁.checkSemanticEq b₁ && (n₁ == n₂)
    | .iteZero c₁ t₁ e₁, .iteZero c₂ t₂ e₂ =>
      c₁.checkSemanticEq c₂ && t₁.checkSemanticEq t₂ && e₁.checkSemanticEq e₂
    | .rexp a₁, .rexp b₁ => a₁.checkSemanticEq b₁
    | .rsqrt a₁, .rsqrt b₁ => a₁.checkSemanticEq b₁
    | .rlog a₁, .rlog b₁ => a₁.checkSemanticEq b₁
    | .expMulLogSub a₁ b₁ c₁, .expMulLogSub a₂ b₂ c₂ =>
      a₁.checkSemanticEq a₂ && b₁.checkSemanticEq b₂ && c₁.checkSemanticEq c₂
    | _, _ => false
termination_by sizeOf a

set_option maxHeartbeats 800000 in
/-- Soundness of semantic equality: if checkSemanticEq returns true,
    then the two expressions denote the same real number. -/
theorem RExpr.eq_of_checkSemanticEq (lhs rhs : RExpr)
    (h : lhs.checkSemanticEq rhs = true) :
    lhs.denote = rhs.denote := by
  induction lhs generalizing rhs with
  | nat n =>
    rw [RExpr.checkSemanticEq.eq_def] at h; split at h
    · rename_i q₁ q₂ hq₁ hq₂; simp only [beq_iff_eq] at h
      rw [RExpr.evalExact_sound _ q₁ hq₁, RExpr.evalExact_sound _ q₂ hq₂, h]
    · cases rhs with | nat n' => simp only [beq_iff_eq] at h; subst h; rfl | _ => simp at h
  | ratCast q =>
    rw [RExpr.checkSemanticEq.eq_def] at h; split at h
    · rename_i q₁ q₂ hq₁ hq₂; simp only [beq_iff_eq] at h
      rw [RExpr.evalExact_sound _ q₁ hq₁, RExpr.evalExact_sound _ q₂ hq₂, h]
    · cases rhs <;> simp at h
  | add a₁ a₂ ih₁ ih₂ =>
    rw [RExpr.checkSemanticEq.eq_def] at h; split at h
    · rename_i q₁ q₂ hq₁ hq₂; simp only [beq_iff_eq] at h
      rw [RExpr.evalExact_sound _ q₁ hq₁, RExpr.evalExact_sound _ q₂ hq₂, h]
    · cases rhs with
      | add b₁ b₂ =>
        simp only [Bool.and_eq_true] at h
        exact congrArg₂ (· + ·) (ih₁ _ h.1) (ih₂ _ h.2)
      | _ => simp at h
  | mul a₁ a₂ ih₁ ih₂ =>
    rw [RExpr.checkSemanticEq.eq_def] at h; split at h
    · rename_i q₁ q₂ hq₁ hq₂; simp only [beq_iff_eq] at h
      rw [RExpr.evalExact_sound _ q₁ hq₁, RExpr.evalExact_sound _ q₂ hq₂, h]
    · cases rhs with
      | mul b₁ b₂ =>
        simp only [Bool.and_eq_true] at h
        exact congrArg₂ (· * ·) (ih₁ _ h.1) (ih₂ _ h.2)
      | _ => simp at h
  | div a₁ a₂ ih₁ ih₂ =>
    rw [RExpr.checkSemanticEq.eq_def] at h; split at h
    · rename_i q₁ q₂ hq₁ hq₂; simp only [beq_iff_eq] at h
      rw [RExpr.evalExact_sound _ q₁ hq₁, RExpr.evalExact_sound _ q₂ hq₂, h]
    · cases rhs with
      | div b₁ b₂ =>
        simp only [Bool.and_eq_true] at h
        exact congrArg₂ (· / ·) (ih₁ _ h.1) (ih₂ _ h.2)
      | _ => simp at h
  | sub a₁ a₂ ih₁ ih₂ =>
    rw [RExpr.checkSemanticEq.eq_def] at h; split at h
    · rename_i q₁ q₂ hq₁ hq₂; simp only [beq_iff_eq] at h
      rw [RExpr.evalExact_sound _ q₁ hq₁, RExpr.evalExact_sound _ q₂ hq₂, h]
    · cases rhs with
      | sub b₁ b₂ =>
        simp only [Bool.and_eq_true] at h
        exact congrArg₂ (· - ·) (ih₁ _ h.1) (ih₂ _ h.2)
      | _ => simp at h
  | neg a₁ ih₁ =>
    rw [RExpr.checkSemanticEq.eq_def] at h; split at h
    · rename_i q₁ q₂ hq₁ hq₂; simp only [beq_iff_eq] at h
      rw [RExpr.evalExact_sound _ q₁ hq₁, RExpr.evalExact_sound _ q₂ hq₂, h]
    · cases rhs with
      | neg b₁ => exact congrArg (- ·) (ih₁ _ h)
      | _ => simp at h
  | inv a₁ ih₁ =>
    rw [RExpr.checkSemanticEq.eq_def] at h; split at h
    · rename_i q₁ q₂ hq₁ hq₂; simp only [beq_iff_eq] at h
      rw [RExpr.evalExact_sound _ q₁ hq₁, RExpr.evalExact_sound _ q₂ hq₂, h]
    · cases rhs with
      | inv b₁ =>
        show a₁.denote⁻¹ = b₁.denote⁻¹
        rw [ih₁ _ h]
      | _ => simp at h
  | rpow a₁ n ih₁ =>
    rw [RExpr.checkSemanticEq.eq_def] at h; split at h
    · rename_i q₁ q₂ hq₁ hq₂; simp only [beq_iff_eq] at h
      rw [RExpr.evalExact_sound _ q₁ hq₁, RExpr.evalExact_sound _ q₂ hq₂, h]
    · cases rhs with
      | rpow b₁ m =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨h1, h2⟩ := h; subst h2
        rw [rpow_denote_eq, rpow_denote_eq, ih₁ _ h1]
      | _ => simp at h
  | iteZero c t e ihc iht ihe =>
    rw [RExpr.checkSemanticEq.eq_def] at h; split at h
    · rename_i q₁ q₂ hq₁ hq₂; simp only [beq_iff_eq] at h
      rw [RExpr.evalExact_sound _ q₁ hq₁, RExpr.evalExact_sound _ q₂ hq₂, h]
    · cases rhs with
      | iteZero c' t' e' =>
        simp only [Bool.and_eq_true] at h
        unfold denote; rw [ihc _ h.1.1, iht _ h.1.2, ihe _ h.2]
      | _ => simp at h
  | rexp a₁ ih₁ =>
    rw [RExpr.checkSemanticEq.eq_def] at h; split at h
    · rename_i q₁ q₂ hq₁ hq₂; simp only [beq_iff_eq] at h
      rw [RExpr.evalExact_sound _ q₁ hq₁, RExpr.evalExact_sound _ q₂ hq₂, h]
    · cases rhs with
      | rexp b₁ => exact congrArg Real.exp (ih₁ _ h)
      | _ => simp at h
  | rsqrt a₁ ih₁ =>
    rw [RExpr.checkSemanticEq.eq_def] at h; split at h
    · rename_i q₁ q₂ hq₁ hq₂; simp only [beq_iff_eq] at h
      rw [RExpr.evalExact_sound _ q₁ hq₁, RExpr.evalExact_sound _ q₂ hq₂, h]
    · cases rhs with
      | rsqrt b₁ => exact congrArg Real.sqrt (ih₁ _ h)
      | _ => simp at h
  | rlog a₁ ih₁ =>
    rw [RExpr.checkSemanticEq.eq_def] at h; split at h
    · rename_i q₁ q₂ hq₁ hq₂; simp only [beq_iff_eq] at h
      rw [RExpr.evalExact_sound _ q₁ hq₁, RExpr.evalExact_sound _ q₂ hq₂, h]
    · cases rhs with
      | rlog b₁ => exact congrArg Real.log (ih₁ _ h)
      | _ => simp at h
  | expMulLogSub α x c ihα ihx ihc =>
    rw [RExpr.checkSemanticEq.eq_def] at h; split at h
    · rename_i q₁ q₂ hq₁ hq₂; simp only [beq_iff_eq] at h
      rw [RExpr.evalExact_sound _ q₁ hq₁, RExpr.evalExact_sound _ q₂ hq₂, h]
    · cases rhs with
      | expMulLogSub α' x' c' =>
        simp only [Bool.and_eq_true] at h
        unfold denote; rw [ihα _ h.1.1, ihx _ h.1.2, ihc _ h.2]
      | _ => simp at h

/-- If semantically equal, neither side is strictly greater. -/
theorem RExpr.not_gt_of_checkSemanticEq (lhs rhs : RExpr)
    (h : lhs.checkSemanticEq rhs = true) :
    ¬(lhs.denote > rhs.denote) := by
  have heq := eq_of_checkSemanticEq lhs rhs h
  rw [heq]; exact lt_irrefl _

/-- When lhs and rhs denote the same value, lhs > rhs is impossible. -/
theorem RExpr.not_gt_of_denote_eq (lhs rhs : RExpr)
    (h : lhs.denote = rhs.denote) : ¬(lhs.denote > rhs.denote) :=
  h ▸ lt_irrefl _

end Interval
