import Linglib.Core.Interval.QInterval
import Linglib.Core.Interval.PadeExp
import Linglib.Core.Interval.LogInterval
import Linglib.Core.Interval.RpowInterval

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

namespace Linglib.Interval

open Linglib.Interval.QInterval

-- ============================================================================
-- RExpr: Reified Arithmetic Expressions
-- ============================================================================

/-- Reified arithmetic expression over ℝ.

Each constructor corresponds to an operation the `rsa_decide` tactic can reify.
The `denote` function maps back to ℝ; the `eval` function computes a `QInterval`
bounding the value. -/
inductive RExpr where
  | nat : ℕ → RExpr
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
  deriving Repr, Inhabited

-- ============================================================================
-- Denotation: RExpr → ℝ
-- ============================================================================

/-- Map a reified expression to its real value. Noncomputable (uses Real.exp, etc.). -/
noncomputable def RExpr.denote : RExpr → ℝ
  | .nat n => (n : ℝ)  -- Nat.cast n
  | .add a b => a.denote + b.denote
  | .mul a b => a.denote * b.denote
  | .div a b => a.denote / b.denote
  | .neg a => -a.denote
  | .sub a b => a.denote - b.denote
  | .rexp a => Real.exp a.denote
  | .rlog a => Real.log a.denote
  | .rpow a n => Real.rpow a.denote n
  | .inv a => a.denote⁻¹
  | .iteZero c t e => if c.denote = 0 then t.denote else e.denote

-- ============================================================================
-- Evaluation: RExpr → QInterval (computable)
-- ============================================================================

/-- Evaluate a reified expression to a bounding QInterval. Fully computable. -/
def RExpr.eval : RExpr → QInterval
  | .nat n => QInterval.exact n
  | .add a b => (a.eval).add (b.eval)
  | .mul a b =>
    let ra := a.eval
    let rb := b.eval
    -- Zero short-circuit
    if ra.lo == 0 && ra.hi == 0 then QInterval.exact 0
    else if rb.lo == 0 && rb.hi == 0 then QInterval.exact 0
    -- Nonneg fast path
    else if h₁ : 0 ≤ ra.lo then
      if h₂ : 0 ≤ rb.lo then ra.mulNonneg rb h₁ h₂
      else ra.mul rb
    else ra.mul rb
  | .div a b =>
    let ra := a.eval
    let rb := b.eval
    if ra.lo == 0 && ra.hi == 0 then QInterval.exact 0
    else if h₁ : 0 ≤ ra.lo then
      if h₂ : 0 < rb.lo then ra.divPos rb h₁ h₂
      else ⟨-1, 1, by norm_num⟩  -- fallback (guarded by evalValid)
    else ⟨-1, 1, by norm_num⟩
  | .neg a => (a.eval).neg
  | .sub a b => (a.eval).sub (b.eval)
  | .rexp a => expInterval (a.eval)
  | .rlog a =>
    let ra := a.eval
    if h : 0 < ra.lo then logInterval ra h
    else ⟨-1000, 1000, by norm_num⟩  -- fallback (guarded by evalValid)
  | .rpow a n =>
    let ra := a.eval
    if n == 0 then Linglib.Interval.rpowZero
    else if h : 0 ≤ ra.lo then Linglib.Interval.rpowNat ra n h
    else ⟨0, 1, by norm_num⟩  -- fallback (guarded by evalValid)
  | .inv a =>
    let ra := a.eval
    if h : 0 < ra.lo then ra.invPos h
    else ⟨-1, 1, by norm_num⟩  -- fallback (guarded by evalValid)
  | .iteZero c t e =>
    let rc := c.eval
    if rc.lo == 0 && rc.hi == 0 then t.eval    -- cond = 0 → then branch
    else if h : (0 : ℚ) < rc.lo then e.eval      -- cond > 0 → else branch
    else  -- can't decide: take union of both branches
      let rt := t.eval
      let re := e.eval
      ⟨min rt.lo re.lo, max rt.hi re.hi,
       le_trans (min_le_left _ _) (le_trans rt.valid (le_max_left _ _))⟩

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
  | .add a b => a.evalValid && b.evalValid
  | .mul a b => a.evalValid && b.evalValid
  | .div a b =>
    a.evalValid && b.evalValid &&
    ((a.eval.lo == 0 && a.eval.hi == 0) ||
     (decide (0 ≤ a.eval.lo) && decide (0 < b.eval.lo)))
  | .neg a => a.evalValid
  | .sub a b => a.evalValid && b.evalValid
  | .rexp a => a.evalValid
  | .rlog a => a.evalValid && decide (0 < a.eval.lo)
  | .rpow a n => a.evalValid && (n == 0 || decide (0 ≤ a.eval.lo))
  | .inv a => a.evalValid && decide (0 < a.eval.lo)
  | .iteZero c t e => c.evalValid && t.evalValid && e.evalValid

-- ============================================================================
-- Soundness: eval_sound
-- ============================================================================

/-- Key lemma: if interval proves x = 0, then x = 0. -/
private theorem interval_eq_zero {I : QInterval} {x : ℝ}
    (hx : I.containsReal x) (hlo : I.lo = 0) (hhi : I.hi = 0) : x = 0 :=
  QInterval.eq_zero_of_bounds hx (by simp [hlo]) (by simp [hhi])

/-- Key lemma: if interval proves x > 0, then x > 0. -/
private theorem interval_pos {I : QInterval} {x : ℝ}
    (hx : I.containsReal x) (hlo : 0 < I.lo) : 0 < x :=
  lt_of_lt_of_le (by exact_mod_cast hlo) hx.1

/-- Soundness of interval evaluation by reflection.

Every well-formed `RExpr` (one where `evalValid = true`) evaluates to a
`QInterval` that contains the real denotation. The `evalValid` precondition
excludes expressions with degenerate operations (division by non-positive,
log of non-positive, etc.) whose fallback intervals are unsound. -/
theorem RExpr.eval_sound : ∀ (e : RExpr), e.evalValid = true →
    (e.eval).containsReal e.denote
  | .nat n => by
    intro _
    simp only [eval, denote]
    exact QInterval.exact_containsReal n
  | .add a b => by
    intro hv
    simp only [evalValid, Bool.and_eq_true] at hv
    simp only [eval, denote]
    exact QInterval.add_containsReal (eval_sound a hv.1) (eval_sound b hv.2)
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
            exact QInterval.mulNonneg_containsReal ‹_› ‹_› iha ihb
          · exact QInterval.mul_containsReal iha ihb
        · exact QInterval.mul_containsReal iha ihb
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
        · exact QInterval.divPos_containsReal ‹_› ‹_› iha ihb
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
    exact QInterval.sub_containsReal (eval_sound a hv.1) (eval_sound b hv.2)
  | .rexp a => by
    intro hv
    simp only [evalValid] at hv
    simp only [eval, denote]
    exact expInterval_containsReal (eval_sound a hv)
  | .rlog a => by
    intro hv
    simp only [evalValid, Bool.and_eq_true, decide_eq_true_eq] at hv
    simp only [eval, denote]
    have iha := eval_sound a hv.1
    split
    · exact logInterval_containsReal ‹_› iha
    · exact absurd hv.2 ‹_›
  | .rpow a n => by
    intro hv
    simp only [evalValid, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
               decide_eq_true_eq] at hv
    obtain ⟨hva, hcond⟩ := hv
    simp only [eval, denote]
    have iha := eval_sound a hva
    split
    · -- n == 0
      rename_i h; simp [beq_iff_eq] at h; subst h
      simp only [Nat.cast_zero]
      exact rpowZero_containsReal a.denote
    · split
      · -- 0 ≤ ra.lo
        exact rpowNat_containsReal ‹_› iha
      · -- fallback: contradiction from evalValid
        rename_i hNotZeroN hNotNonneg
        simp [beq_iff_eq] at hNotZeroN
        exact absurd (hcond.resolve_left hNotZeroN) hNotNonneg
  | .inv a => by
    intro hv
    simp only [evalValid, Bool.and_eq_true, decide_eq_true_eq] at hv
    simp only [eval, denote]
    have iha := eval_sound a hv.1
    split
    · exact QInterval.invPos_containsReal ‹_› iha
    · exact absurd hv.2 ‹_›
  | .iteZero c t e => by
    intro hv
    simp only [evalValid, Bool.and_eq_true] at hv
    obtain ⟨⟨hvc, hvt⟩, hve⟩ := hv
    simp only [eval, denote]
    have ihc := eval_sound c hvc
    have iht := eval_sound t hvt
    have ihe := eval_sound e hve
    split
    · -- rc.lo == 0 && rc.hi == 0 → cond = 0 → then branch
      rename_i h; simp [beq_iff_eq] at h
      have hzero := interval_eq_zero ihc h.1 h.2
      simp [hzero]
      exact iht
    · split
      · -- 0 < rc.lo → cond > 0 → cond ≠ 0 → else branch
        rename_i _ hpos
        have hcond_pos := interval_pos ihc (by exact hpos)
        have hcond_ne : c.denote ≠ 0 := ne_of_gt hcond_pos
        simp [hcond_ne]
        exact ihe
      · -- can't decide: union covers both branches
        rename_i h1 h2
        simp only [QInterval.containsReal]
        split
        · -- cond = 0 → then branch, need t.denote ∈ [min .., max ..]
          constructor
          · exact le_trans (by exact_mod_cast min_le_left _ _) iht.1
          · exact le_trans iht.2 (by exact_mod_cast le_max_left _ _)
        · -- cond ≠ 0 → else branch
          constructor
          · exact le_trans (by exact_mod_cast min_le_right _ _) ihe.1
          · exact le_trans ihe.2 (by exact_mod_cast le_max_right _ _)

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

end Linglib.Interval
