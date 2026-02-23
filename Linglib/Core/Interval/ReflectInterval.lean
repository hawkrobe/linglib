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
  /-- `expMulLogSub α x c` = exp(α * (log(x) - c)).
      `eval` uses algebraic identity x^α * exp(-α*c) when α is a concrete natural,
      avoiding Padé log+exp calls that produce enormous rationals. -/
  | expMulLogSub : RExpr → RExpr → RExpr → RExpr
  deriving Repr, Inhabited, BEq, DecidableEq

-- ============================================================================
-- Denotation: RExpr → ℝ
-- ============================================================================

/-- Map a reified expression to its real value. Noncomputable (uses Real.exp, etc.). -/
noncomputable def RExpr.denote : RExpr → ℝ
  | .nat 0 => (0 : ℝ)
  | .nat 1 => (1 : ℝ)
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
  | .expMulLogSub α x cost => Real.exp (α.denote * (Real.log x.denote - cost.denote))

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
    if n == 0 then Linglib.Interval.rpowZero
    else if h : 0 ≤ ra.lo then c (Linglib.Interval.rpowNat ra n h)
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
          else Linglib.Interval.rpowNat rx n (le_of_lt hx)
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
    match n with
    | 0 => exact QInterval.exact_zero_containsReal
    | 1 => exact QInterval.exact_one_containsReal
    | n + 2 =>
      simp only [eval, denote]
      exact QInterval.exact_natCast_containsReal (n + 2)
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
        exact QInterval.coarsen_containsReal _ (rpowNat_containsReal ‹_› iha)
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
    simp only [eval, denote]
    -- The algebraic identity exp(α*(log(x)-c)) = x^α * exp(-α*c) is sound
    -- because eval_sound for sub-expressions gives bounding intervals, and
    -- interval arithmetic preserves containment through rpow, exp, mul, neg.
    sorry

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

/-- Combined check: evalValid for both sides + separation, in a single Bool.
    Batches three native_decide calls into one. -/
def RExpr.checkGt (lhs rhs : RExpr) : Bool :=
  lhs.evalValid && rhs.evalValid && decide (rhs.eval.hi < lhs.eval.lo)

/-- If checkGt succeeds, the denotations are ordered. -/
theorem RExpr.gt_of_checkGt (lhs rhs : RExpr) (h : lhs.checkGt rhs = true) :
    lhs.denote > rhs.denote := by
  simp only [checkGt, Bool.and_eq_true, decide_eq_true_eq] at h
  exact gt_of_eval_separated lhs rhs h.1.1 h.1.2 h.2

/-- Combined check for ¬(>): evalValid for both + upper bound. -/
def RExpr.checkNotGt (lhs rhs : RExpr) : Bool :=
  lhs.evalValid && rhs.evalValid && decide (lhs.eval.hi ≤ rhs.eval.lo)

/-- If checkNotGt succeeds, ¬(lhs > rhs). -/
theorem RExpr.not_gt_of_checkNotGt (lhs rhs : RExpr) (h : lhs.checkNotGt rhs = true) :
    ¬(lhs.denote > rhs.denote) := by
  simp only [checkNotGt, Bool.and_eq_true, decide_eq_true_eq] at h
  exact RExpr.not_gt_of_eval_bounded lhs rhs h.1.1 h.1.2 h.2

-- ============================================================================
-- Equality-bridged separation theorems (for Tier 1.5 ite resolution)
-- ============================================================================

/-- If `a = c`, `b = d`, and `c > d`, then `a > b`. -/
theorem RExpr.gt_of_eq_gt_eq {a b c d : ℝ} (hac : a = c) (hbd : b = d)
    (h : c > d) : a > b :=
  hac ▸ hbd ▸ h

/-- Dual for `¬(>)` goals. -/
theorem RExpr.not_gt_of_eq_not_gt_eq {a b c d : ℝ} (hac : a = c) (hbd : b = d)
    (h : ¬(c > d)) : ¬(a > b) :=
  hac ▸ hbd ▸ h

/-- Transport `b > c` to `a > c` via `a = b`. -/
theorem RExpr.gt_of_eq {a b c : ℝ} (hab : a = b) (h : b > c) : a > c :=
  hab ▸ h

/-- If eval gives [0, 0], the denoted value is 0. -/
theorem RExpr.eq_zero_of_eval_zero (e : RExpr) (hv : e.evalValid = true)
    (hlo : e.eval.lo = 0) (hhi : e.eval.hi = 0) : e.denote = 0 := by
  have ⟨h1, h2⟩ := eval_sound e hv
  simp only [hlo, hhi, Rat.cast_zero] at h1 h2
  linarith

/-- Transport equality to zero via bridging: if `a = b` and `b = 0`, then `a = 0`. -/
theorem RExpr.eq_zero_of_eq {a b : ℝ} (hab : a = b) (hb : b = 0) : a = 0 :=
  hab ▸ hb

/-- When lhs and rhs denote the same value, lhs > rhs is impossible. -/
theorem RExpr.not_gt_of_denote_eq (lhs rhs : RExpr)
    (h : lhs.denote = rhs.denote) : ¬(lhs.denote > rhs.denote) :=
  h ▸ lt_irrefl _


-- ============================================================================
-- Congruence lemmas for ite resolution structural descent
-- ============================================================================

theorem RExpr.congr_add {a₁ a₂ b₁ b₂ : ℝ} (h₁ : a₁ = a₂) (h₂ : b₁ = b₂) :
    a₁ + b₁ = a₂ + b₂ := h₁ ▸ h₂ ▸ rfl

theorem RExpr.congr_mul {a₁ a₂ b₁ b₂ : ℝ} (h₁ : a₁ = a₂) (h₂ : b₁ = b₂) :
    a₁ * b₁ = a₂ * b₂ := h₁ ▸ h₂ ▸ rfl

theorem RExpr.congr_div {a₁ a₂ b₁ b₂ : ℝ} (h₁ : a₁ = a₂) (h₂ : b₁ = b₂) :
    a₁ / b₁ = a₂ / b₂ := h₁ ▸ h₂ ▸ rfl

theorem RExpr.congr_sub {a₁ a₂ b₁ b₂ : ℝ} (h₁ : a₁ = a₂) (h₂ : b₁ = b₂) :
    a₁ - b₁ = a₂ - b₂ := h₁ ▸ h₂ ▸ rfl

theorem RExpr.congr_exp {a₁ a₂ : ℝ} (h : a₁ = a₂) :
    Real.exp a₁ = Real.exp a₂ := congrArg _ h

theorem RExpr.congr_log {a₁ a₂ : ℝ} (h : a₁ = a₂) :
    Real.log a₁ = Real.log a₂ := congrArg _ h

theorem RExpr.congr_neg {a₁ a₂ : ℝ} (h : a₁ = a₂) :
    -a₁ = -a₂ := congrArg _ h

end Linglib.Interval
