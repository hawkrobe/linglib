import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.NormNum

/-!
# `ennreal_arith` tactic

Discharges concrete `ℝ≥0∞` arithmetic goals — equalities, strict
inequalities, and negated strict inequalities — between sums of rational
literals. Mathlib's `norm_num` does not extend across `⊤`, and `field_simp`
/ `bound` / `gcongr` / `ring` likewise do not handle `ENNReal`. The
established pattern is to lift through `ENNReal.toReal` (which requires
`≠ ⊤` finiteness witnesses on both sides) and discharge the residual real
arithmetic with `norm_num`.

This file packages that pattern as a tactic. Helper lemmas
`ENNReal.eq_of_toReal`, `ENNReal.lt_of_toReal`, `ENNReal.le_of_toReal`
provide the lifts; the macro tries equality first, then strict
inequality, then negated strict inequality (via `not_lt.mpr` reduces to
non-strict).

Typical usage in finite-PMF construction:
```
PMF.ofFintype (fun w => match w.val with | 0 => 3/8 | 1 => 1/8 | ...)
  (by rw [Fin.sum_univ_four]; ennreal_arith)
```
-/

namespace ENNReal

open scoped ENNReal

/-- Equality of `ℝ≥0∞` values via `toReal`, given finiteness on both sides. -/
lemma eq_of_toReal {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (h : a.toReal = b.toReal) : a = b :=
  (ENNReal.toReal_eq_toReal_iff' ha hb).mp h

/-- Strict inequality of `ℝ≥0∞` values via `toReal`, given finiteness on both
sides. -/
lemma lt_of_toReal {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (h : a.toReal < b.toReal) : a < b :=
  (ENNReal.toReal_lt_toReal ha hb).mp h

/-- Non-strict inequality of `ℝ≥0∞` values via `toReal`, given finiteness on
both sides. -/
lemma le_of_toReal {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (h : a.toReal ≤ b.toReal) : a ≤ b :=
  (ENNReal.toReal_le_toReal ha hb).mp h

end ENNReal

/-- Discharge a concrete `ℝ≥0∞` arithmetic goal — equality `a = b`, strict
inequality `a < b`, or negated strict inequality `¬ a < b` — between
nonnegative real numerical expressions built from `+`, `*`, `/`, and
natural-number literals.

Lifts through `ENNReal.toReal` (with `≠ ⊤` side conditions discharged by
`simp [ENNReal.add_eq_top, ENNReal.div_eq_top]`) and closes the residual
real-arithmetic goal with `norm_num`. -/
macro "ennreal_arith" : tactic => `(tactic| (
  first
  | (apply ENNReal.eq_of_toReal
       (by simp [ENNReal.add_eq_top, ENNReal.div_eq_top])
       (by simp [ENNReal.add_eq_top, ENNReal.div_eq_top])
     simp [ENNReal.toReal_div, ENNReal.toReal_add,
           ENNReal.add_eq_top, ENNReal.div_eq_top]
     try norm_num)
  | (apply ENNReal.lt_of_toReal
       (by simp [ENNReal.add_eq_top, ENNReal.div_eq_top])
       (by simp [ENNReal.add_eq_top, ENNReal.div_eq_top])
     simp [ENNReal.toReal_div, ENNReal.toReal_add,
           ENNReal.add_eq_top, ENNReal.div_eq_top]
     try norm_num)
  | (apply not_lt.mpr
     apply ENNReal.le_of_toReal
       (by simp [ENNReal.add_eq_top, ENNReal.div_eq_top])
       (by simp [ENNReal.add_eq_top, ENNReal.div_eq_top])
     simp [ENNReal.toReal_div, ENNReal.toReal_add,
           ENNReal.add_eq_top, ENNReal.div_eq_top]
     try norm_num)))
