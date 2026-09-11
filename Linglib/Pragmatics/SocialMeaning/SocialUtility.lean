import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Order.MinMax

/-!
# Social utility: Fehr–Schmidt inequity aversion

[fehr-schmidt-1999] model agents who care about fairness and not only about material payoff:
an agent's utility is the agent's own payoff less a penalty for each direction of inequality
with the other agent,

    U = v_self − α · max(0, v_other − v_self) − β · max(0, v_self − v_other),

where `α` weights *disadvantageous* inequity aversion (DIA, disliking getting less than the
other) and `β` weights *advantageous* inequity aversion (AIA, disliking getting more).
[houlihan-kleiman-weiner-hewitt-tenenbaum-saxe-2023] use the two inequities as the social base
features of an inverse planning model whose observers infer the weights from a single choice.

## Implementation notes

* The utility is generic over an ordered field, so that it serves both exact rational
  computations and real-valued models with a value function.

## References

* [fehr-schmidt-1999]
* [houlihan-kleiman-weiner-hewitt-tenenbaum-saxe-2023]
-/

namespace Core

section Field

variable {K : Type*} [Field K] [LinearOrder K]

/-- Disadvantageous inequality: how much worse off I am than the other. -/
def disadvantageousInequality (vSelf vOther : K) : K := max 0 (vOther - vSelf)

/-- Advantageous inequality: how much better off I am than the other. -/
def advantageousInequality (vSelf vOther : K) : K := max 0 (vSelf - vOther)

/-- Fehr–Schmidt inequity-aversion utility with disadvantageous weight `α` and advantageous
weight `β`. -/
def fehrSchmidt (vSelf vOther α β : K) : K :=
  vSelf - α * disadvantageousInequality vSelf vOther - β * advantageousInequality vSelf vOther

variable (vSelf vOther α β : K)

@[simp] theorem disadvantageousInequality_self (v : K) : disadvantageousInequality v v = 0 := by
  simp [disadvantageousInequality]

@[simp] theorem advantageousInequality_self (v : K) : advantageousInequality v v = 0 := by
  simp [advantageousInequality]

theorem disadvantageousInequality_nonneg : 0 ≤ disadvantageousInequality vSelf vOther :=
  le_max_left _ _

theorem advantageousInequality_nonneg : 0 ≤ advantageousInequality vSelf vOther :=
  le_max_left _ _

/-- A purely selfish agent maximizes the agent's own payoff. -/
theorem fehrSchmidt_zero_zero : fehrSchmidt vSelf vOther 0 0 = vSelf := by
  simp [fehrSchmidt]

/-- Equal payoffs carry no inequity penalty. -/
theorem fehrSchmidt_self (v : K) : fehrSchmidt v v α β = v := by
  simp [fehrSchmidt]

end Field

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (vSelf vOther α β : K)

theorem disadvantageousInequality_of_le (h : vOther ≤ vSelf) :
    disadvantageousInequality vSelf vOther = 0 :=
  max_eq_left (sub_nonpos.2 h)

theorem advantageousInequality_of_le (h : vSelf ≤ vOther) :
    advantageousInequality vSelf vOther = 0 :=
  max_eq_left (sub_nonpos.2 h)

theorem disadvantageousInequality_of_ge (h : vSelf ≤ vOther) :
    disadvantageousInequality vSelf vOther = vOther - vSelf :=
  max_eq_right (sub_nonneg.2 h)

theorem advantageousInequality_of_ge (h : vOther ≤ vSelf) :
    advantageousInequality vSelf vOther = vSelf - vOther :=
  max_eq_right (sub_nonneg.2 h)

/-- At most one direction of inequality is positive. -/
theorem disadvantageousInequality_eq_zero_or_advantageousInequality_eq_zero :
    disadvantageousInequality vSelf vOther = 0 ∨ advantageousInequality vSelf vOther = 0 :=
  ((le_total vSelf vOther).imp (advantageousInequality_of_le _ _)
    (disadvantageousInequality_of_le _ _)).symm

/-- Utility is antitone in the disadvantageous weight. -/
theorem fehrSchmidt_anti_left {α₁ α₂ : K} (h : α₁ ≤ α₂) :
    fehrSchmidt vSelf vOther α₂ β ≤ fehrSchmidt vSelf vOther α₁ β := by
  unfold fehrSchmidt
  nlinarith [disadvantageousInequality_nonneg vSelf vOther]

/-- Utility is antitone in the advantageous weight. -/
theorem fehrSchmidt_anti_right {β₁ β₂ : K} (h : β₁ ≤ β₂) :
    fehrSchmidt vSelf vOther α β₂ ≤ fehrSchmidt vSelf vOther α β₁ := by
  unfold fehrSchmidt
  nlinarith [advantageousInequality_nonneg vSelf vOther]

end Core
