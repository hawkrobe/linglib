import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Order.MinMax

/-!
# Social Utility: Fehr-Schmidt Inequity Aversion
@cite{fehr-schmidt-1999} @cite{houlihan-kleiman-weiner-hewitt-tenenbaum-saxe-2023}

@cite{fehr-schmidt-1999} model agents who care about fairness, not just
material payoff. An agent's utility depends on the difference between
their own payoff and others' payoffs:

    U_i = v_i − α · max(0, v_j − v_i) − β · max(0, v_i − v_j)

where α ≥ 0 captures **disadvantageous inequity aversion** (DIA — disliking
getting less than others) and β captures **advantageous inequity aversion**
(AIA — disliking getting more than others).

@cite{houlihan-kleiman-weiner-hewitt-tenenbaum-saxe-2023} use this as the
base utility in their inverse planning model of emotion prediction.
Observers infer agents' α and β weights from observed choices, then
use those inferred social preferences to compute emotion appraisals.

## Connection to RSA

In politeness models (@cite{yoon-etal-2020}), the "social utility" term is
a primitive kindness weight φ. Fehr-Schmidt decomposes social utility into
two structurally distinct components (AIA, DIA), each with its own
behavioral signature. This decomposition predicts which emotions arise:
DIA-weighted appraisals drive *envy*; AIA-weighted appraisals drive *guilt*.
-/

namespace Core

/-! ### Core Utility Function -/

/-- Fehr-Schmidt inequity aversion utility.

    U = v_self − α · max(0, v_other − v_self) − β · max(0, v_self − v_other)

- `α` (DIA): penalty for disadvantageous inequality (I got less)
- `β` (AIA): penalty for advantageous inequality (I got more)

Typically 0 ≤ β ≤ α: people dislike being behind more than being ahead. -/
def fehrSchmidt (vSelf vOther : ℚ) (α β : ℚ) : ℚ :=
  vSelf - α * max 0 (vOther - vSelf) - β * max 0 (vSelf - vOther)

/-- Disadvantageous inequality: how much worse off I am than the other. -/
def disadvantageousInequality (vSelf vOther : ℚ) : ℚ :=
  max 0 (vOther - vSelf)

/-- Advantageous inequality: how much better off I am than the other. -/
def advantageousInequality (vSelf vOther : ℚ) : ℚ :=
  max 0 (vSelf - vOther)

/-- Fehr-Schmidt decomposes into three additive terms. -/
theorem fehrSchmidt_decompose (vSelf vOther α β : ℚ) :
    fehrSchmidt vSelf vOther α β =
    vSelf - α * disadvantageousInequality vSelf vOther
          - β * advantageousInequality vSelf vOther := rfl

/-! ### Special Cases -/

/-- A purely selfish agent (α = β = 0) maximizes own payoff. -/
theorem fehrSchmidt_selfish (vSelf vOther : ℚ) :
    fehrSchmidt vSelf vOther 0 0 = vSelf := by
  unfold fehrSchmidt; ring

/-- Equal payoffs produce no inequity penalty. -/
theorem fehrSchmidt_equal (v α β : ℚ) :
    fehrSchmidt v v α β = v := by
  unfold fehrSchmidt
  simp [sub_self, max_self]

/-- When payoffs are equal, DI = 0. -/
theorem di_zero_when_equal (v : ℚ) :
    disadvantageousInequality v v = 0 := by
  unfold disadvantageousInequality; simp [sub_self, max_self]

/-- When payoffs are equal, AI = 0. -/
theorem ai_zero_when_equal (v : ℚ) :
    advantageousInequality v v = 0 := by
  unfold advantageousInequality; simp [sub_self, max_self]

/-- DI and AI are complementary: exactly one is positive. -/
theorem di_ai_complementary (vSelf vOther : ℚ) :
    disadvantageousInequality vSelf vOther = 0 ∨
    advantageousInequality vSelf vOther = 0 := by
  unfold disadvantageousInequality advantageousInequality
  rcases le_total vSelf vOther with h | h
  · right; simp [max_eq_left (by linarith : (0 : ℚ) ≥ vSelf - vOther)]
  · left; simp [max_eq_left (by linarith : (0 : ℚ) ≥ vOther - vSelf)]

/-! ### Monotonicity -/

/-- Higher α increases DIA penalty (weakly). -/
theorem fehrSchmidt_mono_α (vSelf vOther α₁ α₂ β : ℚ)
    (hα : α₁ ≤ α₂) :
    fehrSchmidt vSelf vOther α₂ β ≤ fehrSchmidt vSelf vOther α₁ β := by
  unfold fehrSchmidt
  have h : 0 ≤ max 0 (vOther - vSelf) := le_max_left 0 _
  nlinarith

/-- Higher β increases AIA penalty (weakly). -/
theorem fehrSchmidt_mono_β (vSelf vOther α β₁ β₂ : ℚ)
    (hβ : β₁ ≤ β₂) :
    fehrSchmidt vSelf vOther α β₂ ≤ fehrSchmidt vSelf vOther α β₁ := by
  unfold fehrSchmidt
  have h : 0 ≤ max 0 (vSelf - vOther) := le_max_left 0 _
  nlinarith

/-! ### Value Function

@cite{houlihan-kleiman-weiner-hewitt-tenenbaum-saxe-2023} apply a value function ν
to raw monetary payoffs to capture diminishing marginal utility.
For their purposes, ν is a sign-adjusted logarithm. We keep the
utility function generic over any monotone transform. -/

/-- Composed Fehr-Schmidt: apply a value function to raw payoffs
before computing inequity penalties. -/
def fehrSchmidtV (ν : ℚ → ℚ) (vSelf vOther : ℚ) (α β : ℚ) : ℚ :=
  fehrSchmidt (ν vSelf) (ν vOther) α β

/-- When ν is the identity, fehrSchmidtV reduces to fehrSchmidt. -/
theorem fehrSchmidtV_id (vSelf vOther α β : ℚ) :
    fehrSchmidtV id vSelf vOther α β = fehrSchmidt vSelf vOther α β := rfl

end Core
