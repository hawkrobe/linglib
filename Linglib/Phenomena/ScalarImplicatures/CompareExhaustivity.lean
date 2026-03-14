import Linglib.Theories.Pragmatics.RSA.Core.Softmax.Limits
import Linglib.Theories.Semantics.Exhaustification.InnocentExclusion
import Linglib.Theories.Semantics.Alternatives.Lexical
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

/-! # RSA L1 at α → ∞ recovers Fox's exh @cite{fox-2007}

This file proves the concrete connection between RSA pragmatic inference and
Neo-Gricean exhaustification for the simplest non-trivial case: the Horn scale
⟨some, all⟩.

**Setup.** Two utterances (weak = "some", strong = "all") and two worlds
(weakOnly = "some but not all", both = "all"). A belief-based RSA speaker S1
chooses utterances proportional to `L0(w|u)^α`, where L0 is the literal
listener posterior under a uniform prior.

**Main result** (`l1_weak_weakOnly_tendsto_one`): The pragmatic listener L1,
hearing "some", assigns probability converging to 1 to the "some but not all"
world as α → ∞. This IS the scalar implicature: some ∧ ¬all.

**Connection to Fox 2007** (§5): Fox's innocent-exclusion computation on the
same scale yields exh(some) = some ∧ ¬all — true at weakOnly, false at both.
The RSA limit concentrates on exactly the worlds where exh returns true.

The proof factors through two key steps:
1. At the weakOnly world, "all" is false so S1(some|weakOnly) = 1 exactly
   (for any α > 0), since `rpow(0, α) = 0`.
2. At the both world, "all" is strictly more informative (L0 = 1 vs 1/2),
   so `rpow_luce_eq_softmax` converts the rpow ratio to a softmax, and
   `tendsto_softmax_infty_not_max` gives S1(some|both) → 0.
-/

namespace Phenomena.ScalarImplicatures.CompareExhaustivity

open Core Real BigOperators Finset Filter Topology
open Exhaustification.InnocentExclusion (exhB ieIndices)

-- ============================================================================
-- § 1. Scale Types
-- ============================================================================

inductive ScaleU where | weak | strong deriving DecidableEq, Fintype
inductive ScaleW where | weakOnly | both deriving DecidableEq, Fintype

instance : Nonempty ScaleU := ⟨.weak⟩
instance : Nonempty ScaleW := ⟨.weakOnly⟩

/-- Literal meaning: weak is true everywhere, strong only at "both". -/
def meaning : ScaleU → ScaleW → Bool
  | .weak, _ => true
  | .strong, .both => true
  | .strong, .weakOnly => false

-- ============================================================================
-- § 2. L0 (literal listener posterior, uniform prior)
-- ============================================================================

/-- L0(w|u): uniform prior, so 1/|⟦u⟧| if true, 0 if false. -/
noncomputable def l0 : ScaleU → ScaleW → ℝ
  | .weak, _ => 1 / 2
  | .strong, .both => 1
  | .strong, .weakOnly => 0

-- ============================================================================
-- § 3. S1 (belief-based speaker)
-- ============================================================================

/-- S1(u|w, α) = rpow(L0(w|u), α) / Σ_u' rpow(L0(w|u'), α). -/
noncomputable def s1 (α : ℝ) (w : ScaleW) (u : ScaleU) : ℝ :=
  l0 u w ^ α / ∑ u' : ScaleU, l0 u' w ^ α

private theorem sum_scaleU (f : ScaleU → ℝ) :
    ∑ u : ScaleU, f u = f .weak + f .strong := by
  have : (Finset.univ : Finset ScaleU) = {.weak, .strong} := by decide
  rw [this, Finset.sum_pair (by decide)]

/-- At weakOnly: s1(weak) = 1 for α > 0.
    "strong" is false, so rpow(0, α) = 0 — "weak" is the only live option. -/
theorem s1_weak_weakOnly (α : ℝ) (hα : 0 < α) :
    s1 α .weakOnly .weak = 1 := by
  simp only [s1, l0, sum_scaleU, zero_rpow (ne_of_gt hα), add_zero]
  exact div_self (ne_of_gt (rpow_pos_of_pos (by norm_num : (0:ℝ) < 1/2) α))

/-- S1(weak | both, α) → 0 as α → ∞.
    "strong" (L0 = 1) is more informative than "weak" (L0 = 1/2),
    so the softmax speaker concentrates on "strong". -/
theorem s1_weak_both_tendsto_zero :
    Tendsto (fun α => s1 α .both .weak) atTop (nhds 0) := by
  have heq : (fun α => s1 α .both .weak) =
      fun α => softmax (fun u : ScaleU => log (l0 u .both)) α .weak := by
    funext α; simp only [s1]
    exact rpow_luce_eq_softmax (fun u => l0 u .both) α
      (by intro u; cases u <;> simp [l0]) .weak
  rw [heq]
  exact Softmax.tendsto_softmax_infty_not_max _ ScaleU.weak ScaleU.strong
    (show log (l0 ScaleU.weak ScaleW.both) < log (l0 ScaleU.strong ScaleW.both) by
      simp only [l0]; exact Real.log_lt_log (by norm_num) (by norm_num))

-- ============================================================================
-- § 4. L1 Limit Theorem
-- ============================================================================

/-- **Scalar implicature limit**: L1(weakOnly | weak, α) → 1 as α → ∞.

    The pragmatic listener hearing "some" concentrates on worlds where
    "all" is false. This IS the scalar implicature: some ∧ ¬all. -/
theorem l1_weak_weakOnly_tendsto_one :
    Tendsto (fun α => s1 α .weakOnly .weak /
      (s1 α .weakOnly .weak + s1 α .both .weak)) atTop (nhds 1) := by
  -- s1(weakOnly, weak) is eventually 1 (for α > 0)
  have hnum : Tendsto (fun α => s1 α .weakOnly .weak) atTop (nhds 1) :=
    tendsto_const_nhds.congr'
      (eventually_atTop.mpr ⟨1, fun α hα =>
        (s1_weak_weakOnly α (by linarith)).symm⟩)
  -- denominator → 1 + 0 = 1
  have hden : Tendsto (fun α => s1 α .weakOnly .weak + s1 α .both .weak)
      atTop (nhds 1) := by
    have := hnum.add s1_weak_both_tendsto_zero
    simp only [add_zero] at this; exact this
  -- ratio → 1/1 = 1
  have := hnum.div hden one_ne_zero
  simp only [div_one] at this; exact this

-- ============================================================================
-- § 5. Connection to Fox 2007's exh
-- ============================================================================

def scaleDomain : List ScaleW := [.weakOnly, .both]
def weakMeaning : ScaleW → Bool := meaning .weak
def strongMeaning : ScaleW → Bool := meaning .strong
def scaleAlts : List (ScaleW → Bool) := [weakMeaning, strongMeaning]

/-- Fox's innocent exclusion: "strong" is the only excludable alternative. -/
theorem scale_ie :
    ieIndices scaleDomain weakMeaning scaleAlts = [1] := by native_decide

/-- exh(weak) = weak ∧ ¬strong. -/
theorem exh_weak :
    ∀ w : ScaleW, exhB scaleDomain scaleAlts weakMeaning w =
      (weakMeaning w && !strongMeaning w) := by
  intro w; cases w <;> native_decide

/-- The world where L1 concentrates is exactly where exh(weak) = true. -/
theorem exh_true_at_weakOnly :
    exhB scaleDomain scaleAlts weakMeaning .weakOnly = true := by native_decide

/-- exh(weak) is false at the "both" world — L1 assigns probability 0 there. -/
theorem exh_false_at_both :
    exhB scaleDomain scaleAlts weakMeaning .both = false := by native_decide

-- ============================================================================
-- § 6. Bridge to AlternativeSource
-- ============================================================================

/-- AlternativeSource instance for the {weak, strong} scale. -/
instance : Alternatives.AlternativeSource ScaleU where
  alternatives _ := [.weak, .strong]

/-- Exhaustifying via AlternativeSource agrees with the hand-crafted exhB call.

    This validates the full pipeline: AlternativeSource instance →
    meanings (via interp = meaning) → exhB → exhaustified meaning. -/
theorem exh_via_alternativeSource :
    ∀ w : ScaleW, exhB scaleDomain
      ((Alternatives.AlternativeSource.alternatives ScaleU.weak).map meaning)
      (meaning ScaleU.weak) w =
      exhB scaleDomain scaleAlts weakMeaning w := by
  intro w; cases w <;> native_decide

end Phenomena.ScalarImplicatures.CompareExhaustivity
