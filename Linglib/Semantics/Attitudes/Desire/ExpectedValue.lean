import Linglib.Core.Probability.Decision.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Expected-value desire semantics

`a wants p` iff the conditional expected value of `p` given `a`'s beliefs exceeds a
contextual threshold — [lassiter-2017]'s scalar semantics for evaluative predicates,
applied to *want* ([lassiter-2011]). `expectedValue` is the conditional expected utility
of the one-action decision problem whose utility is the value function; it is intermediate
on disjoint propositions (`expectedValue_intermediate`), from which Weakening follows
(`Want.union`). The bare threshold admits simultaneous `want p` and `want ¬p`
(`exists_want_and_want_compl`); Sloman's Principle — the wanted proposition strictly
dominates every alternative ([lassiter-2017]) — excludes it (`WantWithSloman.not_compl`).
-/

namespace Desire.ExpectedValue

open Core.DecisionTheory

variable {W : Type*} [Fintype W] (pr V : W → ℚ) (θ : ℚ) (bel p q : Set W)
  [DecidablePred (· ∈ bel)] [DecidablePred (· ∈ p)] [DecidablePred (· ∈ q)]

/-- The one-action decision problem whose utility is the value function `V`. -/
def toDecisionProblem : DecisionProblem ℚ W Unit := ⟨fun w _ => V w, pr⟩

/-- The worlds of `p` compatible with the beliefs. -/
def cell : Finset W := Finset.univ.filter (· ∈ bel ∩ p)

/-- `E_V(p)`: the conditional expected value of `p` given the belief state (`0` on a
zero-mass cell). -/
def expectedValue : ℚ := (toDecisionProblem pr V).condExpectedUtility (cell bel p) ()

/-- `p` carries positive prior mass inside the belief state. -/
def HasPositiveBeliefMass : Prop := 0 < ∑ w ∈ cell bel p, pr w

/-- `a wants p`: the expected value of `p` exceeds the threshold. -/
def Want : Prop := θ < expectedValue pr V bel p

instance : Decidable (Want pr V θ bel p) := inferInstanceAs (Decidable (_ < _))

/-- `s` strictly dominates every other alternative on the expected-value scale. -/
def SlomanPrinciple [DecidableEq W] (alts : List (Finset W)) (s : Finset W) : Prop :=
  ∀ t ∈ alts, t ≠ s → expectedValue pr V bel ↑t < expectedValue pr V bel ↑s

/-- The threshold reading together with Sloman's Principle. -/
def WantWithSloman [DecidableEq W] (alts : List (Finset W)) (s : Finset W) : Prop :=
  Want pr V θ bel ↑s ∧ SlomanPrinciple pr V bel alts s

variable {pr V θ bel p q}

theorem expectedValue_eq (h : HasPositiveBeliefMass pr bel p) :
    expectedValue pr V bel p = (∑ w ∈ cell bel p, pr w * V w) / ∑ w ∈ cell bel p, pr w := by
  have hne := h.ne'
  simp only [expectedValue, DecisionProblem.condExpectedUtility, toDecisionProblem, if_neg hne]
  rw [eq_div_iff hne, Finset.sum_mul]
  exact Finset.sum_congr rfl fun w _ => by field_simp

theorem cell_union [DecidableEq W] : cell bel (p ∪ q) = cell bel p ∪ cell bel q := by
  ext; simp [cell, Set.inter_union_distrib_left]

theorem disjoint_cell [DecidableEq W] (h : Disjoint p q) :
    Disjoint (cell bel p) (cell bel q) :=
  Finset.disjoint_filter.2 fun _ _ hp hq => Set.disjoint_left.1 h hp.2 hq.2

/-- The expected value of a disjoint union lies between the expected values of the
parts. -/
theorem expectedValue_intermediate [DecidableEq W] (hp : HasPositiveBeliefMass pr bel p)
    (hq : HasPositiveBeliefMass pr bel q) (hd : Disjoint p q) :
    min (expectedValue pr V bel p) (expectedValue pr V bel q) ≤
        expectedValue pr V bel (p ∪ q) ∧
      expectedValue pr V bel (p ∪ q) ≤
        max (expectedValue pr V bel p) (expectedValue pr V bel q) := by
  have hpq : HasPositiveBeliefMass pr bel (p ∪ q) := by
    unfold HasPositiveBeliefMass at *
    rw [cell_union, Finset.sum_union (disjoint_cell hd)]
    exact add_pos hp hq
  rw [expectedValue_eq hp, expectedValue_eq hq, expectedValue_eq hpq, cell_union,
    Finset.sum_union (disjoint_cell hd), Finset.sum_union (disjoint_cell hd)]
  unfold HasPositiveBeliefMass at hp hq
  constructor
  · rw [le_div_iff₀ (add_pos hp hq), mul_add]
    exact add_le_add ((le_div_iff₀ hp).1 (min_le_left _ _))
      ((le_div_iff₀ hq).1 (min_le_right _ _))
  · rw [div_le_iff₀ (add_pos hp hq), mul_add]
    exact add_le_add ((div_le_iff₀ hp).1 (le_max_left _ _))
      ((div_le_iff₀ hq).1 (le_max_right _ _))

/-- Weakening: disjoint `p` and `q` both above threshold put their union above it. -/
theorem Want.union [DecidableEq W] (hp' : HasPositiveBeliefMass pr bel p)
    (hq' : HasPositiveBeliefMass pr bel q) (hd : Disjoint p q) (hp : Want pr V θ bel p)
    (hq : Want pr V θ bel q) : Want pr V θ bel (p ∪ q) :=
  lt_of_lt_of_le (lt_min hp hq) (expectedValue_intermediate hp' hq' hd).1

theorem WantWithSloman.not_compl [DecidableEq W] {alts : List (Finset W)} {s : Finset W}
    (hs : s ∈ alts) (hsc : sᶜ ∈ alts) (hne : s ≠ sᶜ) (h : WantWithSloman pr V θ bel alts s) :
    ¬ WantWithSloman pr V θ bel alts sᶜ :=
  fun h' => lt_irrefl _ (lt_trans (h'.2 s hs hne) (h.2 sᶜ hsc hne.symm))

/-- The bare threshold admits simultaneous `want p` and `want ¬p`. -/
theorem exists_want_and_want_compl :
    ∃ (W : Type) (_ : Fintype W) (pr V : W → ℚ) (θ : ℚ) (bel p : Set W)
      (_ : DecidablePred (· ∈ bel)) (_ : DecidablePred (· ∈ p)),
      Want pr V θ bel p ∧ Want pr V θ bel pᶜ :=
  ⟨Bool, inferInstance, fun _ => 1, fun b => if b then 2 else 1, 0, Set.univ, {true},
    inferInstance, inferInstance, by
      constructor <;>
        norm_num [Want, expectedValue, cell, DecisionProblem.condExpectedUtility,
          toDecisionProblem, Finset.sum_filter, Fintype.sum_bool] <;> decide⟩

end Desire.ExpectedValue
