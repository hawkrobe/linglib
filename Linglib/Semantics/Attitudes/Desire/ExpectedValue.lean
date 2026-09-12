import Linglib.Core.Probability.Decision.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Expected-value desire semantics

`a wants p` iff the conditional expected value of `p` given `a`'s beliefs exceeds a
contextual threshold — [lassiter-2017]'s scalar semantics for evaluative predicates,
applied to *want* ([lassiter-2011]). `expectedValue` is the conditional expected utility
of the one-action decision problem whose utility is the value function. It is an interval
scale (`expectedValue_affine`) and intermediate on disjoint propositions
(`expectedValue_intermediate`), from which the threshold reading derives Weakening
(`Want.union`) and, given exclusivity, the Smith Principle (`Want.inter_of_union_eq_univ`).
The bare threshold admits simultaneous `want p` and `want ¬p` (`exists_want_and_want_compl`).

## References

* [lassiter-2011]
* [lassiter-2017]
-/

namespace Desire.ExpectedValue

open Core.DecisionTheory

variable {W : Type*} [Fintype W] (pr V : W → ℚ) (θ : ℚ) (bel p q : Set W)
  [DecidablePred (· ∈ bel)] [DecidablePred (· ∈ p)] [DecidablePred (· ∈ q)]

/-- The one-action decision problem whose utility is the value function `V`. -/
def toDecisionProblem : DecisionProblem ℚ W Unit := ⟨λ w _ => V w, pr⟩

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

variable {pr V θ bel p q}

theorem cell_congr (h : p = q) : cell bel p = cell bel q := by
  subst h; exact Finset.filter_congr_decidable ..

theorem expectedValue_congr (h : p = q) : expectedValue pr V bel p = expectedValue pr V bel q := by
  simp only [expectedValue, cell_congr h]

theorem expectedValue_eq (h : HasPositiveBeliefMass pr bel p) :
    expectedValue pr V bel p = (∑ w ∈ cell bel p, pr w * V w) / ∑ w ∈ cell bel p, pr w := by
  have hne := h.ne'
  simp only [expectedValue, DecisionProblem.condExpectedUtility, toDecisionProblem, if_neg hne]
  rw [eq_div_iff hne, Finset.sum_mul]
  exact Finset.sum_congr rfl λ w _ => by field_simp

/-- Expected value is an interval scale: a positive affine transformation of the value
function transforms expected value by the same coefficients. -/
theorem expectedValue_affine (h : HasPositiveBeliefMass pr bel p) (a b : ℚ) :
    expectedValue pr (λ w => a * V w + b) bel p = a * expectedValue pr V bel p + b := by
  rw [expectedValue_eq h, expectedValue_eq h, div_eq_iff h.ne', add_mul, mul_div_assoc',
    div_mul_cancel₀ _ h.ne', Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl λ w _ => by ring

theorem cell_union [DecidableEq W] : cell bel (p ∪ q) = cell bel p ∪ cell bel q := by
  ext; simp [cell, Set.inter_union_distrib_left]

theorem disjoint_cell [DecidableEq W] (h : Disjoint p q) :
    Disjoint (cell bel p) (cell bel q) :=
  Finset.disjoint_filter.2 λ _ _ hp hq => Set.disjoint_left.1 h hp.2 hq.2

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

/-- A disjoint union above threshold with one part at or below it has the other part
above it. -/
theorem Want.resolve_left [DecidableEq W] (hp' : HasPositiveBeliefMass pr bel p)
    (hq' : HasPositiveBeliefMass pr bel q) (hd : Disjoint p q) (h : Want pr V θ bel (p ∪ q))
    (hp : ¬ Want pr V θ bel p) : Want pr V θ bel q :=
  (lt_max_iff.1 (lt_of_lt_of_le h (expectedValue_intermediate hp' hq' hd).2)).resolve_left hp

/-- The Smith Principle: for exhaustive `p` and `q` both above threshold, so is `p ∩ q`,
provided `want` is exclusive on `q`. -/
theorem Want.inter_of_union_eq_univ [DecidableEq W]
    (hpq : HasPositiveBeliefMass pr bel (p ∩ q)) (hq' : HasPositiveBeliefMass pr bel qᶜ)
    (huniv : p ∪ q = Set.univ) (hp : Want pr V θ bel p) (hex : ¬ Want pr V θ bel qᶜ) :
    Want pr V θ bel (p ∩ q) := by
  have hsub : qᶜ ⊆ p := Set.compl_subset_iff_union.2 (Set.union_comm _ _ ▸ huniv)
  have heq : qᶜ ∪ p ∩ q = p := by
    rw [← Set.inter_eq_right.2 hsub, Set.union_comm, Set.inter_union_compl]
  exact Want.resolve_left hq' hpq (disjoint_compl_left.mono_right Set.inter_subset_right)
    (by unfold Want; rwa [expectedValue_congr heq]) hex

/-- The bare threshold admits simultaneous `want p` and `want ¬p`. -/
theorem exists_want_and_want_compl :
    ∃ (W : Type) (_ : Fintype W) (pr V : W → ℚ) (θ : ℚ) (bel p : Set W)
      (_ : DecidablePred (· ∈ bel)) (_ : DecidablePred (· ∈ p)),
      Want pr V θ bel p ∧ Want pr V θ bel pᶜ :=
  ⟨Bool, inferInstance, λ _ => 1, λ b => if b then 2 else 1, 0, Set.univ, {true},
    inferInstance, inferInstance, by
      constructor <;>
        norm_num [Want, expectedValue, cell, DecisionProblem.condExpectedUtility,
          toDecisionProblem, Finset.sum_filter, Fintype.sum_bool] <;> decide⟩

end Desire.ExpectedValue
