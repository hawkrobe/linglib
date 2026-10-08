module

public import Linglib.Core.Order.Partition.Finpartition
public import Linglib.Core.Probability.Decision.ValueOfInformation

/-!
# The value of a question

Relative to a decision problem, a prior over worlds and a utility for each action in each world,
an answer is worth the gain in decision value from learning it, and a question, a partition of
the worlds, is worth the expected gain from learning its answer. That expectation is the value of
information of the experiment revealing the answer, it is never negative, and one question refines
another exactly when it is at least as useful in every decision problem. A wh-question over a
domain partitions the worlds by the predicate's extension within the domain, so widening the
domain refines the question and cannot lower its value.

## Main statements

* `Question.utility_eq_valueOfInformation`: a question's value is the value of information of
  revealing its answer.
* `Question.le_iff_forall_utility_le`: one question refines another exactly when it is at least
  as useful in every decision problem.
* `Question.utility_wh_mono`: widening the domain of a wh-question cannot lower its value.

## References

* [van-rooy-2003]
* [blackwell-1953]
* [raiffa-schlaifer-1961]
-/

@[expose] public section

namespace Question

open MeasureTheory ProbabilityTheory

universe u

variable {W : Type u} {A : Type*}

/-! ### The value of answers -/

section Value

variable [MeasurableSpace W]

/-- The utility value of learning `C` is the decision value of the prior conditioned on `C`, less
the decision value of the prior. -/
noncomputable def utilityValue (U : W → A → ℝ) (μ : Measure W) (C : Set W) : ℝ :=
  decisionValue U μ[|C] - decisionValue U μ

/-- An answer is better than another when it has a higher utility value, or the same value and
is strictly less informative. -/
def BetterAnswer (U : W → A → ℝ) (μ : Measure W) (C D : Set W) : Prop :=
  toLex (utilityValue U μ D, D) < toLex (utilityValue U μ C, C)

theorem betterAnswer_iff {U : W → A → ℝ} {μ : Measure W} {C D : Set W} :
    BetterAnswer U μ C D ↔ utilityValue U μ D < utilityValue U μ C ∨
      utilityValue U μ C = utilityValue U μ D ∧ D ⊂ C := by
  simp [BetterAnswer, Prod.Lex.toLex_lt_toLex, eq_comm]


/-! ### The utility of questions -/

section Utility

variable [Fintype W] [DecidableEq W]

/-- The expected utility value of a question weights the utility value of each answer by its
probability. -/
noncomputable def utility (U : W → A → ℝ) (μ : Measure W)
    (Q : Finpartition (Finset.univ : Finset W)) : ℝ :=
  ∑ c ∈ Q.parts, μ.real c * utilityValue U μ c

variable [DiscreteMeasurableSpace W] (U : W → A → ℝ) (μ : Measure W) [IsProbabilityMeasure μ]

private theorem utility_eq (Q : Finpartition (Finset.univ : Finset W)) :
    utility U μ Q =
      ∑ c, μ.real (Q.part ⁻¹' {c}) * decisionValue U μ[|Q.part ⁻¹' {c}] - decisionValue U μ := by
  have hmass : ∑ c ∈ Q.parts, μ.real c = 1 := by
    rw [Q.sum_parts_eq_sum_preimage_part (F := μ.real) measureReal_empty,
      sum_measureReal_preimage_singleton _ fun _ _ ↦ .of_discrete]
    simp
  simp only [utility, utilityValue, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    hmass, one_mul]
  rw [Q.sum_parts_eq_sum_preimage_part (F := fun c ↦ μ.real c * decisionValue U μ[|c]) (by simp)]

/-- The expected utility value of a question is the value of information of the experiment that
reveals its answer. -/
theorem utility_eq_valueOfInformation [Nonempty W] [MeasurableSpace (Finset W)]
    [MeasurableSingletonClass (Finset W)] (Q : Finpartition (Finset.univ : Finset W)) :
    utility U μ Q =
      valueOfInformation (decisionValue U) (Kernel.deterministic Q.part .of_discrete) μ := by
  rw [utility_eq, valueOfInformation_deterministic]

/-- A question is never worth less than nothing. -/
theorem utility_nonneg [Finite A] [Nonempty W] (Q : Finpartition (Finset.univ : Finset W)) :
    0 ≤ utility U μ Q := by
  let _ : MeasurableSpace (Finset W) := ⊤
  have : MeasurableSingletonClass (Finset W) := ⟨fun _ ↦ trivial⟩
  rw [utility_eq_valueOfInformation]
  exact valueOfInformation_decisionValue_nonneg U _ μ

/-- A finer question is worth at least as much as a coarser one, since revealing the coarser
answer garbles the finer. -/
theorem utility_anti [Finite A] [Nonempty W] {P Q : Finpartition (Finset.univ : Finset W)}
    (h : P ≤ Q) : utility U μ Q ≤ utility U μ P := by
  let _ : MeasurableSpace (Finset W) := ⊤
  have : MeasurableSingletonClass (Finset W) := ⟨fun _ ↦ trivial⟩
  rw [utility_eq_valueOfInformation, utility_eq_valueOfInformation]
  exact valueOfInformation_decisionValue_le_of_factorsThrough U _ _
    (Finpartition.le_iff_factorsThrough_part.1 h) μ

/-- No question is worth more than the finest one, what the world is like, whose value is the
expected value of perfect information of [raiffa-schlaifer-1961]. -/
theorem utility_le_bot [Finite A] [Nonempty W]
    (Q : Finpartition (Finset.univ : Finset W)) :
    utility U μ Q ≤ utility U μ ⊥ :=
  utility_anti U μ bot_le

/-- The value of sample information of learning `C` compares the best action after learning `C`
with the action `a` taken now. -/
noncomputable def valueSampleInfo (a : A) (C : Set W) : ℝ :=
  decisionValue U μ[|C] - ∫ w, U w a ∂μ[|C]

/-- When `a` is the best action now, the expected utility value of a question is its expected
value of sample information. -/
theorem utility_eq_sum_valueSampleInfo [Nonempty W]
    (Q : Finpartition (Finset.univ : Finset W)) {a : A}
    (ha : ∫ w, U w a ∂μ = decisionValue U μ) :
    utility U μ Q = ∑ c ∈ Q.parts, μ.real c * valueSampleInfo U μ a c := by
  simp only [valueSampleInfo, mul_sub, Finset.sum_sub_distrib]
  rw [utility_eq,
    Q.sum_parts_eq_sum_preimage_part (F := fun c ↦ μ.real c * decisionValue U μ[|c]) (by simp),
    Q.sum_parts_eq_sum_preimage_part (F := fun c ↦ μ.real c * ∫ w, U w a ∂μ[|c]) (by simp),
    sum_measureReal_mul_integral_cond, ha]

variable {U μ}

/-- One question refines another exactly when it is at least as useful in every decision problem
with a probability prior, the special case of [blackwell-1953] stated in section 4.1. -/
theorem le_iff_forall_utility_le [Nonempty W]
    (P Q : Finpartition (Finset.univ : Finset W)) :
    P ≤ Q ↔ ∀ {B : Type u} [Fintype B] (U : W → B → ℝ) (μ : Measure W) [IsProbabilityMeasure μ],
      utility U μ Q ≤ utility U μ P := by
  refine ⟨fun h _ _ U μ _ ↦ utility_anti U μ h, fun h ↦ ?_⟩
  let _ : MeasurableSpace (Finset W) := ⊤
  have : MeasurableSingletonClass (Finset W) := ⟨fun _ ↦ trivial⟩
  obtain ⟨ψ, hψ⟩ := exists_eq_comp_of_forall_valueOfInformation_le P.part Q.part fun U ↦ by
    simpa only [utility_eq_valueOfInformation] using h U (uniformOn Set.univ)
  exact Finpartition.le_iff_factorsThrough_part.2 fun a b hab ↦ by simp [hψ, hab]

/-- Relative to a decision problem, a question is better than another when it is more useful, or
as useful and strictly coarser, since one should not ask for irrelevant information. -/
def Better (U : W → A → ℝ) (μ : Measure W) (Q Q' : Finpartition (Finset.univ : Finset W)) :
    Prop :=
  toLex (utility U μ Q', Q') < toLex (utility U μ Q, Q)

omit [DiscreteMeasurableSpace W] [IsProbabilityMeasure μ] in
theorem better_iff {Q Q' : Finpartition (Finset.univ : Finset W)} :
    Better U μ Q Q' ↔
      utility U μ Q' < utility U μ Q ∨
        utility U μ Q = utility U μ Q' ∧ Q' < Q := by
  simp [Better, Prod.Lex.toLex_lt_toLex, eq_comm]

/-! ### The domain of a wh-phrase -/

variable {D : Type*} [DecidableEq D]

/-- The partition a wh-question induces over a domain puts two worlds together when the
predicate's extension agrees on the domain. -/
def wh (P : W → Finset D) (dom : Finset D) : Finpartition (Finset.univ : Finset W) :=
  Finpartition.ofFun fun w ↦ dom ∩ P w

omit [MeasurableSpace W] [DiscreteMeasurableSpace W] in
/-- Enlarging the domain refines the question, since more individuals give more specific
answers. -/
theorem wh_anti (P : W → Finset D) {dom dom' : Finset D} (h : dom ⊆ dom') :
    wh P dom' ≤ wh P dom :=
  Finpartition.ofFun_le_ofFun_iff.2 fun w v hwv ↦ by
    rw [← Finset.inter_eq_left.2 h, Finset.inter_assoc, Finset.inter_assoc, hwv]

variable (U μ)

/-- Enlarging the domain cannot lower the value of the question, so the domain should contain
every individual that could matter. -/
theorem utility_wh_mono [Finite A] [Nonempty W] (P : W → Finset D)
    {dom dom' : Finset D} (h : dom ⊆ dom') :
    utility U μ (wh P dom) ≤ utility U μ (wh P dom') :=
  utility_anti U μ (wh_anti P h)

omit [DiscreteMeasurableSpace W] [IsProbabilityMeasure μ] in
/-- Of two domains yielding equally useful but different questions, the smaller gives the better
question, so the domain relevance selects contains only individuals that could affect the
decision. -/
theorem better_wh (P : W → Finset D) {dom dom' : Finset D} (h : dom ⊆ dom')
    (heq : utility U μ (wh P dom) = utility U μ (wh P dom'))
    (hne : wh P dom' ≠ wh P dom) :
    Better U μ (wh P dom) (wh P dom') :=
  better_iff.2 (.inr ⟨heq, (wh_anti P h).lt_of_ne hne⟩)

end Utility

end Value

end Question
