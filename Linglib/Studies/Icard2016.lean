module

public import Linglib.Core.LinearAlgebra.Matrix.Farkas
public import Linglib.Core.Probability.Decision.Basic
public import Linglib.Studies.HollidayIcard2013
public import Linglib.Core.MeasureTheory.Measure.Dirac
public import Linglib.Core.MeasureTheory.Measure.Real
public import Linglib.Core.Probability.UniformOn
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp

/-!
# Icard (2016): Pragmatic considerations on comparative probability

[icard-2016] asks what is wrong with a set of comparative probability judgments that no
probability measure represents, such as the explorer's cyclic *A ≻ B ≻ C ≻ A* or the Ellsberg
judgments that [raiffa-1961] turned against themselves. The answer is a Money Pump
([davidson-mckinsey-suppes-1955]) without its diachronic step, resting on three assumptions
that link judgments to choice: a gamble on the event judged more likely is preferred, the
preference is worth a cost, and the preferences agglomerate over weighted combinations of
gambles. Together they turn a subject's judgments into a canonical decision problem against
nature, in which the subject pays `c` to play any act that gambles on the more likely side of
every strict comparison. The paper's theorem says the subject's uniform mixture `Q★` over
those acts avoids strict dominance for some cost iff the judgments are representable
(`representable_iff_exists_not_dominated`). The proof runs through the Main Lemma, that a
measure represents the judgments iff `Q★` maximizes its expected utility for some cost
(`represents_iff_maximizes`), and [pearce-1984]'s lemma that an act which is a best response
to no belief is strictly dominated by a mixed act (`neverBest_iff_strictlyDominated`), derived
here from Gordan's alternative (`Matrix.gordan`).

The motivating examples are stated as the paper states them: the explorer's cyclic judgments
(§2, §7), the Ellsberg urn with the coin-flip weights of Raiffa's comment (§3;
[ellsberg-1961]), and the World Cup judgments of [kraft-pratt-seidenberg-1959] (§4), whose
non-representability is [holliday-icard-2013]'s Theorem 8 example. In each, the subject's
preferred act is dominated by a single pure act that pays the same in every state without
the cost.

## Implementation notes

* Judgments are a finite family of compared pairs with a `Finset` of strict indices, the
  paper's `E ⊆ ℘(Ω) × ℘(Ω)` with `X` and `Y`; `X ≠ ∅` is a hypothesis where the paper assumes
  it. A pure act picks a side of each pair, so the paper's `Σ` is `ι → Bool`.
* The pure acts against nature form a `DecisionProblem` (`Core/Probability/Decision`) whose
  prior is the belief's singleton masses. Mixed acts and beliefs are both probability
  measures, read on their real masses at singletons, and `Q★` is the uniform measure on the
  preferred acts.
* In the refutation direction of the Main Lemma the better mixed act is the pushforward of
  `Q★` along a change of one coordinate rather than the paper's half mixture.
* The explorer's preferred act is dominated by the pure act gambling on the other side of
  each comparison, as well as by the paper's mixture of its three other rows.

## References

* [icard-2016]
* [pearce-1984]
* [davidson-mckinsey-suppes-1955]
* [ellsberg-1961]
* [raiffa-1961]
* [kraft-pratt-seidenberg-1959]
* [holliday-icard-2013]
-/

@[expose] public section

namespace Icard2016

open ComparativeProbability MeasureTheory ProbabilityTheory
open scoped Matrix

variable {Ω : Type*} [Fintype Ω]

/-! ### Decision problems against nature -/

section Game

variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

variable (U : A → Ω → ℝ)

/-- The payoff of the mixed act `μ` in state `ω`, for the payoff table `U`. -/
noncomputable def mixedPayoff (μ : Measure A) (ω : Ω) : ℝ := ∑ a, μ.real {a} * U a ω

omit [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
@[simp] theorem mixedPayoff_dirac (a : A) (ω : Ω) :
    mixedPayoff U (Measure.dirac a) ω = U a ω := by
  classical
  simp [mixedPayoff, measureReal_def, Set.indicator_apply, apply_ite ENNReal.toReal, ite_mul]

omit [MeasurableSingletonClass Ω] in
/-- The decision problem against nature with payoff table `U` and belief `P`. -/
noncomputable def toDecisionProblem (P : Measure Ω) :
    Core.DecisionTheory.DecisionProblem ℝ Ω A :=
  ⟨fun ω a ↦ U a ω, fun ω ↦ P.real {ω}⟩

omit [MeasurableSingletonClass Ω] in
/-- The expected utility of the mixed act `μ` under the belief `P` is the `μ`-average of the
pure acts' expected utilities in the decision problem. -/
noncomputable def expectedUtility (P : Measure Ω) (μ : Measure A) : ℝ :=
  ∑ a, μ.real {a} * (toDecisionProblem U P).expectedUtility a

omit [MeasurableSingletonClass Ω] [MeasurableSingletonClass A] in
theorem expectedUtility_eq_sum (P : Measure Ω) (μ : Measure A) :
    expectedUtility U P μ = ∑ a, μ.real {a} * ∑ ω, P.real {ω} * U a ω := rfl

omit [MeasurableSingletonClass Ω] [MeasurableSingletonClass A] in
/-- Expected utility is the belief-average of the state payoffs. -/
theorem expectedUtility_eq (P : Measure Ω) (μ : Measure A) :
    expectedUtility U P μ = ∑ ω, P.real {ω} * mixedPayoff U μ ω := by
  simp only [expectedUtility, Core.DecisionTheory.DecisionProblem.expectedUtility,
    toDecisionProblem, mixedPayoff, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun ω _ ↦ by ring

omit [MeasurableSingletonClass Ω] in
/-- `μ` maximizes `P`-expected utility among the mixed acts. -/
def MaximizesEU (P : Measure Ω) (μ : Measure A) : Prop :=
  ∀ ν, IsProbabilityMeasure ν → expectedUtility U P ν ≤ expectedUtility U P μ

omit [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- `μ` is strictly dominated when some mixed act pays more in every state. -/
def StrictlyDominated (μ : Measure A) : Prop :=
  ∃ ν : Measure A, IsProbabilityMeasure ν ∧ ∀ ω, mixedPayoff U μ ω < mixedPayoff U ν ω

/-- Some state carries positive belief. -/
theorem exists_pos_singleton (P : Measure Ω) [IsProbabilityMeasure P] : ∃ ω, 0 < P.real {ω} := by
  by_contra hall
  push Not at hall
  have := sum_measureReal_singleton_eq_one P
  have : ∑ ω, P.real {ω} ≤ 0 := Finset.sum_nonpos fun ω _ ↦ hall ω
  linarith

omit [MeasurableSingletonClass A] in
/-- A strictly dominated act has smaller expected utility under every belief. -/
theorem expectedUtility_lt_of_forall_lt (P : Measure Ω) [IsProbabilityMeasure P]
    {μ ν : Measure A} (h : ∀ ω, mixedPayoff U μ ω < mixedPayoff U ν ω) :
    expectedUtility U P μ < expectedUtility U P ν := by
  rw [expectedUtility_eq, expectedUtility_eq]
  obtain ⟨ω₀, hω₀⟩ := exists_pos_singleton P
  exact Finset.sum_lt_sum (fun ω _ ↦ mul_le_mul_of_nonneg_left (h ω).le measureReal_nonneg)
    ⟨ω₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (h ω₀) hω₀⟩

/-- **Pearce's lemma** ([pearce-1984], Lemma 3, folklore in game theory): in a finite decision
problem against nature, a mixed act is a best response to no belief iff it is strictly
dominated by a mixed act. The dominating mixture comes from Gordan's alternative applied to
the excess payoffs of the pure acts over `σ`. -/
theorem neverBest_iff_strictlyDominated (σ : Measure A) [IsProbabilityMeasure σ] :
    (∀ P : Measure Ω, IsProbabilityMeasure P →
        ∃ ν : Measure A, IsProbabilityMeasure ν ∧ expectedUtility U P σ < expectedUtility U P ν) ↔
      StrictlyDominated U σ := by
  constructor
  · intro hnb
    let D : Matrix A Ω ℝ := .of fun a ω ↦ U a ω - mixedPayoff U σ ω
    rcases Matrix.gordan D with ⟨y, hy, hpos⟩ | ⟨x, hx, hx1, hxM⟩
    · rcases isEmpty_or_nonempty Ω with hΩ | hne
      · exact ⟨σ, inferInstance, fun ω ↦ (IsEmpty.false ω).elim⟩
      obtain ⟨ω₁⟩ := hne
      have hs : 0 < ∑ a, y a := by
        by_contra hle
        have hzero : ∀ a, y a = 0 := fun a ↦ le_antisymm
          (by linarith [Finset.single_le_sum (fun a _ ↦ hy a) (Finset.mem_univ a)]) (hy a)
        have := hpos ω₁
        simp [Matrix.vecMul, dotProduct, hzero] at this
      have hw (a : A) : 0 ≤ y a * (∑ a, y a)⁻¹ := mul_nonneg (hy a) (inv_nonneg.2 hs.le)
      let ν : Measure A := ∑ a, ENNReal.ofReal (y a * (∑ a, y a)⁻¹) • Measure.dirac a
      have := Measure.isProbabilityMeasure_sum_ofReal_smul_dirac hw
        (by rw [← Finset.sum_mul, mul_inv_cancel₀ hs.ne'])
      have hν (a : A) : ν.real {a} = y a * (∑ a, y a)⁻¹ := by
        classical
        simp [ν, Measure.sum_ofReal_smul_dirac_real_apply hw, Set.indicator_apply]
      refine ⟨ν, this, fun ω ↦ ?_⟩
      have key : mixedPayoff U ν ω - mixedPayoff U σ ω = (∑ a, y a)⁻¹ * (y ᵥ* D) ω := by
        have h1 : mixedPayoff U σ ω = ∑ a, ν.real {a} * mixedPayoff U σ ω := by
          rw [← Finset.sum_mul, sum_measureReal_singleton_eq_one, one_mul]
        rw [mixedPayoff, h1, ← Finset.sum_sub_distrib, Matrix.vecMul, dotProduct, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        simp only [hν, D, Matrix.of_apply]
        ring
      rw [← sub_pos, key]
      exact mul_pos (inv_pos.2 hs) (hpos ω)
    · let P : Measure Ω := ∑ ω, ENNReal.ofReal (x ω) • Measure.dirac ω
      have hP1 := Measure.isProbabilityMeasure_sum_ofReal_smul_dirac hx hx1
      obtain ⟨ν, hν1, hν⟩ := hnb P hP1
      refine absurd hν (not_lt.2 ?_)
      have hP (ω : Ω) : P.real {ω} = x ω := by
        classical
        simp [P, Measure.sum_ofReal_smul_dirac_real_apply hx, Set.indicator_apply]
      have hexp : ∀ a, ∑ ω, P.real {ω} * D a ω ≤ 0 := fun a ↦
        calc ∑ ω, P.real {ω} * D a ω = (D *ᵥ x) a :=
              Finset.sum_congr rfl fun ω _ ↦ by rw [hP, mul_comm]
          _ ≤ 0 := hxM a
      rw [← sub_nonpos]
      calc expectedUtility U P ν - expectedUtility U P σ
          = ∑ a, ν.real {a} * ∑ ω, P.real {ω} * D a ω := by
            rw [expectedUtility_eq_sum, show expectedUtility U P σ =
              ∑ a, ν.real {a} * expectedUtility U P σ by
                rw [← Finset.sum_mul, sum_measureReal_singleton_eq_one, one_mul],
              ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun a _ ↦ ?_
            rw [← mul_sub, expectedUtility_eq, ← Finset.sum_sub_distrib]
            congr 1
            exact Finset.sum_congr rfl fun ω _ ↦ by simp only [D, Matrix.of_apply]; ring
        _ ≤ 0 := Finset.sum_nonpos fun a _ ↦
            mul_nonpos_iff.2 (Or.inl ⟨measureReal_nonneg, hexp a⟩)
  · rintro ⟨ν, hν1, hν⟩ P hP
    exact ⟨ν, hν1, expectedUtility_lt_of_forall_lt U P hν⟩

end Game

/-! ### Judgments and the canonical decision problem -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A subject's comparative judgments judge, for each compared pair `(left i, right i)` of
events, `left i` strictly more likely when `i ∈ strict` and the two equally likely
otherwise. -/
structure Judgments (Ω ι : Type*) where
  /-- The event on the left of comparison `i`. -/
  left : ι → Set Ω
  /-- The event on the right of comparison `i`. -/
  right : ι → Set Ω
  /-- The comparisons judged strict, the paper's `X`. -/
  strict : Finset ι

/-- A pure act picks, for each compared pair, the side it gambles on, `true` for `left`. -/
abbrev Act (ι : Type*) := ι → Bool

/-- The stakes of the canonical decision problem are a positive weight and a pair of utilities,
good above bad, for each comparison. -/
structure Stakes (ι : Type*) where
  /-- The weight of comparison `i`. -/
  weight : ι → ℝ
  /-- The utility of the good outcome of comparison `i`. -/
  good : ι → ℝ
  /-- The utility of the bad outcome of comparison `i`. -/
  bad : ι → ℝ
  weight_pos : ∀ i, 0 < weight i
  bad_lt_good : ∀ i, bad i < good i

namespace Judgments

variable (J : Judgments Ω ι)

omit [Fintype Ω] [Fintype ι] [DecidableEq ι] in
/-- The event on side `t` of comparison `i`. -/
def side (i : ι) : Bool → Set Ω
  | true => J.left i
  | false => J.right i

omit [Fintype Ω] [Fintype ι] [DecidableEq ι] in
/-- The acts the subject prefers, the paper's `Σ★`, are those gambling on the left of every
strict comparison. -/
def Preferred (φ : Act ι) : Prop := ∀ i ∈ J.strict, φ i = true

omit [Fintype Ω] [Fintype ι] [DecidableEq ι] in
instance : DecidablePred J.Preferred := fun _ ↦ Finset.decidableDforallFinset

omit [Fintype Ω] [Fintype ι] [DecidableEq ι] in
theorem preferred_const_true : J.Preferred fun _ ↦ true := fun _ _ ↦ rfl

omit [Fintype Ω] [Fintype ι] [DecidableEq ι] in
theorem not_preferred_const_false (hX : J.strict.Nonempty) : ¬J.Preferred fun _ ↦ false :=
  fun h ↦ let ⟨i, hi⟩ := hX; Bool.false_ne_true (h i hi)

omit [Fintype Ω] [DecidableEq ι] in
open scoped Classical in
/-- The preutility of act `φ` in state `ω` is the weighted payoff of its gambles. -/
noncomputable def preutility (s : Stakes ι) (φ : Act ι) (ω : Ω) : ℝ :=
  ∑ i, s.weight i * if ω ∈ J.side i (φ i) then s.good i else s.bad i

omit [Fintype Ω] [DecidableEq ι] in
/-- The canonical decision problem `D_{w,c}` charges the preferred acts the cost `c`. -/
noncomputable def utility (s : Stakes ι) (c : ℝ) (φ : Act ι) (ω : Ω) : ℝ :=
  J.preutility s φ ω - if J.Preferred φ then c else 0

omit [Fintype Ω] [DecidableEq ι] in
/-- The number of preferred acts. -/
def preferredCard : ℕ := (Finset.univ.filter J.Preferred).card

omit [Fintype Ω] in
theorem preferredCard_pos : 0 < J.preferredCard :=
  Finset.card_pos.2 ⟨fun _ ↦ true, Finset.mem_filter.2 ⟨Finset.mem_univ _, J.preferred_const_true⟩⟩

omit [Fintype Ω] [DecidableEq ι] in
/-- The uniform mixture `Q★` over the preferred acts. -/
noncomputable def uniformPreferred : Measure (Act ι) :=
  uniformOn ↑(Finset.univ.filter J.Preferred)

omit [Fintype Ω] [DecidableEq ι] in
instance : IsProbabilityMeasure J.uniformPreferred :=
  isProbabilityMeasure_uniformOn (Finset.finite_toSet _)
    ⟨fun _ ↦ true, by simpa using J.preferred_const_true⟩

omit [Fintype Ω] in
theorem uniformPreferred_real_singleton (φ : Act ι) :
    J.uniformPreferred.real {φ} = if J.Preferred φ then 1 / (J.preferredCard : ℝ) else 0 := by
  rw [measureReal_def, uniformPreferred, uniformOn_finset_apply_singleton]
  by_cases h : J.Preferred φ <;> simp [h, preferredCard]

variable [MeasurableSpace Ω]

omit [Fintype Ω] [Fintype ι] [DecidableEq ι] in
/-- `P` represents the judgments when strict comparisons hold strictly and indifferences as
equalities. -/
def Represents (P : Measure Ω) : Prop :=
  ∀ i, (i ∈ J.strict → P (J.right i) < P (J.left i)) ∧
    (i ∉ J.strict → P (J.left i) = P (J.right i))

omit [Fintype Ω] [Fintype ι] [DecidableEq ι] in
/-- The judgments are probabilistically representable. -/
def Representable : Prop := ∃ P : Measure Ω, IsProbabilityMeasure P ∧ J.Represents P

/-! ### The Main Lemma -/

section MainLemma

variable [MeasurableSingletonClass Ω] (s : Stakes ι) (P : Measure Ω)

omit [Fintype Ω] [MeasurableSingletonClass Ω] [Fintype ι] [DecidableEq ι] in
/-- The `P`-expected payoff of the unit gamble on side `t` of comparison `i`, the paper's
`b_{E_i}` and `b_{F_i}`. -/
noncomputable def sideValue (i : ι) (t : Bool) : ℝ :=
  P.real (J.side i t) * s.good i + (1 - P.real (J.side i t)) * s.bad i

omit [Fintype Ω] [MeasurableSingletonClass Ω] [Fintype ι] [DecidableEq ι] in
theorem sideValue_true_sub_false (i : ι) :
    J.sideValue s P i true - J.sideValue s P i false =
      (P.real (J.left i) - P.real (J.right i)) * (s.good i - s.bad i) := by
  simp only [sideValue, side]; ring

variable [IsProbabilityMeasure P]

omit [Fintype ι] [DecidableEq ι] in
open scoped Classical in
private theorem sum_mu_ite (A : Set Ω) (a b : ℝ) :
    ∑ ω, P.real {ω} * (if ω ∈ A then a else b) = P.real A * a + (1 - P.real A) * b := by
  classical
  have h1 : ∑ ω, P.real {ω} = 1 := sum_measureReal_singleton_eq_one P
  have h2 : ∑ ω, (if ω ∈ A then P.real {ω} else 0) = P.real A := by
    rw [← Finset.sum_filter, sum_measureReal_singleton]
    congr 1
    ext ω; simp
  calc ∑ ω, P.real {ω} * (if ω ∈ A then a else b)
      = ∑ ω, ((if ω ∈ A then P.real {ω} else 0) * (a - b) + P.real {ω} * b) := by
        refine Finset.sum_congr rfl fun ω _ ↦ ?_
        split_ifs <;> ring
    _ = P.real A * a + (1 - P.real A) * b := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, h1, h2]; ring

omit [DecidableEq ι] in
open scoped Classical in
/-- The expected utility of a pure act is its weighted side values less the cost. -/
theorem sum_mu_utility (c : ℝ) (φ : Act ι) :
    ∑ ω, P.real {ω} * J.utility s c φ ω =
      ∑ i, s.weight i * J.sideValue s P i (φ i) - if J.Preferred φ then c else 0 := by
  simp only [utility, mul_sub, Finset.sum_sub_distrib]
  congr 1
  · simp only [preutility, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [show ∑ ω, P.real {ω} * (s.weight i * if ω ∈ J.side i (φ i) then s.good i else s.bad i) =
        s.weight i * ∑ ω, P.real {ω} * if ω ∈ J.side i (φ i) then s.good i else s.bad i by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun ω _ ↦ by ring]
    rw [sum_mu_ite]
    rfl
  · rw [← Finset.sum_mul, sum_measureReal_singleton_eq_one, one_mul]

theorem expectedUtility_eq (c : ℝ) (μ : Measure (Act ι)) :
    expectedUtility (J.utility s c) P μ =
      ∑ φ, μ.real {φ} *
        (∑ i, s.weight i * J.sideValue s P i (φ i) - if J.Preferred φ then c else 0) := by
  rw [expectedUtility_eq_sum]
  exact Finset.sum_congr rfl fun φ _ ↦ by rw [J.sum_mu_utility]

omit [Fintype Ω] [MeasurableSingletonClass Ω] [DecidableEq ι] [IsProbabilityMeasure P] in
/-- The value of the preferred acts before the cost. -/
noncomputable def preferredValue : ℝ := ∑ i, s.weight i * J.sideValue s P i true

omit [Fintype Ω] [MeasurableSingletonClass Ω] [Fintype ι] [DecidableEq ι]
  [IsProbabilityMeasure P] in
theorem sideValue_eq_of_represents (hP : J.Represents P) {i : ι} (hi : i ∉ J.strict)
    (t : Bool) :
    J.sideValue s P i t = J.sideValue s P i true := by
  cases t
  · have := J.sideValue_true_sub_false s P i
    rw [measureReal_def, measureReal_def, (hP i).2 hi, sub_self, zero_mul] at this
    linarith
  · rfl

omit [Fintype Ω] [MeasurableSingletonClass Ω] [Fintype ι] [DecidableEq ι] in
theorem sideValue_false_lt_true_of_represents (hP : J.Represents P) {i : ι}
    (hi : i ∈ J.strict) : J.sideValue s P i false < J.sideValue s P i true := by
  have := J.sideValue_true_sub_false s P i
  have hlt : P.real (J.right i) < P.real (J.left i) :=
    (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).2 ((hP i).1 hi)
  have hu := s.bad_lt_good i
  nlinarith

omit [Fintype Ω] [MeasurableSingletonClass Ω] [Fintype ι] [DecidableEq ι]
  [IsProbabilityMeasure P] in
/-- The margin by which the preferred acts beat any deviation on a strict comparison. -/
noncomputable def margin (hX : J.strict.Nonempty) : ℝ :=
  J.strict.inf' hX fun i ↦ s.weight i * (J.sideValue s P i true - J.sideValue s P i false)

omit [Fintype Ω] [MeasurableSingletonClass Ω] [Fintype ι] [DecidableEq ι] in
theorem margin_pos (hP : J.Represents P) (hX : J.strict.Nonempty) : 0 < J.margin s P hX := by
  rw [margin, Finset.lt_inf'_iff]
  intro i hi
  exact mul_pos (s.weight_pos i) (sub_pos.2 (J.sideValue_false_lt_true_of_represents s P hP hi))

omit [Fintype Ω] [MeasurableSingletonClass Ω] [Fintype ι] [DecidableEq ι]
  [IsProbabilityMeasure P] in
theorem margin_le (hX : J.strict.Nonempty) {i : ι} (hi : i ∈ J.strict) :
    J.margin s P hX ≤ s.weight i * (J.sideValue s P i true - J.sideValue s P i false) :=
  Finset.inf'_le _ hi

omit [Fintype Ω] [MeasurableSingletonClass Ω] [IsProbabilityMeasure P] in
/-- A preferred act is worth the preferred value under a representing measure. -/
theorem pureValue_of_preferred (hP : J.Represents P) {φ : Act ι} (hφ : J.Preferred φ) :
    ∑ i, s.weight i * J.sideValue s P i (φ i) = J.preferredValue s P := by
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases hi : i ∈ J.strict
  · rw [hφ i hi]
  · rw [J.sideValue_eq_of_represents s P hP hi]

omit [Fintype Ω] [MeasurableSingletonClass Ω] in
/-- A non-preferred act loses at least the margin under a representing measure. -/
theorem pureValue_le_of_not_preferred (hP : J.Represents P) (hX : J.strict.Nonempty)
    {φ : Act ι} (hφ : ¬J.Preferred φ) :
    ∑ i, s.weight i * J.sideValue s P i (φ i) ≤ J.preferredValue s P - J.margin s P hX := by
  simp only [Preferred, not_forall] at hφ
  obtain ⟨h, hh, hfalse⟩ := hφ
  have hfalse' : φ h = false := by simpa using hfalse
  have hle : ∀ i, s.weight i * J.sideValue s P i (φ i) ≤ s.weight i * J.sideValue s P i true := by
    intro i
    refine mul_le_mul_of_nonneg_left ?_ (s.weight_pos i).le
    by_cases hi : i ∈ J.strict
    · cases hφi : φ i
      · exact (J.sideValue_false_lt_true_of_represents s P hP hi).le
      · exact le_rfl
    · rw [J.sideValue_eq_of_represents s P hP hi]
  have hgap : J.margin s P hX ≤
      ∑ i, (s.weight i * J.sideValue s P i true - s.weight i * J.sideValue s P i (φ i)) := by
    refine (J.margin_le s P hX hh).trans ?_
    refine (Finset.single_le_sum (f := fun i ↦
      s.weight i * J.sideValue s P i true - s.weight i * J.sideValue s P i (φ i))
      (fun i _ ↦ sub_nonneg.2 (hle i)) (Finset.mem_univ h)).trans' ?_
    rw [hfalse']; ring_nf; exact le_rfl
  rw [Finset.sum_sub_distrib] at hgap
  unfold preferredValue
  linarith

/-- Under a representing measure the expected utility of a mixed act is at most the preferred
value less the cost, with equality on `Q★`. -/
theorem expectedUtility_le_of_represents (hP : J.Represents P) (hX : J.strict.Nonempty)
    {c : ℝ} (hcm : c ≤ J.margin s P hX) (μ : Measure (Act ι)) [IsProbabilityMeasure μ] :
    expectedUtility (J.utility s c) P μ ≤ J.preferredValue s P - c := by
  rw [J.expectedUtility_eq]
  calc ∑ φ, μ.real {φ} *
        (∑ i, s.weight i * J.sideValue s P i (φ i) - if J.Preferred φ then c else 0)
      ≤ ∑ φ, μ.real {φ} * (J.preferredValue s P - c) := by
        refine Finset.sum_le_sum fun φ _ ↦ mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
        by_cases hφ : J.Preferred φ
        · rw [J.pureValue_of_preferred s P hP hφ, ite_eq_left hφ]
        · rw [ite_eq_right hφ, sub_zero]
          linarith [J.pureValue_le_of_not_preferred s P hP hX hφ]
    _ = J.preferredValue s P - c := by
        rw [← Finset.sum_mul, sum_measureReal_singleton_eq_one, one_mul]

theorem expectedUtility_uniformPreferred_of_represents (hP : J.Represents P) (c : ℝ) :
    expectedUtility (J.utility s c) P J.uniformPreferred = J.preferredValue s P - c := by
  rw [J.expectedUtility_eq]
  have hN : (J.preferredCard : ℝ) ≠ 0 := by exact_mod_cast J.preferredCard_pos.ne'
  calc ∑ φ, J.uniformPreferred.real {φ} *
        (∑ i, s.weight i * J.sideValue s P i (φ i) - if J.Preferred φ then c else 0)
      = ∑ φ, if J.Preferred φ then 1 / (J.preferredCard : ℝ) * (J.preferredValue s P - c)
          else 0 := by
        refine Finset.sum_congr rfl fun φ _ ↦ ?_
        rw [J.uniformPreferred_real_singleton]
        by_cases hφ : J.Preferred φ
        · rw [ite_eq_left hφ, ite_eq_left hφ, ite_eq_left hφ, J.pureValue_of_preferred s P hP hφ]
        · simp [hφ]
    _ = J.preferredValue s P - c := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        change (J.preferredCard : ℝ) * _ = _
        field_simp

omit [MeasurableSingletonClass Ω] [IsProbabilityMeasure P] in
/-- The pushforward of `Q★` along a change of one coordinate beats `Q★` when the change never
hurts a preferred act and helps one. -/
theorem expectedUtility_map_gt {c : ℝ} (f : Act ι → Act ι)
    (hle : ∀ φ, J.Preferred φ →
      ∑ ω, P.real {ω} * J.utility s c φ ω ≤ ∑ ω, P.real {ω} * J.utility s c (f φ) ω)
    (hlt : ∃ φ, J.Preferred φ ∧
      ∑ ω, P.real {ω} * J.utility s c φ ω < ∑ ω, P.real {ω} * J.utility s c (f φ) ω) :
    expectedUtility (J.utility s c) P J.uniformPreferred <
      expectedUtility (J.utility s c) P (J.uniformPreferred.map f) := by
  classical
  have hmap : expectedUtility (J.utility s c) P (J.uniformPreferred.map f) =
      ∑ φ, J.uniformPreferred.real {φ} * ∑ ω, P.real {ω} * J.utility s c (f φ) ω := by
    rw [expectedUtility_eq_sum]
    have : ∀ ψ, (J.uniformPreferred.map f).real {ψ} =
        ∑ φ ∈ Finset.univ.filter (fun φ ↦ f φ = ψ), J.uniformPreferred.real {φ} := fun ψ ↦ by
      rw [map_measureReal_apply .of_discrete (.singleton ψ), sum_measureReal_singleton]
      congr 1
      ext φ; simp
    simp only [this, Finset.sum_mul]
    conv_rhs => rw [← Finset.sum_fiberwise Finset.univ f]
    refine Finset.sum_congr rfl fun ψ _ ↦ Finset.sum_congr rfl fun φ hφ ↦ ?_
    rw [(Finset.mem_filter.1 hφ).2]
  rw [hmap, expectedUtility_eq_sum]
  obtain ⟨φ₀, hφ₀, hlt₀⟩ := hlt
  refine Finset.sum_lt_sum (fun φ _ ↦ ?_) ⟨φ₀, Finset.mem_univ _, ?_⟩
  · by_cases hφ : J.Preferred φ
    · exact mul_le_mul_of_nonneg_left (hle φ hφ) measureReal_nonneg
    · rw [J.uniformPreferred_real_singleton, ite_eq_right hφ, zero_mul, zero_mul]
  · refine mul_lt_mul_of_pos_left hlt₀ ?_
    rw [J.uniformPreferred_real_singleton, ite_eq_left hφ₀]
    have : (0 : ℝ) < J.preferredCard := by exact_mod_cast J.preferredCard_pos
    exact div_pos one_pos this

/-- **Main Lemma** (Lemma 1). A measure represents the judgments iff, for some cost, the
uniform preferred act maximizes its expected utility in the canonical decision problem. -/
theorem represents_iff_maximizes (hX : J.strict.Nonempty) :
    J.Represents P ↔ ∃ c, 0 < c ∧ MaximizesEU (J.utility s c) P J.uniformPreferred := by
  constructor
  · intro hP
    refine ⟨J.margin s P hX, J.margin_pos s P hP hX, fun ν _ ↦ ?_⟩
    rw [J.expectedUtility_uniformPreferred_of_represents s P hP]
    exact J.expectedUtility_le_of_represents s P hP hX le_rfl ν
  · rintro ⟨c, hc, hmax⟩ i
    have hval : ∀ φ t, ∑ ω, P.real {ω} * J.utility s c (Function.update φ i t) ω -
        ∑ ω, P.real {ω} * J.utility s c φ ω =
        s.weight i * (J.sideValue s P i t - J.sideValue s P i (φ i)) -
          ((if J.Preferred (Function.update φ i t) then c else 0) -
            if J.Preferred φ then c else 0) := by
      intro φ t
      rw [J.sum_mu_utility, J.sum_mu_utility]
      have : ∑ j, s.weight j * J.sideValue s P j (Function.update φ i t j) -
          ∑ j, s.weight j * J.sideValue s P j (φ j) =
          s.weight i * (J.sideValue s P i t - J.sideValue s P i (φ i)) := by
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
        · rw [Function.update_self, mul_sub]
        · intro j _ hj; rw [Function.update_of_ne hj, sub_self]
        · intro h; exact absurd (Finset.mem_univ i) h
      rw [← this]
      ring
    constructor
    · intro hi
      rw [← ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _),
        ← measureReal_def, ← measureReal_def]
      by_contra hge
      push Not at hge
      -- flipping a strict comparison drops the cost and loses nothing
      have hgain : ∀ φ, J.Preferred φ → ∑ ω, P.real {ω} * J.utility s c φ ω <
          ∑ ω, P.real {ω} * J.utility s c (Function.update φ i false) ω := by
        intro φ hφ
        have hnot : ¬J.Preferred (Function.update φ i false) := fun h ↦ by
          have := h i hi; simp at this
        have hdiff := J.sideValue_true_sub_false s P i
        have hu := s.bad_lt_good i
        have hw := s.weight_pos i
        have := hval φ false
        rw [ite_eq_right hnot, ite_eq_left hφ, hφ i hi] at this
        have h1 : 0 ≤ J.sideValue s P i false - J.sideValue s P i true := by nlinarith
        have h2 := mul_nonneg hw.le h1
        linarith
      exact absurd (hmax (J.uniformPreferred.map fun φ ↦ Function.update φ i false) inferInstance)
        (not_le.2 (J.expectedUtility_map_gt s P _ (fun φ hφ ↦ (hgain φ hφ).le)
          ⟨_, J.preferred_const_true, hgain _ J.preferred_const_true⟩))
    · intro hi
      rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _),
        ← measureReal_def, ← measureReal_def]
      by_contra hne
      -- moving an indifferent comparison to its likelier side keeps the cost and gains
      have hpref : ∀ φ t, J.Preferred φ → J.Preferred (Function.update φ i t) := by
        intro φ t hφ j hj
        rw [Function.update_of_ne fun (h : j = i) ↦ hi (h ▸ hj)]
        exact hφ j hj
      obtain ⟨t, ht⟩ : ∃ t, J.sideValue s P i (!t) < J.sideValue s P i t := by
        have hdiff := J.sideValue_true_sub_false s P i
        have hu := s.bad_lt_good i
        rcases lt_or_gt_of_ne hne with h | h
        · exact ⟨false, by simp only [Bool.not_false]; nlinarith⟩
        · exact ⟨true, by simp only [Bool.not_true]; nlinarith⟩
      have hgain : ∀ φ, J.Preferred φ → ∑ ω, P.real {ω} * J.utility s c φ ω ≤
          ∑ ω, P.real {ω} * J.utility s c (Function.update φ i t) ω := by
        intro φ hφ
        have := hval φ t
        rw [ite_eq_left (hpref φ t hφ), ite_eq_left hφ, sub_self, sub_zero] at this
        have hw := s.weight_pos i
        have hle : J.sideValue s P i (φ i) ≤ J.sideValue s P i t := by
          by_cases hφt : φ i = t
          · rw [hφt]
          · have : φ i = !t := by cases t <;> cases hφi : φ i <;> simp_all
            rw [this]; exact ht.le
        nlinarith
      have hstrict : ∑ ω, P.real {ω} * J.utility s c (Function.update (fun _ ↦ true) i (!t)) ω <
          ∑ ω, P.real {ω} * J.utility s c
            (Function.update (Function.update (fun _ ↦ true) i (!t)) i t) ω := by
        have hφ := hpref _ (!t) J.preferred_const_true
        have := hval (Function.update (fun _ ↦ true) i (!t)) t
        rw [ite_eq_left (hpref _ t hφ), ite_eq_left hφ, sub_self, sub_zero,
          Function.update_self] at this
        have hw := s.weight_pos i
        nlinarith
      exact absurd (hmax (J.uniformPreferred.map fun φ ↦ Function.update φ i t) inferInstance)
        (not_le.2 (J.expectedUtility_map_gt s P _ hgain
          ⟨_, hpref _ (!t) J.preferred_const_true, hstrict⟩))

end MainLemma

/-! ### Theorem 1 -/

/-- **Theorem 1.** The judgments are probabilistically representable iff, for some cost, the
uniform preferred act `Q★` is not strictly dominated in the canonical decision problem. -/
theorem representable_iff_exists_not_dominated [MeasurableSingletonClass Ω] (s : Stakes ι)
    (hX : J.strict.Nonempty) :
    J.Representable ↔ ∃ c, 0 < c ∧ ¬StrictlyDominated (J.utility s c) J.uniformPreferred := by
  constructor
  · rintro ⟨P, hP1, hP⟩
    obtain ⟨c, hc, hmax⟩ := (J.represents_iff_maximizes s P hX).1 hP
    refine ⟨c, hc, fun ⟨ν, hν1, hν⟩ ↦ ?_⟩
    exact absurd (hmax ν hν1) (not_le.2 (expectedUtility_lt_of_forall_lt _ P hν))
  · rintro ⟨c, hc, hnd⟩
    rw [← neverBest_iff_strictlyDominated] at hnd
    push Not at hnd
    obtain ⟨P, hP1, hP⟩ := hnd
    exact ⟨P, hP1, (J.represents_iff_maximizes s P hX).2 ⟨c, hc, hP⟩⟩

end Judgments

/-! ### The examples -/

/-- Unit weights and a unit good outcome, the stakes of the explorer and the World Cup. -/
noncomputable def unitStakes (ι : Type*) : Stakes ι :=
  ⟨fun _ ↦ 1, fun _ ↦ 1, fun _ ↦ 0, fun _ ↦ one_pos, fun _ ↦ one_pos⟩

omit [Fintype Ω] in
/-- When every comparison is strict, `Q★` is the single act gambling on every left side. -/
theorem mixedPayoff_uniformPreferred_of_strict_eq_univ (J : Judgments Ω ι)
    (h : J.strict = Finset.univ) (U : Act ι → Ω → ℝ) (ω : Ω) :
    mixedPayoff U J.uniformPreferred ω = U (fun _ ↦ true) ω := by
  have hpref : ∀ φ, J.Preferred φ ↔ φ = fun _ ↦ true := fun φ ↦
    ⟨fun hφ ↦ funext fun i ↦ hφ i (h ▸ Finset.mem_univ i), fun hφ i _ ↦ by rw [hφ]⟩
  have hcard : J.preferredCard = 1 := by
    rw [Judgments.preferredCard, Finset.filter_congr fun φ _ ↦ hpref φ, Finset.filter_eq',
      ite_eq_left (Finset.mem_univ _), Finset.card_singleton]
  simp only [mixedPayoff, Judgments.uniformPreferred_real_singleton, hpref, hcard, Nat.cast_one,
    div_one, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The explorer of §1 judges the treasure likelier on `A` than `B`, on `B` than `C`, and on
`C` than `A`. -/
def explorer : Judgments (Fin 3) (Fin 3) :=
  ⟨![{0}, {1}, {2}], ![{1}, {2}, {0}], Finset.univ⟩

/-- Cyclic judgments are not representable. -/
theorem explorer_not_representable : ¬explorer.Representable := by
  rintro ⟨P, -, hP⟩
  have h0 := (hP 0).1 (Finset.mem_univ _)
  have h1 := (hP 1).1 (Finset.mem_univ _)
  have h2 := (hP 2).1 (Finset.mem_univ _)
  simp only [explorer] at h0 h1 h2
  simp at h0 h1 h2
  exact lt_irrefl _ ((h2.trans h1).trans h0)

/-- In §7 the explorer's preferred act, which pays `1 - c` on every island, is strictly
dominated, since gambling on the other side of each comparison pays `1` on every island. -/
theorem explorer_dominated {c : ℝ} (hc : 0 < c) :
    StrictlyDominated (explorer.utility (unitStakes (Fin 3)) c) explorer.uniformPreferred := by
  refine ⟨Measure.dirac fun _ ↦ false, inferInstance, fun ω ↦ ?_⟩
  rw [mixedPayoff_uniformPreferred_of_strict_eq_univ explorer rfl, mixedPayoff_dirac]
  simp only [Judgments.utility, ite_eq_left explorer.preferred_const_true,
    ite_eq_right (explorer.not_preferred_const_false ⟨0, Finset.mem_univ _⟩)]
  fin_cases ω <;> simp [Judgments.preutility, Judgments.side, explorer, unitStakes,
    Fin.sum_univ_three, -Finset.sum_boole] <;> linarith

/-- The Ellsberg urn of §3 ([ellsberg-1961]): red is judged likelier than black, and black
or yellow likelier than red or yellow. -/
def ellsberg : Judgments (Fin 3) (Fin 2) :=
  ⟨![{0}, {1, 2}], ![{1}, {0, 2}], Finset.univ⟩

/-- The coin-flip weights of Raiffa's comment ([raiffa-1961]), with a hundred utiles at stake. -/
noncomputable def coinStakes : Stakes (Fin 2) :=
  ⟨fun _ ↦ 1 / 2, fun _ ↦ 100, fun _ ↦ 0, fun _ ↦ by norm_num, fun _ ↦ by norm_num⟩

/-- The Ellsberg judgments are not representable. -/
theorem ellsberg_not_representable : ¬ellsberg.Representable := by
  rintro ⟨P, _, hP⟩
  have pair : ∀ a b : Fin 3, a ≠ b → P {a, b} = P {a} + P {b} := fun a b hab ↦ by
    rw [Set.insert_eq, measure_union (Set.disjoint_singleton.mpr hab) (.singleton b)]
  have h0 := (hP 0).1 (Finset.mem_univ _)
  have h1 := (hP 1).1 (Finset.mem_univ _)
  simp only [ellsberg] at h0 h1
  simp at h0 h1
  rw [pair 1 2 (by decide), pair 0 2 (by decide),
    ENNReal.add_lt_add_iff_right (measure_ne_top P _)] at h1
  exact lt_asymm h0 h1

/-- In Raiffa's argument, option 1, the subject's preferred act, pays `50 - c` whatever the
ball, and option 2 pays `50`. -/
theorem ellsberg_dominated {c : ℝ} (hc : 0 < c) :
    StrictlyDominated (ellsberg.utility coinStakes c) ellsberg.uniformPreferred := by
  refine ⟨Measure.dirac fun _ ↦ false, inferInstance, fun ω ↦ ?_⟩
  rw [mixedPayoff_uniformPreferred_of_strict_eq_univ ellsberg rfl, mixedPayoff_dirac]
  simp only [Judgments.utility, ite_eq_left ellsberg.preferred_const_true,
    ite_eq_right (ellsberg.not_preferred_const_false ⟨0, Finset.mem_univ _⟩)]
  fin_cases ω <;> simp [Judgments.preutility, Judgments.side, ellsberg, coinStakes,
    Fin.sum_univ_two, -Finset.sum_boole] <;> linarith

/-- The World Cup judgments of §4, with Argentina, Brazil, China, Denmark and England as the
worlds `0`–`4`: Denmark over Argentina or China, Argentina or England over China or Denmark,
Brazil or China over Argentina or Denmark, and Argentina, China or Denmark over Brazil or
England. -/
def worldCup : Judgments (Fin 5) (Fin 4) :=
  ⟨![{3}, {0, 4}, {1, 2}, {0, 2, 3}], ![{0, 2}, {2, 3}, {0, 3}, {1, 4}], Finset.univ⟩

/-- The World Cup judgments are not representable, since they are the Kraft–Pratt–Seidenberg
comparisons, which no finite measure satisfies
(`HollidayIcard2013.worldCup_not_finitelyAdditive`). -/
theorem worldCup_not_representable : ¬worldCup.Representable := by
  rintro ⟨P, _, hP⟩
  refine HollidayIcard2013.worldCup_not_finitelyAdditive P ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨((hP 1).1 (Finset.mem_univ _)).le, not_le.2 ((hP 1).1 (Finset.mem_univ _))⟩
  · exact ⟨((hP 2).1 (Finset.mem_univ _)).le, not_le.2 ((hP 2).1 (Finset.mem_univ _))⟩
  · exact ⟨((hP 0).1 (Finset.mem_univ _)).le, not_le.2 ((hP 0).1 (Finset.mem_univ _))⟩
  · exact ⟨((hP 3).1 (Finset.mem_univ _)).le, not_le.2 ((hP 3).1 (Finset.mem_univ _))⟩

/-- In §4's system of bets, trading the four preferred gambles for the four others changes
nothing whichever team wins, so paying for the trade is strict dominance. -/
theorem worldCup_dominated {c : ℝ} (hc : 0 < c) :
    StrictlyDominated (worldCup.utility (unitStakes (Fin 4)) c) worldCup.uniformPreferred := by
  refine ⟨Measure.dirac fun _ ↦ false, inferInstance, fun ω ↦ ?_⟩
  rw [mixedPayoff_uniformPreferred_of_strict_eq_univ worldCup rfl, mixedPayoff_dirac]
  simp only [Judgments.utility, ite_eq_left worldCup.preferred_const_true,
    ite_eq_right (worldCup.not_preferred_const_false ⟨0, Finset.mem_univ _⟩)]
  fin_cases ω <;> simp [Judgments.preutility, Judgments.side, worldCup, unitStakes,
    Fin.sum_univ_four, -Finset.sum_boole] <;> linarith

end Icard2016
