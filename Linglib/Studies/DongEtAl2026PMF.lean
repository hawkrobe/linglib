import Linglib.Core.Probability.Posterior
import Mathlib.Data.Real.Basic

/-!
# [dong-etal-2026]: the Value-of-Information clarify-or-commit model

A PMF-level formalisation of the decision-theoretic Value of Information
(VoI) framework for adaptive human–agent communication. An agent holds a
belief `b : PMF Θ` over latent user intents and may either **commit** to an
action now or **clarify** by asking a question before committing. The paper
operationalises the choice through the classical Value of Information: ask a
question only when its expected improvement in the downstream decision
outweighs the communication cost.

A question is modelled as an answer kernel `κ : Θ → PMF Y` — the paper's
`p(y ∣ q, θ)`, the distribution of answer `y` were `θ` the true intent. Its
answer marginal `p(y ∣ q, b)` and the updated belief `b_y` are the project's
`PMF.marginal κ b` and `PMF.posterior κ b y`; `weightedPosteriorValue_eq`
identifies the (total) per-answer term used here with `p(y) · V(b_y)`.

## Main definitions

* `EU U b a` — expected utility of committing to action `a` under belief `b`.
* `V U b` — value of acting now, `⨆ a, EU U b a`.
* `Vpost U b κ` — expected value after asking `κ`, `∑' y, p(y) · V(b_y)`.
* `VoI U b κ` — value of information, `Vpost U b κ - V U b`.
* `NetVoI c U b κ` — `VoI` net of the per-question cost `c`.
* `worthAsking c U b κ` — the clarify-or-commit decision, `c < VoI U b κ`.

## Main statements

* `V_le_Vpost` — information never has negative value: `V U b ≤ Vpost U b κ`.
* `V_add_VoI` — `VoI` is the honest increment: `V U b + VoI U b κ = Vpost U b κ`.
* `VoI_smul` — `VoI` is positive-homogeneous in the utility (stakes scale).
* `worthAsking_mono_stakes` — holding belief, question, and cost fixed,
  raising the stakes (scaling the utility) keeps a question worth asking, so
  the commit-without-asking region shrinks as stakes rise. This is the
  *ceteris-paribus mechanism* behind the paper's Mixed-Stakes prediction:
  scaling utility scales `VoI`, so a question clearing a fixed cost at low
  stakes (`U = 1`, guessing an animal) clears it at high stakes (`U = 10`,
  diagnosing a disease). `medical_worth_asking_of_animal` is the named
  instance. The model isolates the utility-scaling mechanism; it does not
  encode the experiments' differing candidate-set sizes or answer models.

## Implementation notes

Utilities are `ℝ≥0∞`-valued so the model lives natively on `PMF`. `VoI` uses
truncated subtraction, but `V_le_Vpost` makes the gap genuine rather than
clipped to `0`. Homogeneity needs only `s ≠ ∞` (via `ENNReal.mul_sub`); no
finiteness of `V`/`Vpost` is assumed, so the core results hold for arbitrary
intent, action, and answer types.

The worth-asking region is the strict `c < VoI U b κ` (equivalently
`0 < NetVoI`), matching the paper's "commit when `max_q NetVoI ≤ 0`" rule.
The cross-question `argmax` selection of the policy is out of scope: the
results here concern the per-question clarify-or-commit decision.

This PMF/`ℝ≥0∞` formulation parallels the `ℝ`-valued expected-information-gain
substrate `Core.Agent.ExperimentDesign.eig` (with value function `V U`):
`V_le_Vpost` is the PMF analogue of `ExperimentDesign.eig_nonneg_of_convex`
and of `TsvilodubEtAl2026.evpi_nonneg`.

`ClarifyRule` is the shared clarify-or-commit decision-rule contract: both
this paper and [tsvilodub-etal-2026] decide clarification from a net
value-of-information signal, this paper through the sharp threshold
`sharpRule` (`worthAsking_iff_sharpRule`), Tsvilodub et al. through a
logistic gate (`TsvilodubEtAl2026.softGateRule`).

## Todo

* Discharge the claim that EVPI (`TsvilodubEtAl2026.evpi`) is the upper
  bound on VoI for any question into a theorem
  `worthAsking c U b κ → c < EVPI`.
* Relate `VoI` / `V_le_Vpost` to `Core.Agent.ExperimentDesign.eig` /
  `eig_nonneg_of_convex` (bridging the `ℝ≥0∞`-on-`PMF` and `ℝ`-on-`Fintype`
  carriers) so the two statements of "information has nonnegative value" become
  one fact.
-/

set_option autoImplicit false

namespace DongEtAl2026

open scoped ENNReal

variable {Θ A Y : Type*}

/-! ### Expected utility and the value of acting now -/

/-- Expected utility of committing to action `a` under belief `b`. -/
noncomputable def EU (U : Θ → A → ℝ≥0∞) (b : PMF Θ) (a : A) : ℝ≥0∞ :=
  ∑' θ, b θ * U θ a

/-- Value of acting now: the best expected utility achievable under `b`. -/
noncomputable def V (U : Θ → A → ℝ≥0∞) (b : PMF Θ) : ℝ≥0∞ :=
  ⨆ a, EU U b a

/-! ### The value of a question -/

/-- Per-answer contribution to the post-question value, written through the
joint `b θ · κ θ y` so it is total — answers with zero marginal contribute
`0` without needing a posterior. Equals `p(y) · V(b_y)` whenever the answer
marginal is non-zero; see `weightedPosteriorValue_eq`. -/
noncomputable def weightedPosteriorValue (U : Θ → A → ℝ≥0∞) (b : PMF Θ)
    (κ : Θ → PMF Y) (y : Y) : ℝ≥0∞ :=
  ⨆ a, ∑' θ, b θ * κ θ y * U θ a

/-- Expected value after asking question `κ` (the per-intent answer model
`p(y ∣ q, θ)`): the answer-marginal expectation of the value of acting on
the resulting posterior belief. -/
noncomputable def Vpost (U : Θ → A → ℝ≥0∞) (b : PMF Θ) (κ : Θ → PMF Y) : ℝ≥0∞ :=
  ∑' y, weightedPosteriorValue U b κ y

/-- Value of information of question `κ`: how much the best achievable
expected utility improves, in expectation, by asking before committing. -/
noncomputable def VoI (U : Θ → A → ℝ≥0∞) (b : PMF Θ) (κ : Θ → PMF Y) : ℝ≥0∞ :=
  Vpost U b κ - V U b

/-- Net value of information: `VoI` minus the per-question communication
cost `c`. -/
noncomputable def NetVoI (c : ℝ≥0∞) (U : Θ → A → ℝ≥0∞) (b : PMF Θ)
    (κ : Θ → PMF Y) : ℝ≥0∞ :=
  VoI U b κ - c

/-- The clarify-or-commit decision: asking `κ` is worth its cost exactly
when its value of information exceeds the communication cost (equivalently
`0 < NetVoI`; see `netVoI_pos_iff_worthAsking`). -/
def worthAsking (c : ℝ≥0∞) (U : Θ → A → ℝ≥0∞) (b : PMF Θ) (κ : Θ → PMF Y) : Prop :=
  c < VoI U b κ

/-- The per-answer term equals the answer probability times the value of
acting on the posterior — the bridge to the project's `PMF.posterior`
substrate (`b_y`) and `PMF.marginal` (`p(y)`). -/
theorem weightedPosteriorValue_eq (U : Θ → A → ℝ≥0∞) (b : PMF Θ)
    (κ : Θ → PMF Y) (y : Y) (h : PMF.marginal κ b y ≠ 0) :
    weightedPosteriorValue U b κ y = PMF.marginal κ b y * V U (PMF.posterior κ b y h) := by
  unfold weightedPosteriorValue V
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun a => ?_
  unfold EU
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun θ => ?_
  rw [← mul_assoc, PMF.marginal_mul_posterior_apply]

/-! ### Information never has negative value -/

/-- **Value of information is nonnegative**: in expectation, the option to
update the belief before acting can only help. The decision-theoretic core
of the framework. -/
theorem V_le_Vpost (U : Θ → A → ℝ≥0∞) (b : PMF Θ) (κ : Θ → PMF Y) :
    V U b ≤ Vpost U b κ := by
  unfold V
  refine iSup_le fun a => ?_
  have key : ∀ θ, b θ * U θ a = ∑' y, b θ * κ θ y * U θ a := fun θ => by
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
  calc EU U b a = ∑' θ, b θ * U θ a := rfl
    _ = ∑' θ, ∑' y, b θ * κ θ y * U θ a := tsum_congr key
    _ = ∑' y, ∑' θ, b θ * κ θ y * U θ a := ENNReal.tsum_comm
    _ ≤ ∑' y, ⨆ a', ∑' θ, b θ * κ θ y * U θ a' :=
        ENNReal.tsum_le_tsum fun y => le_iSup (fun a' => ∑' θ, b θ * κ θ y * U θ a') a
    _ = Vpost U b κ := rfl

/-- `VoI` is the honest gap between acting-now and acting-after-asking, not a
value clipped to `0` by truncated subtraction. -/
theorem V_add_VoI (U : Θ → A → ℝ≥0∞) (b : PMF Θ) (κ : Θ → PMF Y) :
    V U b + VoI U b κ = Vpost U b κ := by
  rw [VoI, add_tsub_cancel_of_le (V_le_Vpost U b κ)]

/-! ### Stakes: positive-homogeneity of the value of information -/

/-- Expected utility is homogeneous of degree one in the utility. -/
@[simp] theorem EU_smul (s : ℝ≥0∞) (U : Θ → A → ℝ≥0∞) (b : PMF Θ) (a : A) :
    EU (s • U) b a = s * EU U b a := by
  unfold EU
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun θ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The value of acting now is homogeneous of degree one in the utility. -/
@[simp] theorem V_smul (s : ℝ≥0∞) (U : Θ → A → ℝ≥0∞) (b : PMF Θ) :
    V (s • U) b = s * V U b := by
  unfold V
  rw [ENNReal.mul_iSup]
  exact iSup_congr fun a => EU_smul s U b a

/-- Each per-answer post-question term is homogeneous of degree one in the
utility. -/
@[simp] theorem weightedPosteriorValue_smul (s : ℝ≥0∞) (U : Θ → A → ℝ≥0∞) (b : PMF Θ)
    (κ : Θ → PMF Y) (y : Y) :
    weightedPosteriorValue (s • U) b κ y = s * weightedPosteriorValue U b κ y := by
  unfold weightedPosteriorValue
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun a => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun θ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The post-question value is homogeneous of degree one in the utility. -/
@[simp] theorem Vpost_smul (s : ℝ≥0∞) (U : Θ → A → ℝ≥0∞) (b : PMF Θ) (κ : Θ → PMF Y) :
    Vpost (s • U) b κ = s * Vpost U b κ := by
  unfold Vpost
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun y => weightedPosteriorValue_smul s U b κ y

/-- Scaling every utility by a finite stakes factor `s` scales the value of
information by `s`: `VoI` is positive-homogeneous of degree one. -/
theorem VoI_smul {s : ℝ≥0∞} (hs : s ≠ ∞) (U : Θ → A → ℝ≥0∞) (b : PMF Θ)
    (κ : Θ → PMF Y) :
    VoI (s • U) b κ = s * VoI U b κ := by
  unfold VoI
  rw [Vpost_smul, V_smul, ENNReal.mul_sub fun _ _ => hs]

/-- The agent's policy is `worthAsking` exactly when net value of information
is positive — the strict side of the paper's `NetVoI ≤ 0` commit rule. -/
theorem netVoI_pos_iff_worthAsking (c : ℝ≥0∞) (U : Θ → A → ℝ≥0∞) (b : PMF Θ)
    (κ : Θ → PMF Y) :
    0 < NetVoI c U b κ ↔ worthAsking c U b κ := by
  rw [NetVoI, worthAsking, tsub_pos_iff_lt]

/-- **Stakes monotonicity**: if a question is worth asking at stakes `s`, it
remains worth asking at any higher (finite) stakes `s'`. Raising the stakes
shrinks the region in which the agent commits without clarifying. -/
theorem worthAsking_mono_stakes {s s' : ℝ≥0∞} (hs : s ≠ ∞) (hs' : s' ≠ ∞)
    (hss' : s ≤ s') (c : ℝ≥0∞) (U : Θ → A → ℝ≥0∞) (b : PMF Θ) (κ : Θ → PMF Y)
    (h : worthAsking c (s • U) b κ) : worthAsking c (s' • U) b κ := by
  rw [worthAsking, VoI_smul hs] at h
  rw [worthAsking, VoI_smul hs']
  exact lt_of_lt_of_le h (by gcongr)

/-- The Mixed-Stakes mechanism, holding belief, question, and cost fixed: a
question worth its cost at low (animal, `U = 1`) stakes is worth its cost at
high (medical, `U = 10`) stakes, because scaling utility scales `VoI`. -/
theorem medical_worth_asking_of_animal (c : ℝ≥0∞) (U : Θ → A → ℝ≥0∞)
    (b : PMF Θ) (κ : Θ → PMF Y) (h : worthAsking c U b κ) :
    worthAsking c ((10 : ℝ≥0∞) • U) b κ := by
  have h1 : worthAsking c ((1 : ℝ≥0∞) • U) b κ := by rwa [one_smul]
  exact worthAsking_mono_stakes ENNReal.one_ne_top ENNReal.ofNat_ne_top (by norm_num)
    c U b κ h1

/-! ### Uninformative questions carry no value -/

/-- A constant answer kernel `fun _ => q` (the answer distribution does not
depend on the true intent `θ`) leaves the post-question value equal to the
value of acting now: the posterior never moves off the prior. The structural
converse of `V_le_Vpost`. -/
theorem Vpost_const_eq_V (U : Θ → A → ℝ≥0∞) (b : PMF Θ) (q : PMF Y) :
    Vpost U b (fun _ => q) = V U b := by
  unfold Vpost weightedPosteriorValue V EU
  have hw : ∀ y, (⨆ a, ∑' θ, b θ * q y * U θ a) = q y * ⨆ a, ∑' θ, b θ * U θ a := by
    intro y
    rw [ENNReal.mul_iSup]
    refine iSup_congr fun a => ?_
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun θ => by ring
  simp_rw [hw]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- An uninformative question has zero value of information. -/
theorem VoI_const_eq_zero (U : Θ → A → ℝ≥0∞) (b : PMF Θ) (q : PMF Y) :
    VoI U b (fun _ => q) = 0 := by
  rw [VoI, Vpost_const_eq_V, tsub_self]

/-- **Negative test**: an uninformative question is never worth asking, for
any cost `c` (including `c = 0`). Truncated subtraction does not manufacture
spurious value when the answer is independent of the intent. -/
theorem not_worthAsking_const (c : ℝ≥0∞) (U : Θ → A → ℝ≥0∞) (b : PMF Θ) (q : PMF Y) :
    ¬ worthAsking c U b (fun _ => q) := by
  rw [worthAsking, VoI_const_eq_zero, not_lt]
  exact zero_le'

/-! ### A worked Mixed-Stakes 20 Questions instance

The binary core of the 20-Questions task: two candidate targets, a guess for
each, and a perfectly-informative yes/no question. This is a positive
witness — `worthAsking` is genuinely satisfiable, not vacuous — and shows the
animal → medical transfer concretely. -/

/-- Correct-guess utility: `1` if the guessed action matches the target,
else `0`. -/
def correctnessUtility : Bool → Bool → ℝ≥0∞ := fun θ a => if a = θ then 1 else 0

/-- Uniform prior belief over the two targets. -/
noncomputable def uniformBelief : PMF Bool := PMF.uniformOfFintype Bool

/-- A perfectly-informative question: the answer reveals the target. -/
noncomputable def revealingQuestion : Bool → PMF Bool := fun θ => PMF.pure θ

theorem V_uniform : V correctnessUtility uniformBelief = 2⁻¹ := by
  have hEU : ∀ a : Bool, EU correctnessUtility uniformBelief a = 2⁻¹ := by
    intro a
    unfold EU correctnessUtility uniformBelief
    rw [tsum_fintype, Fintype.sum_bool]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat]
    cases a <;> simp
  unfold V
  simp only [hEU, iSup_const]

theorem Vpost_revealing :
    Vpost correctnessUtility uniformBelief revealingQuestion = 1 := by
  have hwpv : ∀ y : Bool,
      weightedPosteriorValue correctnessUtility uniformBelief revealingQuestion y = 2⁻¹ := by
    intro y
    unfold weightedPosteriorValue correctnessUtility uniformBelief revealingQuestion
    simp only [PMF.pure_apply, PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat,
      tsum_fintype, Fintype.sum_bool, iSup_bool_eq]
    cases y <;> simp
  unfold Vpost
  rw [tsum_fintype, Fintype.sum_bool, hwpv, hwpv, ENNReal.inv_two_add_inv_two]

/-- A revealing question is worth asking at zero cost: its value of
information is strictly positive (`Vpost = 1 > 2⁻¹ = V`). -/
theorem revealing_worth_asking :
    worthAsking 0 correctnessUtility uniformBelief revealingQuestion := by
  rw [worthAsking, VoI, V_uniform, Vpost_revealing, tsub_pos_iff_lt]
  exact ENNReal.inv_lt_one.mpr (by norm_num)

/-- …and therefore worth asking at the high (medical) stakes too. -/
theorem revealing_worth_asking_medical :
    worthAsking 0 ((10 : ℝ≥0∞) • correctnessUtility) uniformBelief revealingQuestion :=
  medical_worth_asking_of_animal 0 _ _ _ revealing_worth_asking

/-! ### The decision rule: a sharp threshold -/

/-- A clarify-or-commit decision rule: clarification propensity as a
monotone `[0, 1]`-valued function of the net value-of-information signal
(value minus cost). The shared contract of this paper's sharp threshold
and [tsvilodub-etal-2026]'s logistic gate
(`TsvilodubEtAl2026.softGateRule`). -/
structure ClarifyRule where
  /-- Clarification propensity given the net value signal. -/
  propensity : ℝ → ℝ
  mono : Monotone propensity
  nonneg : ∀ x, 0 ≤ propensity x
  le_one : ∀ x, propensity x ≤ 1

/-- The sharp-threshold rule: clarify exactly when the net value is
positive (the paper's `worthAsking`; see `worthAsking_iff_sharpRule`). -/
noncomputable def sharpRule : ClarifyRule where
  propensity x := if 0 < x then 1 else 0
  mono x y hxy := by
    show (if 0 < x then (1 : ℝ) else 0) ≤ if 0 < y then 1 else 0
    by_cases hx : 0 < x
    · rw [if_pos hx, if_pos (hx.trans_le hxy)]
    · rw [if_neg hx]
      split <;> norm_num
  nonneg x := by split <;> norm_num
  le_one x := by split <;> norm_num

theorem sharpRule_apply_of_pos {x : ℝ} (h : 0 < x) : sharpRule.propensity x = 1 :=
  if_pos h

theorem sharpRule_apply_of_nonpos {x : ℝ} (h : ¬ 0 < x) : sharpRule.propensity x = 0 :=
  if_neg h

/-- The sharp rule is binary — the formal signature of a threshold process,
against which soft gates contrast (`TsvilodubEtAl2026.softGateRule_apply_zero`). -/
theorem sharpRule_binary (x : ℝ) :
    sharpRule.propensity x = 0 ∨ sharpRule.propensity x = 1 := by
  by_cases hx : 0 < x
  · exact Or.inr (sharpRule_apply_of_pos hx)
  · exact Or.inl (sharpRule_apply_of_nonpos hx)

/-- The account instantiates `sharpRule`: asking is worth its cost exactly
when the sharp-threshold rule fires on the net (real-valued) value signal.
The soft-gate rival is `TsvilodubEtAl2026.softGateRule`. -/
theorem worthAsking_iff_sharpRule {c : ℝ≥0∞} (hc : c ≠ ∞) (U : Θ → A → ℝ≥0∞)
    (b : PMF Θ) (κ : Θ → PMF Y) (hV : VoI U b κ ≠ ∞) :
    worthAsking c U b κ ↔
      sharpRule.propensity ((VoI U b κ).toReal - c.toReal) = 1 := by
  rw [worthAsking]
  constructor
  · intro h
    exact sharpRule_apply_of_pos
      (sub_pos.mpr ((ENNReal.toReal_lt_toReal hc hV).mpr h))
  · intro h
    by_contra hlt
    rw [sharpRule_apply_of_nonpos (not_lt.mpr
      (sub_nonpos.mpr ((ENNReal.toReal_le_toReal hV hc).mpr (not_lt.mp hlt))))] at h
    norm_num at h

end DongEtAl2026
