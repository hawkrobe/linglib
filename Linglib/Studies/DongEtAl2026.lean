import Linglib.Core.Probability.Decision.ExperimentDesign

/-!
# Dong et al. (2026): Value of Information: A Framework for Human–Agent Communication

This file formalizes the clarify-or-commit policy of [dong-etal-2026]. An agent holds a belief
`b` over a user's latent intent `θ`, may commit to an action `a` of utility `U(θ, a)`, or may
ask a closed-ended question `q` whose answer `y` it predicts by an answer model `p(y ∣ q, θ)`
and which costs the user `c`. The expected utility of committing, (1), and the value of acting
now, (2), are [van-rooy-2003]'s expected utility and decision value; the value of a question,
(3), is the answer-marginal expectation of the value of the posterior belief, so the value of
information, (4), `VoI(q) = Vpost(b, q) − V(b)`, is [lindley-1956]'s expected information gain
of the question as an experiment under the decision value, `ObservationModel.eig`, and the net
value, (5), subtracts the cost. The agent clarifies with a question of positive net value and
commits when none has one. Information cannot have negative value, `voi_nonneg`, so an
uninformative question is never asked, `not_clarifies_of_const`; scaling the stakes scales the
value of information, `voi_stakes`, so a question worth asking at low stakes is worth asking at
higher stakes, `clarifies_stakes`, and a costlier question is asked less, `clarifies_of_le`.
This is the risk awareness of the framework's Appendix A: on a two-candidate task with a yes/no
question of reliability `r`, whose value of information is `r − 1/2` by `voi_reliability`, a
moderately informative question is skipped when a correct guess is worth `1` and asked when
it is worth `10`, at one and the same cost.

## Implementation notes

The belief and the utility form a `DecisionProblem ℝ Θ A` and the questions an
`ObservationModel Θ Q Y`, questions indexing experiments and answers observations, so (1) to
(4) are the substrate's definitions and the clarify-or-commit decision is the only new object.
The policy's choice among the questions of positive net value, the sequential loop of
Algorithm 1 with its clarification budget and linear cost `T · c`, and the language-model
estimates of belief and answer distributions of §4.2 are not represented: the theorems concern
the decision at one turn, at a fixed belief. Stakes are a scalar on the utility, as in the
Mixed-Stakes task where a correct animal guess is worth `1` and a correct diagnosis `10`.

## References

* [dong-etal-2026]
* [raiffa-schlaifer-1961]
* [lindley-1956]
* [van-rooy-2003]
-/

namespace DongEtAl2026

open Core.DecisionTheory ProbabilityTheory Finset

variable {Θ A Q Y : Type*} [Fintype Θ] [Fintype Y]

/-! ### The value of information and the clarify-or-commit decision, (3) to (5) -/

variable (dp : DecisionProblem ℝ Θ A) (actions : Finset A) (om : ObservationModel Θ Q Y)

/-- The value of asking question `q`, (3): the expected value of the posterior belief. -/
noncomputable def postValue (q : Q) : ℝ :=
  ∑ y, om.marginal dp.prior q y * decisionValue dp.utility actions (om.posterior dp.prior q y)

/-- The value of information of question `q`, (4): [raiffa-schlaifer-1961]'s value of
information, the expected information gain of the question under the decision value. -/
noncomputable def voi (q : Q) : ℝ := om.eig dp.prior (decisionValue dp.utility actions) q

theorem voi_eq (q : Q) : voi dp actions om q = postValue dp actions om q - dp.value actions :=
  rfl

/-- The net value of information of question `q` at cost `c`, (5). -/
noncomputable def netVoi (c : ℝ) (q : Q) : ℝ := voi dp actions om q - c

/-- The clarify-or-commit decision: the agent clarifies when some question of `questions` has
positive net value, and commits otherwise. -/
def Clarifies (c : ℝ) (questions : Finset Q) : Prop := ∃ q ∈ questions, 0 < netVoi dp actions om c q

theorem not_clarifies_iff (c : ℝ) (questions : Finset Q) :
    ¬ Clarifies dp actions om c questions ↔ ∀ q ∈ questions, netVoi dp actions om c q ≤ 0 := by
  simp only [Clarifies, not_exists, not_and, not_lt]

/-- The paper's commit rule: the agent commits exactly when the best net value is at most `0`. -/
theorem not_clarifies_iff_sup'_le (c : ℝ) {questions : Finset Q} (h : questions.Nonempty) :
    ¬ Clarifies dp actions om c questions ↔ questions.sup' h (netVoi dp actions om c) ≤ 0 := by
  rw [not_clarifies_iff, sup'_le_iff]

/-- Clarifying with a question of positive net value raises the expected utility net of its
cost above the value of committing now. -/
theorem value_add_lt_postValue {c : ℝ} {q : Q} (h : 0 < netVoi dp actions om c q) :
    dp.value actions + c < postValue dp actions om q := by
  unfold netVoi at h
  rw [voi_eq] at h
  linarith

/-- A costlier question is asked less: the clarifying region shrinks as the cost rises. -/
theorem clarifies_of_le {c c' : ℝ} (hcc' : c ≤ c') {questions : Finset Q}
    (h : Clarifies dp actions om c' questions) : Clarifies dp actions om c questions := by
  obtain ⟨q, hq, hpos⟩ := h
  exact ⟨q, hq, by unfold netVoi at hpos ⊢; linarith⟩

/-- Information cannot have negative value. -/
theorem voi_nonneg (hprior : ∀ θ, 0 ≤ dp.prior θ) (hsum : ∑ θ, dp.prior θ = 1) (q : Q) :
    0 ≤ voi dp actions om q :=
  om.eig_nonneg_decisionValue dp.utility actions q hprior hsum

/-- A question whose answer does not depend on the intent has no value of information. -/
theorem voi_of_const (hsum : ∑ θ, dp.prior θ = 1) {q : Q} {ℓ : Y → ℝ}
    (hℓ : ∀ θ, om.likelihood θ q = ℓ) : voi dp actions om q = 0 :=
  om.eig_eq_zero_of_const hsum _ hℓ

/-- Uninformative questions are never asked, at any nonnegative cost. -/
theorem not_clarifies_of_const (hsum : ∑ θ, dp.prior θ = 1) {c : ℝ} (hc : 0 ≤ c)
    {questions : Finset Q} (hℓ : ∀ q ∈ questions, ∃ ℓ : Y → ℝ, ∀ θ, om.likelihood θ q = ℓ) :
    ¬ Clarifies dp actions om c questions := by
  rw [not_clarifies_iff]
  intro q hq
  obtain ⟨ℓ, hℓ⟩ := hℓ q hq
  unfold netVoi
  rw [voi_of_const dp actions om hsum hℓ]
  linarith

/-! ### Stakes, Appendix A -/

/-- The decision problem with every utility scaled by the stakes `s`. -/
def stakes (s : ℝ) : DecisionProblem ℝ Θ A := { dp with utility := s • dp.utility }

/-- Scaling the stakes scales the value of information. -/
theorem voi_stakes {s : ℝ} (hs : 0 ≤ s) (q : Q) :
    voi (stakes dp s) actions om q = s * voi dp actions om q := by
  show om.eig dp.prior (decisionValue (s • dp.utility) actions) q = _
  rw [decisionValue_smul _ _ hs, om.eig_smul]
  rfl

/-- A question worth asking at stakes `s` is worth asking at any higher stakes `s'`: the
commit-without-asking region shrinks as the stakes rise. -/
theorem clarifies_stakes (hprior : ∀ θ, 0 ≤ dp.prior θ) (hsum : ∑ θ, dp.prior θ = 1) {s s' : ℝ}
    (hs : 0 ≤ s) (hss' : s ≤ s') {c : ℝ} {questions : Finset Q}
    (h : Clarifies (stakes dp s) actions om c questions) :
    Clarifies (stakes dp s') actions om c questions := by
  obtain ⟨q, hq, hpos⟩ := h
  refine ⟨q, hq, ?_⟩
  unfold netVoi at hpos ⊢
  rw [voi_stakes dp actions om hs] at hpos
  rw [voi_stakes dp actions om (hs.trans hss')]
  have := mul_le_mul_of_nonneg_right hss' (voi_nonneg dp actions om hprior hsum q)
  linarith

/-! ### A two-candidate task with a yes/no question -/

/-- A correct guess is worth `1`. -/
def correct : Bool → Bool → ℝ := λ θ a => if a = θ then 1 else 0

/-- The uniform belief over two candidates. -/
noncomputable def uniform : DecisionProblem ℝ Bool Bool := ⟨correct, λ _ => 1 / 2⟩

/-- A yes/no question of reliability `r`: the answer is correct with probability `r`. -/
noncomputable def question {r : ℝ} (h₀ : 0 ≤ r) (h₁ : r ≤ 1) : ObservationModel Bool Unit Bool where
  likelihood θ _ y := if y = θ then r else 1 - r
  likelihood_nonneg _ _ _ := by split <;> linarith
  likelihood_sum θ _ := by cases θ <;> simp

theorem decisionValue_correct (p : Bool → ℝ) :
    decisionValue correct univ p = max (p true) (p false) := by
  have hEU : ∀ a, ∑ w, p w * correct w a = p a := λ a => by
    cases a <;> simp [correct]
  simp only [decisionValue, univ_nonempty, ↓reduceDIte, hEU]
  refine le_antisymm (sup'_le _ _ λ a _ => ?_)
    (max_le (le_sup' _ (mem_univ true)) (le_sup' _ (mem_univ false)))
  cases a <;> simp

/-- The value of information of a yes/no question of reliability `r ≥ 1/2` on a two-candidate
task is `r − 1/2`. -/
theorem voi_reliability {r : ℝ} (h₀ : 1 / 2 ≤ r) (h₁ : r ≤ 1) :
    voi uniform univ (question (by linarith) h₁) () = r - 1 / 2 := by
  have hm : ∀ y, (question (by linarith) h₁).marginal uniform.prior () y = 1 / 2 := λ y => by
    cases y <;> simp [ObservationModel.marginal, question, uniform] <;> ring
  have hp : ∀ y, (question (by linarith) h₁).posterior uniform.prior () y =
      λ θ => if y = θ then r else 1 - r := λ y => by
    funext θ
    simp only [ObservationModel.posterior]
    rw [hm, if_neg (by norm_num)]
    simp only [question, uniform]
    split_ifs <;> ring
  have hr : 1 - r ≤ r := by linarith
  unfold voi ObservationModel.eig
  rw [Fintype.sum_bool, hm, hm, hp, hp]
  simp only [uniform, decisionValue_correct]
  simp [max_eq_left hr, max_eq_right hr]
  ring

/-- Appendix A: at cost `1/20`, a question of reliability `27/50` is skipped when a correct
guess is worth `1` and asked when it is worth `10`. -/
theorem appendixA :
    ¬ Clarifies (stakes uniform 1) univ (question (r := 27 / 50) (by norm_num) (by norm_num))
        (1 / 20) {()} ∧
      Clarifies (stakes uniform 10) univ (question (r := 27 / 50) (by norm_num) (by norm_num))
        (1 / 20) {()} := by
  constructor
  · rw [not_clarifies_iff]
    intro q _
    cases q
    unfold netVoi
    rw [voi_stakes (s := 1) _ _ _ zero_le_one, voi_reliability (by norm_num) (by norm_num)]
    norm_num
  · refine ⟨(), mem_singleton_self _, ?_⟩
    unfold netVoi
    rw [voi_stakes (s := 10) _ _ _ (by norm_num), voi_reliability (by norm_num) (by norm_num)]
    norm_num

end DongEtAl2026
