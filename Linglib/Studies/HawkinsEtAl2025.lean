import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.DeriveFintype
import Linglib.Core.Probability.Choice.RationalAction
import Linglib.Core.Probability.Decision.ExperimentDesign

/-!
# Hawkins, Tsvilodub, Bergey, Goodman and Franke (2025): Relevant answers to polar questions

This file formalizes the PRIOR-PQ model of [hawkins-etal-2025], a Rational Speech Act model
of question answering grounded in the questioner's decision problem. The base-level
respondent `R0` answers with any true and safe response (2.1), where a response is safe for
a question when a questioner who knew it would know the answer (`Safe`, with the
belief-state characterization `safe_iff_forall_settles`). The questioner `questioner`
soft-maximizes the expected value of the decision problem updated by the base respondent's
answer less its cost (2.3), with the Bayesian update (2.4) as the posterior of the
observation model `R0Model` and the policy value of (2.2) as `value`;
`questionScore_eq_eig` identifies the score with [lindley-1956]'s expected information gain
of the question as an experiment. The pragmatic respondent `respondent` infers the
questioner's decision problem from the question (`respondentPosterior`,
`respondentPosterior_lt_iff`: a question is a signal about the goal) and soft-maximizes a
mixture of informativity and action relevance less cost (2.5); `respondentScore_beta_one`
and `respondentScore_beta_zero` are its two pure ends. `posterior_lt_iff_card` is the size
principle of §2b: a response is strengthened towards the worlds with fewer true and safe
alternatives.

Case study 1 (§3a) instantiates the model on the credit cards: `polar_exhaustive_safe` and
`mention_safe_iff` classify the responses, `yes_value_eq_exhaustive` is the reason the
exhaustive list is dispreferred after a question about a card the questioner holds (3), and
`generalYes_posterior_pos` the residual uncertainty after the general question (5).

## Implementation notes

* Softmaxes are `Core.RationalAction.fromSoftmax`; beliefs are functions `W → ℝ`, as in
  `ProbabilityTheory.ObservationModel`, and the Kullback–Leibler term of (2.5) is the finite
  sum `kl` in the direction the paper writes it.
* Both the safe base respondent of (2.1) and its truth-only relaxation `R0'` of §2c are
  `RationalAction`s; the observation model needs every world to admit a true and safe
  response, which `polar_admissible` supplies for polar questions.
* The case study fixes the parameters the paper leaves free only where a theorem needs a
  sign; the fitted values of the electronic supplementary material are not reproduced.

## TODO

* Case studies 2 and 3 (the iced tea and blanket vignettes) with the elicited utilities.

## References

* [hawkins-etal-2025]
* [lindley-1956]
-/

namespace HawkinsEtAl2025

open Core ProbabilityTheory Finset

variable {W Q R A D : Type*}

/-! ### Safe answers (§2a) -/

/-- A belief state settles a proposition when it entails it or its negation. -/
def Settles (s : Set W) (p : W → Prop) : Prop := s ⊆ {w | p w} ∨ s ⊆ {w | ¬ p w}

/-- A response `r` is safe for the polar question `q` (§2a): a questioner who knew `r` would
know the answer to `q`, so `r` entails one of the complete answers. -/
def Safe (q r : W → Prop) : Prop := (∀ w, r w → q w) ∨ (∀ w, r w → ¬ q w)

instance [Fintype W] (q r : W → Prop) [DecidablePred q] [DecidablePred r] :
    Decidable (Safe q r) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Safety in belief states: every state verifying `r` settles `q`. -/
theorem safe_iff_forall_settles (q r : W → Prop) :
    Safe q r ↔ ∀ s : Set W, s ⊆ {w | r w} → Settles s q := by
  constructor
  · rintro (h | h) s hs
    · exact Or.inl λ w hw => h w (hs hw)
    · exact Or.inr λ w hw => h w (hs hw)
  · intro h
    rcases h {w | r w} le_rfl with h' | h'
    · exact Or.inl λ w hw => h' hw
    · exact Or.inr λ w hw => h' hw

theorem safe_self (q : W → Prop) : Safe q q := Or.inl λ _ h => h

theorem safe_not (q : W → Prop) : Safe q (λ w => ¬ q w) := Or.inr λ _ h => h

/-! ### The model -/

/-- A PRIOR-PQ model: the propositions questions and responses denote, the questioner's
decision problems, and the cost of responses. -/
structure Model (W Q R A D : Type*) where
  /-- The proposition a polar question asks about. -/
  question : Q → W → Prop
  /-- The proposition a response asserts. -/
  response : R → W → Prop
  /-- The utility function of a decision problem. -/
  utility : D → W → A → ℝ
  /-- The questioner's prior over worlds under a decision problem. -/
  prior : D → W → ℝ
  /-- The production cost of a response. -/
  cost : R → ℝ

variable (m : Model W Q R A D) [∀ q, DecidablePred (m.question q)]
  [∀ r, DecidablePred (m.response r)] [Fintype R] [Fintype W]

/-- A response is admissible at a world and question when it is true there and safe. -/
def Model.Admissible (w : W) (q : Q) (r : R) : Prop :=
  m.response r w ∧ Safe (m.question q) (m.response r)

instance (w : W) (q : Q) (r : R) : Decidable (m.Admissible w q r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- (2.1): the base-level respondent, uniform over the true and safe responses. -/
noncomputable def Model.R0 : RationalAction (W × Q) R where
  score wq r := if m.Admissible wq.1 wq.2 r then 1 else 0
  score_nonneg _ _ := by split_ifs <;> norm_num

/-- §2c: the truth-only relaxation of the base respondent, uniform over the true responses. -/
noncomputable def Model.R0' : RationalAction (W × Q) R where
  score wq r := if m.response r wq.1 then 1 else 0
  score_nonneg _ _ := by split_ifs <;> norm_num

/-- The number of true and safe responses at a world and question. -/
def Model.admissibleCard (w : W) (q : Q) : ℕ := (univ.filter (m.Admissible w q)).card

theorem Model.R0_totalScore (w : W) (q : Q) :
    m.R0.totalScore (w, q) = m.admissibleCard w q := by
  simp [RationalAction.totalScore, Model.R0, Model.admissibleCard, sum_boole]

/-- The base respondent gives a response positive probability iff it is true and safe. -/
theorem Model.R0_policy_pos_iff {w : W} {q : Q} {r : R} (h : 0 < m.admissibleCard w q) :
    0 < m.R0.policy (w, q) r ↔ m.Admissible w q r := by
  have hne : m.R0.totalScore (w, q) ≠ 0 := by
    rw [Model.R0_totalScore]; exact_mod_cast h.ne'
  have hcard : (0 : ℝ) < m.admissibleCard w q := by exact_mod_cast h
  simp only [RationalAction.policy, hne, ↓reduceIte]
  rw [Model.R0_totalScore]
  change 0 < (if m.Admissible w q r then (1 : ℝ) else 0) / _ ↔ _
  split_ifs with hadm
  · simp [hadm, hcard]
  · simp [hadm]

/-- The base respondent as an observation model, with questions as experiments and
responses as observations, given that every world admits a true and safe response. -/
noncomputable def Model.R0Model (h : ∀ w q, 0 < m.admissibleCard w q) :
    ObservationModel W Q R where
  likelihood w q r := m.R0.policy (w, q) r
  likelihood_nonneg w q r := m.R0.policy_nonneg (w, q) r
  likelihood_sum w q := m.R0.policy_sum_eq_one (w, q)
    (by rw [Model.R0_totalScore]; exact_mod_cast (h w q).ne')

/-- The truth-only base respondent as an observation model, given that every world makes
some response true. -/
noncomputable def Model.R0Model' (h : ∀ w, ∃ r, m.response r w) : ObservationModel W Q R where
  likelihood w q r := m.R0'.policy (w, q) r
  likelihood_nonneg w q r := m.R0'.policy_nonneg (w, q) r
  likelihood_sum w q := m.R0'.policy_sum_eq_one (w, q) (by
    obtain ⟨r, hr⟩ := h w
    refine ne_of_gt (lt_of_lt_of_le ?_ (single_le_sum (λ r' _ => m.R0'.score_nonneg _ r')
      (mem_univ r)))
    simp [Model.R0', hr])

section Positivity

variable (h : ∀ w q, 0 < m.admissibleCard w q) (d : D)

theorem Model.R0Model_likelihood_pos_iff {w : W} {q : Q} {r : R} :
    0 < (m.R0Model h).likelihood w q r ↔ m.Admissible w q r :=
  m.R0_policy_pos_iff (h w q)

/-- The marginal of a response is positive when some world of positive prior admits it. -/
theorem Model.R0Model_marginal_pos (hπ : ∀ w, 0 < m.prior d w) {q : Q} {r : R} {w : W}
    (hadm : m.Admissible w q r) : 0 < (m.R0Model h).marginal (m.prior d) q r :=
  lt_of_lt_of_le (mul_pos (hπ w) ((m.R0Model_likelihood_pos_iff h).2 hadm))
    (single_le_sum (λ w' _ => mul_nonneg (hπ w').le ((m.R0Model h).likelihood_nonneg w' q r))
      (mem_univ w))

/-- Under positive priors a world has positive posterior after a response iff the response
is true and safe there. -/
theorem Model.R0Model_posterior_pos_iff (hπ : ∀ w, 0 < m.prior d w) {q : Q} {r : R}
    (hm : (m.R0Model h).marginal (m.prior d) q r ≠ 0) {w : W} :
    0 < (m.R0Model h).posterior (m.prior d) q r w ↔ m.Admissible w q r := by
  have hmpos : 0 < (m.R0Model h).marginal (m.prior d) q r :=
    lt_of_le_of_ne ((m.R0Model h).marginal_nonneg (λ w => (hπ w).le) q r) hm.symm
  simp only [ObservationModel.posterior, hm, ↓reduceIte]
  rw [div_pos_iff_of_pos_right hmpos]
  constructor
  · intro hpos
    exact (m.R0Model_likelihood_pos_iff h).1 (pos_of_mul_pos_right hpos (hπ w).le)
  · intro hadm
    exact mul_pos (hπ w) ((m.R0Model_likelihood_pos_iff h).2 hadm)

end Positivity

/-- The size principle (§2b): between two worlds of equal prior at which a response is true
and safe, the posterior favours the world with fewer true and safe alternatives. -/
theorem Model.posterior_lt_iff_card (h : ∀ w q, 0 < m.admissibleCard w q) (d : D) (q : Q)
    (r : R) {w₁ w₂ : W} (hπ : ∀ w, 0 ≤ m.prior d w) (hp : m.prior d w₁ = m.prior d w₂)
    (hpos : 0 < m.prior d w₁) (h₁ : m.Admissible w₁ q r) (h₂ : m.Admissible w₂ q r)
    (hm : (m.R0Model h).marginal (m.prior d) q r ≠ 0) :
    (m.R0Model h).posterior (m.prior d) q r w₁ < (m.R0Model h).posterior (m.prior d) q r w₂ ↔
      m.admissibleCard w₂ q < m.admissibleCard w₁ q := by
  have hmpos : 0 < (m.R0Model h).marginal (m.prior d) q r :=
    lt_of_le_of_ne ((m.R0Model h).marginal_nonneg hπ q r) hm.symm
  have hc : ∀ w, (0 : ℝ) < m.admissibleCard w q := λ w => by exact_mod_cast h w q
  have hlik : ∀ w, m.Admissible w q r →
      (m.R0Model h).likelihood w q r = 1 / (m.admissibleCard w q : ℝ) := by
    intro w hw
    have hne : m.R0.totalScore (w, q) ≠ 0 := by
      rw [Model.R0_totalScore]; exact_mod_cast (h w q).ne'
    show m.R0.policy (w, q) r = _
    simp only [RationalAction.policy, hne, ↓reduceIte]
    rw [Model.R0_totalScore]
    change (if m.Admissible w q r then (1 : ℝ) else 0) / _ = _
    rw [if_pos hw]
  simp only [ObservationModel.posterior, hm, ↓reduceIte, hlik w₁ h₁, hlik w₂ h₂, ← hp]
  rw [div_lt_div_iff_of_pos_right hmpos]
  constructor
  · intro hlt
    exact_mod_cast lt_of_one_div_lt_one_div (hc w₁) (lt_of_mul_lt_mul_left hlt hpos.le)
  · intro hlt
    exact mul_lt_mul_of_pos_left (one_div_lt_one_div_of_lt (hc w₂) (by exact_mod_cast hlt)) hpos

/-! ### The questioner (§2b) -/

variable [Fintype A]

/-- (2.2): the policy of a decision problem under beliefs `π`, a softmax over expected
utility with rationality `αℵ`. -/
noncomputable def policy (U : W → A → ℝ) (αℵ : ℝ) (π : W → ℝ) : A → ℝ :=
  Real.softmax (λ a => αℵ * ∑ w, π w * U w a)

/-- The value `V(D)` of a decision problem: the expected utility of following its policy. -/
noncomputable def value [Nonempty A] (U : W → A → ℝ) (αℵ : ℝ) (π : W → ℝ) : ℝ :=
  ∑ a, policy U αℵ π a * ∑ w, π w * U w a

variable [Nonempty A]

omit [Fintype A] [Nonempty A] in
/-- Beliefs whose support sees a constant utility profile have that profile as expected
utility. -/
theorem expectedUtility_eq_of_support {π : W → ℝ} {U : W → A → ℝ} {c : A → ℝ}
    (hsum : ∑ w, π w = 1) (hU : ∀ w, π w ≠ 0 → ∀ a, U w a = c a) (a : A) :
    ∑ w, π w * U w a = c a := by
  calc ∑ w, π w * U w a = ∑ w, π w * c a := by
        refine sum_congr rfl λ w _ => ?_
        by_cases hw : π w = 0
        · simp [hw]
        · rw [hU w hw a]
    _ = c a := by rw [← sum_mul, hsum, one_mul]

/-- Two beliefs seeing the same constant utility profile have the same value. -/
theorem value_eq_of_support {π π' : W → ℝ} {U : W → A → ℝ} {c : A → ℝ} (αℵ : ℝ)
    (hsum : ∑ w, π w = 1) (hsum' : ∑ w, π' w = 1)
    (hU : ∀ w, π w ≠ 0 → ∀ a, U w a = c a) (hU' : ∀ w, π' w ≠ 0 → ∀ a, U w a = c a) :
    value U αℵ π = value U αℵ π' := by
  simp only [value, policy, expectedUtility_eq_of_support hsum hU,
    expectedUtility_eq_of_support hsum' hU']

/-- The expected value to the questioner of asking `q` (2.3): the expected value of the
updated decision problem after the base respondent's answer, less the weighted cost. -/
noncomputable def Model.questionScore (om : ObservationModel W Q R) (αℵ wc : ℝ) (d : D)
    (q : Q) : ℝ :=
  ∑ r, om.marginal (m.prior d) q r *
    (value (m.utility d) αℵ (om.posterior (m.prior d) q r) - wc * m.cost r)

omit [∀ q, DecidablePred (m.question q)] [∀ r, DecidablePred (m.response r)] in
/-- The question score is [lindley-1956]'s expected information gain of the question under
the policy value, plus the value of the prior, less the expected cost. -/
theorem Model.questionScore_eq_eig (om : ObservationModel W Q R) (αℵ wc : ℝ) (d : D) (q : Q) :
    m.questionScore om αℵ wc d q =
      om.eig (m.prior d) (value (m.utility d) αℵ) q + value (m.utility d) αℵ (m.prior d) -
        wc * ∑ r, om.marginal (m.prior d) q r * m.cost r := by
  have hcost : ∑ r, om.marginal (m.prior d) q r * (wc * m.cost r) =
      wc * ∑ r, om.marginal (m.prior d) q r * m.cost r := by
    rw [mul_sum]; exact sum_congr rfl λ r _ => by ring
  simp only [Model.questionScore, ObservationModel.eig, mul_sub, sum_sub_distrib, hcost]
  ring

variable [Fintype Q]

/-- (2.3): the questioner, a softmax over question scores with rationality `αQ`. -/
noncomputable def Model.questioner (om : ObservationModel W Q R) (αℵ wc αQ : ℝ) :
    RationalAction D Q :=
  RationalAction.fromSoftmax (m.questionScore om αℵ wc) αQ

/-! ### The pragmatic respondent (§2c) -/

variable [Fintype D]

/-- The respondent's posterior over decision problems after hearing `q`: Bayesian theory of
mind through the questioner, `π(D ∣ q) ∝ Q(q ∣ D) π(D)`. -/
noncomputable def Model.respondentPosterior (om : ObservationModel W Q R) (αℵ wc αQ : ℝ)
    (πD : D → ℝ) (q : Q) (d : D) : ℝ :=
  let z := ∑ d', (m.questioner om αℵ wc αQ).policy d' q * πD d'
  if z = 0 then 0 else (m.questioner om αℵ wc αQ).policy d q * πD d / z

omit [∀ q, DecidablePred (m.question q)] [∀ r, DecidablePred (m.response r)] in
/-- A question is a signal about the goal: with equal priors, the decision problem under
which the question was the more probable is the more probable after it. -/
theorem Model.respondentPosterior_lt_iff (om : ObservationModel W Q R) (αℵ wc αQ : ℝ)
    (πD : D → ℝ) (hπ : ∀ d, 0 ≤ πD d) (q : Q) {d₁ d₂ : D} (hp : πD d₁ = πD d₂)
    (hpos : 0 < πD d₁)
    (hz : ∑ d', (m.questioner om αℵ wc αQ).policy d' q * πD d' ≠ 0) :
    m.respondentPosterior om αℵ wc αQ πD q d₁ <
        m.respondentPosterior om αℵ wc αQ πD q d₂ ↔
      (m.questioner om αℵ wc αQ).policy d₁ q <
        (m.questioner om αℵ wc αQ).policy d₂ q := by
  have hzpos : 0 < ∑ d', (m.questioner om αℵ wc αQ).policy d' q * πD d' :=
    lt_of_le_of_ne (sum_nonneg λ d' _ =>
      mul_nonneg ((m.questioner om αℵ wc αQ).policy_nonneg d' q) (hπ d')) (Ne.symm hz)
  simp only [Model.respondentPosterior, hz, ↓reduceIte, ← hp]
  rw [div_lt_div_iff_of_pos_right hzpos]
  exact ⟨λ hlt => lt_of_mul_lt_mul_right hlt hpos.le,
    λ hlt => mul_lt_mul_of_pos_right hlt hpos⟩

/-- The finite Kullback–Leibler divergence of beliefs, in the direction of (2.5). -/
noncomputable def kl (p q : W → ℝ) : ℝ := ∑ w, p w * Real.log (p w / q w)

/-- The utility of a response under one decision problem (2.5): informativity weighted
`1 − β`, action relevance weighted `β`, less the weighted cost. -/
noncomputable def Model.singleScore (om om' : ObservationModel W Q R) (αℵ wc β : ℝ)
    (πW : W → ℝ) (d : D) (q : Q) (r : R) : ℝ :=
  (1 - β) * (- kl (om'.posterior (m.prior d) q r) πW) +
    β * value (m.utility d) αℵ (om.posterior (m.prior d) q r) - wc * m.cost r

/-- (2.5): the pragmatic respondent's score, the expected utility of a response over the
inferred decision problem. -/
noncomputable def Model.respondentScore (om om' : ObservationModel W Q R) (αℵ wc αQ β : ℝ)
    (πD : D → ℝ) (πW : W → ℝ) (q : Q) (r : R) : ℝ :=
  ∑ d, m.respondentPosterior om αℵ wc αQ πD q d * singleScore m om om' αℵ wc β πW d q r

/-- (2.5): the pragmatic respondent, a softmax over response scores with rationality `αR`. -/
noncomputable def Model.respondent (om om' : ObservationModel W Q R) (αℵ wc αQ β αR : ℝ)
    (πD : D → ℝ) (πW : W → ℝ) : RationalAction Q R :=
  RationalAction.fromSoftmax (respondentScore m om om' αℵ wc αQ β πD πW) αR

omit [∀ q, DecidablePred (m.question q)] [∀ r, DecidablePred (m.response r)] in
/-- At `β = 1` the respondent weighs only action relevance and cost. -/
theorem Model.respondentScore_beta_one (om om' : ObservationModel W Q R) (αℵ wc αQ : ℝ)
    (πD : D → ℝ) (πW : W → ℝ) (q : Q) (r : R) :
    respondentScore m om om' αℵ wc αQ 1 πD πW q r =
      ∑ d, m.respondentPosterior om αℵ wc αQ πD q d *
        (value (m.utility d) αℵ (om.posterior (m.prior d) q r) - wc * m.cost r) := by
  simp [Model.respondentScore, Model.singleScore]

omit [∀ q, DecidablePred (m.question q)] [∀ r, DecidablePred (m.response r)] in
/-- At `β = 0` the respondent weighs only informativity and cost. -/
theorem Model.respondentScore_beta_zero (om om' : ObservationModel W Q R) (αℵ wc αQ : ℝ)
    (πD : D → ℝ) (πW : W → ℝ) (q : Q) (r : R) :
    respondentScore m om om' αℵ wc αQ 0 πD πW q r =
      ∑ d, m.respondentPosterior om αℵ wc αQ πD q d *
        (- kl (om'.posterior (m.prior d) q r) πW - wc * m.cost r) := by
  simp [Model.respondentScore, Model.singleScore]

/-! ### Case study 1: credit cards (§3a) -/

/-- The three cards. -/
inductive Card where
  | amex
  | mastercard
  | carteBlanche
  deriving DecidableEq, Fintype, Repr

/-- The questioner's actions. -/
inductive Act where
  | stay
  | go
  deriving DecidableEq, Fintype, Repr, Inhabited

/-- The responses: a polar answer to whether any card of `S` is accepted, the mention of some
accepted cards, or the exhaustive list of the accepted cards. -/
inductive Resp where
  | polar (S : Finset Card) (b : Bool)
  | mention (T : Finset Card)
  | exhaustive (T : Finset Card)
  deriving DecidableEq, Fintype

/-- The decision problems: `U1`, whether any of the questioner's cards `C` is accepted, and
`U2`, whether any card is accepted. -/
inductive Goal where
  | ownCards (C : Finset Card)
  | anyCard
  deriving DecidableEq, Fintype

/-- The utility of §3a: 5 for going when a relevant card is accepted or staying when none is,
0 otherwise. -/
def cardUtility : Goal → Finset Card → Act → ℝ
  | .ownCards C, w, .go => if (C ∩ w).Nonempty then 5 else 0
  | .ownCards C, w, .stay => if (C ∩ w).Nonempty then 0 else 5
  | .anyCard, w, .go => if w.Nonempty then 5 else 0
  | .anyCard, w, .stay => if w.Nonempty then 0 else 5

/-- The proposition a response asserts. -/
def respProp : Resp → Finset Card → Prop
  | .polar S b, w => (S ∩ w).Nonempty ↔ b = true
  | .mention T, w => T ⊆ w
  | .exhaustive T, w => T = w

instance : ∀ r, DecidablePred (respProp r)
  | .polar S b, w => inferInstanceAs (Decidable ((S ∩ w).Nonempty ↔ b = true))
  | .mention T, w => inferInstanceAs (Decidable (T ⊆ w))
  | .exhaustive T, w => inferInstanceAs (Decidable (T = w))

/-- The credit-card model: a question asks whether any card of a set is accepted, worlds are
the sets of accepted cards, priors are uniform over the eight worlds, and a response costs
the cards it mentions. -/
noncomputable def cards : Model (Finset Card) (Finset Card) Resp Act Goal where
  question S w := (S ∩ w).Nonempty
  response := respProp
  utility := cardUtility
  prior _ _ := 1 / 8
  cost
    | .polar _ _ => 0
    | .mention T => T.card
    | .exhaustive T => T.card

instance : ∀ S, DecidablePred (cards.question S) :=
  λ S w => inferInstanceAs (Decidable (S ∩ w).Nonempty)

instance : ∀ r, DecidablePred (cards.response r) :=
  λ r => inferInstanceAs (DecidablePred (respProp r))

/-- Polar answers to the question asked are safe, as are exhaustive lists. -/
theorem polar_exhaustive_safe :
    (∀ S b, Safe (cards.question S) (cards.response (.polar S b))) ∧
      ∀ S T, Safe (cards.question S) (cards.response (.exhaustive T)) := by
  decide

/-- Mentioning accepted cards is safe for a question exactly when one of them was asked
about: in (2), naming a third card after a question about two others is not. -/
theorem mention_safe_iff (S T : Finset Card) (hS : S.Nonempty) :
    Safe (cards.question S) (cards.response (.mention T)) ↔ (T ∩ S).Nonempty := by
  revert S T; decide

/-- Every world admits a true and safe response to every question: the true polar answer. -/
theorem polar_admissible : ∀ w q, 0 < cards.admissibleCard w q := λ w q =>
  Finset.card_pos.2 ⟨.polar q (decide (q ∩ w).Nonempty), Finset.mem_filter.2 ⟨mem_univ _,
    ⟨by show (q ∩ w).Nonempty ↔ decide (q ∩ w).Nonempty = true; simp,
      polar_exhaustive_safe.1 q _⟩⟩⟩

/-- The base respondent as an observation model for the credit cards. -/
noncomputable def cardsModel : ObservationModel (Finset Card) (Finset Card) Resp :=
  cards.R0Model polar_admissible

private theorem cards_prior_pos (d : Goal) : ∀ w, 0 < cards.prior d w := λ _ => by
  simp [cards]

/-- (3): for a questioner holding the card asked about, after the answer "yes" the value of
the decision problem already equals its value after the exhaustive list, since every world
compatible with either answer accepts a card the questioner holds; only the cost separates
the two answers. -/
theorem yes_value_eq_exhaustive (C w : Finset Card) (hC : .amex ∈ C) (hw : .amex ∈ w)
    (αℵ : ℝ) :
    value (cards.utility (.ownCards C)) αℵ
        (cardsModel.posterior (cards.prior (.ownCards C)) {.amex} (.polar {.amex} true)) =
      value (cards.utility (.ownCards C)) αℵ
        (cardsModel.posterior (cards.prior (.ownCards C)) {.amex} (.exhaustive w)) := by
  have hyes : cards.Admissible w {.amex} (.polar {.amex} true) := by
    refine ⟨?_, (polar_exhaustive_safe.1 _ _)⟩
    show ({Card.amex} ∩ w).Nonempty ↔ true = true
    simp [Finset.singleton_inter_of_mem hw]
  have hexh : cards.Admissible w {.amex} (.exhaustive w) :=
    ⟨rfl, polar_exhaustive_safe.2 _ _⟩
  have hm₁ :=
    (cards.R0Model_marginal_pos polar_admissible (.ownCards C) (cards_prior_pos _) hyes).ne'
  have hm₂ :=
    (cards.R0Model_marginal_pos polar_admissible (.ownCards C) (cards_prior_pos _) hexh).ne'
  refine value_eq_of_support (c := λ a => match a with | .go => 5 | .stay => 0) αℵ
    (cardsModel.sum_posterior hm₁) (cardsModel.sum_posterior hm₂) ?_ ?_
  · intro w' hw' a
    have hadm := (cards.R0Model_posterior_pos_iff polar_admissible _ (cards_prior_pos _) hm₁).1
      (lt_of_le_of_ne (cardsModel.posterior_nonneg (λ w => (cards_prior_pos _ w).le) _ _ w')
        (Ne.symm hw'))
    have : Card.amex ∈ w' := by
      obtain ⟨x, hx⟩ : ({Card.amex} ∩ w').Nonempty := (hadm.1 : _ ↔ true = true).2 rfl
      rw [Finset.mem_inter, Finset.mem_singleton] at hx
      exact hx.1 ▸ hx.2
    have hCw : (C ∩ w').Nonempty := ⟨.amex, Finset.mem_inter.2 ⟨hC, this⟩⟩
    cases a <;> simp [cards, cardUtility, hCw]
  · intro w' hw' a
    have hadm := (cards.R0Model_posterior_pos_iff polar_admissible _ (cards_prior_pos _) hm₂).1
      (lt_of_le_of_ne (cardsModel.posterior_nonneg (λ w => (cards_prior_pos _ w).le) _ _ w')
        (Ne.symm hw'))
    have hw'w : w = w' := hadm.1
    subst hw'w
    have hCw : (C ∩ w).Nonempty := ⟨.amex, Finset.mem_inter.2 ⟨hC, hw⟩⟩
    cases a <;> simp [cards, cardUtility, hCw]

/-- (5): after "yes" to the general question, a world accepting only MasterCard keeps
positive posterior, so a questioner holding American Express remains uncertain; after "yes"
to the question about American Express it does not. -/
theorem generalYes_posterior_pos :
    0 < cardsModel.posterior (cards.prior (.ownCards {.amex})) univ (.polar univ true)
        {.mastercard} ∧
      cardsModel.posterior (cards.prior (.ownCards {.amex})) {.amex} (.polar {.amex} true)
        {.mastercard} = 0 := by
  have h₁ : cards.Admissible {.mastercard} univ (.polar univ true) := by decide
  have h₂ : ¬ cards.Admissible {.mastercard} {.amex} (.polar {.amex} true) := by decide
  have h₃ : cards.Admissible {.amex} {.amex} (.polar {.amex} true) := by decide
  have hm₁ := (cards.R0Model_marginal_pos polar_admissible (.ownCards {.amex})
    (cards_prior_pos _) h₁).ne'
  refine ⟨(cards.R0Model_posterior_pos_iff polar_admissible (.ownCards {.amex})
    (cards_prior_pos _) hm₁).2 h₁, ?_⟩
  have hm := (cards.R0Model_marginal_pos polar_admissible (.ownCards {.amex})
    (cards_prior_pos _) h₃).ne'
  by_contra hne
  exact h₂ ((cards.R0Model_posterior_pos_iff polar_admissible _ (cards_prior_pos _) hm).1
    (lt_of_le_of_ne (cardsModel.posterior_nonneg (λ w => (cards_prior_pos _ w).le) _ _ _)
      (Ne.symm hne)))

end HawkinsEtAl2025
