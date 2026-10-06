module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.Analysis.SpecialFunctions.Softmax
public import Linglib.Core.Probability.Decision.ValueOfInformation

/-!
# Hawkins, Tsvilodub, Bergey, Goodman and Franke (2025): Relevant answers to polar questions

This file formalizes the PRIOR-PQ model of [hawkins-etal-2025], a Rational Speech Act model
of question answering grounded in the questioner's decision problem. The base-level
respondent `R0` answers with any true and safe response (2.1), where a response is safe for
a question when a questioner who knew it would know the answer (`Safe`, with the
belief-state characterization `safe_iff_forall_settles`). The questioner `questioner`
soft-maximizes the expected value of the decision problem updated by the base respondent's
answer less its cost (2.3), with the Bayesian update (2.4) as the posterior of the base
respondent's kernel `R0Kernel` and the policy value of (2.2) as `value`;
`questionScore_eq_valueOfInformation` reads the score as the value of information of the
question under the policy value. The pragmatic respondent `respondent` infers the questioner's
decision problem from the question (`respondentPosterior`, `respondentPosterior_lt_iff`: a
question is a signal about the goal) and soft-maximizes a mixture of informativity and action
relevance less cost (2.5); `respondentScore_beta_one` and `respondentScore_beta_zero` are its
two pure ends. `posterior_R0Kernel_real_lt_iff` is the size principle of §2b: a response is
strengthened towards the worlds with fewer true and safe alternatives.

Case study 1 (§3a) instantiates the model on the credit cards: `polar_exhaustive_safe` and
`mention_safe_iff` classify the responses, `yes_value_eq_exhaustive` is the reason the
exhaustive list is dispreferred after a question about a card the questioner holds (3), and
`generalYes_posterior_ne_zero` the residual uncertainty after the general question (5).

## Implementation notes

* Beliefs over worlds are probability measures and the base respondent to a question is a
  kernel from worlds to responses, so the update (2.4) is its posterior and the
  Kullback–Leibler term of (2.5) is `klDiv`, in the direction the paper writes it. The
  questioner, the pragmatic respondent and its belief over decision problems are
  `Real.softmax` weight vectors.
* The safe base respondent of (2.1) and its truth-only relaxation `R0'` of §2c are
  `ProbabilityTheory.uniformOn` over the true and safe (respectively true) responses. The base
  respondent always responds when every world admits a true and safe response, which
  `polar_admissible` supplies for polar questions.
* The case study fixes the parameters the paper leaves free only where a theorem needs a
  sign; the fitted values of the electronic supplementary material are not reproduced.

## TODO

* Case studies 2 and 3 (the iced tea and blanket vignettes) with the elicited utilities.
* The respondent's belief over decision problems as the posterior of the questioner's kernel.

## References

* [hawkins-etal-2025]
-/

@[expose] public section

namespace HawkinsEtAl2025

open MeasureTheory ProbabilityTheory InformationTheory Finset

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

/-- A response is safe exactly when every belief state verifying `r` settles `q`. -/
theorem safe_iff_forall_settles (q r : W → Prop) :
    Safe q r ↔ ∀ s : Set W, s ⊆ {w | r w} → Settles s q := by
  constructor
  · rintro (h | h) s hs
    · exact Or.inl fun w hw ↦ h w (hs hw)
    · exact Or.inr fun w hw ↦ h w (hs hw)
  · intro h
    rcases h {w | r w} le_rfl with h' | h'
    · exact Or.inl fun w hw ↦ h' hw
    · exact Or.inr fun w hw ↦ h' hw

theorem safe_self (q : W → Prop) : Safe q q := Or.inl fun _ h ↦ h

theorem safe_not (q : W → Prop) : Safe q (fun w ↦ ¬ q w) := Or.inr fun _ h ↦ h

/-! ### The model -/

/-- A PRIOR-PQ model gives the propositions that questions and responses denote, the
questioner's decision problems, and the cost of responses. -/
structure Model (W Q R A D : Type*) [MeasurableSpace W] where
  /-- The proposition a polar question asks about. -/
  question : Q → W → Prop
  /-- The proposition a response asserts. -/
  response : R → W → Prop
  /-- The utility function of a decision problem. -/
  utility : D → W → A → ℝ
  /-- The questioner's prior over worlds under a decision problem. -/
  prior : D → Measure W
  /-- The production cost of a response. -/
  cost : R → ℝ

variable [MeasurableSpace W] [MeasurableSpace R] (m : Model W Q R A D)

/-- A response is admissible at a world and question when it is true there and safe. -/
def Model.Admissible (w : W) (q : Q) (r : R) : Prop :=
  m.response r w ∧ Safe (m.question q) (m.response r)

instance [Fintype W] [∀ q, DecidablePred (m.question q)] [∀ r, DecidablePred (m.response r)]
    (w : W) (q : Q) (r : R) : Decidable (m.Admissible w q r) :=
  inferInstanceAs (Decidable (_ ∧ _))

section BaseRespondent

/-- The base-level respondent (2.1) is uniform over the true and safe responses. -/
noncomputable def Model.R0 (w : W) (q : Q) : Measure R := uniformOn {r | m.Admissible w q r}

/-- The truth-only relaxation of the base respondent (§2c) is uniform over the true responses. -/
noncomputable def Model.R0' (w : W) : Measure R := uniformOn {r | m.response r w}

section Kernel

variable [DiscreteMeasurableSpace W] [Countable W]

/-- The base respondent to the question `q` draws a response at each world. -/
noncomputable def Model.R0Kernel (q : Q) : Kernel W R :=
  Kernel.ofFunOfCountable fun w ↦ m.R0 w q

/-- The truth-only base respondent draws a response at each world. -/
noncomputable def Model.R0Kernel' : Kernel W R :=
  Kernel.ofFunOfCountable fun w ↦ m.R0' w

@[simp] theorem Model.R0Kernel_apply (q : Q) (w : W) : m.R0Kernel q w = m.R0 w q := rfl

instance (q : Q) : IsFiniteKernel (m.R0Kernel q) :=
  ⟨⟨1, ENNReal.one_lt_top, fun w ↦ show uniformOn {r | m.Admissible w q r} Set.univ ≤ 1 from
    prob_le_one⟩⟩

instance : IsFiniteKernel m.R0Kernel' :=
  ⟨⟨1, ENNReal.one_lt_top, fun w ↦ show uniformOn {r | m.response r w} Set.univ ≤ 1 from
    prob_le_one⟩⟩

end Kernel

variable [∀ q, DecidablePred (m.question q)] [∀ r, DecidablePred (m.response r)] [Fintype W]
  [Fintype R] [MeasurableSingletonClass R]

/-- `admissibleCard w q` counts the true and safe responses to `q` at `w`. -/
def Model.admissibleCard (w : W) (q : Q) : ℕ := (univ.filter (m.Admissible w q)).card

/-- The base respondent gives each true and safe response the reciprocal of their number, and
every other response nothing. -/
theorem Model.R0_real_singleton (w : W) (q : Q) (r : R) :
    (m.R0 w q).real {r} = if m.Admissible w q r then ((m.admissibleCard w q : ℕ) : ℝ)⁻¹ else 0 := by
  have hcard : ({r | m.Admissible w q r} : Set R).ncard = m.admissibleCard w q := by
    rw [Set.ncard_eq_toFinset_card', Model.admissibleCard, Set.toFinset_ofPred]
  rw [Model.R0, uniformOn_real_apply, hcard]
  by_cases h : m.Admissible w q r
  · rw [Set.inter_eq_right.2 (Set.singleton_subset_iff.2
      (show r ∈ {r | m.Admissible w q r} from h)), Set.ncard_singleton]
    simp [h]
  · rw [Set.inter_singleton_eq_empty.2 (show r ∉ {r | m.Admissible w q r} from h),
      Set.ncard_empty]
    simp [h]

/-- The base respondent gives a response positive probability iff it is true and safe. -/
theorem Model.R0_apply_singleton_ne_zero_iff {w : W} {q : Q} {r : R} :
    m.R0 w q {r} ≠ 0 ↔ m.Admissible w q r := by
  classical
  rw [Model.R0, ← Finset.coe_filter_univ, uniformOn_finset_apply_singleton]
  simp

variable [DiscreteMeasurableSpace W]

/-- When every world admits a true and safe response, the base respondent always responds. -/
theorem Model.isMarkovKernel_R0Kernel (h : ∀ w q, 0 < m.admissibleCard w q) (q : Q) :
    IsMarkovKernel (m.R0Kernel q) :=
  ⟨fun w ↦ by
    obtain ⟨r, hr⟩ := Finset.card_pos.1 (h w q)
    exact isProbabilityMeasure_uniformOn (Set.toFinite _) ⟨r, (Finset.mem_filter.1 hr).2⟩⟩

section Posterior

variable {d : D} (hπ : ∀ w, m.prior d {w} ≠ 0)
include hπ

/-- Under a prior of full support, a response has positive marginal when some world admits
it. -/
theorem Model.R0Kernel_comp_apply_ne_zero {q : Q} {r : R} {w : W} (hadm : m.Admissible w q r) :
    (m.R0Kernel q ∘ₘ m.prior d) {r} ≠ 0 := by
  rw [Measure.comp_apply_singleton, Ne, Finset.sum_eq_zero_iff]
  exact fun h ↦ mul_ne_zero (hπ w) (m.R0_apply_singleton_ne_zero_iff.2 hadm) (h w (mem_univ w))

variable [Nonempty W] [IsFiniteMeasure (m.prior d)]

/-- Under a prior of full support, a world keeps positive posterior after a response iff the
response is true and safe there. -/
theorem Model.posterior_R0Kernel_apply_ne_zero_iff {q : Q} {r : R}
    (hm : (m.R0Kernel q ∘ₘ m.prior d) {r} ≠ 0) {w : W} :
    ((m.R0Kernel q)†(m.prior d)) r {w} ≠ 0 ↔ m.Admissible w q r := by
  rw [posterior_apply_singleton_ne_zero_iff _ _ hm]
  exact ⟨fun h ↦ m.R0_apply_singleton_ne_zero_iff.1 h.2,
    fun h ↦ ⟨hπ w, m.R0_apply_singleton_ne_zero_iff.2 h⟩⟩

end Posterior

/-- By the size principle (§2b), between two worlds of equal prior at which a response is true
and safe, the posterior favours the world with fewer true and safe alternatives. -/
theorem Model.posterior_R0Kernel_real_lt_iff [Nonempty W] {d : D} [IsFiniteMeasure (m.prior d)]
    {q : Q} {r : R} {w₁ w₂ : W} (hp : m.prior d {w₁} = m.prior d {w₂})
    (hpos : m.prior d {w₁} ≠ 0) (h₁ : m.Admissible w₁ q r) (h₂ : m.Admissible w₂ q r)
    (hm : (m.R0Kernel q ∘ₘ m.prior d) {r} ≠ 0) :
    (((m.R0Kernel q)†(m.prior d)) r).real {w₁} < (((m.R0Kernel q)†(m.prior d)) r).real {w₂} ↔
      m.admissibleCard w₂ q < m.admissibleCard w₁ q := by
  have hc : ∀ w, m.Admissible w q r → (0 : ℝ) < m.admissibleCard w q := fun w hw ↦
    Nat.cast_pos.2 (Finset.card_pos.2 ⟨r, Finset.mem_filter.2 ⟨mem_univ r, hw⟩⟩)
  have hμ : 0 < (m.prior d).real {w₁} := ENNReal.toReal_pos hpos (measure_ne_top _ _)
  have := posterior_real_finset_lt_iff (m.R0Kernel q) (m.prior d) hm {w₁} {w₂}
  simp only [Finset.coe_singleton, Finset.sum_singleton] at this
  have hp' : (m.prior d).real {w₂} = (m.prior d).real {w₁} := by
    rw [measureReal_def, measureReal_def, hp]
  simp only [Model.R0Kernel_apply, m.R0_real_singleton, h₁, h₂, ↓reduceIte] at this
  rw [this, hp', mul_lt_mul_iff_of_pos_left hμ, inv_lt_inv₀ (hc w₁ h₁) (hc w₂ h₂), Nat.cast_lt]

end BaseRespondent

/-! ### The questioner (§2b) -/

variable [Fintype A]

/-- The policy (2.2) of a decision problem under beliefs `π` is a softmax over expected utility
with rationality `αℵ`. -/
noncomputable def policy (U : W → A → ℝ) (αℵ : ℝ) (π : Measure W) : A → ℝ :=
  Real.softmax fun a ↦ αℵ * ∫ w, U w a ∂π

/-- The value `V(D)` of a decision problem is the expected utility of following its policy. -/
noncomputable def value [Nonempty A] (U : W → A → ℝ) (αℵ : ℝ) (π : Measure W) : ℝ :=
  ∑ a, policy U αℵ π a * ∫ w, U w a ∂π

variable [Nonempty A]

omit [Fintype A] [Nonempty A] in
/-- A belief under which the utility profile is almost surely `c` has `c` as expected
utility. -/
theorem integral_eq_of_ae {π : Measure W} [IsProbabilityMeasure π] {U : W → A → ℝ}
    {c : A → ℝ} (hU : ∀ᵐ w ∂π, U w = c) (a : A) : ∫ w, U w a ∂π = c a := by
  rw [integral_congr_ae (hU.mono fun w hw ↦ congrFun hw a)]
  simp

/-- Two beliefs under which the utility profile is almost surely the same have the same
value. -/
theorem value_eq_of_ae {π π' : Measure W} [IsProbabilityMeasure π] [IsProbabilityMeasure π']
    {U : W → A → ℝ} {c : A → ℝ} (αℵ : ℝ) (hU : ∀ᵐ w ∂π, U w = c) (hU' : ∀ᵐ w ∂π', U w = c) :
    value U αℵ π = value U αℵ π' := by
  simp only [value, policy, integral_eq_of_ae hU, integral_eq_of_ae hU']

variable [StandardBorelSpace W] [Nonempty W] [∀ d, IsFiniteMeasure (m.prior d)]
  (κ : Q → Kernel W R) [∀ q, IsFiniteKernel (κ q)]

/-- The expected value to the questioner of asking `q` (2.3) is the expected value of the
updated decision problem after the response drawn by `κ q`, less the weighted cost. -/
noncomputable def Model.questionScore (αℵ wc : ℝ) (d : D) (q : Q) : ℝ :=
  ∫ r, (value (m.utility d) αℵ (((κ q)†(m.prior d)) r) - wc * m.cost r) ∂(κ q ∘ₘ m.prior d)

/-- The question score is the value of information of the question under the policy value, plus
the value of the prior, less the expected cost. -/
theorem Model.questionScore_eq_valueOfInformation [Finite R] [MeasurableSingletonClass R]
    (αℵ wc : ℝ) (d : D) (q : Q) :
    m.questionScore κ αℵ wc d q =
      valueOfInformation (value (m.utility d) αℵ) (κ q) (m.prior d) +
        value (m.utility d) αℵ (m.prior d) - wc * ∫ r, m.cost r ∂(κ q ∘ₘ m.prior d) := by
  rw [Model.questionScore, integral_sub .of_finite .of_finite, integral_const_mul,
    valueOfInformation]
  ring

variable [Fintype Q]

/-- The questioner (2.3) is a softmax over question scores with rationality `αQ`. -/
noncomputable def Model.questioner (αℵ wc αQ : ℝ) (d : D) : Q → ℝ :=
  Real.softmax (αQ • m.questionScore κ αℵ wc d)

/-! ### The pragmatic respondent (§2c) -/

variable [Fintype D]

/-- The respondent's posterior over decision problems after hearing `q` inverts the questioner
by Bayes' rule, `π(D ∣ q) ∝ Q(q ∣ D) π(D)`. -/
noncomputable def Model.respondentPosterior (αℵ wc αQ : ℝ) (πD : D → ℝ) (q : Q) (d : D) : ℝ :=
  let z := ∑ d', m.questioner κ αℵ wc αQ d' q * πD d'
  if z = 0 then 0 else m.questioner κ αℵ wc αQ d q * πD d / z

/-- A question is a signal about the goal: with equal priors, the decision problem under
which the question was the more probable is the more probable after it. -/
theorem Model.respondentPosterior_lt_iff (αℵ wc αQ : ℝ) (πD : D → ℝ) (hπ : ∀ d, 0 ≤ πD d)
    (q : Q) {d₁ d₂ : D} (hp : πD d₁ = πD d₂) (hpos : 0 < πD d₁)
    (hz : ∑ d', m.questioner κ αℵ wc αQ d' q * πD d' ≠ 0) :
    m.respondentPosterior κ αℵ wc αQ πD q d₁ < m.respondentPosterior κ αℵ wc αQ πD q d₂ ↔
      m.questioner κ αℵ wc αQ d₁ q < m.questioner κ αℵ wc αQ d₂ q := by
  have : Nonempty Q := ⟨q⟩
  have hzpos : 0 < ∑ d', m.questioner κ αℵ wc αQ d' q * πD d' :=
    lt_of_le_of_ne (sum_nonneg fun d' _ ↦
      mul_nonneg (Real.softmax_nonneg _ q) (hπ d')) (Ne.symm hz)
  simp only [Model.respondentPosterior, hz, ↓reduceIte, ← hp]
  rw [div_lt_div_iff_of_pos_right hzpos]
  exact ⟨fun hlt ↦ lt_of_mul_lt_mul_right hlt hpos.le,
    fun hlt ↦ mul_lt_mul_of_pos_right hlt hpos⟩

/-- The utility of a response under one decision problem (2.5) weighs informativity by `1 − β`
and action relevance by `β`, less the weighted cost. -/
noncomputable def Model.singleScore (κ' : Q → Kernel W R) [∀ q, IsFiniteKernel (κ' q)]
    (αℵ wc β : ℝ) (πW : Measure W) (d : D) (q : Q) (r : R) : ℝ :=
  (1 - β) * -(klDiv (((κ' q)†(m.prior d)) r) πW).toReal +
    β * value (m.utility d) αℵ (((κ q)†(m.prior d)) r) - wc * m.cost r

variable (κ' : Q → Kernel W R) [∀ q, IsFiniteKernel (κ' q)]

/-- The pragmatic respondent's score (2.5) is the expected utility of a response over the
inferred decision problem. -/
noncomputable def Model.respondentScore (αℵ wc αQ β : ℝ) (πD : D → ℝ) (πW : Measure W) (q : Q)
    (r : R) : ℝ :=
  ∑ d, m.respondentPosterior κ αℵ wc αQ πD q d * m.singleScore κ κ' αℵ wc β πW d q r

/-- The pragmatic respondent (2.5) is a softmax over response scores with rationality `αR`. -/
noncomputable def Model.respondent [Fintype R] (αℵ wc αQ β αR : ℝ) (πD : D → ℝ) (πW : Measure W)
    (q : Q) :
    R → ℝ :=
  Real.softmax (αR • m.respondentScore κ κ' αℵ wc αQ β πD πW q)

/-- At `β = 1` the respondent weighs only action relevance and cost. -/
theorem Model.respondentScore_beta_one (αℵ wc αQ : ℝ) (πD : D → ℝ) (πW : Measure W) (q : Q)
    (r : R) :
    m.respondentScore κ κ' αℵ wc αQ 1 πD πW q r =
      ∑ d, m.respondentPosterior κ αℵ wc αQ πD q d *
        (value (m.utility d) αℵ (((κ q)†(m.prior d)) r) - wc * m.cost r) := by
  simp [Model.respondentScore, Model.singleScore]

/-- At `β = 0` the respondent weighs only informativity and cost. -/
theorem Model.respondentScore_beta_zero (αℵ wc αQ : ℝ) (πD : D → ℝ) (πW : Measure W) (q : Q)
    (r : R) :
    m.respondentScore κ κ' αℵ wc αQ 0 πD πW q r =
      ∑ d, m.respondentPosterior κ αℵ wc αQ πD q d *
        (-(klDiv (((κ' q)†(m.prior d)) r) πW).toReal - wc * m.cost r) := by
  simp [Model.respondentScore, Model.singleScore]

/-! ### Case study 1: credit cards (§3a) -/

/-- A card is one of the three credit cards of §3a. -/
inductive Card where
  | amex
  | mastercard
  | carteBlanche
  deriving DecidableEq, Fintype, Repr

/-- The questioner either stays or goes. -/
inductive Act where
  | stay
  | go
  deriving DecidableEq, Fintype, Repr, Inhabited

/-- A response is a polar answer to whether any card of `S` is accepted, the mention of some
accepted cards, or the exhaustive list of the accepted cards. -/
inductive Resp where
  | polar (S : Finset Card) (b : Bool)
  | mention (T : Finset Card)
  | exhaustive (T : Finset Card)
  deriving DecidableEq, Fintype

instance : MeasurableSpace Resp := ⊤

instance : MeasurableSpace (Finset Card) := ⊤

instance : DiscreteMeasurableSpace (Finset Card) := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩

/-- The decision problem `U1` turns on whether any of the questioner's cards `C` is accepted,
and `U2` on whether any card is accepted. -/
inductive Goal where
  | ownCards (C : Finset Card)
  | anyCard
  deriving DecidableEq, Fintype

/-- The utility of §3a is 5 for going when a relevant card is accepted or staying when none is,
and 0 otherwise. -/
def cardUtility : Goal → Finset Card → Act → ℝ
  | .ownCards C, w, .go => if (C ∩ w).Nonempty then 5 else 0
  | .ownCards C, w, .stay => if (C ∩ w).Nonempty then 0 else 5
  | .anyCard, w, .go => if w.Nonempty then 5 else 0
  | .anyCard, w, .stay => if w.Nonempty then 0 else 5

/-- `respProp r` is the proposition the response `r` asserts. -/
def respProp : Resp → Finset Card → Prop
  | .polar S b, w => (S ∩ w).Nonempty ↔ b = true
  | .mention T, w => T ⊆ w
  | .exhaustive T, w => T = w

instance : ∀ r, DecidablePred (respProp r)
  | .polar S b, w => inferInstanceAs (Decidable ((S ∩ w).Nonempty ↔ b = true))
  | .mention T, w => inferInstanceAs (Decidable (T ⊆ w))
  | .exhaustive T, w => inferInstanceAs (Decidable (T = w))

/-- In the credit-card model, a question asks whether any card of a set is accepted, worlds are
the sets of accepted cards, priors are uniform over the eight worlds, and a response costs
the cards it mentions. -/
noncomputable def cards : Model (Finset Card) (Finset Card) Resp Act Goal where
  question S w := (S ∩ w).Nonempty
  response := respProp
  utility := cardUtility
  prior _ := uniformOn Set.univ
  cost
    | .polar _ _ => 0
    | .mention T => T.card
    | .exhaustive T => T.card

instance : ∀ S, DecidablePred (cards.question S) :=
  fun S w ↦ inferInstanceAs (Decidable (S ∩ w).Nonempty)

instance : ∀ r, DecidablePred (cards.response r) :=
  fun r ↦ inferInstanceAs (DecidablePred (respProp r))

instance (d : Goal) : IsProbabilityMeasure (cards.prior d) :=
  inferInstanceAs (IsProbabilityMeasure (uniformOn Set.univ))

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
theorem polar_admissible : ∀ w q, 0 < cards.admissibleCard w q := fun w q ↦
  Finset.card_pos.2 ⟨.polar q (decide (q ∩ w).Nonempty), Finset.mem_filter.2 ⟨mem_univ _,
    ⟨by show (q ∩ w).Nonempty ↔ decide (q ∩ w).Nonempty = true; simp,
      polar_exhaustive_safe.1 q _⟩⟩⟩

private theorem cards_prior_ne_zero (d : Goal) (w : Finset Card) : cards.prior d {w} ≠ 0 :=
  uniformOn_univ_singleton_ne_zero w

/-- In (3), for a questioner holding the card asked about, after the answer "yes" the value of
the decision problem already equals its value after the exhaustive list, since every world
compatible with either answer accepts a card the questioner holds; only the cost separates
the two answers. -/
theorem yes_value_eq_exhaustive (C w : Finset Card) (hC : .amex ∈ C) (hw : .amex ∈ w)
    (αℵ : ℝ) :
    haveI := cards.isMarkovKernel_R0Kernel polar_admissible {.amex}
    value (cards.utility (.ownCards C)) αℵ
        (((cards.R0Kernel {.amex})†(cards.prior (.ownCards C))) (.polar {.amex} true)) =
      value (cards.utility (.ownCards C)) αℵ
        (((cards.R0Kernel {.amex})†(cards.prior (.ownCards C))) (.exhaustive w)) := by
  have hπ := cards_prior_ne_zero (.ownCards C)
  have hyes : cards.Admissible w {.amex} (.polar {.amex} true) := by
    refine ⟨?_, polar_exhaustive_safe.1 _ _⟩
    show ({Card.amex} ∩ w).Nonempty ↔ true = true
    simp [Finset.singleton_inter_of_mem hw]
  have hexh : cards.Admissible w {.amex} (.exhaustive w) := ⟨rfl, polar_exhaustive_safe.2 _ _⟩
  have hm₁ := cards.R0Kernel_comp_apply_ne_zero hπ hyes
  have hm₂ := cards.R0Kernel_comp_apply_ne_zero hπ hexh
  have hgo : ∀ w' : Finset Card, Card.amex ∈ w' →
      cards.utility (.ownCards C) w' = fun a ↦ match a with | .go => 5 | .stay => 0 :=
    fun w' hw' ↦ funext fun a ↦ by
      have hCw : (C ∩ w').Nonempty := ⟨.amex, Finset.mem_inter.2 ⟨hC, hw'⟩⟩
      cases a <;> simp [cards, cardUtility, hCw]
  refine value_eq_of_ae αℵ (ae_iff_of_countable.2 fun w' hw' ↦ hgo w' ?_)
    (ae_iff_of_countable.2 fun w' hw' ↦ hgo w' ?_)
  · obtain ⟨x, hx⟩ : ({Card.amex} ∩ w').Nonempty :=
      ((cards.posterior_R0Kernel_apply_ne_zero_iff hπ hm₁).1 hw').1.2 rfl
    rw [Finset.mem_inter, Finset.mem_singleton] at hx
    exact hx.1 ▸ hx.2
  · exact ((cards.posterior_R0Kernel_apply_ne_zero_iff hπ hm₂).1 hw').1 ▸ hw

/-- In (5), after "yes" to the general question, a world accepting only MasterCard keeps
positive posterior, so a questioner holding American Express remains uncertain; after "yes"
to the question about American Express it does not. -/
theorem generalYes_posterior_ne_zero :
    ((cards.R0Kernel univ)†(cards.prior (.ownCards {.amex}))) (.polar univ true)
        {{.mastercard}} ≠ 0 ∧
      ((cards.R0Kernel {.amex})†(cards.prior (.ownCards {.amex}))) (.polar {.amex} true)
        {{.mastercard}} = 0 := by
  have hπ := cards_prior_ne_zero (.ownCards {.amex})
  have h₁ : cards.Admissible {.mastercard} univ (.polar univ true) := by decide
  have h₂ : ¬ cards.Admissible {.mastercard} {.amex} (.polar {.amex} true) := by decide
  have h₃ : cards.Admissible {.amex} {.amex} (.polar {.amex} true) := by decide
  exact ⟨(cards.posterior_R0Kernel_apply_ne_zero_iff hπ
      (cards.R0Kernel_comp_apply_ne_zero hπ h₁)).2 h₁,
    not_not.1 fun h ↦ h₂ ((cards.posterior_R0Kernel_apply_ne_zero_iff hπ
      (cards.R0Kernel_comp_apply_ne_zero hπ h₃)).1 h)⟩

end HawkinsEtAl2025
