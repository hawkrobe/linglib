import Linglib.Pragmatics.RSA.Canonical
import Linglib.Pragmatics.RSA.LatentOperators
import Linglib.Pragmatics.RSA.QUD
import Linglib.Semantics.Exhaustification.Finite

/-!
# Exhaustivity and anti-exhaustivity in the Rational Speech Act framework

A listener who hears *A* where *A and B* was available infers that B is false. In the
baseline Rational Speech Act model the inference can reverse: a prior biased towards the
world where both A and B hold makes the literal listener already expect that world on
hearing *A*, so the speaker uses the cheap *A* there rather than in the world where only A
holds, and the pragmatic listener raises the probability of both A and B above her prior.
Over two worlds and the messages *A*, *A and B* and *A and not B*, the speaker prefers *A* to
*A and B* in the world of both exactly when the information *A and B* would add, the negated
log prior, is not worth its cost, and the listener is anti-exhaustive exactly when the log
odds of the prior exceed the cost disadvantage of *A and not B* over *A and B*, a condition
independent of the rationality parameter. The models that lift a parameter of the baseline
divide by whether they block this. Lexical uncertainty over free strengthenings, where *A*
may mean *A and B*, and the wonky-world models, where the listener doubts the speaker's
prior, remain anti-exhaustive for suitable priors, the Bayesian wonky model exactly when a
wonkiness-weighted difference of logistic values is positive. Lexical uncertainty restricted
to the grammatical exhaustification of *A*, the lexical-intentions speaker who chooses a
message together with its interpretation, and the supervaluationist speaker who addresses a
question under discussion and averages over the interpretations, all keep the posterior of
both A and B below its prior whenever *A and B* costs no more than *A and not B*, the
supervaluationist model for every cost. The experiment found no anti-exhaustivity in
production or in comprehension; the wonky and supervaluationist models fit best, and once the
two conjunctions are constrained to cost the same the models that cannot block
anti-exhaustivity fall behind.

## Implementation notes

* Meanings are interpretation functions on the three messages; the exhaustified one is
  derived by innocent exclusion from the substrate rather than stipulated. The literal
  listener is the substrate's prior-weighted conditioning, the speaker its softmax of the
  standard informativity utility with the paper's rationality and costs, and the pragmatic
  listener its Bayesian posterior; latent interpretations, questions and backgrounds enter
  through the substrate's marginalised and joint listeners. Every result is stated for an
  arbitrary prior in the open unit interval, positive rationality and arbitrary costs of the
  two conjunctions, as in the paper's appendix; the supervaluationist listener takes any prior
  on the questions that gives the fine one positive probability, while its speaker fixes the
  two interpretations equiprobable, as the paper's fits do.
* The supervaluationist speaker's expected utility over the two interpretations is defined
  here, on the substrate's projection of a listener onto the cells of a question; the prior of
  the question, common to every message, is left out of the utility.
* The paper's anti-exhaustivity is the posterior of both A and B exceeding the prior; the
  substrate's comparison of a posterior with its prior reduces it, over two worlds, to the
  comparison of the two likelihoods of *A*, and the closed forms of those likelihoods are
  logistic functions of utility differences. The non-Bayesian wonky model's anti-exhaustivity
  is reduced to the paper's rational inequality, which the paper resolves numerically.

## TODO

* The non-Bayesian wonky model's limits in the prior for positive wonkiness, anti-exhaustive
  as the prior tends to zero and exhaustive as it tends to one, are not proved.
* The Bayesian wonky model's threshold on the wonkiness, the limit of its condition as the
  prior tends to one, is not derived from the condition.
* Higher-order speakers and listeners, at which anti-exhaustivity can reappear in the
  grammatical models, the second-level analyses of the supervaluationist model, and the model
  fits are prose.

## References

* [A. Cremers, E. G. Wilcox, B. Spector, *Exhaustivity and anti-exhaustivity in the RSA
  framework* (2023)][cremers-wilcox-spector-2023]
* [M. C. Frank, N. D. Goodman, *Predicting pragmatic reasoning in language games*
  (2012)][frank-goodman-2012]
* [J. Degen et al., *Wonky worlds* (2015)][degen-etal-2015]
* [B. Spector, *The pragmatics of plural predication* (2017)][spector-2017]
* [L. Bergen, R. Levy, N. D. Goodman, *Pragmatic reasoning through semantic inference*
  (2016)][bergen-levy-goodman-2016]
* [M. Franke, L. Bergen, *Theory-driven statistical modeling for semantics and pragmatics*
  (2020)][franke-bergen-2020]
-/

open scoped ENNReal
open RSA.Canonical

namespace CremersWilcoxSpector2023

/-! ### Worlds, messages and interpretations -/

/-- The two worlds: only A true, or both A and B true. -/
inductive World where
  | wa
  | wab
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- The three messages: *A*, *A and B*, *A and not B*. -/
inductive Message where
  | a
  | aAndB
  | aAndNotB
  deriving DecidableEq, Repr, Fintype

/-- The literal meaning of each message. -/
def truth : Message → World → Bool
  | .a, _ => true
  | .aAndB, .wab => true
  | .aAndB, .wa => false
  | .aAndNotB, .wa => true
  | .aAndNotB, .wab => false

/-- The alternatives of a message: *A* has the scale-mate *A and B*. -/
def alternatives : Message → List (World → Bool)
  | .a => [truth .a, truth .aAndB]
  | u => [truth u]

/-- The exhaustified meaning, by innocent exclusion of the alternatives. -/
def exh (u : Message) (w : World) : Bool :=
  decide (w ∈ Exhaustification.innocent.exh (Exhaustification.altsFromPreds (alternatives u))
    (Exhaustification.predToFinset (truth u)))

/-- Exhaustification reads *A* as *A and not B*. -/
theorem exh_a (w : World) : exh .a w = truth .aAndNotB w := by cases w <;> decide

/-- *A and B* has no stronger alternative. -/
theorem exh_aAndB (w : World) : exh .aAndB w = truth .aAndB w := by cases w <;> decide

/-- *A and not B* has no stronger alternative. -/
theorem exh_aAndNotB (w : World) : exh .aAndNotB w = truth .aAndNotB w := by
  cases w <;> decide

/-- An interpretation function under which every message is true somewhere and every world
is described by some message, so that the literal listener and the speaker are defined. -/
structure Meaning where
  /-- The truth value of a message at a world. -/
  sat : Message → World → Bool
  /-- Every message is true somewhere. -/
  exists_world : ∀ u, ∃ w, sat u w = true
  /-- Every world is described by some message. -/
  exists_message : ∀ w, ∃ u, sat u w = true

/-- The literal interpretation. -/
def literal : Meaning := ⟨truth, by decide, by decide⟩

/-- The exhaustified interpretation, *A* read as *A and not B*. -/
def exhaustified : Meaning := ⟨exh, by decide, by decide⟩

/-- The anti-exhaustive interpretation of the free lexical-uncertainty model, *A* read as
*A and B*. -/
def antiExhaustive : Meaning :=
  ⟨λ u w => match u with | .a => truth .aAndB w | u => truth u w, by decide, by decide⟩

/-- The two grammatical interpretations, literal and exhaustified. -/
inductive Interpretation where
  | lit
  | exh
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- The meaning of a grammatical interpretation. -/
def Interpretation.meaning : Interpretation → Meaning
  | .lit => literal
  | .exh => exhaustified

/-- The three interpretations of the free lexical-uncertainty model. -/
inductive FreeInterpretation where
  | lit
  | exh
  | antiExh
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- The meaning of a free interpretation. -/
def FreeInterpretation.meaning : FreeInterpretation → Meaning
  | .lit => literal
  | .exh => exhaustified
  | .antiExh => antiExhaustive

/-- The wonky-world listener's two backgrounds: the speaker assumes a uniform prior or the
measured one. -/
inductive Background where
  | wonky
  | measured
  deriving DecidableEq, Repr, Fintype

/-- The questions under discussion: whether A holds, which the two worlds answer alike, or
which world obtains. -/
inductive QUD where
  | coarse
  | fine
  deriving DecidableEq, Repr, Fintype

section Sums

variable {β : Type*} [AddCommMonoid β]

/-- A sum over the two worlds. -/
theorem sum_World (f : World → β) : ∑ w, f w = f .wa + f .wab := by
  rw [show ∑ w, f w = f .wa + (f .wab + 0) from rfl, add_zero]

/-- A sum over the three messages. -/
theorem sum_Message (f : Message → β) : ∑ u, f u = f .a + f .aAndB + f .aAndNotB := by
  rw [show ∑ u, f u = f .a + (f .aAndB + (f .aAndNotB + 0)) from rfl, add_zero, add_assoc]

/-- A sum over the two grammatical interpretations. -/
theorem sum_Interpretation (f : Interpretation → β) : ∑ i, f i = f .lit + f .exh := by
  rw [show ∑ i, f i = f .lit + (f .exh + 0) from rfl, add_zero]

/-- A sum over the three free interpretations. -/
theorem sum_FreeInterpretation (f : FreeInterpretation → β) :
    ∑ i, f i = f .lit + f .exh + f .antiExh := by
  rw [show ∑ i, f i = f .lit + (f .exh + (f .antiExh + 0)) from rfl, add_zero, add_assoc]

/-- A sum over the two backgrounds. -/
theorem sum_Background (f : Background → β) : ∑ b, f b = f .wonky + f .measured := by
  rw [show ∑ b, f b = f .wonky + (f .measured + 0) from rfl, add_zero]

/-- A sum over the two questions. -/
theorem sum_QUD (f : QUD → β) : ∑ q, f q = f .coarse + f .fine := by
  rw [show ∑ q, f q = f .coarse + (f .fine + 0) from rfl, add_zero]

end Sums

/-! ### Priors and parameters -/

/-- The parameters of a model: the prior probability of both A and B, the rationality, and
the costs of the two conjunctions, *A* itself costing nothing. -/
structure Setting where
  /-- The prior probability of the world where both A and B hold. -/
  p : ℝ
  /-- The rationality, the paper's λ. -/
  lam : ℝ
  /-- The cost of *A and B*. -/
  cAB : ℝ
  /-- The cost of *A and not B*. -/
  cAnotB : ℝ
  /-- The world of both has positive prior probability. -/
  p_pos : 0 < p
  /-- The world of A alone has positive prior probability. -/
  p_lt_one : p < 1
  /-- The rationality is positive. -/
  lam_pos : 0 < lam

namespace Setting

variable (s : Setting)

/-- The cost of a message. -/
def cost : Message → ℝ
  | .a => 0
  | .aAndB => s.cAB
  | .aAndNotB => s.cAnotB

/-- The measured prior over the two worlds. -/
noncomputable def prior : PMF World :=
  PMF.ofFintype (λ w => match w with
    | .wa => ENNReal.ofReal (1 - s.p)
    | .wab => ENNReal.ofReal s.p) (by
    rw [sum_World]
    show ENNReal.ofReal (1 - s.p) + ENNReal.ofReal s.p = 1
    rw [← ENNReal.ofReal_add (by linarith [s.p_lt_one]) s.p_pos.le, sub_add_cancel,
      ENNReal.ofReal_one])

/-- The prior of the world of A alone. -/
theorem prior_wa : s.prior .wa = ENNReal.ofReal (1 - s.p) := rfl

/-- The prior of the world of both. -/
theorem prior_wab : s.prior .wab = ENNReal.ofReal s.p := rfl

/-- The prior is positive on both worlds. -/
theorem prior_ne_zero (w : World) : s.prior w ≠ 0 := by
  cases w
  · exact (ENNReal.ofReal_pos.mpr (by linarith [s.p_lt_one])).ne'
  · exact (ENNReal.ofReal_pos.mpr s.p_pos).ne'

/-- The prior of the world of A alone, as a real. -/
theorem prior_wa_toReal : (s.prior .wa).toReal = 1 - s.p :=
  ENNReal.toReal_ofReal (by linarith [s.p_lt_one])

/-- The prior of the world of both, as a real. -/
theorem prior_wab_toReal : (s.prior .wab).toReal = s.p := ENNReal.toReal_ofReal s.p_pos.le

/-- The prior sums to one. -/
theorem prior_add : s.prior .wa + s.prior .wab = 1 := by
  rw [prior_wa, prior_wab, ← ENNReal.ofReal_add (by linarith [s.p_lt_one]) s.p_pos.le,
    sub_add_cancel, ENNReal.ofReal_one]

end Setting

/-- The wonky prior: uniform over the two worlds. -/
noncomputable def wonkyPrior : PMF World := PMF.uniformOfFintype World

/-- The wonky prior gives each world a half. -/
theorem wonkyPrior_apply (w : World) : wonkyPrior w = 2⁻¹ := by
  rw [wonkyPrior, PMF.uniformOfFintype_apply, show Fintype.card World = 2 from rfl]
  norm_cast

/-- The wonky prior is positive on both worlds. -/
theorem wonkyPrior_ne_zero (w : World) : wonkyPrior w ≠ 0 := by rw [wonkyPrior_apply]; simp

/-- The wonky prior of a world, as a real. -/
theorem wonkyPrior_toReal (w : World) : (wonkyPrior w).toReal = 2⁻¹ := by
  rw [wonkyPrior_apply, ENNReal.toReal_inv]; simp

/-! ### The literal listener and the speaker under an interpretation (eqs. 1 to 3) -/

section Speaker

variable (P : PMF World) (hP : ∀ w, P w ≠ 0) (m : Meaning)
include hP

/-- The prior mass of a message's extension is positive. -/
theorem meaning_ne_zero (u : Message) :
    (∑' w, P w * (if m.sat u w then (1 : ℝ≥0∞) else 0)) ≠ 0 := by
  obtain ⟨w, hw⟩ := m.exists_world u
  exact ENNReal.summable.tsum_ne_zero_iff.mpr ⟨w, by rw [hw]; simpa using hP w⟩

/-- eq. (1): the literal listener, the prior conditioned on the message's meaning. -/
noncomputable def L0 (u : Message) : PMF World :=
  RSA.L0LassiterGoodman P m.sat u (meaning_ne_zero P hP m u)

/-- The literal listener in closed form. -/
theorem L0_apply (u : Message) (w : World) :
    L0 P hP m u w =
      P w * (if m.sat u w then 1 else 0) * (∑' w', P w' * (if m.sat u w' then 1 else 0))⁻¹ :=
  RSA.L0LassiterGoodman_apply _ _ _ _ _

/-- A message true at a world has positive mass there. -/
theorem L0_ne_zero {u : Message} {w : World} (h : m.sat u w = true) : L0 P hP m u w ≠ 0 :=
  (PMF.mem_support_iff _ _).mp
    ((RSA.mem_support_L0LassiterGoodman_iff _ _ _ _ w).mpr ⟨hP w, h⟩)

/-- A message false at a world gets no mass there. -/
theorem L0_eq_zero {u : Message} {w : World} (h : m.sat u w = false) : L0 P hP m u w = 0 := by
  rw [L0_apply, h]; simp

/-- A message true at one world only puts all its mass there. -/
theorem L0_eq_one {u : Message} {w : World} (h : m.sat u w = true)
    (h' : ∀ w', m.sat u w' = true → w' = w) : L0 P hP m u w = 1 := by
  rw [L0_apply, tsum_eq_single w (λ w' hne => by
    rw [Bool.eq_false_iff.mpr (λ hw => hne (h' w' hw))]; simp), h]
  simp [ENNReal.mul_inv_cancel (hP w) (PMF.apply_ne_top P w)]

/-- The tautology *A* leaves the prior unchanged. -/
theorem L0_literal_a (w : World) : L0 P hP literal .a w = P w :=
  RSA.L0LassiterGoodman_apply_of_meaning_true P truth .a (λ w => by cases w <;> rfl) _ w

/-- *A and B* singles out the world of both. -/
theorem L0_literal_aAndB_wab : L0 P hP literal .aAndB .wab = 1 :=
  L0_eq_one _ _ _ rfl (by decide)

/-- *A and B* is false in the world of A alone. -/
theorem L0_literal_aAndB_wa : L0 P hP literal .aAndB .wa = 0 := L0_eq_zero _ _ _ rfl

/-- *A and not B* singles out the world of A alone. -/
theorem L0_literal_aAndNotB_wa : L0 P hP literal .aAndNotB .wa = 1 :=
  L0_eq_one _ _ _ rfl (by decide)

/-- *A and not B* is false in the world of both. -/
theorem L0_literal_aAndNotB_wab : L0 P hP literal .aAndNotB .wab = 0 := L0_eq_zero _ _ _ rfl

/-- Exhaustified *A* singles out the world of A alone. -/
theorem L0_exhaustified_a_wa : L0 P hP exhaustified .a .wa = 1 :=
  L0_eq_one _ _ _ (by decide) (by decide)

/-- Exhaustified *A* is false in the world of both. -/
theorem L0_exhaustified_a_wab : L0 P hP exhaustified .a .wab = 0 :=
  L0_eq_zero _ _ _ (by decide)

/-- Under exhaustification *A and B* still singles out the world of both. -/
theorem L0_exhaustified_aAndB_wab : L0 P hP exhaustified .aAndB .wab = 1 :=
  L0_eq_one _ _ _ (by decide) (by decide)

/-- Under exhaustification *A and B* is still false in the world of A alone. -/
theorem L0_exhaustified_aAndB_wa : L0 P hP exhaustified .aAndB .wa = 0 :=
  L0_eq_zero _ _ _ (by decide)

/-- Under exhaustification *A and not B* still singles out the world of A alone. -/
theorem L0_exhaustified_aAndNotB_wa : L0 P hP exhaustified .aAndNotB .wa = 1 :=
  L0_eq_one _ _ _ (by decide) (by decide)

/-- Under exhaustification *A and not B* is still false in the world of both. -/
theorem L0_exhaustified_aAndNotB_wab : L0 P hP exhaustified .aAndNotB .wab = 0 :=
  L0_eq_zero _ _ _ (by decide)

/-- Anti-exhaustive *A* singles out the world of both. -/
theorem L0_antiExhaustive_a_wab : L0 P hP antiExhaustive .a .wab = 1 :=
  L0_eq_one _ _ _ rfl (by decide)

/-- Anti-exhaustive *A* is false in the world of A alone. -/
theorem L0_antiExhaustive_a_wa : L0 P hP antiExhaustive .a .wa = 0 := L0_eq_zero _ _ _ rfl

/-- Under the anti-exhaustive reading *A and B* still singles out the world of both. -/
theorem L0_antiExhaustive_aAndB_wab : L0 P hP antiExhaustive .aAndB .wab = 1 :=
  L0_eq_one _ _ _ rfl (by decide)

/-- Under the anti-exhaustive reading *A and not B* is still false in the world of both. -/
theorem L0_antiExhaustive_aAndNotB_wab : L0 P hP antiExhaustive .aAndNotB .wab = 0 :=
  L0_eq_zero _ _ _ rfl

variable (s : Setting)

/-- eq. (2): the utility of a message at a world for the literal listener under the
interpretation, the rationality times the log probability of the world less the cost. -/
noncomputable def utility (w : World) (u : Message) : EReal :=
  rsaUtility (λ w u => L0 P hP m u w) s.cost s.lam w u

instance : ViableSpeaker (utility P hP m s) :=
  viableSpeaker_rsaUtility _ _ s.lam_pos (λ _ _ => PMF.apply_ne_top _ _) λ w =>
    let ⟨u, hu⟩ := m.exists_message w
    ⟨u, L0_ne_zero P hP m hu⟩

/-- eq. (3): the speaker, the softmax of the utility. -/
noncomputable def speaker (w : World) : PMF Message := S1 (utility P hP m s) w

/-- The utility is `⊥` at a message false at the world and otherwise real. -/
theorem utility_eq (w : World) (u : Message) :
    utility P hP m s w u =
      if L0 P hP m u w = 0 then ⊥
      else ((s.lam * (Real.log (L0 P hP m u w).toReal - s.cost u) : ℝ) : EReal) :=
  rsaUtility_eq _ _ s.lam_pos (PMF.apply_ne_top _ _)

/-- The softmax weight of a message: zero at a message false at the world. -/
theorem softmaxWeight_utility (w : World) (u : Message) :
    PMF.softmaxWeight (utility P hP m s w) u =
      if L0 P hP m u w = 0 then 0
      else ENNReal.ofReal (Real.exp (s.lam * (Real.log (L0 P hP m u w).toReal - s.cost u))) :=
  softmaxWeight_rsaUtility _ _ s.lam_pos (PMF.apply_ne_top _ _)

/-- The speaker in closed form. -/
theorem speaker_apply (w : World) (u : Message) :
    speaker P hP m s w u =
      PMF.softmaxWeight (utility P hP m s w) u / ∑ v, PMF.softmaxWeight (utility P hP m s w) v :=
  PMF.softmax_apply _ (ViableSpeaker.no_top w) (ViableSpeaker.some_finite w) u

/-- The speaker uses every message true at the world. -/
theorem speaker_ne_zero {w : World} {u : Message} (h : m.sat u w = true) :
    speaker P hP m s w u ≠ 0 :=
  S1_ne_zero _ (by rw [utility_eq, if_neg (L0_ne_zero P hP m h)]; exact EReal.coe_ne_bot _)

end Speaker

/-- The literal listener with the measured prior. -/
noncomputable abbrev Setting.L0 (s : Setting) (m : Meaning) : Message → PMF World :=
  CremersWilcoxSpector2023.L0 s.prior s.prior_ne_zero m

/-- The speaker with the measured prior in the literal listener. -/
noncomputable abbrev Setting.speaker (s : Setting) (m : Meaning) : World → PMF Message :=
  CremersWilcoxSpector2023.speaker s.prior s.prior_ne_zero m s

/-! ### Closed forms: the speaker's use of *A* is a logistic function -/

section ClosedForms

variable (P : PMF World) (hP : ∀ w, P w ≠ 0) (s : Setting)

/-- eq. (A.3): in the world of both, the literal speaker's use of *A* is the logistic
function of the cost of *A and B* plus the log prior. -/
theorem speaker_literal_wab_a :
    speaker P hP literal s .wab .a =
      ENNReal.ofReal (Real.sigmoid (s.lam * (s.cAB + Real.log (P .wab).toReal))) := by
  rw [speaker_apply, sum_Message]
  simp only [softmaxWeight_utility, L0_literal_a, L0_literal_aAndB_wab, L0_literal_aAndNotB_wab,
    hP .wab, one_ne_zero, ↓reduceIte, add_zero, ENNReal.toReal_one, Real.log_one, Setting.cost]
  rw [ENNReal.ofReal_exp_div_add_ofReal_exp]
  congr 2; ring

/-- eq. (A.2): in the world of A alone, the use of *A* is the logistic function of the
cost of *A and not B* plus the log prior. -/
theorem speaker_literal_wa_a :
    speaker P hP literal s .wa .a =
      ENNReal.ofReal (Real.sigmoid (s.lam * (s.cAnotB + Real.log (P .wa).toReal))) := by
  rw [speaker_apply, sum_Message]
  simp only [softmaxWeight_utility, L0_literal_a, L0_literal_aAndB_wa, L0_literal_aAndNotB_wa,
    hP .wa, one_ne_zero, ↓reduceIte, add_zero, ENNReal.toReal_one, Real.log_one, Setting.cost]
  rw [ENNReal.ofReal_exp_div_add_ofReal_exp]
  congr 2; ring

/-- Under the exhaustified interpretation *A* is as informative as *A and not B* in the
world of A alone, so its use is the logistic function of the latter's cost. -/
theorem speaker_exhaustified_wa_a :
    speaker P hP exhaustified s .wa .a = ENNReal.ofReal (Real.sigmoid (s.lam * s.cAnotB)) := by
  rw [speaker_apply, sum_Message]
  simp only [softmaxWeight_utility, L0_exhaustified_a_wa, L0_exhaustified_aAndB_wa,
    L0_exhaustified_aAndNotB_wa, one_ne_zero, ↓reduceIte, add_zero, ENNReal.toReal_one,
    Real.log_one, Setting.cost]
  rw [ENNReal.ofReal_exp_div_add_ofReal_exp]
  congr 2; ring

/-- Under the exhaustified interpretation *A* is false in the world of both. -/
theorem speaker_exhaustified_wab_a : speaker P hP exhaustified s .wab .a = 0 := by
  rw [speaker_apply, softmaxWeight_utility, L0_exhaustified_a_wab, if_pos rfl, ENNReal.zero_div]

/-- Under the anti-exhaustive interpretation *A* is as informative as *A and B* in the world
of both. -/
theorem speaker_antiExhaustive_wab_a :
    speaker P hP antiExhaustive s .wab .a = ENNReal.ofReal (Real.sigmoid (s.lam * s.cAB)) := by
  rw [speaker_apply, sum_Message]
  simp only [softmaxWeight_utility, L0_antiExhaustive_a_wab, L0_antiExhaustive_aAndB_wab,
    L0_antiExhaustive_aAndNotB_wab, one_ne_zero, ↓reduceIte, add_zero, ENNReal.toReal_one,
    Real.log_one, Setting.cost]
  rw [ENNReal.ofReal_exp_div_add_ofReal_exp]
  congr 2; ring

/-- Under the anti-exhaustive interpretation *A* is false in the world of A alone. -/
theorem speaker_antiExhaustive_wa_a : speaker P hP antiExhaustive s .wa .a = 0 := by
  rw [speaker_apply, softmaxWeight_utility, L0_antiExhaustive_a_wa, if_pos rfl,
    ENNReal.zero_div]

end ClosedForms

/-! ### Two-world Bayes -/

/-- Against a two-point prior, the likelihood at a point exceeds the marginal likelihood
exactly when it exceeds the likelihood at the other point. -/
private theorem two_world_lt {a b x y : ℝ≥0∞} (hab : a + b = 1) (ha : a ≠ 0) (hx : x ≠ ⊤) :
    a * y + b * x < x ↔ y < x := by
  have ha' : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hab ▸ le_self_add)
  have hb' : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hab ▸ le_add_self)
  have h : a * y + b * x < a * x + b * x ↔ y < x := by
    rw [ENNReal.add_lt_add_iff_right (ENNReal.mul_ne_top hb' hx),
      ENNReal.mul_lt_mul_iff_right ha ha']
  rwa [← add_mul, hab, one_mul] at h

private theorem lt_two_world {a b x y : ℝ≥0∞} (hab : a + b = 1) (ha : a ≠ 0) (hx : x ≠ ⊤) :
    x < a * y + b * x ↔ x < y := by
  have ha' : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hab ▸ le_self_add)
  have hb' : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hab ▸ le_add_self)
  have h : a * x + b * x < a * y + b * x ↔ x < y := by
    rw [ENNReal.add_lt_add_iff_right (ENNReal.mul_ne_top hb' hx),
      ENNReal.mul_lt_mul_iff_right ha ha']
  rwa [← add_mul, hab, one_mul] at h

/-! ### The baseline model (§3) -/

section Baseline

variable (s : Setting)

/-- (6a): in the world of both, the speaker prefers *A* to *A and B* exactly when the
information *A and B* would add, the negated log prior, does not exceed its cost. -/
theorem baseline_aAndB_lt_a_iff :
    s.speaker literal .wab .aAndB < s.speaker literal .wab .a ↔ -s.cAB < Real.log s.p := by
  dsimp only [Setting.speaker]
  rw [speaker, S1_prefers_iff, utility_eq, utility_eq, L0_literal_aAndB_wab, L0_literal_a,
    if_neg one_ne_zero, if_neg (s.prior_ne_zero _), Setting.prior_wab_toReal,
    ENNReal.toReal_one, Real.log_one, EReal.coe_lt_coe_iff]
  simp only [Setting.cost, zero_sub, sub_zero]
  exact mul_lt_mul_iff_of_pos_left s.lam_pos

/-- (7): in the world of A alone, the speaker prefers *A and not B* to *A* exactly when
the negated log prior exceeds its cost. -/
theorem baseline_a_lt_aAndNotB_iff :
    s.speaker literal .wa .a < s.speaker literal .wa .aAndNotB ↔
      Real.log (1 - s.p) < -s.cAnotB := by
  dsimp only [Setting.speaker]
  rw [speaker, S1_prefers_iff, utility_eq, utility_eq, L0_literal_aAndNotB_wa, L0_literal_a,
    if_neg one_ne_zero, if_neg (s.prior_ne_zero _), Setting.prior_wa_toReal,
    ENNReal.toReal_one, Real.log_one, EReal.coe_lt_coe_iff]
  simp only [Setting.cost, zero_sub, sub_zero]
  exact mul_lt_mul_iff_of_pos_left s.lam_pos

/-- Every message is used somewhere, so has positive marginal likelihood. -/
theorem baseline_marginal_ne_zero (u : Message) :
    PMF.marginal (s.speaker literal) s.prior u ≠ 0 :=
  let ⟨w, hw⟩ := literal.exists_world u
  PMF.marginal_ne_zero _ _ _ (s.prior_ne_zero w) (speaker_ne_zero _ _ _ _ hw)

/-- eq. (4): the pragmatic listener. -/
noncomputable def listener (u : Message) : PMF World :=
  RSA.L1 (s.speaker literal) s.prior u (baseline_marginal_ne_zero s u)

/-- (A.4): the listener is anti-exhaustive, the posterior of both A and B exceeding the
prior, exactly when the speaker uses *A* more in the world of both than in the world of A
alone. -/
theorem prior_lt_listener_iff_speaker_lt :
    s.prior .wab < listener s .a .wab ↔ s.speaker literal .wa .a < s.speaker literal .wab .a := by
  rw [listener, RSA.L1, PMF.lt_posterior_iff_marginal_lt _ _ _ _ (s.prior_ne_zero _)]
  unfold PMF.marginal
  rw [PMF.bind_apply_eq_finset_sum, sum_World]
  exact two_world_lt s.prior_add (s.prior_ne_zero _) (PMF.apply_ne_top _ _)

/-- (6b): the listener is anti-exhaustive exactly when the log odds of the prior exceed the
cost disadvantage of *A and not B* over *A and B*, whatever the rationality. -/
theorem prior_lt_listener_iff :
    s.prior .wab < listener s .a .wab ↔
      s.cAnotB - s.cAB < Real.log s.p - Real.log (1 - s.p) := by
  rw [prior_lt_listener_iff_speaker_lt]
  dsimp only [Setting.speaker]
  rw [speaker_literal_wa_a, speaker_literal_wab_a, Setting.prior_wa_toReal,
    Setting.prior_wab_toReal, ENNReal.ofReal_lt_ofReal_iff (Real.sigmoid_pos _),
    Real.sigmoid_lt_iff, mul_lt_mul_iff_of_pos_left s.lam_pos]
  constructor <;> intro h <;> linarith

/-- With equal costs, anti-exhaustivity is a prior biased towards the world of both. -/
theorem prior_lt_listener_iff_of_cost_eq (hc : s.cAB = s.cAnotB) :
    s.prior .wab < listener s .a .wab ↔ 1 / 2 < s.p := by
  rw [prior_lt_listener_iff, hc, sub_self, sub_pos,
    Real.log_lt_log_iff (by linarith [s.p_lt_one]) s.p_pos]
  constructor <;> intro <;> linarith

/-- At the costs of the paper's first figure, a half and one, anti-exhaustivity sets in
where the log odds of the prior exceed a half, whatever the rationality. -/
theorem prior_lt_listener_iff_of_cost (hAB : s.cAB = 1 / 2) (hAnotB : s.cAnotB = 1) :
    s.prior .wab < listener s .a .wab ↔ 1 / 2 < Real.log s.p - Real.log (1 - s.p) := by
  rw [prior_lt_listener_iff, hAB, hAnotB]; norm_num

end Baseline

/-! ### Lexical uncertainty (§4.3) -/

section LexicalUncertainty

variable (s : Setting)

/-- The speaker of the grammatical lexical-uncertainty model, marginalised over the two
equiprobable interpretations. -/
noncomputable def luSpeaker (w : World) : PMF Message :=
  RSA.marginalizeKernel (PMF.uniformOfFintype Interpretation)
    (λ i w => s.speaker i.meaning w) w

/-- The grammatical lexical-uncertainty speaker in closed form. -/
theorem luSpeaker_apply (w : World) (u : Message) :
    luSpeaker s w u = 2⁻¹ * s.speaker literal w u + 2⁻¹ * s.speaker exhaustified w u := by
  rw [luSpeaker, RSA.marginalizeKernel_apply, tsum_fintype, sum_Interpretation]
  simp [PMF.uniformOfFintype_apply, Interpretation.meaning, show Fintype.card Interpretation = 2
    from rfl]

/-- Every message is used somewhere, so has positive marginal likelihood. -/
theorem luMarginal_ne_zero (u : Message) : PMF.marginal (luSpeaker s) s.prior u ≠ 0 :=
  let ⟨w, hw⟩ := literal.exists_world u
  PMF.marginal_ne_zero _ _ _ (s.prior_ne_zero w) (by
    rw [luSpeaker_apply]
    intro h
    rcases mul_eq_zero.mp (add_eq_zero.mp h).1 with h | h
    · simp at h
    · exact speaker_ne_zero _ _ _ _ hw h)

/-- item 4 of the §4.3 model: the pragmatic listener of the grammatical lexical-uncertainty
model. -/
noncomputable def luListener (u : Message) : PMF World :=
  RSA.L1 (luSpeaker s) s.prior u (luMarginal_ne_zero s u)

/-- Grammatical lexical uncertainty blocks anti-exhaustivity whenever *A and B* costs no more
than *A and not B*: the exhaustified interpretation never uses *A* in the world of both but
uses it in the world of A alone more than the literal interpretation uses it in the world of
both. -/
theorem luListener_lt_prior (hc : s.cAB ≤ s.cAnotB) : luListener s .a .wab < s.prior .wab := by
  rw [luListener, RSA.L1, PMF.posterior_lt_iff_lt_marginal _ _ _ _ (s.prior_ne_zero _)]
  unfold PMF.marginal
  rw [PMF.bind_apply_eq_finset_sum, sum_World,
    lt_two_world s.prior_add (s.prior_ne_zero _) (PMF.apply_ne_top _ _), luSpeaker_apply,
    luSpeaker_apply]
  dsimp only [Setting.speaker]
  rw [speaker_literal_wab_a, speaker_exhaustified_wab_a, speaker_literal_wa_a,
    speaker_exhaustified_wa_a, mul_zero, add_zero, ← mul_add,
    ENNReal.mul_lt_mul_iff_right (by simp) (by simp), Setting.prior_wab_toReal,
    Setting.prior_wa_toReal, ← ENNReal.ofReal_add (Real.sigmoid_nonneg _) (Real.sigmoid_nonneg _),
    ENNReal.ofReal_lt_ofReal_iff (add_pos (Real.sigmoid_pos _) (Real.sigmoid_pos _))]
  calc Real.sigmoid (s.lam * (s.cAB + Real.log s.p)) < Real.sigmoid (s.lam * s.cAnotB) :=
        Real.sigmoid_lt (mul_lt_mul_of_pos_left
          (by linarith [Real.log_neg s.p_pos s.p_lt_one]) s.lam_pos)
    _ ≤ _ := le_add_of_nonneg_left (Real.sigmoid_nonneg _)

/-- The speaker of the free lexical-uncertainty model, marginalised over the three
equiprobable interpretations. -/
noncomputable def freeSpeaker (w : World) : PMF Message :=
  RSA.marginalizeKernel (PMF.uniformOfFintype FreeInterpretation)
    (λ i w => s.speaker i.meaning w) w

/-- The free lexical-uncertainty speaker in closed form. -/
theorem freeSpeaker_apply (w : World) (u : Message) :
    freeSpeaker s w u =
      3⁻¹ * s.speaker literal w u + 3⁻¹ * s.speaker exhaustified w u +
        3⁻¹ * s.speaker antiExhaustive w u := by
  rw [freeSpeaker, RSA.marginalizeKernel_apply, tsum_fintype, sum_FreeInterpretation]
  simp [PMF.uniformOfFintype_apply, FreeInterpretation.meaning,
    show Fintype.card FreeInterpretation = 3 from rfl]

/-- Every message is used somewhere, so has positive marginal likelihood. -/
theorem freeMarginal_ne_zero (u : Message) : PMF.marginal (freeSpeaker s) s.prior u ≠ 0 :=
  let ⟨w, hw⟩ := literal.exists_world u
  PMF.marginal_ne_zero _ _ _ (s.prior_ne_zero w) (by
    rw [freeSpeaker_apply]
    intro h
    rcases mul_eq_zero.mp (add_eq_zero.mp (add_eq_zero.mp h).1).1 with h | h
    · simp at h
    · exact speaker_ne_zero _ _ _ _ hw h)

/-- The pragmatic listener of the free lexical-uncertainty model. -/
noncomputable def freeListener (u : Message) : PMF World :=
  RSA.L1 (freeSpeaker s) s.prior u (freeMarginal_ne_zero s u)

/-- Free lexical uncertainty is anti-exhaustive exactly when the literal and anti-exhaustive
uses of *A* in the world of both outweigh the literal and exhaustified uses in the world of A
alone. -/
theorem prior_lt_freeListener_iff :
    s.prior .wab < freeListener s .a .wab ↔
      Real.sigmoid (s.lam * (s.cAnotB + Real.log (1 - s.p))) +
          Real.sigmoid (s.lam * s.cAnotB) <
        Real.sigmoid (s.lam * (s.cAB + Real.log s.p)) + Real.sigmoid (s.lam * s.cAB) := by
  rw [freeListener, RSA.L1, PMF.lt_posterior_iff_marginal_lt _ _ _ _ (s.prior_ne_zero _)]
  unfold PMF.marginal
  rw [PMF.bind_apply_eq_finset_sum, sum_World,
    two_world_lt s.prior_add (s.prior_ne_zero _) (PMF.apply_ne_top _ _), freeSpeaker_apply,
    freeSpeaker_apply]
  dsimp only [Setting.speaker]
  rw [speaker_literal_wab_a, speaker_exhaustified_wab_a, speaker_antiExhaustive_wab_a,
    speaker_literal_wa_a, speaker_exhaustified_wa_a, speaker_antiExhaustive_wa_a]
  simp only [mul_zero, add_zero]
  rw [← mul_add, ← mul_add, ENNReal.mul_lt_mul_iff_right (by simp) (by simp),
    Setting.prior_wab_toReal, Setting.prior_wa_toReal,
    ← ENNReal.ofReal_add (Real.sigmoid_nonneg _) (Real.sigmoid_nonneg _),
    ← ENNReal.ofReal_add (Real.sigmoid_nonneg _) (Real.sigmoid_nonneg _),
    ENNReal.ofReal_lt_ofReal_iff (add_pos (Real.sigmoid_pos _) (Real.sigmoid_pos _))]

/-- With equal costs, free lexical uncertainty is anti-exhaustive exactly when the baseline
is: for a prior biased towards the world of both. -/
theorem prior_lt_freeListener_iff_of_cost_eq (hc : s.cAB = s.cAnotB) :
    s.prior .wab < freeListener s .a .wab ↔ 1 / 2 < s.p := by
  rw [prior_lt_freeListener_iff, hc, add_lt_add_iff_right, Real.sigmoid_lt_iff,
    mul_lt_mul_iff_of_pos_left s.lam_pos, add_lt_add_iff_left,
    Real.log_lt_log_iff (by linarith [s.p_lt_one]) s.p_pos]
  constructor <;> intro <;> linarith

end LexicalUncertainty

/-! ### Lexical intentions (§4.4) -/

section LexicalIntentions

variable (s : Setting)

/-- item 2 of the §4.4 model: the utility of a message together with the interpretation the
literal listener will give it. -/
noncomputable def liUtility (w : World) (x : Message × Interpretation) : EReal :=
  rsaUtility (λ w x => s.L0 x.2.meaning x.1 w) (λ x => s.cost x.1) s.lam w x

instance : ViableSpeaker (liUtility s) :=
  viableSpeaker_rsaUtility _ _ s.lam_pos (λ _ _ => PMF.apply_ne_top _ _) λ w =>
    ⟨(.a, .lit), L0_ne_zero _ _ _ (by cases w <;> rfl)⟩

/-- item 3 of the §4.4 model: the joint speaker over messages and interpretations. -/
noncomputable def liSpeaker (w : World) : PMF (Message × Interpretation) := S1 (liUtility s) w

/-- item 5 of the §4.4 model: the speaker's messages, the interpretations marginalised. -/
noncomputable def liMessageSpeaker (w : World) : PMF Message := (liSpeaker s w).map Prod.fst

/-- The lexical-intentions speaker's use of a message sums its two interpretations. -/
theorem liMessageSpeaker_apply (w : World) (u : Message) :
    liMessageSpeaker s w u = liSpeaker s w (u, .lit) + liSpeaker s w (u, .exh) := by
  rw [liMessageSpeaker, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, sum_Message]
  cases u <;> simp [sum_Interpretation]

/-- The joint speaker in closed form. -/
theorem liSpeaker_apply (w : World) (x : Message × Interpretation) :
    liSpeaker s w x =
      PMF.softmaxWeight (liUtility s w) x / ∑ y, PMF.softmaxWeight (liUtility s w) y :=
  PMF.softmax_apply _ (ViableSpeaker.no_top w) (ViableSpeaker.some_finite w) x

/-- The lexical-intentions utility is `⊥` at a message false at the world under its
interpretation and otherwise real. -/
theorem liUtility_eq (w : World) (x : Message × Interpretation) :
    liUtility s w x =
      if s.L0 x.2.meaning x.1 w = 0 then ⊥
      else ((s.lam * (Real.log (s.L0 x.2.meaning x.1 w).toReal - s.cost x.1) : ℝ) : EReal) :=
  rsaUtility_eq _ _ s.lam_pos (PMF.apply_ne_top _ _)

/-- The softmax weight of a message under an interpretation. -/
theorem softmaxWeight_liUtility (w : World) (x : Message × Interpretation) :
    PMF.softmaxWeight (liUtility s w) x =
      if s.L0 x.2.meaning x.1 w = 0 then 0
      else ENNReal.ofReal (Real.exp
        (s.lam * (Real.log (s.L0 x.2.meaning x.1 w).toReal - s.cost x.1))) :=
  softmaxWeight_rsaUtility _ _ s.lam_pos (PMF.apply_ne_top _ _)

/-- In the world of both, the lexical-intentions speaker uses *A*, under its literal
interpretation only, against the two interpretations of *A and B*. -/
theorem liMessageSpeaker_wab_a :
    liMessageSpeaker s .wab .a =
      ENNReal.ofReal (Real.exp (s.lam * Real.log s.p) /
        (Real.exp (s.lam * Real.log s.p) + 2 * Real.exp (-(s.lam * s.cAB)))) := by
  rw [liMessageSpeaker_apply, liSpeaker_apply, liSpeaker_apply, Fintype.sum_prod_type,
    sum_Message]
  simp only [sum_Interpretation, softmaxWeight_liUtility, Interpretation.meaning, Setting.L0,
    L0_literal_a, L0_exhaustified_a_wab, L0_literal_aAndB_wab, L0_exhaustified_aAndB_wab,
    L0_literal_aAndNotB_wab, L0_exhaustified_aAndNotB_wab, s.prior_ne_zero, one_ne_zero,
    ↓reduceIte, add_zero, ENNReal.toReal_one, Real.log_one, Setting.cost,
    Setting.prior_wab_toReal, sub_zero, zero_sub, mul_neg]
  rw [ENNReal.div_add_div_same, ← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
    ← two_mul, add_zero, ← ENNReal.ofReal_add (Real.exp_pos _).le (by positivity),
    ← ENNReal.ofReal_div_of_pos (by positivity)]

/-- In the world of A alone, the lexical-intentions speaker uses *A* under both
interpretations, the exhaustified one as informative as *A and not B*. -/
theorem liMessageSpeaker_wa_a :
    liMessageSpeaker s .wa .a =
      ENNReal.ofReal ((Real.exp (s.lam * Real.log (1 - s.p)) + 1) /
        (Real.exp (s.lam * Real.log (1 - s.p)) + 1 + 2 * Real.exp (-(s.lam * s.cAnotB)))) := by
  rw [liMessageSpeaker_apply, liSpeaker_apply, liSpeaker_apply, Fintype.sum_prod_type,
    sum_Message]
  simp only [sum_Interpretation, softmaxWeight_liUtility, Interpretation.meaning, Setting.L0,
    L0_literal_a, L0_exhaustified_a_wa, L0_literal_aAndB_wa, L0_exhaustified_aAndB_wa,
    L0_literal_aAndNotB_wa, L0_exhaustified_aAndNotB_wa, s.prior_ne_zero, one_ne_zero,
    ↓reduceIte, add_zero, ENNReal.toReal_one, Real.log_one, Setting.cost,
    Setting.prior_wa_toReal, sub_zero, zero_sub, mul_neg, mul_zero, Real.exp_zero,
    ENNReal.ofReal_one]
  rw [ENNReal.div_add_div_same, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add (Real.exp_pos _).le zero_le_one,
    ← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, ← two_mul,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_div_of_pos (by positivity)]

/-- Every message is used somewhere, so has positive marginal likelihood. -/
theorem liMarginal_ne_zero (u : Message) : PMF.marginal (liMessageSpeaker s) s.prior u ≠ 0 :=
  let ⟨w, hw⟩ := literal.exists_world u
  PMF.marginal_ne_zero _ _ _ (s.prior_ne_zero w) (by
    rw [liMessageSpeaker_apply]
    intro h
    exact S1_ne_zero (liUtility s) (u := (u, .lit)) (by
      rw [liUtility_eq, if_neg]
      · exact EReal.coe_ne_bot _
      · exact L0_ne_zero _ _ _ hw) (add_eq_zero.mp h).1)

/-- item 6 of the §4.4 model: the pragmatic listener of the lexical-intentions model. -/
noncomputable def liListener (u : Message) : PMF World :=
  RSA.L1 (liMessageSpeaker s) s.prior u (liMarginal_ne_zero s u)

/-- The lexical-intentions model blocks anti-exhaustivity whenever *A and B* costs no more
than *A and not B*: *A* is never likelier in the world of both than in the world of A
alone. -/
theorem liListener_lt_prior (hc : s.cAB ≤ s.cAnotB) : liListener s .a .wab < s.prior .wab := by
  rw [liListener, RSA.L1, PMF.posterior_lt_iff_lt_marginal _ _ _ _ (s.prior_ne_zero _)]
  unfold PMF.marginal
  rw [PMF.bind_apply_eq_finset_sum, sum_World,
    lt_two_world s.prior_add (s.prior_ne_zero _) (PMF.apply_ne_top _ _), liMessageSpeaker_wab_a,
    liMessageSpeaker_wa_a, ENNReal.ofReal_lt_ofReal_iff (by positivity),
    div_lt_div_iff₀ (by positivity) (by positivity)]
  have h₁ : Real.exp (s.lam * Real.log s.p) < 1 :=
    Real.exp_lt_one_iff.mpr (mul_neg_of_pos_of_neg s.lam_pos (Real.log_neg s.p_pos s.p_lt_one))
  have h₂ : Real.exp (-(s.lam * s.cAnotB)) ≤ Real.exp (-(s.lam * s.cAB)) :=
    Real.exp_le_exp.mpr (by nlinarith [s.lam_pos])
  have h₃ := Real.exp_pos (-(s.lam * s.cAnotB))
  have h₄ := Real.exp_pos (s.lam * Real.log (1 - s.p))
  nlinarith [mul_lt_mul_of_pos_right h₁ h₃, mul_pos h₄ (Real.exp_pos (-(s.lam * s.cAB)))]

end LexicalIntentions

/-! ### The supervaluationist model (§4.2) -/

section Supervaluationist

variable (s : Setting)

/-- The cells of a question: the coarse question does not distinguish the worlds, the fine
one does. -/
def QUD.project : QUD → World → Option World
  | .coarse, _ => none
  | .fine, w => some w

/-- item 3 of the §4.2 model, conditioned on the question: the literal listener's mass,
under an interpretation, on the cell of a world in a question. -/
noncomputable def cell (i : Interpretation) (q : QUD) (u : Message) (w : World) : ℝ≥0∞ :=
  RSA.QUD.proj QUD.project (s.L0 i.meaning u) q w

/-- The fine question's cells are the worlds. -/
theorem cell_fine (i : Interpretation) (u : Message) (w : World) :
    cell s i .fine u w = s.L0 i.meaning u w := by
  simp [cell, RSA.QUD.proj, QUD.project, Finset.filter_eq']

/-- The coarse question has one cell, which carries all the mass. -/
theorem cell_coarse (i : Interpretation) (u : Message) (w : World) :
    cell s i .coarse u w = 1 := by
  simp only [cell, RSA.QUD.proj, QUD.project, Finset.filter_true_of_mem (λ _ _ => trivial)]
  exact (tsum_fintype _).symm.trans (PMF.tsum_coe _)

/-- A cell's mass is finite. -/
theorem cell_ne_top (i : Interpretation) (q : QUD) (u : Message) (w : World) :
    cell s i q u w ≠ ⊤ :=
  RSA.QUD.proj_ne_top_of_pmf _ _ _ _

/-- item 4 of the §4.2 model: the supervaluationist utility, the expected log probability of
the cell over the two interpretations, taken equiprobable, less the cost; the prior of the
question, common to every message, is left out. -/
noncomputable def svUtility (x : World × QUD) (u : Message) : EReal :=
  (s.lam : EReal) *
    (((1 / 2 : ℝ) : EReal) * ENNReal.log (cell s .lit x.2 u x.1) +
      ((1 / 2 : ℝ) : EReal) * ENNReal.log (cell s .exh x.2 u x.1) - (s.cost u : EReal))

/-- The supervaluationist utility is `⊥` when the message is false on the cell under some
interpretation, and otherwise real. -/
theorem svUtility_eq (x : World × QUD) (u : Message) :
    svUtility s x u =
      if cell s .lit x.2 u x.1 = 0 ∨ cell s .exh x.2 u x.1 = 0 then ⊥
      else ((s.lam * (1 / 2 * Real.log (cell s .lit x.2 u x.1).toReal +
        1 / 2 * Real.log (cell s .exh x.2 u x.1).toReal - s.cost u) : ℝ) : EReal) := by
  unfold svUtility
  split_ifs with h
  · rcases h with h | h
    · rw [h, ENNReal.log_zero, EReal.mul_bot_of_pos (by norm_num), EReal.bot_add, EReal.bot_sub,
        EReal.mul_bot_of_pos (by exact_mod_cast s.lam_pos)]
    · rw [h, ENNReal.log_zero, EReal.mul_bot_of_pos (by norm_num), EReal.add_bot, EReal.bot_sub,
        EReal.mul_bot_of_pos (by exact_mod_cast s.lam_pos)]
  · push Not at h
    rw [ENNReal.log_pos_real h.1 (cell_ne_top _ _ _ _ _),
      ENNReal.log_pos_real h.2 (cell_ne_top _ _ _ _ _)]
    norm_cast

/-- Under the fine question a message true at a world under both interpretations has finite
utility there. -/
theorem svUtility_fine_ne_bot {w : World} {u : Message} (hl : truth u w = true)
    (he : exh u w = true) : svUtility s (w, .fine) u ≠ ⊥ := by
  rw [svUtility_eq, if_neg (by
    simp only [cell_fine, Interpretation.meaning, Setting.L0, not_or]
    exact ⟨L0_ne_zero _ _ _ hl, L0_ne_zero _ _ _ he⟩)]
  exact EReal.coe_ne_bot _

instance : ViableSpeaker (svUtility s) where
  no_top x u := by
    rw [svUtility_eq]
    split_ifs
    · exact bot_ne_top
    · exact EReal.coe_ne_top _
  some_finite x := by
    obtain ⟨w, q⟩ := x
    cases q
    · exact ⟨.a, by
        rw [svUtility_eq, if_neg (by simp [cell_coarse])]
        exact EReal.coe_ne_bot _⟩
    · cases w
      · exact ⟨.a, svUtility_fine_ne_bot s rfl (by decide)⟩
      · exact ⟨.aAndB, svUtility_fine_ne_bot s rfl (by decide)⟩

/-- item 5 of the §4.2 model: the supervaluationist speaker, at a world and a question. -/
noncomputable def svSpeaker (x : World × QUD) : PMF Message := S1 (svUtility s) x

/-- Under the coarse question every message is true on the one cell, so the speaker does not
depend on the world. -/
theorem svSpeaker_coarse : svSpeaker s (.wa, .coarse) = svSpeaker s (.wab, .coarse) := by
  have h : svUtility s (.wa, .coarse) = svUtility s (.wab, .coarse) := by
    funext u; simp only [svUtility, cell_coarse]
  exact PMF.ext λ u => by
    rw [svSpeaker, svSpeaker, S1, S1, PMF.softmax_apply, PMF.softmax_apply, h]

/-- Under the fine question the exhaustified *A* is false in the world of both, so its
expected utility there is `⊥` and the speaker never uses it. -/
theorem svSpeaker_wab_fine_a : svSpeaker s (.wab, .fine) .a = 0 := by
  have h : svUtility s (.wab, .fine) .a = ⊥ := by
    rw [svUtility_eq, if_pos (Or.inr (by
      simp [cell_fine, Interpretation.meaning, L0_exhaustified_a_wab]))]
  rw [svSpeaker, S1, PMF.softmax_apply, PMF.softmaxWeight_apply, h, EReal.exp_bot,
    ENNReal.zero_div]

/-- Under the fine question *A* is used in the world of A alone. -/
theorem svSpeaker_wa_fine_a_ne_zero : svSpeaker s (.wa, .fine) .a ≠ 0 :=
  S1_ne_zero _ (svUtility_fine_ne_bot s rfl (by decide))

/-- Appendix A.3, the speaker: under either question, *A* is used no more in the world of
both than in the world of A alone. -/
theorem svSpeaker_wab_le_wa (q : QUD) : svSpeaker s (.wab, q) .a ≤ svSpeaker s (.wa, q) .a := by
  cases q
  · rw [svSpeaker_coarse]
  · rw [svSpeaker_wab_fine_a]; exact zero_le

variable (Q : PMF QUD) (hQ : Q .fine ≠ 0)

/-- The joint prior over worlds and questions, independent. -/
noncomputable def svJoint : PMF (World × QUD) := RSA.jointPrior Q (λ _ => s.prior)

/-- The joint prior factors. -/
theorem svJoint_apply (w : World) (q : QUD) : svJoint s Q (w, q) = Q q * s.prior w :=
  RSA.jointPrior_apply _ _ _ _

/-- The world marginal of the joint prior is the measured prior. -/
theorem svJoint_fst (w : World) : (svJoint s Q).fst w = s.prior w := by
  rw [PMF.fst_apply, sum_QUD, svJoint_apply, svJoint_apply, ← add_mul, ← sum_QUD,
    (tsum_fintype _).symm.trans (PMF.tsum_coe Q), one_mul]

include hQ in
/-- Every message is used somewhere under the fine question, so has positive marginal
likelihood. -/
theorem svMarginal_ne_zero (u : Message) : PMF.marginal (svSpeaker s) (svJoint s Q) u ≠ 0 := by
  cases u
  · exact PMF.marginal_ne_zero _ _ _ (a := (.wa, .fine))
      (by rw [svJoint_apply]; exact mul_ne_zero hQ (s.prior_ne_zero _))
      (S1_ne_zero _ (svUtility_fine_ne_bot s rfl (by decide)))
  · exact PMF.marginal_ne_zero _ _ _ (a := (.wab, .fine))
      (by rw [svJoint_apply]; exact mul_ne_zero hQ (s.prior_ne_zero _))
      (S1_ne_zero _ (svUtility_fine_ne_bot s rfl (by decide)))
  · exact PMF.marginal_ne_zero _ _ _ (a := (.wa, .fine))
      (by rw [svJoint_apply]; exact mul_ne_zero hQ (s.prior_ne_zero _))
      (S1_ne_zero _ (svUtility_fine_ne_bot s rfl (by decide)))

/-- item 6 of the §4.2 model: the pragmatic listener, jointly over worlds and questions. -/
noncomputable def svListener (u : Message) : PMF (World × QUD) :=
  RSA.Canonical.L1 (svSpeaker s) (svJoint s Q) u (svMarginal_ne_zero s Q hQ u)

private theorem sv_aux {a b c d z y : ℝ≥0∞} (hab : a + b = 1) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ ⊤) (hd : d ≠ 0) (hz : z ≠ ⊤) (hy : y ≠ 0) :
    c * b * z < b * (c * a * z + d * a * y + c * b * z) := by
  have hb' : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hab ▸ le_add_self)
  have h : b * (c * a * z + d * a * y + c * b * z) = c * b * z + b * (d * a * y) := by
    calc b * (c * a * z + d * a * y + c * b * z) = c * b * ((a + b) * z) + b * (d * a * y) := by
          ring
      _ = _ := by rw [hab, one_mul]
  rw [h]
  exact ENNReal.lt_add_right (ENNReal.mul_ne_top (ENNReal.mul_ne_top hc hb') hz)
    (mul_ne_zero hb (mul_ne_zero (mul_ne_zero hd ha) hy))

/-- Appendix A.3, the listener: the posterior of both A and B falls below its prior, for
every prior in the open interval, every prior on the questions that gives the fine one
positive probability, and every cost, since the fine question contributes a use of *A* in the
world of A alone and none in the world of both. -/
theorem svListener_fst_lt_prior : (svListener s Q hQ .a).fst .wab < s.prior .wab := by
  rw [svListener, RSA.Canonical.L1, ← svJoint_fst s Q, PMF.posterior_fst_lt_fst_iff, svJoint_fst]
  unfold PMF.marginal
  rw [PMF.bind_apply_eq_finset_sum]
  simp only [Fintype.sum_prod_type, sum_World, sum_QUD, svJoint_apply, svSpeaker_wab_fine_a,
    ← svSpeaker_coarse, mul_zero, add_zero]
  exact sv_aux s.prior_add (s.prior_ne_zero _) (s.prior_ne_zero _) (PMF.apply_ne_top _ _) hQ
    (PMF.apply_ne_top _ _) (svSpeaker_wa_fine_a_ne_zero s)

end Supervaluationist

/-! ### The wonky-world models (§4.1) -/

section Wonky

variable (s : Setting) (ω : ℝ) (hω₀ : 0 ≤ ω) (hω₁ : ω ≤ 1)

/-- The speaker under a background: the literal listener uses the uniform prior in the wonky
background and the measured prior otherwise. -/
noncomputable def bgSpeaker : Background → World → PMF Message
  | .wonky => speaker wonkyPrior wonkyPrior_ne_zero literal s
  | .measured => s.speaker literal

/-- The prior on backgrounds: wonky with the wonkiness. -/
noncomputable def bgPrior : PMF Background :=
  PMF.ofFintype (λ b => match b with
    | .wonky => ENNReal.ofReal ω
    | .measured => ENNReal.ofReal (1 - ω)) (by
    rw [sum_Background]
    show ENNReal.ofReal ω + ENNReal.ofReal (1 - ω) = 1
    rw [← ENNReal.ofReal_add hω₀ (by linarith), add_sub_cancel, ENNReal.ofReal_one])

/-- The prior of the wonky background. -/
theorem bgPrior_wonky : bgPrior ω hω₀ hω₁ .wonky = ENNReal.ofReal ω := rfl

/-- The prior of the measured background. -/
theorem bgPrior_measured : bgPrior ω hω₀ hω₁ .measured = ENNReal.ofReal (1 - ω) := rfl

/-- The wonky speaker's use of *A* in the world of both: the logistic function of the cost of
*A and B* less the log of two. -/
theorem bgSpeaker_wonky_wab_a :
    bgSpeaker s .wonky .wab .a =
      ENNReal.ofReal (Real.sigmoid (s.lam * (s.cAB - Real.log 2))) := by
  rw [bgSpeaker, speaker_literal_wab_a, wonkyPrior_toReal, Real.log_inv, ← sub_eq_add_neg]

/-- The wonky speaker's use of *A* in the world of A alone: the logistic function of the cost
of *A and not B* less the log of two. -/
theorem bgSpeaker_wonky_wa_a :
    bgSpeaker s .wonky .wa .a =
      ENNReal.ofReal (Real.sigmoid (s.lam * (s.cAnotB - Real.log 2))) := by
  rw [bgSpeaker, speaker_literal_wa_a, wonkyPrior_toReal, Real.log_inv, ← sub_eq_add_neg]

/-- item 5 of the §4.1 model, the Bayesian version: the speaker marginalised over the
listener's uncertainty about the speaker's prior. -/
noncomputable def bayesWonkySpeaker (w : World) : PMF Message :=
  RSA.marginalizeKernel (bgPrior ω hω₀ hω₁) (λ b w => bgSpeaker s b w) w

/-- The Bayesian wonky speaker in closed form. -/
theorem bayesWonkySpeaker_apply (w : World) (u : Message) :
    bayesWonkySpeaker s ω hω₀ hω₁ w u =
      ENNReal.ofReal ω * bgSpeaker s .wonky w u +
        ENNReal.ofReal (1 - ω) * bgSpeaker s .measured w u := by
  rw [bayesWonkySpeaker, RSA.marginalizeKernel_apply, tsum_fintype, sum_Background,
    bgPrior_wonky, bgPrior_measured]

/-- Without wonkiness the Bayesian wonky speaker is the baseline speaker. -/
theorem bayesWonkySpeaker_zero (w : World) :
    bayesWonkySpeaker s 0 le_rfl zero_le_one w = s.speaker literal w :=
  PMF.ext λ u => by
    rw [bayesWonkySpeaker_apply, ENNReal.ofReal_zero, zero_mul, zero_add, sub_zero,
      ENNReal.ofReal_one, one_mul, bgSpeaker]

/-- Every message is used somewhere under either background, so has positive marginal
likelihood. -/
theorem bayesWonkyMarginal_ne_zero (u : Message) :
    PMF.marginal (bayesWonkySpeaker s ω hω₀ hω₁) s.prior u ≠ 0 :=
  let ⟨w, hw⟩ := literal.exists_world u
  PMF.marginal_ne_zero _ _ _ (s.prior_ne_zero w) (by
    rw [bayesWonkySpeaker_apply]
    intro h
    rcases add_eq_zero.mp h with ⟨h₁, h₂⟩
    rcases mul_eq_zero.mp h₁ with h₁ | h₁
    · rcases mul_eq_zero.mp h₂ with h₂ | h₂
      · rw [ENNReal.ofReal_eq_zero] at h₁ h₂; linarith
      · exact speaker_ne_zero _ _ _ _ hw h₂
    · exact speaker_ne_zero _ _ _ _ hw h₁)

/-- The Bayesian wonky listener, with the measured prior. -/
noncomputable def bayesWonkyListener (u : Message) : PMF World :=
  RSA.L1 (bayesWonkySpeaker s ω hω₀ hω₁) s.prior u (bayesWonkyMarginal_ne_zero s ω hω₀ hω₁ u)

/-- Appendix A.2, the Bayesian model: anti-exhaustivity exactly when the wonkiness-weighted
excess of the use of *A* in the world of both over its use in the world of A alone is
positive. -/
theorem prior_lt_bayesWonkyListener_iff :
    s.prior .wab < bayesWonkyListener s ω hω₀ hω₁ .a .wab ↔
      0 < (1 - ω) * (Real.sigmoid (s.lam * (s.cAB + Real.log s.p)) -
          Real.sigmoid (s.lam * (s.cAnotB + Real.log (1 - s.p)))) +
        ω * (Real.sigmoid (s.lam * (s.cAB - Real.log 2)) -
          Real.sigmoid (s.lam * (s.cAnotB - Real.log 2))) := by
  have hσ₁ := Real.sigmoid_pos (s.lam * (s.cAnotB - Real.log 2))
  have hσ₂ := Real.sigmoid_pos (s.lam * (s.cAB - Real.log 2))
  have hσ₃ := Real.sigmoid_pos (s.lam * (s.cAnotB + Real.log (1 - s.p)))
  have hσ₄ := Real.sigmoid_pos (s.lam * (s.cAB + Real.log s.p))
  have hω' : 0 ≤ 1 - ω := by linarith
  rw [bayesWonkyListener, RSA.L1, PMF.lt_posterior_iff_marginal_lt _ _ _ _ (s.prior_ne_zero _)]
  unfold PMF.marginal
  rw [PMF.bind_apply_eq_finset_sum, sum_World,
    two_world_lt s.prior_add (s.prior_ne_zero _) (PMF.apply_ne_top _ _),
    bayesWonkySpeaker_apply, bayesWonkySpeaker_apply, bgSpeaker_wonky_wab_a,
    bgSpeaker_wonky_wa_a, bgSpeaker]
  dsimp only [Setting.speaker]
  rw [speaker_literal_wab_a, speaker_literal_wa_a, Setting.prior_wab_toReal,
    Setting.prior_wa_toReal]
  simp (disch := positivity) only [← ENNReal.ofReal_mul, ← ENNReal.ofReal_add]
  rw [ENNReal.ofReal_lt_ofReal_iff (by
    rcases hω₁.lt_or_eq with hω | hω
    · exact add_pos_of_nonneg_of_pos (by positivity) (mul_pos (by linarith) hσ₄)
    · exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) hσ₂) (by positivity))]
  constructor <;> intro h <;> nlinarith

/-- The joint prior of the non-Bayesian model: the background, then the world under it. -/
noncomputable def wonkyJoint : PMF (World × Background) :=
  RSA.jointPrior (bgPrior ω hω₀ hω₁) λ b => match b with
    | .wonky => wonkyPrior
    | .measured => s.prior

/-- The joint prior of a world under the wonky background. -/
theorem wonkyJoint_wonky (w : World) :
    wonkyJoint s ω hω₀ hω₁ (w, .wonky) = ENNReal.ofReal ω * 2⁻¹ := by
  rw [wonkyJoint, RSA.jointPrior_apply, bgPrior_wonky, wonkyPrior_apply]

/-- The joint prior of a world under the measured background. -/
theorem wonkyJoint_measured (w : World) :
    wonkyJoint s ω hω₀ hω₁ (w, .measured) = ENNReal.ofReal (1 - ω) * s.prior w := by
  rw [wonkyJoint, RSA.jointPrior_apply, bgPrior_measured]

/-- The speaker of the non-Bayesian model, at a world under a background. -/
noncomputable abbrev wonkySpeaker : World × Background → PMF Message :=
  λ x => bgSpeaker s x.2 x.1

/-- Every message is used somewhere under whichever background has positive prior, so has
positive marginal likelihood. -/
theorem wonkyMarginal_ne_zero (u : Message) :
    PMF.marginal (wonkySpeaker s) (wonkyJoint s ω hω₀ hω₁) u ≠ 0 :=
  let ⟨w, hw⟩ := literal.exists_world u
  (hω₀.lt_or_eq).elim
    (λ hω => PMF.marginal_ne_zero _ _ _ (a := (w, .wonky))
      (by rw [wonkyJoint_wonky]; exact mul_ne_zero (ENNReal.ofReal_pos.mpr hω).ne' (by simp))
      (speaker_ne_zero _ _ _ _ hw))
    (λ hω => PMF.marginal_ne_zero _ _ _ (a := (w, .measured))
      (by
        rw [wonkyJoint_measured]
        exact mul_ne_zero (ENNReal.ofReal_pos.mpr (by linarith)).ne' (s.prior_ne_zero _))
      (speaker_ne_zero _ _ _ _ hw))

/-- item 4 of the §4.1 model: the non-Bayesian listener, uncertain about the world and the
speaker's background jointly. -/
noncomputable def wonkyListener (u : Message) : PMF World :=
  RSA.jointListener (wonkySpeaker s) (wonkyJoint s ω hω₀ hω₁) u
    (wonkyMarginal_ne_zero s ω hω₀ hω₁ u)

/-- (A.5a): the non-Bayesian model is anti-exhaustive with respect to the measured prior
exactly when the prior times the marginal use of *A* falls below the background-weighted use
of *A* in the world of both; the paper resolves this inequality numerically. -/
theorem prior_lt_wonkyListener_iff :
    s.prior .wab < wonkyListener s ω hω₀ hω₁ .a .wab ↔
      s.p * (ω * 2⁻¹ * (Real.sigmoid (s.lam * (s.cAnotB - Real.log 2)) +
          Real.sigmoid (s.lam * (s.cAB - Real.log 2))) +
        (1 - ω) * ((1 - s.p) * Real.sigmoid (s.lam * (s.cAnotB + Real.log (1 - s.p))) +
          s.p * Real.sigmoid (s.lam * (s.cAB + Real.log s.p)))) <
      ω * 2⁻¹ * Real.sigmoid (s.lam * (s.cAB - Real.log 2)) +
        (1 - ω) * (s.p * Real.sigmoid (s.lam * (s.cAB + Real.log s.p))) := by
  have hσ₁ := Real.sigmoid_pos (s.lam * (s.cAnotB - Real.log 2))
  have hσ₂ := Real.sigmoid_pos (s.lam * (s.cAB - Real.log 2))
  have hσ₃ := Real.sigmoid_pos (s.lam * (s.cAnotB + Real.log (1 - s.p)))
  have hσ₄ := Real.sigmoid_pos (s.lam * (s.cAB + Real.log s.p))
  have hω' : 0 ≤ 1 - ω := by linarith
  have hp := s.p_pos
  have hp' : 0 ≤ 1 - s.p := by linarith [s.p_lt_one]
  rw [wonkyListener, RSA.jointListener_apply,
    ENNReal.lt_div_iff_mul_lt (Or.inl (wonkyMarginal_ne_zero s ω hω₀ hω₁ _))
      (Or.inl (PMF.marginal_ne_top _ _ _))]
  unfold PMF.marginal
  rw [PMF.bind_apply_eq_finset_sum]
  simp only [Fintype.sum_prod_type, sum_World, sum_Background, wonkyJoint_wonky,
    wonkyJoint_measured, wonkySpeaker, bgSpeaker, Setting.speaker, speaker_literal_wab_a,
    speaker_literal_wa_a, wonkyPrior_toReal, Setting.prior_wa, Setting.prior_wab,
    ENNReal.toReal_ofReal hp', ENNReal.toReal_ofReal hp.le, Real.log_inv, ← sub_eq_add_neg]
  rw [show (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal 2⁻¹ from by
    rw [ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]]
  simp (disch := positivity) only [← ENNReal.ofReal_mul, ← ENNReal.ofReal_add]
  rw [ENNReal.ofReal_lt_ofReal_iff (by
    rcases hω₁.lt_or_eq with hω | hω
    · exact add_pos_of_nonneg_of_pos (by positivity) (by positivity)
    · subst hω; simp only [sub_self, zero_mul, add_zero]; positivity)]
  constructor <;> intro h <;> linarith

end Wonky

end CremersWilcoxSpector2023
