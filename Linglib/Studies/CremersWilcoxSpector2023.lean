import Linglib.Core.Analysis.SpecialFunctions.Sigmoid
import Linglib.Core.Probability.Kernel.Mixture
import Linglib.Core.Probability.UniformOn
import Linglib.Pragmatics.RSA.Basic
import Linglib.Semantics.Exhaustification.Finite

/-!
# Exhaustivity and anti-exhaustivity in the Rational Speech Act framework

A listener who hears *A* where *A and B* was available infers that B is false. In the
baseline Rational Speech Act model a prior biased towards the world of both A and B reverses
the inference: the listener is anti-exhaustive exactly when the log odds of the prior exceed
the cost disadvantage of *A and not B* over *A and B*, whatever the rationality. Lexical
uncertainty over free strengthenings and the wonky-world models stay anti-exhaustive for
suitable priors, while grammatical lexical uncertainty, the lexical-intentions speaker and
the supervaluationist speaker keep the posterior of both below the prior whenever *A and B*
costs no more than *A and not B*. The experiment finds no anti-exhaustivity.

We state each model on the substrate's kernel face and prove the paper's conditions on reals
for an arbitrary prior, rationality and costs.

## TODO

* The non-Bayesian wonky model's limits in the prior and the Bayesian wonky model's
  wonkiness threshold are not derived.

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

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CremersWilcoxSpector2023

/-! ### Worlds, messages and interpretations -/

/-- The two worlds: only A true, or both A and B true. -/
inductive World where
  | wa
  | wab
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace World := ⊤

/-- The three messages: *A*, *A and B*, *A and not B*. -/
inductive Message where
  | a
  | aAndB
  | aAndNotB
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace Message := ⊤

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
theorem exh_a : exh .a = truth .aAndNotB := by decide

/-- *A and B* has no stronger alternative. -/
theorem exh_aAndB : exh .aAndB = truth .aAndB := by decide

/-- *A and not B* has no stronger alternative. -/
theorem exh_aAndNotB : exh .aAndNotB = truth .aAndNotB := by decide

/-- An interpretation function under which every message is true somewhere and every world
is described by some message, so that the literal listener and the speaker are defined. -/
structure Meaning where
  /-- The truth value of a message at a world. -/
  sat : Message → World → Bool
  /-- Every message is true somewhere. -/
  exists_world : ∀ u, ∃ w, sat u w = true
  /-- Every world is described by some message. -/
  exists_message : ∀ w, ∃ u, sat u w = true

namespace Meaning

variable (m : Meaning)

/-- The extension of a message. -/
def extension (u : Message) : Set World := {w | m.sat u w = true}

theorem mem_extension {u : Message} {w : World} : w ∈ m.extension u ↔ m.sat u w = true :=
  Iff.rfl

/-- A message true everywhere has the full extension. -/
theorem extension_eq_univ {u : Message} (h : ∀ w, m.sat u w = true) :
    m.extension u = Set.univ :=
  Set.eq_univ_of_forall h

/-- A message true at one world only has that world as its extension. -/
theorem extension_eq_singleton {u : Message} {w : World}
    (h : ∀ w', m.sat u w' = true ↔ w' = w) : m.extension u = {w} :=
  Set.ext λ w' => (h w').trans Set.mem_singleton_iff.symm

end Meaning

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
  deriving DecidableEq, Fintype

instance : MeasurableSpace Interpretation := ⊤

/-- The meaning of a grammatical interpretation. -/
def Interpretation.meaning : Interpretation → Meaning
  | .lit => literal
  | .exh => exhaustified

/-- The three interpretations of the free lexical-uncertainty model. -/
inductive FreeInterpretation where
  | lit
  | exh
  | antiExh
  deriving DecidableEq, Fintype

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
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace Background := ⊤

/-- The questions under discussion: whether A holds, which the two worlds answer alike, or
which world obtains. -/
inductive QUD where
  | coarse
  | fine
  deriving DecidableEq, Fintype, Nonempty

instance : MeasurableSpace QUD := ⊤

section Sums

variable {β : Type*} [AddCommMonoid β]

/-- A sum over the two worlds. -/
theorem sum_world (f : World → β) : ∑ w, f w = f .wa + f .wab := by
  rw [show ∑ w, f w = f .wa + (f .wab + 0) from rfl, add_zero]

/-- A sum over the three messages. -/
theorem sum_message (f : Message → β) : ∑ u, f u = f .a + f .aAndB + f .aAndNotB := by
  rw [show ∑ u, f u = f .a + (f .aAndB + (f .aAndNotB + 0)) from rfl, add_zero, add_assoc]

/-- A sum over the two grammatical interpretations. -/
theorem sum_interpretation (f : Interpretation → β) : ∑ i, f i = f .lit + f .exh := by
  rw [show ∑ i, f i = f .lit + (f .exh + 0) from rfl, add_zero]

/-- A sum over the three free interpretations. -/
theorem sum_freeInterpretation (f : FreeInterpretation → β) :
    ∑ i, f i = f .lit + f .exh + f .antiExh := by
  rw [show ∑ i, f i = f .lit + (f .exh + (f .antiExh + 0)) from rfl, add_zero, add_assoc]

/-- A sum over the two backgrounds. -/
theorem sum_background (f : Background → β) : ∑ b, f b = f .wonky + f .measured := by
  rw [show ∑ b, f b = f .wonky + (f .measured + 0) from rfl, add_zero]

/-- A sum over the two questions. -/
theorem sum_qud (f : QUD → β) : ∑ q, f q = f .coarse + f .fine := by
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
  cAndB : ℝ
  /-- The cost of *A and not B*. -/
  cAndNotB : ℝ
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
  | .aAndB => s.cAndB
  | .aAndNotB => s.cAndNotB

/-- The cost factor of a message: the exponential of its cost scaled by the rationality. -/
noncomputable def costFactor (u : Message) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(s.lam * s.cost u)))

theorem costFactor_ne_zero (u : Message) : s.costFactor u ≠ 0 :=
  (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

theorem costFactor_ne_top (u : Message) : s.costFactor u ≠ ∞ := ENNReal.ofReal_ne_top

theorem costFactor_toReal (u : Message) :
    (s.costFactor u).toReal = Real.exp (-(s.lam * s.cost u)) :=
  ENNReal.toReal_ofReal (Real.exp_pos _).le

/-- The paper's `f_λ`: the logistic function with rate the rationality. -/
noncomputable def logistic (x : ℝ) : ℝ := Real.sigmoid (s.lam * x)

theorem logistic_nonneg (x : ℝ) : 0 ≤ s.logistic x := Real.sigmoid_nonneg _

theorem logistic_lt_iff {x y : ℝ} : s.logistic x < s.logistic y ↔ x < y := by
  rw [logistic, logistic, Real.sigmoid_lt_iff, mul_lt_mul_iff_of_pos_left s.lam_pos]

theorem logistic_lt {x y : ℝ} (h : x < y) : s.logistic x < s.logistic y :=
  s.logistic_lt_iff.mpr h

/-- The weight of a world under the measured prior. -/
noncomputable def priorWeight : World → ℝ≥0∞
  | .wa => ENNReal.ofReal (1 - s.p)
  | .wab => ENNReal.ofReal s.p

/-- The measured prior over the two worlds. -/
noncomputable def prior : Measure World := ∑ w, s.priorWeight w • Measure.dirac w

theorem prior_apply_singleton (w : World) : s.prior {w} = s.priorWeight w :=
  Measure.sum_smul_dirac_apply_singleton _ w

/-- The prior of the world of A alone. -/
theorem prior_wa : s.prior {.wa} = ENNReal.ofReal (1 - s.p) := prior_apply_singleton s .wa

/-- The prior of the world of both. -/
theorem prior_wab : s.prior {.wab} = ENNReal.ofReal s.p := prior_apply_singleton s .wab

instance : IsProbabilityMeasure s.prior :=
  ⟨by
    rw [← Finset.coe_univ, ← sum_measure_singleton, sum_world, prior_wa, prior_wab,
      ← ENNReal.ofReal_add (by linarith [s.p_lt_one]) s.p_pos.le, sub_add_cancel,
      ENNReal.ofReal_one]⟩

/-- The prior is positive on both worlds. -/
theorem prior_ne_zero (w : World) : s.prior {w} ≠ 0 := by
  cases w
  · exact prior_wa s ▸ (ENNReal.ofReal_pos.mpr (by linarith [s.p_lt_one])).ne'
  · exact prior_wab s ▸ (ENNReal.ofReal_pos.mpr s.p_pos).ne'

/-- The prior is carried by the two worlds. -/
theorem prior_support (w : World) (_ : s.prior {w} ≠ 0) : w = .wab ∨ w = .wa := by
  cases w <;> simp

/-- The prior of the world of A alone, as a real. -/
theorem prior_real_wa : s.prior.real {.wa} = 1 - s.p := by
  rw [measureReal_def, prior_wa, ENNReal.toReal_ofReal (by linarith [s.p_lt_one])]

/-- The prior of the world of both, as a real. -/
theorem prior_real_wab : s.prior.real {.wab} = s.p := by
  rw [measureReal_def, prior_wab, ENNReal.toReal_ofReal s.p_pos.le]

end Setting

/-- The wonky prior: uniform over the two worlds. -/
noncomputable def wonkyPrior : Measure World := uniformOn Set.univ

instance : IsProbabilityMeasure wonkyPrior :=
  isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty

/-- The wonky prior gives each world a half. -/
theorem wonkyPrior_apply_singleton (w : World) : wonkyPrior {w} = 2⁻¹ := by
  rw [wonkyPrior, uniformOn_univ_apply_singleton, show Fintype.card World = 2 from rfl]
  norm_cast

/-- The wonky prior is positive on both worlds. -/
theorem wonkyPrior_ne_zero (w : World) : wonkyPrior {w} ≠ 0 := by
  rw [wonkyPrior_apply_singleton]; simp

/-- The wonky prior of a world, as a real. -/
theorem wonkyPrior_real_singleton (w : World) : wonkyPrior.real {w} = 2⁻¹ := by
  rw [wonkyPrior, uniformOn_univ_real_singleton, show Fintype.card World = 2 from rfl]
  norm_num

/-! ### The literal listener and the speaker under an interpretation (eqs. 1 to 3) -/

section Speaker

variable (P : Measure World) [IsFiniteMeasure P] (hP : ∀ w, P {w} ≠ 0) (m : Meaning)

/-- The literal listener: the prior conditioned on the message's extension (eq. 1). -/
noncomputable def L0 : Kernel Message World :=
  RSA.literalListener P λ u => (m.extension u).indicator 1

omit [IsFiniteMeasure P] in
/-- The literal listener is a subprobability at every world. -/
theorem L0_le_one (u : Message) (w : World) : L0 P m u {w} ≤ 1 :=
  RSA.literalListener_apply_le_one _ _ _ _

omit [IsFiniteMeasure P] in
theorem L0_ne_top (u : Message) (w : World) : L0 P m u {w} ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (L0_le_one P m u w)

omit [IsFiniteMeasure P] in
/-- A message false at a world gets no mass there. -/
theorem L0_eq_zero {u : Message} {w : World} (h : m.sat u w = false) : L0 P m u {w} = 0 :=
  RSA.literalListener_indicator_apply_singleton_of_notMem P m.extension
    (by rw [Meaning.mem_extension, h]; exact Bool.false_ne_true)

omit [IsFiniteMeasure P] in
/-- The tautology *A* leaves the prior unchanged. -/
theorem L0_literal_a [IsProbabilityMeasure P] (w : World) : L0 P literal .a {w} = P {w} :=
  RSA.literalListener_indicator_apply_singleton_of_eq_univ P literal.extension
    (literal.extension_eq_univ λ w => by cases w <;> rfl) w

variable (s : Setting)

/-- The speaker: the power-weight best response to the literal listener with the rationality
as exponent and the cost factors as weights (eqs. 2 and 3). -/
noncomputable def speaker : Kernel World Message := RSA.speaker s.lam s.costFactor (L0 P m)

instance : IsFiniteKernel (speaker P m s) := inferInstanceAs (IsFiniteKernel (RSA.speaker _ _ _))

omit [IsFiniteMeasure P] in
/-- The weight of a message is finite. -/
theorem weight_ne_top (u : Message) (w : World) :
    L0 P m u {w} ^ s.lam * s.costFactor u ≠ ∞ :=
  ENNReal.mul_ne_top (RSA.weight_rpow_ne_top s.lam_pos.le (L0_le_one P m u w))
    (s.costFactor_ne_top u)

omit [IsFiniteMeasure P] in
/-- A message false at a world has no weight there. -/
theorem weight_eq_zero {u : Message} {w : World} (h : m.sat u w = false) :
    L0 P m u {w} ^ s.lam * s.costFactor u = 0 := by
  rw [L0_eq_zero P m h, ENNReal.zero_rpow_of_pos s.lam_pos, zero_mul]

omit [IsFiniteMeasure P] in
/-- A message false at a world is never used there. -/
theorem speaker_eq_zero {u : Message} {w : World} (h : m.sat u w = false) :
    speaker P m s w {u} = 0 :=
  RSA.speaker_apply_singleton_eq_zero s.lam_pos (L0_eq_zero P m h)

include hP

/-- A message true at a world has positive mass there. -/
theorem L0_ne_zero {u : Message} {w : World} (h : m.sat u w = true) : L0 P m u {w} ≠ 0 := by
  rw [L0, RSA.literalListener_indicator_apply_singleton P m.extension h]
  exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) (hP w)

/-- A message true at one world only puts all its mass there. -/
theorem L0_eq_one {u : Message} {w : World} (h : ∀ w', m.sat u w' = true ↔ w' = w) :
    L0 P m u {w} = 1 :=
  RSA.literalListener_indicator_apply_singleton_of_eq_singleton P m.extension
    (m.extension_eq_singleton h) (hP w)

/-- The literal listener is a probability measure. -/
theorem L0_apply_univ (u : Message) : L0 P m u Set.univ = 1 :=
  let ⟨w, hw⟩ := m.exists_world u
  RSA.literalListener_indicator_apply_univ P m.extension λ h =>
    hP w (measure_mono_null (Set.singleton_subset_iff.mpr hw) h)

/-- A message true at a world has positive weight there. -/
theorem weight_ne_zero {u : Message} {w : World} (h : m.sat u w = true) :
    L0 P m u {w} ^ s.lam * s.costFactor u ≠ 0 :=
  mul_ne_zero (RSA.weight_rpow_ne_zero s.lam_pos.le (L0_ne_zero P hP m h)) (s.costFactor_ne_zero u)

/-- The weight of a message true at a world, on reals: the exponential of the paper's scaled
utility. -/
theorem weight_toReal {u : Message} {w : World} (h : m.sat u w = true) :
    (L0 P m u {w} ^ s.lam * s.costFactor u).toReal =
      Real.exp (s.lam * (Real.log (L0 P m u {w}).toReal - s.cost u)) := by
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    Real.rpow_def_of_pos (ENNReal.toReal_pos (L0_ne_zero P hP m h) (L0_ne_top P m u w)),
    Setting.costFactor_toReal, ← Real.exp_add]
  congr 1; ring

/-- A message true at a world is used there. -/
theorem speaker_ne_zero {u : Message} {w : World} (h : m.sat u w = true) :
    speaker P m s w {u} ≠ 0 :=
  RSA.speaker_apply_singleton_ne_zero s.lam_pos.le s.costFactor_ne_zero s.costFactor_ne_top
    (λ v => L0_le_one P m v w) (L0_ne_zero P hP m h)

/-- Between two messages true at a world, the speaker prefers the one of higher utility. -/
theorem speaker_real_singleton_lt_iff {u v : Message} {w : World} (hu : m.sat u w = true)
    (hv : m.sat v w = true) :
    (speaker P m s w).real {u} < (speaker P m s w).real {v} ↔
      Real.log (L0 P m u {w}).toReal - s.cost u < Real.log (L0 P m v {w}).toReal - s.cost v := by
  rw [speaker, RSA.speaker_real_singleton_lt_iff s.lam_pos.le s.costFactor_ne_top
      (λ v => L0_le_one P m v w) ⟨u, weight_ne_zero P hP m s hu⟩,
    ← ENNReal.toReal_lt_toReal (weight_ne_top P m s u w) (weight_ne_top P m s v w),
    weight_toReal P hP m s hu, weight_toReal P hP m s hv, Real.exp_lt_exp,
    mul_lt_mul_iff_of_pos_left s.lam_pos]

/-- When exactly two messages are true at a world, the speaker's use of one is the logistic
function of the utility difference. -/
theorem speaker_real_singleton_of_pair {u v : Message} {w : World} (huv : u ≠ v)
    (hu : m.sat u w = true) (hv : m.sat v w = true)
    (hsupp : ∀ x, m.sat x w = true → x = u ∨ x = v) :
    (speaker P m s w).real {u} =
      s.logistic ((Real.log (L0 P m u {w}).toReal - s.cost u) -
        (Real.log (L0 P m v {w}).toReal - s.cost v)) := by
  rw [speaker, RSA.speaker, Kernel.ofWeights_real_singleton_of_pair w huv
      (λ x => weight_ne_top P m s x w)
      (λ x hx => hsupp x (of_not_not (mt (λ h => weight_eq_zero P m s
        (Bool.eq_false_iff.mpr h)) hx))),
    weight_toReal P hP m s hu, weight_toReal P hP m s hv, Real.exp_div_add_exp_eq_sigmoid,
    Setting.logistic]
  congr 1; ring

end Speaker

/-- The literal listener with the measured prior. -/
noncomputable abbrev Setting.L0 (s : Setting) (m : Meaning) : Kernel Message World :=
  CremersWilcoxSpector2023.L0 s.prior m

/-- The speaker with the measured prior in the literal listener. -/
noncomputable abbrev Setting.speaker (s : Setting) (m : Meaning) : Kernel World Message :=
  CremersWilcoxSpector2023.speaker s.prior m s

/-! ### Closed forms: the speaker's use of *A* is a logistic function -/

section ClosedForms

variable (P : Measure World) [IsProbabilityMeasure P] (hP : ∀ w, P {w} ≠ 0) (s : Setting)
include hP

/-- In the world of both, the literal speaker's use of *A* is the logistic function of the
cost of *A and B* plus the log prior (eq. A.3). -/
theorem speaker_literal_wab_a :
    (speaker P literal s .wab).real {.a} = s.logistic (s.cAndB + Real.log (P.real {.wab})) := by
  rw [speaker_real_singleton_of_pair P hP literal s (v := .aAndB) (by decide) rfl rfl
    (by decide)]
  simp (disch := decide) only [L0_literal_a, L0_eq_one P hP literal, ENNReal.toReal_one,
    Real.log_one, Setting.cost, ← measureReal_def]
  congr 1; ring

/-- In the world of A alone, the use of *A* is the logistic function of the cost of
*A and not B* plus the log prior (eq. A.2). -/
theorem speaker_literal_wa_a :
    (speaker P literal s .wa).real {.a} = s.logistic (s.cAndNotB + Real.log (P.real {.wa})) := by
  rw [speaker_real_singleton_of_pair P hP literal s (v := .aAndNotB) (by decide) rfl rfl
    (by decide)]
  simp (disch := decide) only [L0_literal_a, L0_eq_one P hP literal, ENNReal.toReal_one,
    Real.log_one, Setting.cost, ← measureReal_def]
  congr 1; ring

end ClosedForms

section SettingClosedForms

variable (s : Setting)

/-- Under the exhaustified interpretation *A* is as informative as *A and not B* in the
world of A alone, so its use is the logistic function of the latter's cost. -/
theorem speaker_exhaustified_wa_a :
    (s.speaker exhaustified .wa).real {.a} = s.logistic s.cAndNotB := by
  rw [Setting.speaker, speaker_real_singleton_of_pair s.prior s.prior_ne_zero exhaustified s
    (v := .aAndNotB) (by decide) (by decide) (by decide) (by decide)]
  simp (disch := decide) only [L0_eq_one s.prior s.prior_ne_zero exhaustified,
    ENNReal.toReal_one, Real.log_one, Setting.cost]
  congr 1; ring

/-- Under the exhaustified interpretation *A* is false in the world of both. -/
theorem speaker_exhaustified_wab_a : (s.speaker exhaustified .wab).real {.a} = 0 :=
  (measureReal_eq_zero_iff (measure_ne_top _ _)).mpr (speaker_eq_zero _ _ _ (by decide))

/-- Under the anti-exhaustive interpretation *A* is as informative as *A and B* in the world
of both. -/
theorem speaker_antiExhaustive_wab_a :
    (s.speaker antiExhaustive .wab).real {.a} = s.logistic s.cAndB := by
  rw [Setting.speaker, speaker_real_singleton_of_pair s.prior s.prior_ne_zero antiExhaustive s
    (v := .aAndB) (by decide) rfl rfl (by decide)]
  simp (disch := decide) only [L0_eq_one s.prior s.prior_ne_zero antiExhaustive,
    ENNReal.toReal_one, Real.log_one, Setting.cost]
  congr 1; ring

/-- Under the anti-exhaustive interpretation *A* is false in the world of A alone. -/
theorem speaker_antiExhaustive_wa_a : (s.speaker antiExhaustive .wa).real {.a} = 0 :=
  (measureReal_eq_zero_iff (measure_ne_top _ _)).mpr (speaker_eq_zero _ _ _ rfl)

end SettingClosedForms

/-! ### The baseline model (§3) -/

section Baseline

variable (s : Setting)

/-- In the world of both, the speaker prefers *A* to *A and B* exactly when the information
*A and B* would add, the negated log prior, does not exceed its cost (6a). -/
theorem baseline_aAndB_lt_a_iff :
    (s.speaker literal .wab).real {.aAndB} < (s.speaker literal .wab).real {.a} ↔
      -s.cAndB < Real.log s.p := by
  rw [Setting.speaker, speaker_real_singleton_lt_iff s.prior s.prior_ne_zero literal s rfl rfl]
  simp (disch := decide) only [L0_literal_a, L0_eq_one s.prior s.prior_ne_zero literal,
    ENNReal.toReal_one, Real.log_one, Setting.cost, ← measureReal_def, Setting.prior_real_wab,
    zero_sub, sub_zero]

/-- In the world of A alone, the speaker prefers *A and not B* to *A* exactly when the
negated log prior exceeds its cost (7). -/
theorem baseline_a_lt_aAndNotB_iff :
    (s.speaker literal .wa).real {.a} < (s.speaker literal .wa).real {.aAndNotB} ↔
      Real.log (1 - s.p) < -s.cAndNotB := by
  rw [Setting.speaker, speaker_real_singleton_lt_iff s.prior s.prior_ne_zero literal s rfl rfl]
  simp (disch := decide) only [L0_literal_a, L0_eq_one s.prior s.prior_ne_zero literal,
    ENNReal.toReal_one, Real.log_one, Setting.cost, ← measureReal_def, Setting.prior_real_wa,
    zero_sub, sub_zero]

/-- Every message is used somewhere, so is heard with positive probability. -/
theorem comp_speaker_literal_ne_zero (u : Message) : (s.speaker literal ∘ₘ s.prior) {u} ≠ 0 :=
  let ⟨w, hw⟩ := literal.exists_world u
  comp_apply_singleton_ne_zero _ _ (s.prior_ne_zero w) (speaker_ne_zero _ s.prior_ne_zero _ s hw)

/-- The pragmatic listener (eq. 4). -/
noncomputable def listener : Kernel Message World :=
  RSA.pragmaticListener s.lam s.costFactor (s.L0 literal) s.prior

/-- The listener is anti-exhaustive, the posterior of both A and B exceeding the prior,
exactly when the speaker uses *A* more in the world of both than in the world of A alone
(A.4). -/
theorem prior_lt_listener_iff_speaker_lt :
    s.prior.real {.wab} < (listener s .a).real {.wab} ↔
      (s.speaker literal .wa).real {.a} < (s.speaker literal .wab).real {.a} :=
  real_lt_posterior_real_singleton_iff_of_pair (s.speaker literal) s.prior (by decide)
    s.prior_support (comp_speaker_literal_ne_zero s _) (s.prior_ne_zero _) (s.prior_ne_zero _)

/-- The listener is anti-exhaustive exactly when the log odds of the prior exceed the cost
disadvantage of *A and not B* over *A and B*, whatever the rationality (6b). -/
theorem prior_lt_listener_iff :
    s.prior.real {.wab} < (listener s .a).real {.wab} ↔
      s.cAndNotB - s.cAndB < Real.log s.p - Real.log (1 - s.p) := by
  rw [prior_lt_listener_iff_speaker_lt, Setting.speaker, speaker_literal_wa_a _ s.prior_ne_zero,
    speaker_literal_wab_a _ s.prior_ne_zero, Setting.prior_real_wa, Setting.prior_real_wab,
    s.logistic_lt_iff, sub_lt_sub_iff, add_comm (Real.log s.p)]

/-- With equal costs, anti-exhaustivity is a prior biased towards the world of both. -/
theorem prior_lt_listener_iff_of_cost_eq (hc : s.cAndB = s.cAndNotB) :
    s.prior.real {.wab} < (listener s .a).real {.wab} ↔ 1 / 2 < s.p := by
  rw [prior_lt_listener_iff, hc, sub_self, sub_pos,
    Real.log_lt_log_iff (by linarith [s.p_lt_one]) s.p_pos]
  constructor <;> intro <;> linarith

end Baseline

/-! ### Lexical uncertainty (§4.3) -/

section LexicalUncertainty

variable (s : Setting)

/-- The speaker marginalised over the two equiprobable interpretations (item 4 of the §4.3
model). -/
noncomputable def luSpeaker : Kernel World Message :=
  Kernel.mixture (λ _ : Interpretation => 2⁻¹) λ i => s.speaker i.meaning

instance : IsFiniteKernel (luSpeaker s) :=
  Kernel.isFiniteKernel_mixture _ _ λ _ => ENNReal.inv_ne_top.mpr two_ne_zero

/-- The grammatical lexical-uncertainty speaker on reals. -/
theorem luSpeaker_real_singleton (w : World) (u : Message) :
    (luSpeaker s w).real {u} =
      2⁻¹ * (s.speaker literal w).real {u} + 2⁻¹ * (s.speaker exhaustified w).real {u} := by
  rw [luSpeaker, Kernel.mixture_real _ _ (λ _ => ENNReal.inv_ne_top.mpr two_ne_zero),
    sum_interpretation]
  simp only [Interpretation.meaning, ENNReal.toReal_inv, ENNReal.toReal_ofNat]

/-- Every message is used somewhere, so is heard with positive probability. -/
theorem comp_luSpeaker_ne_zero (u : Message) : (luSpeaker s ∘ₘ s.prior) {u} ≠ 0 :=
  let ⟨w, hw⟩ := literal.exists_world u
  comp_apply_singleton_ne_zero _ _ (s.prior_ne_zero w)
    ((Kernel.mixture_apply_ne_zero_iff _ _ _ _).mpr
      ⟨.lit, by simp, speaker_ne_zero _ s.prior_ne_zero _ s hw⟩)

/-- The Bayesian inverse of the marginalised speaker (item 4 of the §4.3 model). -/
noncomputable def luListener : Kernel Message World := (luSpeaker s)†s.prior

/-- Grammatical lexical uncertainty blocks anti-exhaustivity whenever *A and B* costs no more
than *A and not B*: the exhaustified interpretation never uses *A* in the world of both but
uses it in the world of A alone more than the literal interpretation uses it in the world of
both. -/
theorem luListener_lt_prior (hc : s.cAndB ≤ s.cAndNotB) :
    (luListener s .a).real {.wab} < s.prior.real {.wab} := by
  rw [luListener, posterior_real_singleton_lt_iff_of_pair _ _ (by decide) s.prior_support
      (comp_luSpeaker_ne_zero s _) (s.prior_ne_zero _) (s.prior_ne_zero _),
    luSpeaker_real_singleton, luSpeaker_real_singleton, speaker_exhaustified_wab_a,
    speaker_exhaustified_wa_a, Setting.speaker, speaker_literal_wab_a _ s.prior_ne_zero,
    speaker_literal_wa_a _ s.prior_ne_zero, Setting.prior_real_wab, Setting.prior_real_wa]
  have h₁ := s.logistic_lt (show s.cAndB + Real.log s.p < s.cAndNotB by
    linarith [Real.log_neg s.p_pos s.p_lt_one])
  have h₂ := s.logistic_nonneg (s.cAndNotB + Real.log (1 - s.p))
  linarith

/-- The speaker of the free lexical-uncertainty model, marginalised over the three
equiprobable interpretations. -/
noncomputable def freeSpeaker : Kernel World Message :=
  Kernel.mixture (λ _ : FreeInterpretation => 3⁻¹) λ i => s.speaker i.meaning

instance : IsFiniteKernel (freeSpeaker s) :=
  Kernel.isFiniteKernel_mixture _ _ λ _ => ENNReal.inv_ne_top.mpr three_ne_zero

/-- The free lexical-uncertainty speaker on reals. -/
theorem freeSpeaker_real_singleton (w : World) (u : Message) :
    (freeSpeaker s w).real {u} =
      3⁻¹ * (s.speaker literal w).real {u} + 3⁻¹ * (s.speaker exhaustified w).real {u} +
        3⁻¹ * (s.speaker antiExhaustive w).real {u} := by
  rw [freeSpeaker, Kernel.mixture_real _ _ (λ _ => ENNReal.inv_ne_top.mpr three_ne_zero),
    sum_freeInterpretation]
  simp only [FreeInterpretation.meaning, ENNReal.toReal_inv, ENNReal.toReal_ofNat]

/-- Every message is used somewhere, so is heard with positive probability. -/
theorem comp_freeSpeaker_ne_zero (u : Message) : (freeSpeaker s ∘ₘ s.prior) {u} ≠ 0 :=
  let ⟨w, hw⟩ := literal.exists_world u
  comp_apply_singleton_ne_zero _ _ (s.prior_ne_zero w)
    ((Kernel.mixture_apply_ne_zero_iff _ _ _ _).mpr
      ⟨.lit, by simp, speaker_ne_zero _ s.prior_ne_zero _ s hw⟩)

/-- The pragmatic listener of the free lexical-uncertainty model. -/
noncomputable def freeListener : Kernel Message World := (freeSpeaker s)†s.prior

/-- Free lexical uncertainty is anti-exhaustive exactly when the literal and anti-exhaustive
uses of *A* in the world of both outweigh the literal and exhaustified uses in the world of A
alone. -/
theorem prior_lt_freeListener_iff :
    s.prior.real {.wab} < (freeListener s .a).real {.wab} ↔
      s.logistic (s.cAndNotB + Real.log (1 - s.p)) + s.logistic s.cAndNotB <
        s.logistic (s.cAndB + Real.log s.p) + s.logistic s.cAndB := by
  rw [freeListener, real_lt_posterior_real_singleton_iff_of_pair _ _ (by decide) s.prior_support
      (comp_freeSpeaker_ne_zero s _) (s.prior_ne_zero _) (s.prior_ne_zero _),
    freeSpeaker_real_singleton, freeSpeaker_real_singleton, speaker_exhaustified_wab_a,
    speaker_exhaustified_wa_a, speaker_antiExhaustive_wab_a, speaker_antiExhaustive_wa_a,
    Setting.speaker, speaker_literal_wab_a _ s.prior_ne_zero,
    speaker_literal_wa_a _ s.prior_ne_zero, Setting.prior_real_wab, Setting.prior_real_wa]
  constructor <;> intro h <;> linarith

/-- With equal costs, free lexical uncertainty is anti-exhaustive exactly when the baseline
is: for a prior biased towards the world of both. -/
theorem prior_lt_freeListener_iff_of_cost_eq (hc : s.cAndB = s.cAndNotB) :
    s.prior.real {.wab} < (freeListener s .a).real {.wab} ↔ 1 / 2 < s.p := by
  rw [prior_lt_freeListener_iff, hc, add_lt_add_iff_right, s.logistic_lt_iff,
    add_lt_add_iff_left, Real.log_lt_log_iff (by linarith [s.p_lt_one]) s.p_pos]
  constructor <;> intro <;> linarith

end LexicalUncertainty

/-! ### Lexical intentions (§4.4) -/

section LexicalIntentions

variable (s : Setting)

/-- The literal listener of a message under a chosen interpretation (item 1 of the §4.4
model). -/
noncomputable def liL0 : Kernel (Message × Interpretation) World :=
  RSA.literalListener s.prior λ x => (x.2.meaning.extension x.1).indicator 1

theorem liL0_apply (x : Message × Interpretation) : liL0 s x = s.L0 x.2.meaning x.1 := rfl

/-- The speaker over messages and interpretations (item 3 of the §4.4 model). -/
noncomputable def liSpeaker : Kernel World (Message × Interpretation) :=
  RSA.speaker s.lam (λ x => s.costFactor x.1) (liL0 s)

instance : IsFiniteKernel (liSpeaker s) := inferInstanceAs (IsFiniteKernel (RSA.speaker _ _ _))

/-- The speaker's messages, the interpretations marginalised (item 5 of the §4.4 model). -/
noncomputable def liMessageSpeaker : Kernel World Message := (liSpeaker s).map Prod.fst

instance : IsFiniteKernel (liMessageSpeaker s) :=
  inferInstanceAs (IsFiniteKernel (Kernel.map _ _))

/-- The lexical-intentions speaker's use of a message sums its two interpretations. -/
theorem liMessageSpeaker_apply_singleton (w : World) (u : Message) :
    liMessageSpeaker s w {u} = liSpeaker s w {(u, .lit)} + liSpeaker s w {(u, .exh)} := by
  rw [liMessageSpeaker, Kernel.map_apply _ measurable_fst]
  exact (Measure.fst_apply_singleton (liSpeaker s w) u).trans (sum_interpretation _)

/-- The lexical-intentions speaker's use of a message, on reals. -/
theorem liMessageSpeaker_real_singleton (w : World) (u : Message) :
    (liMessageSpeaker s w).real {u} =
      (liSpeaker s w).real {(u, .lit)} + (liSpeaker s w).real {(u, .exh)} := by
  rw [liMessageSpeaker, Kernel.map_apply _ measurable_fst]
  exact (Measure.fst_real_singleton_eq_sum (liSpeaker s w) u).trans (sum_interpretation _)

/-- The weight of a message under an interpretation is finite. -/
theorem liWeight_ne_top (w : World) (x : Message × Interpretation) :
    liL0 s x {w} ^ s.lam * s.costFactor x.1 ≠ ∞ :=
  weight_ne_top s.prior x.2.meaning s x.1 w

/-- In the world of both, the lexical-intentions speaker uses *A*, under its literal
interpretation only, against the two interpretations of *A and B*. -/
theorem liMessageSpeaker_real_wab_a :
    (liMessageSpeaker s .wab).real {.a} =
      Real.exp (s.lam * Real.log s.p) /
        (Real.exp (s.lam * Real.log s.p) + 2 * Real.exp (-(s.lam * s.cAndB))) := by
  rw [liMessageSpeaker_real_singleton, liSpeaker, RSA.speaker,
    Kernel.ofWeights_real_singleton _ _ (liWeight_ne_top s .wab),
    Kernel.ofWeights_real_singleton _ _ (liWeight_ne_top s .wab), Fintype.sum_prod_type,
    sum_message]
  simp (disch := decide) only [sum_interpretation, liL0_apply, Interpretation.meaning, Setting.L0,
    weight_toReal s.prior s.prior_ne_zero, weight_eq_zero s.prior, ENNReal.toReal_zero]
  simp (disch := decide) only [L0_literal_a, L0_eq_one s.prior s.prior_ne_zero, ← measureReal_def,
    Setting.prior_real_wab, ENNReal.toReal_one, Real.log_one, Setting.cost, sub_zero, zero_sub,
    mul_neg, add_zero]
  ring

/-- In the world of A alone, the lexical-intentions speaker uses *A* under both
interpretations, the exhaustified one as informative as *A and not B*. -/
theorem liMessageSpeaker_real_wa_a :
    (liMessageSpeaker s .wa).real {.a} =
      (Real.exp (s.lam * Real.log (1 - s.p)) + 1) /
        (Real.exp (s.lam * Real.log (1 - s.p)) + 1 + 2 * Real.exp (-(s.lam * s.cAndNotB))) := by
  rw [liMessageSpeaker_real_singleton, liSpeaker, RSA.speaker,
    Kernel.ofWeights_real_singleton _ _ (liWeight_ne_top s .wa),
    Kernel.ofWeights_real_singleton _ _ (liWeight_ne_top s .wa), Fintype.sum_prod_type,
    sum_message]
  simp (disch := decide) only [sum_interpretation, liL0_apply, Interpretation.meaning, Setting.L0,
    weight_toReal s.prior s.prior_ne_zero, weight_eq_zero s.prior, ENNReal.toReal_zero]
  simp (disch := decide) only [L0_literal_a, L0_eq_one s.prior s.prior_ne_zero, ← measureReal_def,
    Setting.prior_real_wa, ENNReal.toReal_one, Real.log_one, Setting.cost, sub_zero, zero_sub,
    mul_neg, mul_zero, Real.exp_zero, add_zero]
  ring

/-- A message true at a world is used there under its literal interpretation. -/
theorem liSpeaker_ne_zero {w : World} {u : Message} (hw : literal.sat u w = true) :
    liSpeaker s w {(u, .lit)} ≠ 0 :=
  Kernel.ofWeights_apply_singleton_ne_zero (weight_ne_zero s.prior s.prior_ne_zero literal s hw)
    (liWeight_ne_top s w)

/-- Every message is used somewhere, so is heard with positive probability. -/
theorem comp_liMessageSpeaker_ne_zero (u : Message) :
    (liMessageSpeaker s ∘ₘ s.prior) {u} ≠ 0 :=
  let ⟨w, hw⟩ := literal.exists_world u
  comp_apply_singleton_ne_zero _ _ (s.prior_ne_zero w) (by
    rw [liMessageSpeaker_apply_singleton]
    exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr (liSpeaker_ne_zero s hw)) le_self_add))

/-- The pragmatic listener of the lexical-intentions model (item 6 of the §4.4 model). -/
noncomputable def liListener : Kernel Message World := (liMessageSpeaker s)†s.prior

/-- The lexical-intentions model blocks anti-exhaustivity whenever *A and B* costs no more
than *A and not B*: *A* is never likelier in the world of both than in the world of A
alone. -/
theorem liListener_lt_prior (hc : s.cAndB ≤ s.cAndNotB) :
    (liListener s .a).real {.wab} < s.prior.real {.wab} := by
  rw [liListener, posterior_real_singleton_lt_iff_of_pair _ _ (by decide) s.prior_support
      (comp_liMessageSpeaker_ne_zero s _) (s.prior_ne_zero _) (s.prior_ne_zero _),
    liMessageSpeaker_real_wab_a, liMessageSpeaker_real_wa_a,
    div_lt_div_iff₀ (by positivity) (by positivity)]
  have h₁ : Real.exp (s.lam * Real.log s.p) < 1 :=
    Real.exp_lt_one_iff.mpr (mul_neg_of_pos_of_neg s.lam_pos (Real.log_neg s.p_pos s.p_lt_one))
  have h₂ : Real.exp (-(s.lam * s.cAndNotB)) ≤ Real.exp (-(s.lam * s.cAndB)) :=
    Real.exp_le_exp.mpr (by nlinarith [s.lam_pos])
  have h₃ := Real.exp_pos (-(s.lam * s.cAndNotB))
  have h₄ := Real.exp_pos (s.lam * Real.log (1 - s.p))
  nlinarith [mul_lt_mul_of_pos_right h₁ h₃, mul_pos h₄ (Real.exp_pos (-(s.lam * s.cAndB)))]

end LexicalIntentions

/-! ### The supervaluationist model (§4.2) -/

section Supervaluationist

variable (s : Setting)

/-- The cell of a world in a question: the coarse question does not distinguish the worlds,
the fine one does. -/
def QUD.cell : QUD → World → Set World
  | .coarse, _ => Set.univ
  | .fine, w => {w}

/-- The literal listener's mass, under an interpretation, on the cell of a world in a question
(item 3 of the §4.2 model, conditioned on the question). -/
noncomputable def cell (i : Interpretation) (q : QUD) (u : Message) (w : World) : ℝ≥0∞ :=
  s.L0 i.meaning u (q.cell w)

/-- The coarse question has one cell, which carries all the mass. -/
theorem cell_coarse (i : Interpretation) (u : Message) (w : World) :
    cell s i .coarse u w = 1 :=
  L0_apply_univ s.prior s.prior_ne_zero _ u

/-- The fine question's cells are the worlds. -/
theorem cell_fine (i : Interpretation) (u : Message) (w : World) :
    cell s i .fine u w = s.L0 i.meaning u {w} := rfl

/-- A cell's mass is at most one. -/
theorem cell_le_one (i : Interpretation) (q : QUD) (u : Message) (w : World) :
    cell s i q u w ≤ 1 :=
  RSA.literalListener_apply_le_one _ _ _ _

/-- The supervaluationist weight: the geometric mean over the two interpretations, taken
equiprobable, of the literal listener's mass on the cell, raised to the rationality, times the
cost factor; the prior of the question, common to every message, is left out (item 4 of the
§4.2 model). -/
noncomputable def svWeight (x : World × QUD) (u : Message) : ℝ≥0∞ :=
  cell s .lit x.2 u x.1 ^ (s.lam / 2) * cell s .exh x.2 u x.1 ^ (s.lam / 2) * s.costFactor u

theorem svWeight_ne_top (x : World × QUD) (u : Message) : svWeight s x u ≠ ∞ :=
  ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (RSA.weight_rpow_ne_top (half_pos s.lam_pos).le (cell_le_one s _ _ _ _))
      (RSA.weight_rpow_ne_top (half_pos s.lam_pos).le (cell_le_one s _ _ _ _)))
    (s.costFactor_ne_top u)

/-- Under the fine question a message true at a world under both interpretations has positive
weight there. -/
theorem svWeight_fine_ne_zero {w : World} {u : Message} (hl : truth u w = true)
    (he : exh u w = true) : svWeight s (w, .fine) u ≠ 0 :=
  mul_ne_zero
    (mul_ne_zero
      (RSA.weight_rpow_ne_zero (half_pos s.lam_pos).le
        (L0_ne_zero s.prior s.prior_ne_zero literal hl))
      (RSA.weight_rpow_ne_zero (half_pos s.lam_pos).le
        (L0_ne_zero s.prior s.prior_ne_zero exhaustified he)))
    (s.costFactor_ne_zero u)

/-- The supervaluationist speaker, at a world and a question (item 5 of the §4.2 model). -/
noncomputable def svSpeaker : Kernel (World × QUD) Message := Kernel.ofWeights (svWeight s)

instance : IsFiniteKernel (svSpeaker s) := inferInstanceAs (IsFiniteKernel (Kernel.ofWeights _))

/-- Under the coarse question every message is true on the one cell, so the speaker does not
depend on the world. -/
theorem svSpeaker_coarse : svSpeaker s (.wa, .coarse) = svSpeaker s (.wab, .coarse) := by
  have h : svWeight s (.wa, .coarse) = svWeight s (.wab, .coarse) :=
    funext λ u => by simp only [svWeight, cell_coarse]
  simp only [svSpeaker, Kernel.ofWeights, Kernel.ofFunOfCountable_apply, h]

/-- Under the fine question the exhaustified *A* is false in the world of both, so the
speaker never uses it. -/
theorem svSpeaker_wab_fine_a : svSpeaker s (.wab, .fine) {.a} = 0 :=
  Kernel.ofWeights_apply_singleton_eq_zero (by
    simp (disch := decide) only [svWeight, cell_fine, Setting.L0, Interpretation.meaning,
      L0_eq_zero, ENNReal.zero_rpow_of_pos (half_pos s.lam_pos), mul_zero, zero_mul])

theorem svSpeaker_real_wab_fine_a : (svSpeaker s (.wab, .fine)).real {.a} = 0 :=
  (measureReal_eq_zero_iff (measure_ne_top _ _)).mpr (svSpeaker_wab_fine_a s)

/-- Under the fine question a message true at a world under both interpretations is used
there. -/
theorem svSpeaker_fine_ne_zero {w : World} {u : Message} (hl : truth u w = true)
    (he : exh u w = true) : svSpeaker s (w, .fine) {u} ≠ 0 :=
  Kernel.ofWeights_apply_singleton_ne_zero (svWeight_fine_ne_zero s hl he) (svWeight_ne_top s _)

/-- Under either question, *A* is used no more in the world of both than in the world of A
alone (Appendix A.3, the speaker). -/
theorem svSpeaker_wab_le_wa (q : QUD) : svSpeaker s (.wab, q) {.a} ≤ svSpeaker s (.wa, q) {.a} := by
  cases q
  · rw [svSpeaker_coarse]
  · rw [svSpeaker_wab_fine_a]; exact zero_le

variable (Q : Measure QUD) [IsProbabilityMeasure Q] (hQ : Q {.fine} ≠ 0)

/-- The joint prior over worlds and questions, independent. -/
noncomputable def svJoint : Measure (World × QUD) := s.prior.prod Q

instance : IsProbabilityMeasure (svJoint s Q) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.prod _ _))

omit [IsProbabilityMeasure Q] in
theorem svJoint_apply_singleton (w : World) (q : QUD) :
    svJoint s Q {(w, q)} = s.prior {w} * Q {q} := by
  show (s.prior.prod Q) {(w, q)} = _
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]

omit [IsProbabilityMeasure Q] in
theorem svJoint_real_singleton (w : World) (q : QUD) :
    (svJoint s Q).real {(w, q)} = s.prior.real {w} * Q.real {q} :=
  Measure.prod_real_singleton _ _ _ _

/-- Every message is true somewhere under both grammatical interpretations. -/
theorem exists_truth_and_exh (u : Message) : ∃ w, truth u w = true ∧ exh u w = true := by
  cases u
  · exact ⟨.wa, rfl, by decide⟩
  · exact ⟨.wab, rfl, by decide⟩
  · exact ⟨.wa, rfl, by decide⟩

omit [IsProbabilityMeasure Q] in
include hQ in
/-- Every message is used somewhere under the fine question, so is heard with positive
probability. -/
theorem comp_svSpeaker_ne_zero (u : Message) : (svSpeaker s ∘ₘ svJoint s Q) {u} ≠ 0 :=
  let ⟨w, hw⟩ := exists_truth_and_exh u
  have hj : svJoint s Q {(w, .fine)} ≠ 0 := by
    rw [svJoint_apply_singleton]; exact mul_ne_zero (s.prior_ne_zero w) hQ
  comp_apply_singleton_ne_zero _ _ hj (svSpeaker_fine_ne_zero s hw.1 hw.2)

/-- The pragmatic listener, jointly over worlds and questions (item 6 of the §4.2 model). -/
noncomputable def svListener : Kernel Message (World × QUD) := (svSpeaker s)†(svJoint s Q)

include hQ in
/-- The posterior of both A and B falls below its prior, for every prior in the open interval,
every prior on the questions that gives the fine one positive probability, and every cost,
since the fine question contributes a use of *A* in the world of A alone and none in the
world of both (Appendix A.3, the listener). -/
theorem svListener_fst_lt_prior : (svListener s Q .a).fst.real {.wab} < s.prior.real {.wab} := by
  have hm : 0 < (svSpeaker s ∘ₘ svJoint s Q).real {.a} :=
    ENNReal.toReal_pos (comp_svSpeaker_ne_zero s Q hQ _) (measure_ne_top _ _)
  have hy : 0 < (svSpeaker s (.wa, .fine)).real {.a} :=
    ENNReal.toReal_pos (svSpeaker_fine_ne_zero s rfl (by decide)) (measure_ne_top _ _)
  have hqf : 0 < Q.real {.fine} := ENNReal.toReal_pos hQ (measure_ne_top _ _)
  have hz := measureReal_nonneg (μ := svSpeaker s (.wa, .coarse)) (s := {.a})
  have hqc := measureReal_nonneg (μ := Q) (s := {.coarse})
  have hp' : 0 < 1 - s.p := by linarith [s.p_lt_one]
  rw [svListener, posterior_fst_real_singleton _ _ (comp_svSpeaker_ne_zero s Q hQ _),
    div_lt_iff₀ hm, Measure.comp_real_singleton]
  simp only [Fintype.sum_prod_type, sum_world, sum_qud, svJoint_real_singleton,
    Setting.prior_real_wa, Setting.prior_real_wab, svSpeaker_real_wab_fine_a, ← svSpeaker_coarse,
    mul_zero, add_zero]
  nlinarith [mul_pos (mul_pos (mul_pos s.p_pos hp') hqf) hy]

end Supervaluationist

/-! ### The wonky-world models (§4.1) -/

section Wonky

variable (s : Setting) (ω : ℝ) (hω₀ : 0 ≤ ω) (hω₁ : ω ≤ 1)

/-- The speaker's prior under a background: uniform in the wonky background, measured
otherwise. -/
noncomputable def worldPrior : Background → Measure World
  | .wonky => wonkyPrior
  | .measured => s.prior

instance (b : Background) : IsProbabilityMeasure (worldPrior s b) := by
  cases b <;> dsimp only [worldPrior] <;> infer_instance

theorem worldPrior_ne_zero (b : Background) (w : World) : worldPrior s b {w} ≠ 0 := by
  cases b
  · exact wonkyPrior_ne_zero w
  · exact s.prior_ne_zero w

/-- The speaker under a background, with the background's prior in the literal listener
(items 1 to 3 of the §4.1 model). -/
noncomputable def bgSpeaker (b : Background) : Kernel World Message :=
  speaker (worldPrior s b) literal s

instance (b : Background) : IsFiniteKernel (bgSpeaker s b) :=
  inferInstanceAs (IsFiniteKernel (speaker _ _ _))

/-- The wonky speaker's use of *A* in the world of both: the logistic function of the cost of
*A and B* less the log of two. -/
theorem bgSpeaker_wonky_wab_a :
    (bgSpeaker s .wonky .wab).real {.a} = s.logistic (s.cAndB - Real.log 2) := by
  rw [bgSpeaker, speaker_literal_wab_a _ (worldPrior_ne_zero s .wonky), worldPrior,
    wonkyPrior_real_singleton, Real.log_inv, ← sub_eq_add_neg]

/-- The wonky speaker's use of *A* in the world of A alone: the logistic function of the cost
of *A and not B* less the log of two. -/
theorem bgSpeaker_wonky_wa_a :
    (bgSpeaker s .wonky .wa).real {.a} = s.logistic (s.cAndNotB - Real.log 2) := by
  rw [bgSpeaker, speaker_literal_wa_a _ (worldPrior_ne_zero s .wonky), worldPrior,
    wonkyPrior_real_singleton, Real.log_inv, ← sub_eq_add_neg]

/-- The measured speaker's use of *A* in the world of both. -/
theorem bgSpeaker_measured_wab_a :
    (bgSpeaker s .measured .wab).real {.a} = s.logistic (s.cAndB + Real.log s.p) := by
  rw [bgSpeaker, speaker_literal_wab_a _ (worldPrior_ne_zero s .measured), worldPrior,
    Setting.prior_real_wab]

/-- The measured speaker's use of *A* in the world of A alone. -/
theorem bgSpeaker_measured_wa_a :
    (bgSpeaker s .measured .wa).real {.a} = s.logistic (s.cAndNotB + Real.log (1 - s.p)) := by
  rw [bgSpeaker, speaker_literal_wa_a _ (worldPrior_ne_zero s .measured), worldPrior,
    Setting.prior_real_wa]

/-- The weight of a background: wonky with the wonkiness. -/
noncomputable def bgWeight : Background → ℝ≥0∞
  | .wonky => ENNReal.ofReal ω
  | .measured => ENNReal.ofReal (1 - ω)

theorem bgWeight_ne_top (b : Background) : bgWeight ω b ≠ ∞ := by
  cases b <;> exact ENNReal.ofReal_ne_top

/-- Some background has positive weight. -/
theorem bgWeight_exists_ne_zero : ∃ b, bgWeight ω b ≠ 0 :=
  (le_or_gt ω 0).elim (λ h => ⟨.measured, by simp [bgWeight]; linarith⟩)
    (λ h => ⟨.wonky, by simp [bgWeight, h]⟩)

/-- The speaker marginalised over the listener's uncertainty about the speaker's prior (item 5
of the §4.1 model, the Bayesian version). -/
noncomputable def bayesWonkySpeaker : Kernel World Message :=
  Kernel.mixture (bgWeight ω) (bgSpeaker s)

instance : IsFiniteKernel (bayesWonkySpeaker s ω) :=
  Kernel.isFiniteKernel_mixture _ _ (bgWeight_ne_top ω)

include hω₀ hω₁ in
/-- The Bayesian wonky speaker on reals. -/
theorem bayesWonkySpeaker_real_singleton (w : World) (u : Message) :
    (bayesWonkySpeaker s ω w).real {u} =
      ω * (bgSpeaker s .wonky w).real {u} + (1 - ω) * (bgSpeaker s .measured w).real {u} := by
  rw [bayesWonkySpeaker, Kernel.mixture_real _ _ (bgWeight_ne_top ω), sum_background]
  simp only [bgWeight, ENNReal.toReal_ofReal hω₀, ENNReal.toReal_ofReal (sub_nonneg.mpr hω₁)]

/-- Without wonkiness the Bayesian wonky speaker is the baseline speaker. -/
theorem bayesWonkySpeaker_zero (w : World) : bayesWonkySpeaker s 0 w = s.speaker literal w := by
  rw [bayesWonkySpeaker, Kernel.mixture_apply, sum_background]
  simp [bgWeight, bgSpeaker, worldPrior]

/-- Every message is used somewhere under a positively weighted background, so is heard with
positive probability. -/
theorem comp_bayesWonkySpeaker_ne_zero (u : Message) :
    (bayesWonkySpeaker s ω ∘ₘ s.prior) {u} ≠ 0 :=
  let ⟨w, hw⟩ := literal.exists_world u
  let ⟨b, hb⟩ := bgWeight_exists_ne_zero ω
  comp_apply_singleton_ne_zero _ _ (s.prior_ne_zero w)
    ((Kernel.mixture_apply_ne_zero_iff _ _ _ _).mpr
      ⟨b, hb, speaker_ne_zero _ (worldPrior_ne_zero s b) _ s hw⟩)

/-- The Bayesian wonky listener, with the measured prior. -/
noncomputable def bayesWonkyListener : Kernel Message World := (bayesWonkySpeaker s ω)†s.prior

include hω₀ hω₁ in
/-- Anti-exhaustivity exactly when the wonkiness-weighted excess of the use of *A* in the
world of both over its use in the world of A alone is positive (Appendix A.2, the Bayesian
model). -/
theorem prior_lt_bayesWonkyListener_iff :
    s.prior.real {.wab} < (bayesWonkyListener s ω .a).real {.wab} ↔
      0 < (1 - ω) * (s.logistic (s.cAndB + Real.log s.p) -
          s.logistic (s.cAndNotB + Real.log (1 - s.p))) +
        ω * (s.logistic (s.cAndB - Real.log 2) - s.logistic (s.cAndNotB - Real.log 2)) := by
  rw [bayesWonkyListener, real_lt_posterior_real_singleton_iff_of_pair _ _ (by decide)
      s.prior_support (comp_bayesWonkySpeaker_ne_zero s ω _) (s.prior_ne_zero _)
      (s.prior_ne_zero _),
    bayesWonkySpeaker_real_singleton s ω hω₀ hω₁, bayesWonkySpeaker_real_singleton s ω hω₀ hω₁,
    bgSpeaker_wonky_wab_a, bgSpeaker_wonky_wa_a, bgSpeaker_measured_wab_a,
    bgSpeaker_measured_wa_a]
  constructor <;> intro h <;> nlinarith

/-- The prior on backgrounds: wonky with the wonkiness. -/
noncomputable def bgPrior : Measure Background := ∑ b, bgWeight ω b • Measure.dirac b

theorem bgPrior_apply_singleton (b : Background) : bgPrior ω {b} = bgWeight ω b :=
  Measure.sum_smul_dirac_apply_singleton _ b

instance : IsFiniteMeasure (bgPrior ω) :=
  ⟨by
    rw [bgPrior, Measure.finsetSum_apply]
    exact ENNReal.sum_lt_top.mpr λ b _ => by
      rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
      exact (bgWeight_ne_top ω b).lt_top⟩

/-- The world given the background. -/
noncomputable def worldKernel : Kernel Background World := Kernel.ofFunOfCountable (worldPrior s)

instance : IsMarkovKernel (worldKernel s) :=
  ⟨λ b => by rw [worldKernel, Kernel.ofFunOfCountable_apply]; infer_instance⟩

/-- The prior of the non-Bayesian model: the background, then the world under it (item 4 of
the §4.1 model). -/
noncomputable def wonkyJoint : Measure (Background × World) := bgPrior ω ⊗ₘ worldKernel s

instance : IsFiniteMeasure (wonkyJoint s ω) :=
  inferInstanceAs (IsFiniteMeasure (bgPrior ω ⊗ₘ worldKernel s))

theorem wonkyJoint_apply_singleton (b : Background) (w : World) :
    wonkyJoint s ω {(b, w)} = bgWeight ω b * worldPrior s b {w} := by
  rw [wonkyJoint, Measure.compProd_apply_singleton, bgPrior_apply_singleton, worldKernel,
    Kernel.ofFunOfCountable_apply]

theorem wonkyJoint_real_singleton (b : Background) (w : World) :
    (wonkyJoint s ω).real {(b, w)} = (bgWeight ω b).toReal * (worldPrior s b).real {w} := by
  rw [measureReal_def, wonkyJoint_apply_singleton, ENNReal.toReal_mul, measureReal_def]

/-- The speaker of the non-Bayesian model, at a background and a world. -/
noncomputable def wonkySpeaker : Kernel (Background × World) Message :=
  Kernel.ofFunOfCountable λ x => bgSpeaker s x.1 x.2

theorem wonkySpeaker_apply (x : Background × World) : wonkySpeaker s x = bgSpeaker s x.1 x.2 :=
  rfl

instance : IsFiniteKernel (wonkySpeaker s) :=
  ⟨⟨1, ENNReal.one_lt_top, λ x => by
    rw [wonkySpeaker_apply, bgSpeaker, speaker, RSA.speaker]
    exact Kernel.ofWeights_apply_univ_le_one _ _⟩⟩

/-- A message true at a world is used there under either background. -/
theorem wonkySpeaker_ne_zero {w : World} {u : Message} (b : Background)
    (hw : literal.sat u w = true) : wonkySpeaker s (b, w) {u} ≠ 0 := by
  rw [wonkySpeaker_apply]
  exact speaker_ne_zero _ (worldPrior_ne_zero s _) _ s hw

/-- Every message is used somewhere under a positively weighted background, so is heard with
positive probability. -/
theorem comp_wonkySpeaker_ne_zero (u : Message) : (wonkySpeaker s ∘ₘ wonkyJoint s ω) {u} ≠ 0 :=
  let ⟨w, hw⟩ := literal.exists_world u
  let ⟨b, hb⟩ := bgWeight_exists_ne_zero ω
  have hj : wonkyJoint s ω {(b, w)} ≠ 0 := by
    rw [wonkyJoint_apply_singleton]; exact mul_ne_zero hb (worldPrior_ne_zero s b w)
  comp_apply_singleton_ne_zero _ _ hj (wonkySpeaker_ne_zero s b hw)

/-- The non-Bayesian listener, uncertain about the background and the world jointly (item 4
of the §4.1 model). -/
noncomputable def wonkyListener : Kernel Message (Background × World) :=
  (wonkySpeaker s)†(wonkyJoint s ω)

include hω₀ hω₁ in
/-- The non-Bayesian model is anti-exhaustive with respect to the measured prior exactly when
the prior times the marginal use of *A* falls below the background-weighted use of *A* in the
world of both; the paper resolves this inequality numerically (A.5a). -/
theorem prior_lt_wonkyListener_iff :
    s.prior.real {.wab} < (wonkyListener s ω .a).snd.real {.wab} ↔
      s.p * (ω * 2⁻¹ * (s.logistic (s.cAndNotB - Real.log 2) + s.logistic (s.cAndB - Real.log 2)) +
        (1 - ω) * ((1 - s.p) * s.logistic (s.cAndNotB + Real.log (1 - s.p)) +
          s.p * s.logistic (s.cAndB + Real.log s.p))) <
      ω * 2⁻¹ * s.logistic (s.cAndB - Real.log 2) +
        (1 - ω) * (s.p * s.logistic (s.cAndB + Real.log s.p)) := by
  have hm : 0 < (wonkySpeaker s ∘ₘ wonkyJoint s ω).real {.a} :=
    ENNReal.toReal_pos (comp_wonkySpeaker_ne_zero s ω _) (measure_ne_top _ _)
  rw [wonkyListener, posterior_snd_real_singleton _ _ (comp_wonkySpeaker_ne_zero s ω _),
    lt_div_iff₀ hm, Measure.comp_real_singleton]
  simp only [Fintype.sum_prod_type, sum_background, sum_world, wonkyJoint_real_singleton,
    wonkySpeaker_apply, bgSpeaker_wonky_wab_a, bgSpeaker_wonky_wa_a, bgSpeaker_measured_wab_a,
    bgSpeaker_measured_wa_a, bgWeight, ENNReal.toReal_ofReal hω₀,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hω₁), worldPrior, wonkyPrior_real_singleton,
    Setting.prior_real_wa, Setting.prior_real_wab]
  constructor <;> intro h <;> linarith

end Wonky

end CremersWilcoxSpector2023
