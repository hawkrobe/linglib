import Linglib.Pragmatics.RSA.QUD
import Linglib.Semantics.Attitudes.Factivity
import Linglib.Core.Probability.Kernel.Posterior

/-!
# Scontras and Tonhauser (2025): Projection without Lexically-Specified Presupposition

This file formalizes the paper's Rational Speech Act model of the projection of the complement
of *know* from under negation, on the RSA kernel pipeline. A world settles whether Cole believes
the complement and whether it is true; the six utterances of (3) have the literal meanings of
(4), *know* factive and *think* not (`literal`, from `Factivity`); the two questions of the
experiments, whether Cole believes the complement and whether it is true, partition the worlds
(`project`); a literal listener interprets the utterance within the speaker's private
assumptions, a set of worlds, and answers the question (5) (`L0`); the speaker best-responds at
rationality `α`, paying a cost that doubles for the complex utterances (6) (`S1`); and the
pragmatic listener, who hears the utterance and the question, inverts the speaker jointly over
worlds and assumptions (7) (`L1`), the private-assumption model of
[qing-goodman-lassiter-2016].

The paper's empirical targets (2), which its two experiments establish, are that the complement
projects more from under negated *know* than negated *think*, more when its prior probability is
higher, and more when it is not at issue; Figure 7 reports the model's predictions at the
parameters of [qing-goodman-lassiter-2016]. The prior effect is a theorem of the model: the
world prior enters at the pragmatic listener alone, so the posterior probability of the
complement rises with its prior probability under every utterance, question, rationality, cost
and assumption prior (`L1_c_mono`). The utterance and question effects rest on the speaker.
Negated *think* is semantically stronger than negated *know*
(`sem_thinkNeg_ssubset_sem_knowNeg`), so a speaker without assumptions who addresses whether
Cole believes the complement prefers it at a world where he does not
(`S1_univ_bel_knowNeg_lt_thinkNeg`); a speaker who assumes the complement finds the two equally
informative under either question (`S1_knowNeg_eq_thinkNeg`), negated *know* then answering the
belief question fully (`L0_knowNeg_bel_eq_one`); and under the belief question the speaker's
choice depends on the world only through Cole's belief (`S1_bel_congr`). The listener therefore
reads negated *know* as a sign that the speaker assumed the complement, most under the belief
question; the sizes of these effects (Figure 7a, c) are computations at the paper's parameters
and are not restated.

## Implementation notes

* Equation (5) carries a world prior, but in the released model the literal listener draws
  worlds uniformly within the assumption set and the world prior enters at (7) alone. The file
  follows the released model, whose predictions Figure 7 reports; this is what makes the prior
  effect a theorem. The listener's prior puts the actual world in the assumption set, as the
  released model does.
* The world prior is a parameter, in the theorems a product of a belief prior and a complement
  prior; the paper's is such a product, the complement twice as likely as not or half as likely.
  The prior over assumption sets is a parameter; the paper's is that of
  [qing-goodman-lassiter-2016].
* The cost factor is `κ` for a simple utterance and `κ ^ 2` for a complex one, `κ = exp (-α c)`
  for the paper's cost `c` of a simple utterance.
* The revised model of the paper's fourth section, which backs off toward the prior by the
  divergence of the posterior from it, and the experiments' ratings are described but not
  formalized.

## References

* [scontras-tonhauser-2025]
* [qing-goodman-lassiter-2016]
* [kao-etal-2014-hyperbole]
* [degen-tonhauser-2021]
-/

open MeasureTheory ProbabilityTheory RSA Factivity
open scoped ENNReal

namespace ScontrasTonhauser2025

/-- A world (4): whether Cole believes the complement and whether it is true. -/
abbrev World := Bool × Bool

instance : HasBelief World := ⟨Prod.fst⟩
instance : HasComplement World := ⟨Prod.snd⟩

instance : MeasurableSpace (Finset World) := ⊤
instance : DiscreteMeasurableSpace (Finset World) := ⟨λ _ => trivial⟩

/-- The utterances of (3): *Cole knows that C*, *Cole doesn't know that C*, *Cole thinks that
C*, *Cole doesn't think that C*, *C* and *not C*. -/
inductive Utt
  | knowPos | knowNeg | thinkPos | thinkNeg | cPos | cNeg
  deriving DecidableEq, Fintype

instance : MeasurableSpace Utt := ⊤
instance : DiscreteMeasurableSpace Utt := ⟨λ _ => trivial⟩

/-- A complex utterance embeds the complement under an attitude verb. -/
def Utt.Complex (u : Utt) : Prop := u ≠ .cPos ∧ u ≠ .cNeg

instance : DecidablePred Utt.Complex := λ u => inferInstanceAs (Decidable (u ≠ .cPos ∧ u ≠ .cNeg))

/-! ### Semantics and questions -/

/-- The literal meanings (4): *know* is factive and *think* is not, and the simple utterances
assert the complement or its negation. -/
def literal : Utt → World → Bool
  | .knowPos => factivePos
  | .knowNeg => factiveNeg
  | .thinkPos => nonFactivePos
  | .thinkNeg => nonFactiveNeg
  | .cPos => HasComplement.c
  | .cNeg => λ w => !HasComplement.c w

/-- The extension of an utterance. -/
def sem (u : Utt) : Finset World := Finset.univ.filter λ w => literal u w = true

/-- Negated *think* is semantically stronger than negated *know*: it excludes the world in which
Cole believes a false complement as well. -/
theorem sem_thinkNeg_ssubset_sem_knowNeg : sem .thinkNeg ⊂ sem .knowNeg := by decide

/-- The projections of the two questions: whether Cole believes the complement, and whether it
is true. -/
def project : QUD → World → Bool
  | .bel, w => w.1
  | .c, w => w.2

/-- The cell of a world under a question. -/
def cell (q : QUD) (w : World) : Finset World :=
  Finset.univ.filter λ w' => project q w' = project q w

theorem cell_preimage (q : QUD) (w : World) : project q ⁻¹' {project q w} = ↑(cell q w) := by
  ext w'
  simp [cell]

/-! ### The literal listener within an assumption set (5) -/

/-- The literal listener within an assumption set (5): uniform on the worlds of the set at which
the utterance is true, projected onto the question's answers. -/
noncomputable def L0 (A : Finset World) (q : QUD) : Kernel Utt World :=
  projListener project
    (literalListener (Measure.count.restrict ↑A) λ u => (↑(sem u) : Set World).indicator 1) q

/-- The counts behind the literal listener: worlds of the assumption set at which the utterance
is true and the question's answer is the world's, over those at which the utterance is true. -/
def l0 (A : Finset World) (q : QUD) (u : Utt) (w : World) : ℕ × ℕ :=
  (((A ∩ sem u).filter (· ∈ cell q w)).card, (A ∩ sem u).card)

theorem L0_apply (A : Finset World) (q : QUD) (u : Utt) (w : World) :
    L0 A q u {w} = ((l0 A q u w).1 : ℝ≥0∞) / (l0 A q u w).2 := by
  have e1 : (↑(sem u) : Set World) ∩ ↑A = ↑(A ∩ sem u) := by ext; simp [and_comm]
  have e2 : (↑(sem u) : Set World) ∩ ↑(cell q w) ∩ ↑A = ↑((A ∩ sem u).filter (· ∈ cell q w)) := by
    ext; simp; tauto
  rw [L0, projListener_apply_singleton, cell_preimage, literalListener_indicator,
    Kernel.ofFunOfCountable_apply, cond_apply MeasurableSet.of_discrete,
    Measure.restrict_apply MeasurableSet.of_discrete,
    Measure.restrict_apply MeasurableSet.of_discrete, e1, e2, Measure.count_apply_finset,
    Measure.count_apply_finset, l0, ENNReal.div_eq_inv_mul]

theorem L0_le_one (A : Finset World) (q : QUD) (u : Utt) (w : World) : L0 A q u {w} ≤ 1 := by
  rw [L0_apply]
  exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact_mod_cast Finset.card_filter_le _ _)

/-- A speaker who assumes the complement interprets negated *know* and negated *think* alike:
within the assumption set, the belief is false under both. -/
theorem L0_knowNeg_eq_thinkNeg {A : Finset World} (hA : A ⊆ sem .cPos) (q : QUD) :
    L0 A q .knowNeg = L0 A q .thinkNeg := by
  have h : A ∩ sem .knowNeg = A ∩ sem .thinkNeg := by
    ext w
    obtain ⟨b, c⟩ := w
    simp only [Finset.mem_inter, sem, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> rintro ⟨hw, hl⟩ <;> refine ⟨hw, ?_⟩ <;>
      have hc := (Finset.mem_filter.mp (hA hw)).2 <;>
      revert hc hl <;> cases b <;> cases c <;> decide
  exact Measure.ext_of_singleton λ w => by rw [L0_apply, L0_apply, l0, l0, h]

/-- Under the belief question, a speaker who assumes the complement answers fully with negated
*know* at a world in which Cole does not believe the complement. -/
theorem L0_knowNeg_bel_eq_one {A : Finset World} (hA : A ⊆ sem .cPos) {w : World} (hw : w ∈ A)
    (hb : w.1 = false) : L0 A .bel .knowNeg {w} = 1 := by
  rw [L0_apply, l0, Finset.filter_true_of_mem]
  · refine ENNReal.div_self ?_ (ENNReal.natCast_ne_top _)
    refine Nat.cast_ne_zero.mpr (Finset.card_pos.mpr ⟨w, Finset.mem_inter.mpr ⟨hw, ?_⟩⟩).ne'
    obtain ⟨b, c⟩ := w
    have hc := (Finset.mem_filter.mp (hA hw)).2
    simp only at hb
    subst hb
    revert hc
    cases c <;> decide
  · intro w' hw'
    obtain ⟨hw'A, hl⟩ := Finset.mem_inter.mp hw'
    have hc := (Finset.mem_filter.mp (hA hw'A)).2
    obtain ⟨b, c⟩ := w'
    obtain ⟨b₀, c₀⟩ := w
    simp only at hb
    subst hb
    simp only [cell, project, Finset.mem_filter, Finset.mem_univ, true_and]
    revert hc hl
    cases b <;> cases c <;> decide

/-- Without assumptions, negated *think* answers the belief question fully at a world in which
Cole does not believe the complement. -/
theorem L0_univ_bel_thinkNeg {w : World} (hb : w.1 = false) :
    L0 Finset.univ .bel .thinkNeg {w} = 1 := by
  obtain ⟨b, c⟩ := w
  simp only at hb
  subst hb
  rw [L0_apply, show l0 Finset.univ .bel .thinkNeg (false, c) = (2, 2) from by cases c <;> decide]
  exact ENNReal.div_self (by norm_num) (by norm_num)

/-- Without assumptions, negated *know* leaves the belief question open at such a world: it is
also true where Cole believes a false complement. -/
theorem L0_univ_bel_knowNeg {w : World} (hb : w.1 = false) :
    L0 Finset.univ .bel .knowNeg {w} = 2 / 3 := by
  obtain ⟨b, c⟩ := w
  simp only at hb
  subst hb
  rw [L0_apply, show l0 Finset.univ .bel .knowNeg (false, c) = (2, 3) from by cases c <;> decide]
  norm_num

/-! ### The speaker (6) -/

/-- The cost factor of (6): `κ` for a simple utterance and `κ ^ 2` for a complex one, the
complex utterances being twice as costly. -/
noncomputable def cost (κ : ℝ≥0∞) (u : Utt) : ℝ≥0∞ := if u.Complex then κ ^ 2 else κ

theorem cost_ne_zero {κ : ℝ≥0∞} (hκ : κ ≠ 0) (u : Utt) : cost κ u ≠ 0 := by
  unfold cost
  split_ifs <;> simp [hκ]

theorem cost_ne_top {κ : ℝ≥0∞} (hκ : κ ≠ ∞) (u : Utt) : cost κ u ≠ ∞ := by
  unfold cost
  split_ifs <;> simp [hκ]

/-- The speaker within an assumption set (6): the best response at rationality `α` to the literal
listener projected by the question, with the cost factor. -/
noncomputable def S1 (α : ℝ) (κ : ℝ≥0∞) (A : Finset World) (q : QUD) : Kernel World Utt :=
  speaker α (cost κ) (L0 A q)

variable (α : ℝ) (κ : ℝ≥0∞)

/-- A speaker who assumes the complement produces negated *know* and negated *think* alike,
under either question: they are equally informative and equally costly. -/
theorem S1_knowNeg_eq_thinkNeg {A : Finset World} (hA : A ⊆ sem .cPos) (q : QUD) (w : World) :
    S1 α κ A q w {.knowNeg} = S1 α κ A q w {.thinkNeg} := by
  rw [S1, speaker_apply_singleton, speaker_apply_singleton, L0_knowNeg_eq_thinkNeg hA]
  rfl

/-- Without assumptions, a speaker addressing the belief question at a world in which Cole does
not believe the complement prefers negated *think* to negated *know*: the stronger utterance is
the more informative. -/
theorem S1_univ_bel_knowNeg_lt_thinkNeg (hα : 0 < α) (hκ0 : κ ≠ 0) (hκ : κ ≠ ∞) {w : World}
    (hb : w.1 = false) :
    (S1 α κ Finset.univ .bel w).real {.knowNeg} < (S1 α κ Finset.univ .bel w).real {.thinkNeg} := by
  have hc : cost κ .thinkNeg = κ ^ 2 := if_pos (by decide)
  have hc' : cost κ .knowNeg = κ ^ 2 := if_pos (by decide)
  rw [S1, speaker_real_singleton_lt_iff hα.le (cost_ne_top hκ) (L0_le_one Finset.univ .bel · w)
    ⟨.thinkNeg, by
      rw [L0_univ_bel_thinkNeg hb, ENNReal.one_rpow, one_mul]
      exact cost_ne_zero hκ0 _⟩,
    hc, hc', L0_univ_bel_thinkNeg hb, L0_univ_bel_knowNeg hb, ENNReal.one_rpow]
  refine ENNReal.mul_lt_mul_left (pow_ne_zero 2 hκ0) (ENNReal.pow_ne_top hκ) ?_
  rw [← ENNReal.one_rpow α]
  refine ENNReal.rpow_lt_rpow ?_ hα
  rw [ENNReal.div_lt_iff (Or.inl three_ne_zero) (Or.inl (ENNReal.ofNat_ne_top)), one_mul]
  norm_num

/-- Under the belief question the speaker's choice depends on the world only through Cole's
belief: the question's cells do. -/
theorem S1_bel_congr (A : Finset World) {w w' : World} (h : w.1 = w'.1) :
    S1 α κ A .bel w = S1 α κ A .bel w' := by
  have hc : cell .bel w = cell .bel w' := by ext; simp [cell, project, h]
  rw [S1, speaker]
  exact Measure.ext_of_singleton λ u => by
    simp only [Kernel.ofWeights_apply_singleton, L0_apply, l0, hc]

/-! ### The pragmatic listener (7) -/

/-- The listener's prior: a world with an assumption set containing it, weighted by the world
prior and the assumption prior. -/
noncomputable def pairPrior (μ : Measure World) (ν : Measure (Finset World)) :
    Measure (World × Finset World) :=
  (μ.prod ν).restrict {p | p.1 ∈ p.2}

variable (μ : Measure World) (ν : Measure (Finset World))

theorem pairPrior_singleton [SFinite ν] (w : World) (A : Finset World) :
    pairPrior μ ν {(w, A)} = if w ∈ A then μ {w} * ν {A} else 0 := by
  rw [pairPrior, Measure.restrict_apply (measurableSet_singleton _)]
  split_ifs with h
  · rw [Set.inter_eq_self_of_subset_left (s := ({(w, A)} : Set (World × Finset World)))
        (Set.singleton_subset_iff.mpr h),
      ← Set.singleton_prod_singleton, Measure.prod_prod]
  · rw [(Set.singleton_inter_eq_empty (a := (w, A))
        (s := {p : World × Finset World | p.1 ∈ p.2})).mpr h, measure_empty]

instance [IsFiniteMeasure μ] [IsFiniteMeasure ν] : IsFiniteMeasure (pairPrior μ ν) :=
  inferInstanceAs (IsFiniteMeasure ((μ.prod ν).restrict _))

/-- The pragmatic listener (7): the family listener over assumption sets, hearing the utterance
under a known question. -/
noncomputable def L1 [IsFiniteMeasure μ] [IsFiniteMeasure ν] (q : QUD) :
    Kernel Utt (World × Finset World) :=
  familyListener (λ A => L0 A q) α (cost κ) (pairPrior μ ν)

theorem pairPrior_real [IsFiniteMeasure μ] [IsFiniteMeasure ν] (w : World) (A : Finset World) :
    (pairPrior μ ν).real {(w, A)} = if w ∈ A then μ.real {w} * ν.real {A} else 0 := by
  rw [measureReal_def, pairPrior_singleton]
  split_ifs <;> simp [measureReal_def, ENNReal.toReal_mul]

/-! ### The prior effect (2b) -/

/-- An utterance true at a world of positive prior lying in an assumption set of positive prior
has a positive marginal. -/
theorem comp_ne_zero [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hα : 0 ≤ α) (hκ0 : κ ≠ 0)
    (hκ : κ ≠ ∞) (q : QUD) {u : Utt} {w : World} {A : Finset World} (hw : w ∈ A)
    (hu : w ∈ sem u) (hμ : μ {w} ≠ 0) (hν : ν {A} ≠ 0) :
    (familySpeaker (λ A => L0 A q) α (cost κ) ∘ₘ pairPrior μ ν) {u} ≠ 0 := by
  refine comp_familySpeaker_ne_zero (w := w) (l := A) ?_ ?_
  · rw [pairPrior_singleton, if_pos hw]
    exact mul_ne_zero hμ hν
  · refine speaker_apply_singleton_ne_zero hα (cost_ne_zero hκ0) (cost_ne_top hκ)
      (λ u' => L0_le_one A q u' w) ?_
    rw [L0_apply, ne_eq, ENNReal.div_eq_zero_iff, not_or]
    refine ⟨Nat.cast_ne_zero.mpr (Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr
      ⟨Finset.mem_inter.mpr ⟨hw, hu⟩, ?_⟩⟩).ne', ENNReal.natCast_ne_top _⟩
    simp [cell]

/-! ### The prior effect (2b) -/

section PriorEffect

variable (β γ : Measure Bool) (q : QUD) (u : Utt)

/-- The listener's evidence for a value of the complement: the speaker's production of the
utterance at the worlds with that value, weighted by the belief prior and by the assumption
prior over the assumption sets containing them. It does not depend on the complement prior. -/
noncomputable def cWeight (c : Bool) : ℝ :=
  ∑ b, ∑ A, if (b, c) ∈ A then β.real {b} * ν.real {A} * (S1 α κ A q (b, c)).real {u} else 0

theorem cWeight_nonneg (c : Bool) : 0 ≤ cWeight α κ ν β q u c :=
  Finset.sum_nonneg λ _ _ => Finset.sum_nonneg λ _ _ => by
    split_ifs
    · exact mul_nonneg (mul_nonneg measureReal_nonneg measureReal_nonneg) measureReal_nonneg
    · exact le_rfl

private theorem sum_pairs (f : World × Finset World → ℝ) :
    ∑ p, f p = ∑ b, ∑ c, ∑ A, f ((b, c), A) := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]

private theorem sum_pairs_c (f : World × Finset World → ℝ) :
    ∑ p ∈ Finset.univ.filter (λ p : World × Finset World => p.1.2 = true), f p
      = ∑ b, ∑ A, f ((b, true), A) := by
  rw [Finset.sum_filter, sum_pairs]
  simp

variable [IsProbabilityMeasure β] [IsProbabilityMeasure γ] [IsProbabilityMeasure ν]

private theorem comp_real :
    (familySpeaker (λ A => L0 A q) α (cost κ) ∘ₘ pairPrior (β.prod γ) ν).real {u}
      = γ.real {true} * cWeight α κ ν β q u true + γ.real {false} * cWeight α κ ν β q u false := by
  rw [Measure.comp_real_singleton, sum_pairs, Finset.sum_comm, Fintype.sum_bool]
  simp only [pairPrior_real, Measure.prod_real_singleton, familySpeaker_apply, cWeight,
    Finset.mul_sum, mul_ite, mul_zero, ite_mul, zero_mul]
  refine congrArg₂ (· + ·) ?_ ?_ <;>
    refine Finset.sum_congr rfl λ b _ => Finset.sum_congr rfl λ A _ => ?_ <;>
    split_ifs <;> first | rfl | (simp only [S1]; ring)

/-- The posterior probability of the complement (fn. 11): its prior probability times the
evidence for it, over the evidence for either value. -/
theorem L1_c_real (hu : (familySpeaker (λ A => L0 A q) α (cost κ) ∘ₘ pairPrior (β.prod γ) ν)
    {u} ≠ 0) :
    (L1 α κ (β.prod γ) ν q u).real {p | p.1.2 = true}
      = γ.real {true} * cWeight α κ ν β q u true
        / (γ.real {true} * cWeight α κ ν β q u true
          + γ.real {false} * cWeight α κ ν β q u false) := by
  have hE : ({p : World × Finset World | p.1.2 = true} : Set _)
      = ↑(Finset.univ.filter λ p : World × Finset World => p.1.2 = true) := by ext; simp
  rw [measureReal_def, L1, familyListener, hE, posterior_apply_finset _ _ hu, ENNReal.toReal_div,
    ENNReal.toReal_sum (λ _ _ => ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)),
    ← measureReal_def, comp_real]
  simp only [ENNReal.toReal_mul, ← measureReal_def]
  rw [sum_pairs_c]
  simp only [pairPrior_real, Measure.prod_real_singleton, familySpeaker_apply, cWeight,
    Finset.mul_sum, mul_ite, mul_zero, ite_mul, zero_mul]
  congr 1
  refine Finset.sum_congr rfl λ b _ => Finset.sum_congr rfl λ A _ => ?_
  split_ifs <;> first | rfl | (simp only [S1]; ring)

private theorem real_false_eq (ρ : Measure Bool) [IsProbabilityMeasure ρ] :
    ρ.real {false} = 1 - ρ.real {true} := by
  have h := probReal_univ (μ := ρ)
  rw [← Finset.coe_univ, ← sum_measureReal_singleton, Fintype.sum_bool] at h
  linarith

/-- The prior effect (2b): the posterior probability of the complement rises with its prior
probability, under every utterance, question, rationality, cost and assumption prior, since the
world prior enters the model at the pragmatic listener alone. -/
theorem L1_c_mono (γ' : Measure Bool) [IsProbabilityMeasure γ']
    (hu : (familySpeaker (λ A => L0 A q) α (cost κ) ∘ₘ pairPrior (β.prod γ) ν) {u} ≠ 0)
    (hu' : (familySpeaker (λ A => L0 A q) α (cost κ) ∘ₘ pairPrior (β.prod γ') ν) {u} ≠ 0)
    (h : γ.real {true} ≤ γ'.real {true}) :
    (L1 α κ (β.prod γ) ν q u).real {p | p.1.2 = true}
      ≤ (L1 α κ (β.prod γ') ν q u).real {p | p.1.2 = true} := by
  have hd : 0 < γ.real {true} * cWeight α κ ν β q u true
      + γ.real {false} * cWeight α κ ν β q u false := by
    rw [← comp_real]
    exact ENNReal.toReal_pos hu (measure_ne_top _ _)
  have hd' : 0 < γ'.real {true} * cWeight α κ ν β q u true
      + γ'.real {false} * cWeight α κ ν β q u false := by
    rw [← comp_real]
    exact ENNReal.toReal_pos hu' (measure_ne_top _ _)
  rw [L1_c_real _ _ _ _ _ _ _ hu, L1_c_real _ _ _ _ _ _ _ hu', div_le_div_iff₀ hd hd']
  rw [real_false_eq γ, real_false_eq γ'] at *
  nlinarith [mul_nonneg (mul_nonneg (cWeight_nonneg α κ ν β q u true)
    (cWeight_nonneg α κ ν β q u false)) (sub_nonneg.2 h)]

end PriorEffect

end ScontrasTonhauser2025
