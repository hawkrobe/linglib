import Linglib.Pragmatics.DecisionTheoretic.Basic
import Linglib.Core.Probability.ENNRealArith
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# [cummins-franke-2021]: Rational Interpretation of Numerical Quantity
[cummins-franke-2021] [merin-1999-relevance]

[cummins-franke-2021] applies [merin-1999-relevance]'s log-likelihood-ratio measure of
argumentative strength to numerical quantity expressions: the strength of utterance u toward
goal G is log (P(u∣G) / P(u∣¬G)) (eq. 17), and a pragmatic variant replaces truth with
felicitous assertability (eq. 25). The §5 worked example: a conference succeeds iff more than
120 people register, registrations are uniform on [0, 200], and the speaker chooses between
*more than 100* and *more than 110*.

## Main results

- `bayesFactor_lt_of_goal_entails`: §5.1's alignment of semantic and argumentative strength,
  in general form — between utterances entailed by the goal, the semantically stronger one is
  the argumentatively stronger one, since its extra content can only shed ¬G-worlds.
- `cond_prod_byInterpretation`: §5.2's computation pattern in general form — over the
  enriched/literal interpretation mixture, an interpretation-dependent event's conditional
  probability is the mixture of its branches' conditional probabilities.
- `strength_reversal`: the paper's central demonstration — semantically *more than 110* is
  the stronger argument for success (`semantic_ordering`, Bayes factors 6 < 12), but under
  assertability with a 90%-enriching listener the ordering *reverses* (21/8 vs 6/5).

The §5.1–5.2 Bayes-factor values are computed against a counting prior over 20 bands of
width 10 (every threshold in the example — 100, 110, 120, 150 — is a band boundary, so the
paper's continuous uniform distribution on [0, 200] is represented exactly, and conditioning
normalizes away the total mass). Concrete masses evaluate by `count_apply_fintype` and
comparisons transfer to ℝ, following the countable-space register of
`Mathlib.Probability.Decision.Risk.Countable`. The measure `strength` is `Real.log` (nats)
of `DTS.bayesFactor`; the paper leaves the log base unspecified (its printed values are base
10) and uses it only ordinally.

Deviation: for *more than 110* the paper prints log 11, computed from "the probability that
*more than 100* is true given that *more than 110* is false equals 1/11" — the Bayes factor
of *more than 100* toward the goal *more than 110* (`bayesFactor_moreThan100_toward110`).
Toward the example's stated goal (*more than 120*) the factor is 12
(`bayesFactor_moreThan110`); the semantic ordering is the same either way.

Not formalized: the §5.4 rational-hearer conditions (eqs. 27–28), which compare an
utterance's strength against the alternatives assertable in ¬G-worlds and are stated but not
computed with in the paper; and the §6 corpus study of research-ranking reports.
-/

namespace CumminsFranke2021

open DTS MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {W : Type*} [MeasurableSpace W]

/-! ### Semantic strength and goal entailment (§5.1) -/

/-- §5.1's alignment of semantic and argumentative strength: between two utterances entailed
by the goal, the semantically stronger (smaller) one is the argumentatively stronger one —
both are certain given the goal, and the weaker utterance's extra extension can only add
¬G-mass to the denominator of the Bayes factor. -/
theorem bayesFactor_lt_of_goal_entails (ctx : DTS.Context W) [IsFiniteMeasure ctx.prior]
    {u₁ u₂ : Set W} (h₂m : MeasurableSet u₂)
    (hsub : u₂ ⊆ u₁) (hent : ctx.topic ⊆ u₂) (hG : ctx.prior ctx.topic ≠ 0)
    (hgap : ctx.prior ((ctx.topicᶜ ∩ u₁) \ u₂) ≠ 0)
    (hpos : ctx.prior (ctx.topicᶜ ∩ u₂) ≠ 0) :
    bayesFactor ctx u₁ < bayesFactor ctx u₂ := by
  have hHm := ctx.topicMeasurable
  have hNH : ctx.prior ctx.topicᶜ ≠ 0 := fun h =>
    hpos (measure_mono_null Set.inter_subset_left h)
  have hd : ctx.prior (ctx.topicᶜ ∩ u₂) < ctx.prior (ctx.topicᶜ ∩ u₁) := by
    have hsplit := measure_inter_add_sdiff (μ := ctx.prior) (ctx.topicᶜ ∩ u₁) h₂m
    rw [show ctx.topicᶜ ∩ u₁ ∩ u₂ = ctx.topicᶜ ∩ u₂ from
      Set.ext fun w => ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hsub h.2⟩, h.2⟩⟩] at hsplit
    rw [← hsplit]
    exact ENNReal.lt_add_right (measure_ne_top _ _) hgap
  rw [bayesFactor_def, bayesFactor_def,
    cond_eq_one_of_subset _ hHm (hent.trans hsub) hG,
    cond_eq_one_of_subset _ hHm hent hG,
    cond_apply hHm.compl, cond_apply hHm.compl, one_div, one_div,
    ENNReal.inv_lt_inv]
  exact ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
    (ENNReal.inv_ne_top.mpr hNH) hd

/-! ### The §5 example -/

/-- Registration totals in bands of width 10: band k covers (10k, 10(k+1)]. Every threshold
in the §5 example (100, 110, 120, 150) is a band boundary, so the paper's continuous uniform
distribution on [0, 200] is represented exactly by a counting prior over the 20 bands. -/
abbrev Band := Fin 20

/-- The extension of *more than n*, for thresholds n that are multiples of 10: every total in
band k exceeds n iff n ≤ 10k. -/
def moreThan (n : ℕ) : Set Band := {k | n ≤ 10 * (k : ℕ)}

instance (n : ℕ) : DecidablePred (· ∈ moreThan n) := fun k =>
  inferInstanceAs (Decidable (n ≤ 10 * (k : ℕ)))

/-- §5.1: the goal is S = *more than 120* (conference success), with the counting prior
(conditioning normalizes, so counting and uniform priors induce the same strengths). -/
noncomputable abbrev successContext : DTS.Context Band :=
  ⟨moreThan 120, .of_discrete, .count⟩

private lemma count_ne {e : Set Band} [DecidablePred (· ∈ e)]
    (h : (Finset.univ.filter (· ∈ e)).card ≠ 0) :
    (Measure.count : Measure Band) e ≠ 0 := by
  rw [count_apply_fintype]
  exact Nat.cast_ne_zero.mpr h

private lemma cond_count_ne {s e : Set Band} [DecidablePred (· ∈ s)] [DecidablePred (· ∈ e)]
    (h : (Finset.univ.filter (· ∈ s ∩ e)).card ≠ 0) :
    (Measure.count : Measure Band)[|s] e ≠ 0 := by
  rw [cond_apply MeasurableSet.of_discrete]
  exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) (count_ne h)

/-- §5.1: the Bayes factor of *more than 100* toward success is 1 / (1/6) = 6 (the paper's
log 6 ≈ 0.78). -/
theorem bayesFactor_moreThan100 : bayesFactor successContext (moreThan 100) = 6 := by
  rw [bayesFactor_def]
  refine ENNReal.eq_of_toReal
    ((ENNReal.div_lt_top (cond_apply_ne_top _ MeasurableSet.of_discrete _)
      (cond_count_ne (by decide))).ne) (by finiteness) ?_
  rw [ENNReal.toReal_div, cond_real_apply _ MeasurableSet.of_discrete,
    cond_real_apply _ MeasurableSet.of_discrete]
  simp only [count_apply_fintype, ENNReal.toReal_natCast, Set.mem_inter_iff,
    Set.mem_compl_iff]
  norm_num [show (Finset.univ.filter fun x : Band =>
      x ∈ moreThan 120 ∧ x ∈ moreThan 100).card = 8 from by decide,
    show (Finset.univ.filter (· ∈ moreThan 120)).card = 8 from by decide,
    show (Finset.univ.filter fun x : Band =>
      x ∉ moreThan 120 ∧ x ∈ moreThan 100).card = 2 from by decide,
    show (Finset.univ.filter fun x : Band => x ∉ moreThan 120).card = 12 from by decide]

/-- The Bayes factor of *more than 110* toward success is 1 / (1/12) = 12. The paper instead
prints log 11 (see `bayesFactor_moreThan100_toward110`); the ordering against
`bayesFactor_moreThan100` is the same. -/
theorem bayesFactor_moreThan110 : bayesFactor successContext (moreThan 110) = 12 := by
  rw [bayesFactor_def]
  refine ENNReal.eq_of_toReal
    ((ENNReal.div_lt_top (cond_apply_ne_top _ MeasurableSet.of_discrete _)
      (cond_count_ne (by decide))).ne) (by finiteness) ?_
  rw [ENNReal.toReal_div, cond_real_apply _ MeasurableSet.of_discrete,
    cond_real_apply _ MeasurableSet.of_discrete]
  simp only [count_apply_fintype, ENNReal.toReal_natCast, Set.mem_inter_iff,
    Set.mem_compl_iff]
  norm_num [show (Finset.univ.filter fun x : Band =>
      x ∈ moreThan 120 ∧ x ∈ moreThan 110).card = 8 from by decide,
    show (Finset.univ.filter (· ∈ moreThan 120)).card = 8 from by decide,
    show (Finset.univ.filter fun x : Band =>
      x ∉ moreThan 120 ∧ x ∈ moreThan 110).card = 1 from by decide,
    show (Finset.univ.filter fun x : Band => x ∉ moreThan 120).card = 12 from by decide]

/-- The quantity behind the paper's printed log 11: the Bayes factor of *more than 100*
toward the goal *more than 110* ("the probability that *more than 100* is true given that
*more than 110* is false equals 1/11"). -/
theorem bayesFactor_moreThan100_toward110 :
    bayesFactor ⟨moreThan 110, .of_discrete, .count⟩ (moreThan 100) = 11 := by
  rw [bayesFactor_def]
  refine ENNReal.eq_of_toReal
    ((ENNReal.div_lt_top (cond_apply_ne_top _ MeasurableSet.of_discrete _)
      (cond_count_ne (by decide))).ne) (by finiteness) ?_
  rw [ENNReal.toReal_div, cond_real_apply _ MeasurableSet.of_discrete,
    cond_real_apply _ MeasurableSet.of_discrete]
  simp only [count_apply_fintype, ENNReal.toReal_natCast, Set.mem_inter_iff,
    Set.mem_compl_iff]
  norm_num [show (Finset.univ.filter fun x : Band =>
      x ∈ moreThan 110 ∧ x ∈ moreThan 100).card = 9 from by decide,
    show (Finset.univ.filter (· ∈ moreThan 110)).card = 9 from by decide,
    show (Finset.univ.filter fun x : Band =>
      x ∉ moreThan 110 ∧ x ∈ moreThan 100).card = 1 from by decide,
    show (Finset.univ.filter fun x : Band => x ∉ moreThan 110).card = 11 from by decide]

/-- §5.1 as an instance of `bayesFactor_lt_of_goal_entails`: both utterances are entailed by
the goal and *more than 110* is semantically stronger, so it is the stronger argument. -/
theorem semantic_ordering :
    bayesFactor successContext (moreThan 100) < bayesFactor successContext (moreThan 110) :=
  bayesFactor_lt_of_goal_entails successContext .of_discrete
    (fun k hk => le_trans (show (100 : ℕ) ≤ 110 by norm_num) hk)
    (fun k hk => le_trans (show (110 : ℕ) ≤ 120 by norm_num) hk)
    (count_ne (by decide)) (count_ne (by decide)) (count_ne (by decide))

/-! ### The assertability mixture (§5.2)

Assertability is stochastic: with probability 9/10 the listener enriches the utterance with
its scalar implicature (*more than 100* ⇝ *not more than 150*, *more than 110* ⇝ *not more
than 120*), so u is felicitously assertable only if the implicature is also true; with
probability 1/10 the utterance is interpreted literally. The mixture lives on the product of
worlds and interpretations, where interpretation-dependent events are unions of rectangles
and conditional probabilities decompose branchwise. -/

/-- How the listener resolves an utterance (§5.2): enriched with its scalar implicature, or
literal. -/
inductive Interpretation where
  | enriched | literal
  deriving DecidableEq

instance : Fintype Interpretation where
  elems := {.enriched, .literal}
  complete := fun x => by cases x <;> simp

instance : MeasurableSpace Interpretation := ⊤
instance : DiscreteMeasurableSpace Interpretation := ⟨fun _ => trivial⟩

/-- An interpretation-dependent event: `enr` under enrichment, `lit` under literal
interpretation. -/
def byInterpretation (enr lit : Set W) : Set (W × Interpretation) :=
  enr ×ˢ {Interpretation.enriched} ∪ lit ×ˢ {Interpretation.literal}

/-- Mass of an interpretation-dependent event under a product prior: the branches weigh
their events by the interpretation probabilities. -/
theorem prod_byInterpretation (μ : Measure W) (ν : Measure Interpretation) [SFinite ν]
    {enr lit : Set W} (hlit : MeasurableSet lit) :
    (μ.prod ν) (byInterpretation enr lit) =
      μ enr * ν {Interpretation.enriched} + μ lit * ν {Interpretation.literal} := by
  rw [byInterpretation, measure_union
      (Set.disjoint_prod.mpr (Or.inr (by simp)))
      (hlit.prod MeasurableSet.of_discrete),
    Measure.prod_prod, Measure.prod_prod]

/-- §5.2's computation pattern: conditional on a lifted event, an interpretation-dependent
event's probability is the mixture of its branches' conditional probabilities. -/
theorem cond_prod_byInterpretation (μ : Measure W) (ν : Measure Interpretation)
    [IsProbabilityMeasure ν] {s enr lit : Set W} (hs : MeasurableSet s)
    (hlit : MeasurableSet lit) :
    (μ.prod ν)[|s ×ˢ (Set.univ : Set Interpretation)] (byInterpretation enr lit) =
      ν {Interpretation.enriched} * μ[|s] enr + ν {Interpretation.literal} * μ[|s] lit := by
  rw [cond_apply (hs.prod MeasurableSet.univ),
    show s ×ˢ (Set.univ : Set Interpretation) ∩ byInterpretation enr lit =
      byInterpretation (s ∩ enr) (s ∩ lit) from by
      ext p
      simp only [byInterpretation, Set.mem_inter_iff, Set.mem_union, Set.mem_prod,
        Set.mem_univ, Set.mem_singleton_iff, and_true]
      tauto,
    prod_byInterpretation μ ν (hs.inter hlit), Measure.prod_prod, measure_univ, mul_one,
    cond_apply hs, cond_apply hs]
  ring

/-- The §5.2 interpretation mixture: enriched with probability 9/10, literal otherwise. -/
noncomputable def interpretationMeasure : Measure Interpretation :=
  (9/10 : ℝ≥0∞) • Measure.dirac .enriched + (1/10 : ℝ≥0∞) • Measure.dirac .literal

instance : IsProbabilityMeasure interpretationMeasure := by
  constructor
  rw [interpretationMeasure]
  simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [ENNReal.div_add_div_same, show (9 + 1 : ℝ≥0∞) = 10 by norm_num]
  exact ENNReal.div_self (by norm_num) (by finiteness)

private lemma interp_enriched : interpretationMeasure {Interpretation.enriched} = 9/10 := by
  simp [interpretationMeasure, Measure.dirac_apply' _ MeasurableSet.of_discrete]

private lemma interp_literal : interpretationMeasure {Interpretation.literal} = 1/10 := by
  simp [interpretationMeasure, Measure.dirac_apply' _ MeasurableSet.of_discrete]

/-! ### Assertability in the example (§5.2) -/

/-- §5.2: the assertability context — bands crossed with the listener's interpretation,
goal lifted along the band. -/
noncomputable def assertabilityContext : DTS.Context (Band × Interpretation) :=
  ⟨moreThan 120 ×ˢ Set.univ, MeasurableSet.of_discrete.prod .univ,
    Measure.count.prod interpretationMeasure⟩

/-- Felicitous assertability of *more than n* whose enrichment is *not more than cap*: under
enrichment both the content and the implicature must hold; under literal interpretation only
the content. -/
def assertable (n cap : ℕ) : Set (Band × Interpretation) :=
  byInterpretation (moreThan n \ moreThan cap) (moreThan n)

/-- The assertability Bayes factor in the §5.2 example, decomposed by
`cond_prod_byInterpretation` into the paper's own "(9/10 × ⋯ + 1/10 × ⋯)" form. -/
private lemma assertable_bayesFactor_eval (n cap : ℕ) :
    bayesFactor assertabilityContext (assertable n cap) =
      (9/10 * (Measure.count : Measure Band)[|moreThan 120] (moreThan n \ moreThan cap) +
        1/10 * (Measure.count : Measure Band)[|moreThan 120] (moreThan n)) /
      (9/10 * (Measure.count : Measure Band)[|(moreThan 120)ᶜ] (moreThan n \ moreThan cap) +
        1/10 * (Measure.count : Measure Band)[|(moreThan 120)ᶜ] (moreThan n)) := by
  have hcompl : (moreThan 120 ×ˢ (Set.univ : Set Interpretation))ᶜ =
      (moreThan 120)ᶜ ×ˢ (Set.univ : Set Interpretation) := by
    ext p; simp [Set.mem_prod]
  rw [bayesFactor_def, assertabilityContext, assertable]
  simp only
  rw [hcompl, cond_prod_byInterpretation _ _ MeasurableSet.of_discrete .of_discrete,
    cond_prod_byInterpretation _ _ MeasurableSet.of_discrete .of_discrete,
    interp_enriched, interp_literal]

private lemma ennreal_910_ne_top : (9/10 : ℝ≥0∞) ≠ ⊤ :=
  ((ENNReal.div_lt_top (by finiteness) (by norm_num) : (9 : ℝ≥0∞) / 10 < ⊤)).ne

private lemma ennreal_110_ne_top : (1/10 : ℝ≥0∞) ≠ ⊤ :=
  ((ENNReal.div_lt_top (by finiteness) (by norm_num) : (1 : ℝ≥0∞) / 10 < ⊤)).ne

/-- §5.2's value for *more than 100* (enriched to *not more than 150*):
P(A(u)∣S) = (9/10)·(3/8) + (1/10)·1 = 35/80 against P(A(u)∣¬S) = 1/6, giving Bayes factor
21/8 (the paper's log (21/8) = 0.419). -/
theorem assertable_bayesFactor_moreThan100 :
    bayesFactor assertabilityContext (assertable 100 150) = 21/8 := by
  have hfin : ∀ (s e : Set Band) (hs : MeasurableSet s),
      (Measure.count : Measure Band)[|s] e ≠ ⊤ :=
    fun s e hs => cond_apply_ne_top _ hs e
  rw [assertable_bayesFactor_eval]
  refine ENNReal.eq_of_toReal
    ((ENNReal.div_lt_top
      (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ennreal_910_ne_top (hfin _ _ .of_discrete),
        ENNReal.mul_ne_top ennreal_110_ne_top (hfin _ _ .of_discrete)⟩)
      (fun h => absurd (add_eq_zero.mp h).2
        (mul_ne_zero (by norm_num) (cond_count_ne (by decide))))).ne)
    (by finiteness) ?_
  rw [ENNReal.toReal_div,
    ENNReal.toReal_add (ENNReal.mul_ne_top ennreal_910_ne_top (hfin _ _ .of_discrete))
      (ENNReal.mul_ne_top ennreal_110_ne_top (hfin _ _ .of_discrete)),
    ENNReal.toReal_add (ENNReal.mul_ne_top ennreal_910_ne_top (hfin _ _ .of_discrete))
      (ENNReal.mul_ne_top ennreal_110_ne_top (hfin _ _ .of_discrete)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    cond_real_apply _ MeasurableSet.of_discrete, cond_real_apply _ MeasurableSet.of_discrete,
    cond_real_apply _ MeasurableSet.of_discrete, cond_real_apply _ MeasurableSet.of_discrete]
  simp only [count_apply_fintype, ENNReal.toReal_natCast, Set.mem_inter_iff, Set.mem_sdiff,
    Set.mem_compl_iff]
  norm_num [ENNReal.toReal_div,
    show (Finset.univ.filter fun x : Band =>
      x ∈ moreThan 120 ∧ x ∈ moreThan 100 ∧ x ∉ moreThan 150).card = 3 from by decide,
    show (Finset.univ.filter fun x : Band =>
      x ∈ moreThan 120 ∧ x ∈ moreThan 100).card = 8 from by decide,
    show (Finset.univ.filter (· ∈ moreThan 120)).card = 8 from by decide,
    show (Finset.univ.filter fun x : Band =>
      x ∉ moreThan 120 ∧ x ∈ moreThan 100 ∧ x ∉ moreThan 150).card = 2 from by decide,
    show (Finset.univ.filter fun x : Band =>
      x ∉ moreThan 120 ∧ x ∈ moreThan 100).card = 2 from by decide,
    show (Finset.univ.filter fun x : Band => x ∉ moreThan 120).card = 12 from by decide]

/-- §5.2's value for *more than 110* (enriched to *not more than 120*): the enriched reading
is incompatible with success, so P(A(u)∣S) = (9/10)·0 + (1/10)·1 = 1/10 against
P(A(u)∣¬S) = 1/12, giving Bayes factor 6/5 (the paper's log (6/5) = 0.079). -/
theorem assertable_bayesFactor_moreThan110 :
    bayesFactor assertabilityContext (assertable 110 120) = 6/5 := by
  have hfin : ∀ (s e : Set Band) (hs : MeasurableSet s),
      (Measure.count : Measure Band)[|s] e ≠ ⊤ :=
    fun s e hs => cond_apply_ne_top _ hs e
  rw [assertable_bayesFactor_eval]
  refine ENNReal.eq_of_toReal
    ((ENNReal.div_lt_top
      (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ennreal_910_ne_top (hfin _ _ .of_discrete),
        ENNReal.mul_ne_top ennreal_110_ne_top (hfin _ _ .of_discrete)⟩)
      (fun h => absurd (add_eq_zero.mp h).2
        (mul_ne_zero (by norm_num) (cond_count_ne (by decide))))).ne)
    (by finiteness) ?_
  rw [ENNReal.toReal_div,
    ENNReal.toReal_add (ENNReal.mul_ne_top ennreal_910_ne_top (hfin _ _ .of_discrete))
      (ENNReal.mul_ne_top ennreal_110_ne_top (hfin _ _ .of_discrete)),
    ENNReal.toReal_add (ENNReal.mul_ne_top ennreal_910_ne_top (hfin _ _ .of_discrete))
      (ENNReal.mul_ne_top ennreal_110_ne_top (hfin _ _ .of_discrete)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    cond_real_apply _ MeasurableSet.of_discrete, cond_real_apply _ MeasurableSet.of_discrete,
    cond_real_apply _ MeasurableSet.of_discrete, cond_real_apply _ MeasurableSet.of_discrete]
  simp only [count_apply_fintype, ENNReal.toReal_natCast, Set.mem_inter_iff, Set.mem_sdiff,
    Set.mem_compl_iff]
  norm_num [ENNReal.toReal_div,
    show (Finset.univ.filter fun x : Band =>
      x ∈ moreThan 120 ∧ x ∈ moreThan 110 ∧ x ∉ moreThan 120).card = 0 from by decide,
    show (Finset.univ.filter fun x : Band =>
      x ∈ moreThan 120 ∧ x ∈ moreThan 110).card = 8 from by decide,
    show (Finset.univ.filter (· ∈ moreThan 120)).card = 8 from by decide,
    show (Finset.univ.filter fun x : Band =>
      x ∉ moreThan 120 ∧ x ∈ moreThan 110 ∧ x ∉ moreThan 120).card = 1 from by decide,
    show (Finset.univ.filter fun x : Band =>
      x ∉ moreThan 120 ∧ x ∈ moreThan 110).card = 1 from by decide,
    show (Finset.univ.filter fun x : Band => x ∉ moreThan 120).card = 12 from by decide]

/-! ### The reversal -/

/-- Argumentative strength (eq. 17; eq. 25 on the assertability space): the log of the Bayes
factor, positive iff the utterance supports the goal. -/
noncomputable def strength (ctx : DTS.Context W) (u : Set W) : ℝ :=
  Real.log (bayesFactor ctx u).toReal

/-- The paper's central §5.2 demonstration: semantically *more than 110* is the stronger
argument for success, but under assertability the ordering reverses — precision that looks
argumentatively optimal is penalized once the listener's enrichment is priced in. -/
theorem strength_reversal :
    strength successContext (moreThan 100) < strength successContext (moreThan 110) ∧
    strength assertabilityContext (assertable 110 120) <
      strength assertabilityContext (assertable 100 150) := by
  unfold strength
  rw [bayesFactor_moreThan100, bayesFactor_moreThan110, assertable_bayesFactor_moreThan110,
    assertable_bayesFactor_moreThan100]
  constructor
  · exact Real.log_lt_log (by norm_num) (by norm_num)
  · exact Real.log_lt_log (by norm_num [ENNReal.toReal_div])
      (by norm_num [ENNReal.toReal_div])

end CumminsFranke2021
