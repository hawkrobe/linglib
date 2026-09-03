/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.InformationTheory.Entropy
import Linglib.Core.Probability.ConditionalProbability
import Linglib.Processing.Memory.LossyContext
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Futrell, Gibson & Levy (2020): lossy-context surprisal

[futrell-gibson-levy-2020] (Cognitive Science 44, e12814) unifies expectation-
based and memory-based theories of processing difficulty: the difficulty of a
word is its expected surprisal given a *lossy memory representation* of the
context (Claims 1–4, eq. (3)). `Processing.Memory.Channel` formalizes the
architecture (`MemoryProcess`, `expectedSurprisal` = eq. (3)) and
`Processing.Memory.LossyContext` its lossless regime (§3.5.1); this file
proves the paper's §5 result — **information locality** — in the
single-dependency configuration, where the paper's first-order eq. (11)
(Supplementary Material C) holds exactly: under erasure noise, expected
surprisal is `h(w) − (1 − e)·pmi(w; y)`, the excess difficulty over plain
surprisal is exactly `e · pmi` (eq. (12)), and the sign of the distance
effect is the sign of the pmi — locality for positively associated words,
anti-locality for negatively associated ones. Structural forgetting (§4) is
parameter-space simulation (Figs. 3–4: forgetting iff the verb-final
relative-clause rate `f` is low, as for English `f ≈ 0.2` but not German
`f = 1`) and stays in prose.

## Main definitions

* `pmi` — pointwise mutual information of the next word with a one-word
  context (§5.1.2), relative to the model's own empty-context prior.
* `erasure` — the erasure-noise memory process (§5.1.3): the context's head
  word survives with probability `1 − e`; an erased word reads as the empty
  context.

## Main results

* `surprisal_eq_sub_pmi` — eq. (10): conditional surprisal is unconditional
  surprisal minus pmi.
* `expectedSurprisal_erasure` — eq. (11), exact single-dependency form:
  `D_lc = h(w) − (1 − e) · pmi`.
* `expectedSurprisal_erasure_sub_surprisal` — eq. (12): the excess difficulty
  over plain surprisal is `e · pmi`.
* `locality`, `antilocality` — §5.1.4: under progressive noise (more distant
  ⇒ larger `e`), difficulty is monotone in the erasure rate, increasing when
  `0 ≤ pmi` and decreasing when `pmi ≤ 0`.
* `erasure_zero`, `erasure_one` — the brackets: no erasure recovers plain
  surprisal (§3.5.1); certain erasure recovers the prior (§3.4.2).
* `mutualInfo_memJoint_le` — §3.2: the data processing inequality as the
  constraint on all admissible noise distributions.
* `bayesDifficulty_memJoint_sub_eq`, `bayesDifficulty_le_memJoint` — the
  average form (§3.4.1, Supp. A, at the §3.3 Bayes-optimal comprehender):
  expected difficulty under lossy memory exceeds expected difficulty under
  veridical context by exactly the predictive information lost to memory,
  `I(W;C) − I(W;M) ≥ 0`.
-/

namespace FutrellGibsonLevy2020

open Processing.LanguageModel Processing.NoisyChannel
open scoped ENNReal NNReal

variable {Voc : Type*} (L : LangModel Voc)

/-- Pointwise mutual information of the next word `w` with the one-word
    context `y` (§5.1.2), relative to the model's empty-context prior. -/
noncomputable def pmi (y w : Voc) : ℝ :=
  Real.log ((L.nextProb [y] w).toReal / (L.nextProb [] w).toReal)

/-- Eq. (10): conditional surprisal decomposes as unconditional surprisal
    minus pointwise mutual information. -/
theorem surprisal_eq_sub_pmi {y w : Voc} (h0 : L.nextProb [] w ≠ 0)
    (hy : L.nextProb [y] w ≠ 0) :
    L.surprisal [y] w = L.surprisal [] w - pmi L y w := by
  unfold LangModel.surprisal pmi
  rw [Real.log_div
    (ENNReal.toReal_ne_zero.mpr ⟨hy, PMF.apply_ne_top _ _⟩)
    (ENNReal.toReal_ne_zero.mpr ⟨h0, PMF.apply_ne_top _ _⟩)]
  ring

/-- The erasure-noise memory process (§5.1.3): the memory retains the
    context's head word with probability `1 − e` and erases it with
    probability `e`; the predictor reads a retained word as a one-word
    context and an erased one as the empty context. -/
noncomputable def erasure [DecidableEq Voc] (e : ℝ≥0) (he : e ≤ 1) :
    MemoryProcess Voc (Option Voc) where
  encode
    | [] => PMF.pure none
    | y :: _ => PMF.ofFinset
        (fun m => if m = none then (e : ℝ≥0∞) else
          if m = some y then 1 - (e : ℝ≥0∞) else 0)
        {none, some y}
        (by rw [Finset.sum_insert (by simp), Finset.sum_singleton, if_pos rfl,
            if_neg (by simp), if_pos rfl,
            add_tsub_cancel_of_le (by exact_mod_cast he : (e : ℝ≥0∞) ≤ 1)])
        (fun m hm => by
          obtain ⟨h1, h2⟩ : m ≠ none ∧ m ≠ some y := by simpa using hm
          rw [if_neg h1, if_neg h2])
  predict m := L.next (m.elim [] fun y => [y])

variable [DecidableEq Voc] {e e' : ℝ≥0} {y w : Voc}

theorem erasure_encode_apply (he : e ≤ 1) (m : Option Voc) :
    (erasure L e he).encode [y] m
      = if m = none then (e : ℝ≥0∞) else
          if m = some y then 1 - (e : ℝ≥0∞) else 0 := by
  simp [erasure, PMF.ofFinset_apply]

/-- The exact single-dependency form of eq. (11): under erasure noise, the
    lossy-context difficulty is the unconditional surprisal minus the
    surviving fraction of the pmi. -/
theorem expectedSurprisal_erasure (he : e ≤ 1) (h0 : L.nextProb [] w ≠ 0)
    (hy : L.nextProb [y] w ≠ 0) :
    (erasure L e he).expectedSurprisal [y] w
      = L.surprisal [] w - (1 - (e : ℝ)) * pmi L y w := by
  classical
  have hsum : (erasure L e he).expectedSurprisal [y] w
      = (e : ℝ) * L.surprisal [] w + (1 - (e : ℝ)) * L.surprisal [y] w := by
    unfold MemoryProcess.expectedSurprisal
    rw [tsum_eq_sum (s := ({none, some y} : Finset (Option Voc)))
      (fun m hm => ?_)]
    · rw [Finset.sum_insert (by simp), Finset.sum_singleton,
        erasure_encode_apply, erasure_encode_apply, if_pos rfl,
        if_neg (by simp), if_pos rfl]
      simp only [ENNReal.coe_toReal]
      rw [ENNReal.toReal_sub_of_le (by exact_mod_cast he) ENNReal.one_ne_top,
        ENNReal.toReal_one, ENNReal.coe_toReal]
      rfl
    · rw [erasure_encode_apply]
      obtain ⟨h1, h2⟩ : m ≠ none ∧ m ≠ some y := by simpa using hm
      rw [if_neg h1, if_neg h2]
      simp
  rw [hsum, surprisal_eq_sub_pmi L h0 hy]
  ring

/-- Eq. (12): the excess difficulty of erasure-noise processing over plain
    surprisal is exactly the erased fraction of the pmi. -/
theorem expectedSurprisal_erasure_sub_surprisal (he : e ≤ 1)
    (h0 : L.nextProb [] w ≠ 0) (hy : L.nextProb [y] w ≠ 0) :
    (erasure L e he).expectedSurprisal [y] w - L.surprisal [y] w
      = (e : ℝ) * pmi L y w := by
  rw [expectedSurprisal_erasure L he h0 hy, surprisal_eq_sub_pmi L h0 hy]
  ring

/-- **Information locality** (§5.1.4): under progressive noise — a more
    distant context word has a larger erasure rate — difficulty increases
    with distance whenever the words are positively associated. -/
theorem locality (h : e ≤ e') (he' : e' ≤ 1) (hpmi : 0 ≤ pmi L y w)
    (h0 : L.nextProb [] w ≠ 0) (hy : L.nextProb [y] w ≠ 0) :
    (erasure L e (h.trans he')).expectedSurprisal [y] w
      ≤ (erasure L e' he').expectedSurprisal [y] w := by
  rw [expectedSurprisal_erasure L (h.trans he') h0 hy,
    expectedSurprisal_erasure L he' h0 hy]
  have : (e : ℝ) ≤ e' := by exact_mod_cast h
  nlinarith

/-- **Anti-locality** (§5.1.4, cf. the Konieczny effects of §2): when the
    words are negatively associated, losing the context word *lowers*
    difficulty, so difficulty decreases with distance. -/
theorem antilocality (h : e ≤ e') (he' : e' ≤ 1) (hpmi : pmi L y w ≤ 0)
    (h0 : L.nextProb [] w ≠ 0) (hy : L.nextProb [y] w ≠ 0) :
    (erasure L e' he').expectedSurprisal [y] w
      ≤ (erasure L e (h.trans he')).expectedSurprisal [y] w := by
  rw [expectedSurprisal_erasure L (h.trans he') h0 hy,
    expectedSurprisal_erasure L he' h0 hy]
  have : (e : ℝ) ≤ e' := by exact_mod_cast h
  nlinarith

/-- No erasure recovers plain surprisal (§3.5.1's special case, at the toy
    configuration; the general statement is
    `Processing.NoisyChannel.expectedSurprisal_eq_surprisal_of_lossless`). -/
theorem erasure_zero (h0 : L.nextProb [] w ≠ 0) (hy : L.nextProb [y] w ≠ 0) :
    (erasure L 0 zero_le_one).expectedSurprisal [y] w = L.surprisal [y] w := by
  rw [expectedSurprisal_erasure L zero_le_one h0 hy, surprisal_eq_sub_pmi L h0 hy]
  simp

/-- Certain erasure recovers the prior (§3.4.2: "regression to prior
    expectations"; the general statement is
    `Processing.NoisyChannel.MemoryProcess.expectedSurprisal_of_constantEncoder`). -/
theorem erasure_one (h0 : L.nextProb [] w ≠ 0) (hy : L.nextProb [y] w ≠ 0) :
    (erasure L 1 le_rfl).expectedSurprisal [y] w = L.surprisal [] w := by
  rw [expectedSurprisal_erasure L le_rfl h0 hy]
  simp

section AverageForm

/-! ### The average form (§3.4.1, Supplementary Material A)

Averaged over contexts, the difficulty of the Bayes-optimal comprehender
(§3.3, eqs. (4)–(9)) under lossy memory exceeds its difficulty under
veridical context by exactly the predictive information lost to memory. -/

open InformationTheory MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {W C M : Type*} [Fintype W] [Fintype C] [Fintype M]
  [MeasurableSpace W] [MeasurableSpace C] [MeasurableSpace M]
  [MeasurableSingletonClass W] [MeasurableSingletonClass C] [MeasurableSingletonClass M]
  (J : Measure (W × C)) [IsProbabilityMeasure J] (mem : Kernel C M) [IsMarkovKernel mem]

/-- The (word, memory) joint induced by passing the context coordinate through
    the memory encoder (Claims 1 and 3). -/
noncomputable def memJoint : Measure (W × M) := (Kernel.id ∥ₖ mem) ∘ₘ J

instance : IsProbabilityMeasure (memJoint J mem) :=
  inferInstanceAs (IsProbabilityMeasure ((Kernel.id ∥ₖ mem) ∘ₘ J))

/-- §3.2's constraint on noise distributions, as the mutual-information form
    of the data processing inequality: a memory representation generated from
    the context (Claim 3) carries no more information about the next word than
    the context itself, whatever the noise distribution. -/
theorem mutualInfo_memJoint_le : Im[memJoint J mem] ≤ Im[J] :=
  measureMutualInfo_parallelComp_id_comp_le J mem

variable {α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]

/-- Expected difficulty of the Bayes-optimal comprehender (§3.3): the expected
    surprisal of predicting the first coordinate from the second. -/
noncomputable def bayesDifficulty (G : Measure (α × β)) : ℝ :=
  ∑ x, G.real {x} * -Real.log ((G[|Prod.snd ⁻¹' {x.2}]).real (Prod.fst ⁻¹' {x.1}))

/-- The Bayes-optimal difficulty is the conditional entropy `H(W | ·)`:
    expected surprisal read as the chain rule. -/
theorem bayesDifficulty_eq (G : Measure (α × β)) [IsProbabilityMeasure G] :
    bayesDifficulty G = H[Prod.fst | Prod.snd ; G] := by
  have hfib (a : α) (b : β) :
      Prod.snd ⁻¹' {b} ∩ Prod.fst ⁻¹' {a} = ({(a, b)} : Set (α × β)) := by
    ext ⟨_, _⟩; simp [and_comm]
  have hcond (a : α) (b : β) : (G[|Prod.snd ⁻¹' {b}]).real (Prod.fst ⁻¹' {a})
      = G.real {(a, b)} / G.real (Prod.snd ⁻¹' {b}) := by
    rw [measureReal_def, cond_real_apply G (measurable_snd (measurableSet_singleton b)), hfib]
    rfl
  have key (a : α) (b : β) :
      G.real {(a, b)} * -Real.log ((G[|Prod.snd ⁻¹' {b}]).real (Prod.fst ⁻¹' {a}))
        = G.real (Prod.snd ⁻¹' {b})
          * Real.negMulLog ((G[|Prod.snd ⁻¹' {b}]).real (Prod.fst ⁻¹' {a})) := by
    rw [hcond]
    obtain hq | hq := eq_or_ne (G.real (Prod.snd ⁻¹' {b})) 0
    · have : G.real {(a, b)} = 0 :=
        measureReal_mono_null (hfib a b ▸ Set.inter_subset_left) hq (measure_ne_top _ _)
      simp [this, hq]
    · simp only [Real.negMulLog]
      field_simp
  rw [condEntropy_eq_sum _ measurable_snd, bayesDifficulty, Fintype.sum_prod_type]
  simp_rw [key]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, entropy_eq_sum measurable_fst]

private theorem condEntropy_fst_snd (G : Measure (α × β)) [IsProbabilityMeasure G] :
    H[Prod.fst | Prod.snd ; G] = H[Prod.fst ; G] - Im[G] := by
  have h := mutualInfo_eq_entropy_sub_condEntropy measurable_fst measurable_snd G
  rw [mutualInfo_eq_measureMutualInfo measurable_fst measurable_snd,
    show (fun p : α × β => (p.1, p.2)) = id from rfl, Measure.map_id] at h
  linarith

/-- **The average form of information locality**: the expected excess
    difficulty of lossy-memory comprehension over veridical-context
    comprehension is exactly the predictive information lost to memory. -/
theorem bayesDifficulty_memJoint_sub_eq :
    bayesDifficulty (memJoint J mem) - bayesDifficulty J = Im[J] - Im[memJoint J mem] := by
  have : Nonempty C := J.nonempty_of_neZero.map Prod.snd
  have hfst : H[Prod.fst ; memJoint J mem] = H[Prod.fst ; J] := by
    show Hm[(memJoint J mem).fst] = Hm[J.fst]
    rw [memJoint, Measure.fst_parallelComp_id_comp]
  rw [bayesDifficulty_eq, bayesDifficulty_eq, condEntropy_fst_snd, condEntropy_fst_snd, hfst]
  ring

/-- Lossy memory cannot make comprehension easier on average: the expected
    Bayes-optimal difficulty under memory is at least that under veridical
    context (the §3.4.1 deduction, with the gap given by
    `bayesDifficulty_memJoint_sub_eq` and its sign by the data processing
    inequality). -/
theorem bayesDifficulty_le_memJoint : bayesDifficulty J ≤ bayesDifficulty (memJoint J mem) := by
  have := bayesDifficulty_memJoint_sub_eq J mem
  have := mutualInfo_memJoint_le J mem
  linarith

end AverageForm

end FutrellGibsonLevy2020
