/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Probability.DataProcessing
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
* `mutualInformation_memory_le` — §3.2: the data processing inequality as the
  constraint on all admissible noise distributions.
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

/-- §3.2's constraint on noise distributions, as the mutual-information form
    of the data processing inequality: a memory representation generated from
    the context (Claim 3) carries no more information about the next word than
    the context itself, whatever the noise distribution. -/
theorem mutualInformation_memory_le {W C M : Type*}
    [Fintype W] [Fintype C] [Fintype M]
    [MeasurableSpace W] [MeasurableSpace C] [MeasurableSpace M]
    [MeasurableSingletonClass W] [MeasurableSingletonClass C]
    [MeasurableSingletonClass M] [DecidableEq W] [DecidableEq C]
    (joint : PMF (W × C)) (mem : C → PMF M) :
    PMF.mutualInformation (joint.bind fun x => (mem x.2).map (Prod.mk x.1))
      ≤ PMF.mutualInformation joint :=
  PMF.mutualInformation_bind_snd_le joint mem

end FutrellGibsonLevy2020
