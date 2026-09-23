module

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Linglib.Pragmatics.RSA.NoisyChannel
public import Linglib.Data.Examples.BergenGoodman2015
import all Mathlib.Analysis.SpecialFunctions.BinaryEntropy  -- for unfolding `binEntropy`

/-!
# Bergen & Goodman (2015): The strategic use of noise in pragmatic reasoning

This file formalizes [bergen-goodman-2015]'s two applications of rational speech acts over a
noisy channel (`Linglib.Pragmatics.RSA.NoisyChannel`): the literal listener decodes the intended
utterance before interpreting it (eq. 6), the speaker's utility is the channel-expected log
posterior of the intended meaning (eq. 7), and the pragmatic listener inverts the speaker
composed with the channel (eq. 8). The channel misperceives each utterance as at most one other,
at a rate the speaker lowers by stressing a word (`slipChannel`). Sentence fragments have no
literal meaning, yet both listeners read the fragment "Bob" as the point mass on Bob having gone,
at every positive deletion rate (`Ellipsis.L0_subject`, `Ellipsis.L1_subject`), because only "Bob
went to the movies" deletes to it. Stress halves the rate at which a subject is misheard as the
other, so the exponentiated utility of a subject sentence is `exp (-binEntropy rate) / 2`, and a
speaker who knows that only Bob went prefers "BOB went" to "Bob went"
(`Prosody.S1_bobWent_lt_BOB_went`), the form the paper's exhaustive row records
(`Prosody.model_matches_stress_rows`).

## Main definitions

* `slipChannel` — the channel of a slip rate and a slip target.
* `Ellipsis.L0`, `Ellipsis.S1`, `Ellipsis.L1`, `Prosody.L0`, `Prosody.S1` — eqs. 6–8 for the
  two models.

## Main results

* `Ellipsis.L0_subject`, `Ellipsis.L1_subject` — a subject fragment is the point mass on its
  source, for every positive deletion rate; `Ellipsis.S1_apply` — the speaker utters the full
  sentence.
* `Prosody.channelMix_eq_exp_neg_binEntropy` — a subject sentence's exponentiated utility is
  `exp (-binEntropy rate) / 2`.
* `Prosody.S1_bobWent_lt_BOB_went` — the knowledgeable speaker prefers the stressed form.

## Implementation notes

Priors are unit weights, the rationality parameter is `1`, and the speaker's alternatives are
the utterances of positive prior, entering as the cost factor: the three full sentences for
ellipsis (the paper's simplification) and all five prosodic forms for prosody. Prosody is
perceived, so the stressed and unstressed forms are two copies of the subject-confusion channel
at rates `ε / 2` and `ε`. The prosody speaker is the paper's knowledgeable one, for whom the
divergence utility is eq. 7.

## TODO

* Fragment production (Fig. 1, right) needs utterance costs; the ignorant speaker's lower
  stress rate (Fig. 2, right) needs the divergence utility over observations.
* The listener's exhaustive reading of stress (Fig. 2, left) is the paper's depth-two result
  over knowledge states; at depth one it reduces to the monotonicity in the rate of the
  confusion odds `(r ^ (1 - r) * (1 - r) ^ r) / ((1 - r) ^ (1 - r) * r ^ r)`, not yet proved.

## References

* [bergen-goodman-2015]
* [frank-goodman-2012]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory RSA Finset Real
open scoped ENNReal

namespace BergenGoodman2015

/-! ### The slip channel -/

section Channel

variable {U : Type*} [MeasurableSpace U] [Fintype U] [MeasurableSingletonClass U]

/-- The channel of a slip rate and a slip target: an intended utterance is perceived intact
with probability `1 - rate u` and as `slip u` with probability `rate u`. -/
noncomputable def slipChannel (rate : U → ℝ) (slip : U → U) : Kernel U U :=
  Kernel.ofFunOfCountable fun u =>
    ENNReal.ofReal (1 - rate u) • Measure.dirac u + ENNReal.ofReal (rate u) • Measure.dirac (slip u)

instance (rate : U → ℝ) (slip : U → U) : IsFiniteKernel (slipChannel rate slip) :=
  ⟨⟨∑ u, (ENNReal.ofReal (1 - rate u) + ENNReal.ofReal (rate u)),
    ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,
      ENNReal.ofReal_lt_top⟩,
    fun u => by
      rw [slipChannel, Kernel.ofFunOfCountable_apply, Measure.add_apply, Measure.smul_apply,
        Measure.smul_apply, smul_eq_mul, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _),
        Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one, mul_one]
      exact single_le_sum (f := fun u => ENNReal.ofReal (1 - rate u) + ENNReal.ofReal (rate u))
        (fun _ _ => zero_le) (mem_univ u)⟩⟩

theorem slipChannel_apply_singleton [DecidableEq U] (rate : U → ℝ) (slip : U → U) (u v : U) :
    slipChannel rate slip u {v} = ENNReal.ofReal (1 - rate u) * (if u = v then 1 else 0) +
      ENNReal.ofReal (rate u) * (if slip u = v then 1 else 0) := by
  rw [slipChannel, Kernel.ofFunOfCountable_apply, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply, smul_eq_mul, smul_eq_mul, Measure.dirac_apply' _ (.singleton v),
    Measure.dirac_apply' _ (.singleton v)]
  simp only [Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply]

end Channel

/-! ## Ellipsis

Three meanings and the full sentences expressing them; deletion strikes the predicate, leaving a
subject fragment with no literal meaning. -/

namespace Ellipsis

/-- Who went to the movies. -/
inductive Meaning
  | aliceWent
  | bobWent
  | nobodyWent
  deriving DecidableEq, Fintype, Inhabited

instance : MeasurableSpace Meaning := ⊤

/-- The full sentences and the fragments deletion leaves: a subject alone or the predicate. -/
inductive Utterance
  | full (m : Meaning)
  | subject (m : Meaning)
  | predicate
  deriving DecidableEq, Fintype

instance : MeasurableSpace Utterance := ⊤

/-- Full sentences mean what they say; fragments have no literal meaning. -/
def lit : Utterance → Set Meaning
  | .full m => {m}
  | _ => ∅

/-- Deletion strikes the predicate of a full sentence at rate `δ`. -/
noncomputable def rate (δ : ℝ) : Utterance → ℝ
  | .full _ => δ
  | _ => 0

/-- Deleting the predicate leaves the subject. -/
def slip : Utterance → Utterance
  | .full m => .subject m
  | u => u

/-- The deletion channel at rate `δ`. -/
noncomputable abbrev N (δ : ℝ) : Kernel Utterance Utterance := slipChannel (rate δ) slip

/-- The speaker produces full sentences. -/
noncomputable abbrev uttPrior : Measure Utterance := priorOfWeights fun
  | .full _ => 1
  | _ => 0

/-- The uniform meaning prior. -/
noncomputable abbrev μ : Measure Meaning := priorOfWeights 1

/-- The graded literal meaning. -/
noncomputable abbrev lit' : Utterance → Meaning → ℝ≥0∞ := fun u => (lit u).indicator 1

/-- The literal listener (eq. 6). -/
noncomputable abbrev L0 (δ : ℝ) : Kernel Utterance Meaning :=
  literalListener μ (noisyMeaning (N δ) uttPrior lit')

/-- The speaker (eq. 7), over the full sentences. -/
noncomputable abbrev S1 (δ : ℝ) : Kernel Meaning Utterance :=
  noisySpeaker (N δ) 1 (uttPrior {·}) (L0 δ)

/-- The pragmatic listener (eq. 8). -/
noncomputable abbrev L1 (δ : ℝ) : Kernel Utterance Meaning :=
  noisyPragmaticListener (N δ) 1 (uttPrior {·}) (L0 δ) μ

variable {δ : ℝ} (m : Meaning)

/-- Only the full sentence for `m` deletes to its subject fragment. -/
theorem noisyMeaning_subject (w : Meaning) :
    noisyMeaning (N δ) uttPrior lit' (.subject m) w =
      ENNReal.ofReal δ * ({m} : Set Meaning).indicator 1 w := by
  rw [noisyMeaning_apply, sum_eq_single (.full m)]
  · simp [slipChannel_apply_singleton, rate, slip, lit', lit]
  · rintro (m' | m' | _) _ h <;> simp_all [slipChannel_apply_singleton, rate, slip, lit', lit]
  · exact fun h => absurd (mem_univ _) h

/-- Only the full sentence for `m` survives as itself. -/
theorem noisyMeaning_full (w : Meaning) :
    noisyMeaning (N δ) uttPrior lit' (.full m) w =
      ENNReal.ofReal (1 - δ) * ({m} : Set Meaning).indicator 1 w := by
  rw [noisyMeaning_apply, sum_eq_single (.full m)]
  · simp [slipChannel_apply_singleton, rate, slip, lit', lit]
  · rintro (m' | m' | _) _ h <;> simp_all [slipChannel_apply_singleton, rate, slip, lit', lit]
  · exact fun h => absurd (mem_univ _) h

private theorem L0_of_noisyMeaning {c : ℝ} (hc : 0 < c) {u : Utterance}
    (h : ∀ w, noisyMeaning (N δ) uttPrior lit' u w =
      ENNReal.ofReal c * ({m} : Set Meaning).indicator 1 w) :
    L0 δ u = Measure.dirac m := by
  rw [L0, literalListener_apply_eq_of_eq_mul μ (m := fun _ => ({m} : Set Meaning).indicator 1)
    (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top h]
  refine Measure.ext_of_singleton fun w => ?_
  simp only [Measure.dirac_apply' _ (.singleton w), Set.indicator_apply, Set.mem_singleton_iff,
    Pi.one_apply]
  by_cases hw : m = w
  · subst hw
    rw [literalListener_indicator_apply_singleton_of_eq_singleton μ (fun _ => {m}) rfl (by simp)]
    simp
  · rw [literalListener_indicator_apply_singleton_of_notMem μ (fun _ => {m})
      (by simpa using Ne.symm hw)]
    simp [hw]

/-- A subject fragment is the point mass on the meaning whose full sentence deletes to it, at
every positive deletion rate. -/
theorem L0_subject (hδ : 0 < δ) : L0 δ (.subject m) = Measure.dirac m :=
  L0_of_noisyMeaning m hδ (noisyMeaning_subject m)

/-- A full sentence is interpreted literally, at every deletion rate below `1`. -/
theorem L0_full (hδ : δ < 1) : L0 δ (.full m) = Measure.dirac m :=
  L0_of_noisyMeaning m (by linarith) (noisyMeaning_full m)

variable (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
include hδ₀ hδ₁

/-- The full sentence for `m'` is heard as itself or as its subject, so its channel-mixed
listener at `m` is `1` when `m' = m` and `0` otherwise. -/
theorem channelMix_full (m' : Meaning) :
    channelMix (N δ) (L0 δ) (.full m') m = if m' = m then 1 else 0 := by
  rw [channelMix_eq_prod _ _ (s := {.full m', .subject m'}) fun u hu => by
      rcases u with m'' | m'' | _ <;> simp_all [slipChannel_apply_singleton, rate, slip] <;>
        exact fun h => absurd h.symm hu,
    prod_pair (by simp), L0_full m' hδ₁, L0_subject m' hδ₀]
  have h1 : (ENNReal.ofReal (1 - δ)).toReal = 1 - δ := ENNReal.toReal_ofReal (by linarith)
  have h2 : (ENNReal.ofReal δ).toReal = δ := ENNReal.toReal_ofReal hδ₀.le
  simp only [slipChannel_apply_singleton, rate, slip, ite_true, mul_one,
    Measure.dirac_apply' _ (.singleton m), Set.indicator_apply, Set.mem_singleton_iff,
    Pi.one_apply]
  by_cases h : m' = m
  · simp [h]
  · simp [h, h1, h2, hδ₀, sub_pos.mpr hδ₁]

/-- The speaker utters the full sentence for its meaning. -/
theorem S1_apply : S1 δ m = Measure.dirac (.full m) := by
  refine Kernel.ofWeights_apply_eq_dirac one_ne_zero ENNReal.one_ne_top fun u => ?_
  rcases u with m' | m' | _
  · rw [channelMix_full m hδ₀ hδ₁, ENNReal.rpow_one]
    simp
  · simp
  · simp

/-- The channelled speaker reaches the subject fragment for `m` only from `m`, with the deletion
rate. -/
theorem comp_apply_subject (w : Meaning) :
    (N δ ∘ₖ S1 δ) w {.subject m} = if w = m then ENNReal.ofReal δ else 0 := by
  rw [Kernel.comp_apply_singleton, sum_eq_single (.full w)]
  · rw [S1_apply w hδ₀ hδ₁, Measure.dirac_apply_of_mem (Set.mem_singleton _), one_mul]
    by_cases h : w = m
    · subst h; simp [slipChannel_apply_singleton, rate, slip]
    · simp [slipChannel_apply_singleton, rate, slip, h]
  · intro u _ hu
    rw [S1_apply w hδ₀ hδ₁, Measure.dirac_apply' _ (.singleton u),
      Set.indicator_of_notMem (by simpa using Ne.symm hu), zero_mul]
  · exact fun h => absurd (mem_univ _) h

/-- The pragmatic listener also reads a subject fragment as the point mass on its source. -/
theorem L1_subject : L1 δ (.subject m) = Measure.dirac m := by
  have hmarg : ((N δ ∘ₖ S1 δ) ∘ₘ μ) {.subject m} = ENNReal.ofReal δ := by
    rw [Measure.comp_apply_singleton]
    simp [comp_apply_subject m hδ₀ hδ₁]
  have hx : ((N δ ∘ₖ S1 δ) ∘ₘ μ) {.subject m} ≠ 0 := by
    rw [hmarg]; exact (ENNReal.ofReal_pos.mpr hδ₀).ne'
  refine Measure.ext_of_singleton fun w => ?_
  change ((N δ ∘ₖ S1 δ)†μ) (.subject m) {w} = _
  rw [posterior_apply_singleton _ _ hx, hmarg, comp_apply_subject m hδ₀ hδ₁]
  simp only [Measure.dirac_apply' _ (.singleton w), Set.indicator_apply, Set.mem_singleton_iff,
    Pi.one_apply]
  by_cases h : w = m
  · subst h
    simp [ENNReal.div_self (ENNReal.ofReal_pos.mpr hδ₀).ne' ENNReal.ofReal_ne_top]
  · simp [h, Ne.symm h]

end Ellipsis

/-! ## Prosody

Stress halves the rate at which a subject is misheard as the other (the paper's `ε / n` at
`n = 2`); the conjunction is never misheard. A speaker who knows that only Bob went must keep
the listener from hearing "Alice went", so stress is worth more to them. -/

namespace Prosody

/-- Who went: one of them alone, or both. -/
inductive Meaning
  | onlyAlice
  | onlyBob
  | both
  deriving DecidableEq, Fintype, Inhabited

instance : MeasurableSpace Meaning := ⊤

/-- The subject sentences, stressed (capitals) or not, and the conjunction. -/
inductive Utterance
  | aliceWent
  | ALICE_went
  | bobWent
  | BOB_went
  | aliceAndBobWent
  deriving DecidableEq, Fintype

instance : MeasurableSpace Utterance := ⊤

/-- Lower-bound literal meanings: "Alice went" is true whenever Alice went. -/
def lit : Utterance → Set Meaning
  | .aliceWent | .ALICE_went => {.onlyAlice, .both}
  | .bobWent | .BOB_went => {.onlyBob, .both}
  | .aliceAndBobWent => {.both}

/-- Subjects are confused at rate `ε`, halved under stress; the conjunction is safe. -/
noncomputable def rate (ε : ℝ) : Utterance → ℝ
  | .aliceWent | .bobWent => ε
  | .ALICE_went | .BOB_went => ε / 2
  | .aliceAndBobWent => 0

/-- A subject is misheard as the other subject, with its prosody. -/
def slip : Utterance → Utterance
  | .aliceWent => .bobWent
  | .bobWent => .aliceWent
  | .ALICE_went => .BOB_went
  | .BOB_went => .ALICE_went
  | .aliceAndBobWent => .aliceAndBobWent

/-- The subject-confusion channel at rate `ε`. -/
noncomputable abbrev N (ε : ℝ) : Kernel Utterance Utterance := slipChannel (rate ε) slip

/-- The uniform utterance prior. -/
noncomputable abbrev uttPrior : Measure Utterance := priorOfWeights 1

/-- The uniform meaning prior. -/
noncomputable abbrev μ : Measure Meaning := priorOfWeights 1

/-- The graded literal meaning. -/
noncomputable abbrev lit' : Utterance → Meaning → ℝ≥0∞ := fun u => (lit u).indicator 1

/-- The literal listener (eq. 6). -/
noncomputable abbrev L0 (ε : ℝ) : Kernel Utterance Meaning :=
  literalListener μ (noisyMeaning (N ε) uttPrior lit')

/-- The knowledgeable speaker (eq. 7), over all five forms. -/
noncomputable abbrev S1 (ε : ℝ) : Kernel Meaning Utterance :=
  noisySpeaker (N ε) 1 (fun _ => 1) (L0 ε)

variable {ε : ℝ}

private theorem sum_univ_utt {β : Type*} [AddCommMonoid β] (f : Utterance → β) :
    ∑ u, f u = f .aliceWent + f .ALICE_went + f .bobWent + f .BOB_went + f .aliceAndBobWent := by
  rw [show (univ : Finset Utterance)
      = {.aliceWent, .ALICE_went, .bobWent, .BOB_went, .aliceAndBobWent} from rfl,
    sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_singleton]
  simp only [add_assoc]

private theorem sum_univ_mean {β : Type*} [AddCommMonoid β] (f : Meaning → β) :
    ∑ m, f m = f .onlyAlice + f .onlyBob + f .both := by
  rw [show (univ : Finset Meaning) = {.onlyAlice, .onlyBob, .both} from rfl,
    sum_insert (by decide), sum_insert (by decide), sum_singleton]
  simp only [add_assoc]

/-- The literal posteriors of `onlyBob`: the intact subject sentence at one minus its rate,
the confused one at its rate, each over the two meanings a subject sentence is true of. -/
private theorem L0_onlyBob (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    L0 ε .bobWent {.onlyBob} = ENNReal.ofReal ((1 - ε) / 2) ∧
    L0 ε .aliceWent {.onlyBob} = ENNReal.ofReal (ε / 2) ∧
    L0 ε .BOB_went {.onlyBob} = ENNReal.ofReal ((1 - ε / 2) / 2) ∧
    L0 ε .ALICE_went {.onlyBob} = ENNReal.ofReal (ε / 2 / 2) := by
  have h1 : ENNReal.ofReal (1 - ε) + ENNReal.ofReal ε = 1 := by
    rw [← ENNReal.ofReal_add (by linarith) hε₀, sub_add_cancel, ENNReal.ofReal_one]
  have h2 : ENNReal.ofReal (1 - ε / 2) + ENNReal.ofReal (ε / 2) = 1 := by
    rw [← ENNReal.ofReal_add (by linarith) (by linarith), sub_add_cancel, ENNReal.ofReal_one]
  have h1' := (add_comm _ _).trans h1
  have h2' := (add_comm _ _).trans h2
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [L0, literalListener_apply_singleton]
      simp only [noisyMeaning_apply, sum_univ_utt, sum_univ_mean, slipChannel_apply_singleton,
        rate, slip, lit', lit, priorOfWeights_singleton, Pi.one_apply, Nat.cast_one,
        Set.indicator_apply, Set.mem_insert_iff, Set.mem_singleton_iff]
      simp only [reduceCtorEq, ite_true, ite_false, or_false, false_or, mul_one, mul_zero,
        add_zero, zero_add, h1, h1', h2, h2', one_add_one_eq_two]
      simp only [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat]

/-- Eq. 7 for a subject sentence at slip rate `r`: the exponentiated utility of the meaning it
is true of alone is `exp (-binEntropy r) / 2`. -/
theorem rpow_mul_rpow_eq_exp_neg_binEntropy {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    ((1 - r) / 2) ^ (1 - r) * (r / 2) ^ r = exp (-binEntropy r) / 2 := by
  rw [rpow_def_of_pos (div_pos (by linarith) two_pos), rpow_def_of_pos (div_pos hr₀ two_pos),
    ← exp_add, log_div (sub_ne_zero.mpr hr₁.ne') two_ne_zero, log_div hr₀.ne' two_ne_zero,
    show exp (-binEntropy r) / 2 = exp (-binEntropy r - log 2) by
      rw [exp_sub, exp_log two_pos],
    binEntropy, log_inv, log_inv]
  congr 1; ring

/-- The knowledgeable speaker's channel-mixed listener for the two forms of "Bob went" is the
entropy form of their rates. -/
theorem channelMix_eq_exp_neg_binEntropy (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    channelMix (N ε) (L0 ε) .bobWent .onlyBob = ENNReal.ofReal (exp (-binEntropy ε) / 2) ∧
    channelMix (N ε) (L0 ε) .BOB_went .onlyBob =
      ENNReal.ofReal (exp (-binEntropy (ε / 2)) / 2) := by
  obtain ⟨hb, ha, hB, hA⟩ := L0_onlyBob hε₀.le hε₁.le
  refine ⟨?_, ?_⟩
  · rw [channelMix_eq_prod _ _ (s := {.bobWent, .aliceWent}) fun u hu => by
        rcases u <;> simp_all [slipChannel_apply_singleton, rate, slip],
      prod_pair (by decide), hb, ha]
    simp only [slipChannel_apply_singleton, rate, slip, ite_true, ite_false, mul_one, mul_zero,
      add_zero, zero_add, reduceCtorEq]
    rw [ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal hε₀.le,
      ENNReal.ofReal_rpow_of_nonneg (by linarith) (by linarith),
      ENNReal.ofReal_rpow_of_nonneg (by linarith) hε₀.le,
      ← ENNReal.ofReal_mul (rpow_nonneg (by linarith) _),
      rpow_mul_rpow_eq_exp_neg_binEntropy hε₀ hε₁]
  · rw [channelMix_eq_prod _ _ (s := {.BOB_went, .ALICE_went}) fun u hu => by
        rcases u <;> simp_all [slipChannel_apply_singleton, rate, slip],
      prod_pair (by decide), hB, hA]
    simp only [slipChannel_apply_singleton, rate, slip, ite_true, ite_false, mul_one, mul_zero,
      add_zero, zero_add, reduceCtorEq]
    rw [ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith),
      ENNReal.ofReal_rpow_of_nonneg (by linarith) (by linarith),
      ENNReal.ofReal_rpow_of_nonneg (by linarith) (by linarith),
      ← ENNReal.ofReal_mul (rpow_nonneg (by linarith) _),
      rpow_mul_rpow_eq_exp_neg_binEntropy (half_pos hε₀) (by linarith)]

/-- A speaker who knows that only Bob went prefers "BOB went" to "Bob went": halving the rate
lowers its binary entropy (Fig. 2, right, at depth one). -/
theorem S1_bobWent_lt_BOB_went (hε₀ : 0 < ε) (hε : ε ≤ 1 / 2) :
    (S1 ε .onlyBob).real {.bobWent} < (S1 ε .onlyBob).real {.BOB_went} := by
  obtain ⟨hb, hB⟩ := channelMix_eq_exp_neg_binEntropy hε₀ (by linarith)
  rw [S1, noisySpeaker_real_singleton_lt_iff zero_le_one (fun _ => ENNReal.one_ne_top)
      (fun u => literalListener_apply_le_one _ _ _ _)
      ⟨.BOB_went, by rw [ENNReal.rpow_one, mul_one, hB]; exact (ENNReal.ofReal_pos.mpr
        (by positivity)).ne'⟩,
    ENNReal.rpow_one, ENNReal.rpow_one, mul_one, mul_one, hb, hB,
    ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  refine div_lt_div_of_pos_right (exp_lt_exp.2 (neg_lt_neg ?_)) two_pos
  exact binEntropy_strictMonoOn ⟨by linarith, by norm_num; linarith⟩
    ⟨hε₀.le, by norm_num; linarith⟩ (by linarith)

/-- Utterance adapter: a row's `stress` feature as an utterance. -/
def uttOf (row : Data.Examples.LinguisticExample) : Option Utterance :=
  match row.feature? "stress" with
  | some "subject" => some .BOB_went
  | some "none"    => some .bobWent
  | _              => none

/-- A speaker with the exhaustive meaning prefers the stressed row's form to the unstressed
row's, at the paper's rate. -/
theorem model_matches_stress_rows :
    ∃ u_s u_u, uttOf Examples.stressed_subject = some u_s ∧
      uttOf Examples.unstressed_subject = some u_u ∧
      (S1 (1 / 100) .onlyBob).real {u_u} < (S1 (1 / 100) .onlyBob).real {u_s} :=
  ⟨_, _, rfl, rfl, S1_bobWent_lt_BOB_went (by norm_num) (by norm_num)⟩

end Prosody

end BergenGoodman2015
