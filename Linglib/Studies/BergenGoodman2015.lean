import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Linglib.Data.Examples.BergenGoodman2015

/-!
# Bergen & Goodman (2015): The strategic use of noise in pragmatic reasoning

This file formalizes [bergen-goodman-2015]'s noisy-channel rational speech acts model: a
literal listener who decodes the intended utterance before interpreting it (eq. 6), a speaker
whose utility is the channel-expected log posterior of the intended meaning (eq. 7), and a
pragmatic listener who folds the speaker through the channel (eq. 8), over a channel in which
each utterance is misperceived as at most one other, at a rate the speaker lowers by stressing
a word (`slipChannel`). Sentence fragments have no literal meaning, yet both listeners read the
fragment "Bob" as the point mass on Bob having gone, at every positive deletion rate
(`Ellipsis.l0_subject`, `Ellipsis.l1_subject`), because only "Bob went to the movies" deletes
to it. Stress halves the rate at which a subject is misheard as the other, so the exponentiated
utility of a subject sentence is `exp (-binEntropy rate) / 2`, and a speaker who knows that only
Bob went prefers "BOB went" to "Bob went" (`Prosody.s1_bobWent_lt_BOB_went`), the form the
paper's exhaustive row records (`Prosody.model_matches_stress_rows`).

## Main definitions

* `l0`, `s1`, `l1` — eqs. 6–8 over a literal meaning `lit : U → Finset M`, a channel `N`, and
  a set of speaker alternatives.
* `slipChannel` — the channel of a slip rate and a slip target.

## Main results

* `Ellipsis.l0_subject`, `Ellipsis.l1_subject` — a subject fragment is the point mass on its
  source, for every positive deletion rate.
* `Prosody.s1Score_eq_exp_neg_binEntropy` — a subject sentence's exponentiated utility is
  `exp (-binEntropy rate) / 2`.
* `Prosody.s1_bobWent_lt_BOB_went` — the knowledgeable speaker prefers the stressed form.

## Implementation notes

Priors are uniform, the rationality parameter is `1`, and utterances are costless, so eq. 7's
exponentiated utility is the product of literal posteriors raised to channel probabilities.
The speaker's alternatives are a parameter: the three full sentences for ellipsis (the paper's
simplification) and all five prosodic forms for prosody. Prosody is perceived, so the stressed
and unstressed forms are two copies of the subject-confusion channel at rates `ε / 2` and `ε`.
The prosody speaker is the paper's knowledgeable one, for whom the divergence utility is eq. 7.

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

namespace BergenGoodman2015

open Finset Real

section Model

variable {M U : Type*} {rate : U → ℝ} {slip : U → Option U} {u v : U}
  {lit : U → Finset M} {N : U → U → ℝ}

section Channel

variable [DecidableEq U]

/-- The channel of a slip rate and a slip target: an intended utterance is perceived intact
with probability `1 - rate u` and as `slip u` with probability `rate u`. -/
noncomputable def slipChannel (rate : U → ℝ) (slip : U → Option U) (u_i u_p : U) : ℝ :=
  if u_p = u_i then 1 - rate u_i else if slip u_i = some u_p then rate u_i else 0

theorem slipChannel_self (rate : U → ℝ) (slip : U → Option U) (u : U) :
    slipChannel rate slip u u = 1 - rate u := by simp [slipChannel]

theorem slipChannel_of_slip (h : slip u = some v) (hne : v ≠ u) :
    slipChannel rate slip u v = rate u := by simp [slipChannel, hne, h]

theorem slipChannel_of_ne (h₁ : v ≠ u) (h₂ : slip u ≠ some v) :
    slipChannel rate slip u v = 0 := by simp [slipChannel, h₁, h₂]

theorem slipChannel_nonneg (h₀ : ∀ u, 0 ≤ rate u) (h₁ : ∀ u, rate u ≤ 1) (u v : U) :
    0 ≤ slipChannel rate slip u v := by
  unfold slipChannel; split_ifs <;> linarith [h₀ u, h₁ u]

end Channel

variable [Fintype U] [DecidableEq M]

/-- The literal listener's score for `m` on perceiving `u_p`: the channel summed over the
intended utterances true of `m` (eq. 6, uniform priors). -/
noncomputable def l0Score (lit : U → Finset M) (N : U → U → ℝ) (u_p : U) (m : M) : ℝ :=
  ∑ u_i, if m ∈ lit u_i then N u_i u_p else 0

theorem l0Score_nonneg (hN : ∀ u v, 0 ≤ N u v) (u_p : U) (m : M) : 0 ≤ l0Score lit N u_p m :=
  sum_nonneg fun u _ => by split_ifs <;> [exact hN u u_p; exact le_rfl]

variable [Fintype M]

/-- The literal listener (eq. 6). -/
noncomputable def l0 (lit : U → Finset M) (N : U → U → ℝ) (u_p : U) (m : M) : ℝ :=
  l0Score lit N u_p m / ∑ m', l0Score lit N u_p m'

theorem l0_nonneg (hN : ∀ u v, 0 ≤ N u v) (u_p : U) (m : M) : 0 ≤ l0 lit N u_p m :=
  div_nonneg (l0Score_nonneg hN _ _) (sum_nonneg fun _ _ => l0Score_nonneg hN _ _)

/-- The exponentiated speaker utility (eq. 7): the literal posteriors of `m` at the perceived
utterances, weighted geometrically by the channel. -/
noncomputable def s1Score (lit : U → Finset M) (N : U → U → ℝ) (m : M) (u_i : U) : ℝ :=
  ∏ u_p, l0 lit N u_p m ^ N u_i u_p

theorem s1Score_nonneg (hN : ∀ u v, 0 ≤ N u v) (m : M) (u_i : U) : 0 ≤ s1Score lit N m u_i :=
  prod_nonneg fun _ _ => rpow_nonneg (l0_nonneg hN _ _) _

/-- The speaker, choosing among the alternatives `A` (eq. 4). -/
noncomputable def s1 (lit : U → Finset M) (N : U → U → ℝ) (A : Finset U) (m : M) (u_i : U) :
    ℝ :=
  s1Score lit N m u_i / ∑ u ∈ A, s1Score lit N m u

/-- The pragmatic listener's score: the speaker folded through the channel (eq. 8). -/
noncomputable def l1Score (lit : U → Finset M) (N : U → U → ℝ) (A : Finset U) (u_p : U)
    (m : M) : ℝ :=
  ∑ u_i ∈ A, s1 lit N A m u_i * N u_i u_p

/-- The pragmatic listener (eq. 8). -/
noncomputable def l1 (lit : U → Finset M) (N : U → U → ℝ) (A : Finset U) (u_p : U) (m : M) :
    ℝ :=
  l1Score lit N A u_p m / ∑ m', l1Score lit N A u_p m'

variable [DecidableEq U]

/-- Over a slip channel, eq. 7's product has two factors: the intact and the slipped
perception. -/
theorem s1Score_slipChannel_of_slip (h : slip u = some v) (hne : v ≠ u) (m : M) :
    s1Score lit (slipChannel rate slip) m u =
      l0 lit (slipChannel rate slip) u m ^ (1 - rate u) *
        l0 lit (slipChannel rate slip) v m ^ rate u := by
  unfold s1Score
  rw [← prod_subset (subset_univ {u, v}) fun w _ hw => ?_, prod_pair hne.symm,
    slipChannel_self, slipChannel_of_slip h hne]
  simp only [mem_insert, mem_singleton, not_or] at hw
  rw [slipChannel_of_ne hw.1 (by rw [h]; exact fun e => hw.2 (Option.some.inj e).symm),
    rpow_zero]

end Model

/-! ## Ellipsis

Three meanings and the full sentences expressing them; deletion strikes the predicate, leaving a
subject fragment with no literal meaning. -/

namespace Ellipsis

/-- Who went to the movies. -/
inductive Meaning
  | aliceWent
  | bobWent
  | nobodyWent
  deriving DecidableEq, Fintype

/-- The full sentences and the fragments deletion leaves: a subject alone or the predicate. -/
inductive Utterance
  | full (m : Meaning)
  | subject (m : Meaning)
  | predicate
  deriving DecidableEq, Fintype

/-- Full sentences mean what they say; fragments have no literal meaning. -/
def lit : Utterance → Finset Meaning
  | .full m => {m}
  | _ => ∅

/-- Deletion strikes the predicate of a full sentence at rate `δ`. -/
noncomputable def rate (δ : ℝ) : Utterance → ℝ
  | .full _ => δ
  | _ => 0

/-- Deleting the predicate leaves the subject. -/
def slip : Utterance → Option Utterance
  | .full m => some (.subject m)
  | _ => none

/-- The deletion channel at rate `δ`. -/
noncomputable abbrev N (δ : ℝ) : Utterance → Utterance → ℝ := slipChannel (rate δ) slip

/-- The speaker's alternatives: the three full sentences. -/
def fullSentences : Finset Utterance := univ.map ⟨Utterance.full, fun _ _ => Utterance.full.inj⟩

variable {δ : ℝ} (m : Meaning)

/-- Only the full sentence for `m` is true of `m`. -/
theorem l0Score_eq (u_p : Utterance) : l0Score lit (N δ) u_p m = N δ (.full m) u_p := by
  unfold l0Score
  rw [sum_eq_single (.full m)]
  · simp [lit]
  · rintro (m' | m' | _) _ h
    · have : m ≠ m' := fun e => h (by rw [e])
      simp [lit, this]
    · simp [lit]
    · simp [lit]
  · exact fun h => absurd (mem_univ _) h

theorem l0Score_full (δ : ℝ) : l0Score lit (N δ) (.full m) = Pi.single m (1 - δ) := by
  ext m'
  by_cases h : m' = m
  · subst h; simp [l0Score_eq, N, slipChannel, rate]
  · simp [l0Score_eq, N, slipChannel, slip, h, Ne.symm h]

theorem l0Score_subject (δ : ℝ) : l0Score lit (N δ) (.subject m) = Pi.single m δ := by
  ext m'
  by_cases h : m' = m
  · subst h; simp [l0Score_eq, N, slipChannel, slip, rate]
  · simp [l0Score_eq, N, slipChannel, slip, h]

private theorem l0_of_l0Score {c : ℝ} (hc : c ≠ 0) {u_p : Utterance}
    (h : l0Score lit (N δ) u_p = Pi.single m c) : l0 lit (N δ) u_p = Pi.single m 1 := by
  ext m'
  simp only [l0, h, Pi.single_apply]
  split_ifs <;> simp [div_self hc]

/-- A full sentence is interpreted literally, at every deletion rate below `1`. -/
theorem l0_full (hδ : δ ≠ 1) : l0 lit (N δ) (.full m) = Pi.single m 1 :=
  l0_of_l0Score m (sub_ne_zero.mpr hδ.symm) (l0Score_full m δ)

/-- A subject fragment is the point mass on the meaning whose full sentence deletes to it, at
every positive deletion rate. -/
theorem l0_subject (hδ : δ ≠ 0) : l0 lit (N δ) (.subject m) = Pi.single m 1 :=
  l0_of_l0Score m hδ (l0Score_subject m δ)

/-- The speaker's score is `1` at the full sentence for `m` and `0` at the other full
sentences. -/
theorem s1Score_full (hδ₀ : δ ≠ 0) (hδ₁ : δ ≠ 1) (m' : Meaning) :
    s1Score lit (N δ) m (.full m') = if m' = m then 1 else 0 := by
  rw [N, s1Score_slipChannel_of_slip (show slip (.full m') = some (.subject m') from rfl)
    (by simp), l0_full m' hδ₁, l0_subject m' hδ₀]
  by_cases h : m' = m
  · subst h; simp
  · simp [h, Ne.symm h, rate, zero_rpow (sub_ne_zero.mpr hδ₁.symm), zero_rpow hδ₀]

theorem l1Score_subject (hδ₀ : δ ≠ 0) (hδ₁ : δ ≠ 1) :
    l1Score lit (N δ) fullSentences (.subject m) = Pi.single m δ := by
  ext m'
  simp only [l1Score, s1, fullSentences, sum_map, Function.Embedding.coeFn_mk,
    s1Score_full _ hδ₀ hδ₁, sum_ite_eq', mem_univ, ite_true, div_one, ite_mul, one_mul,
    zero_mul, ← l0Score_eq, l0Score_subject]

/-- The pragmatic listener also reads a subject fragment as the point mass on its source. -/
theorem l1_subject (hδ₀ : δ ≠ 0) (hδ₁ : δ ≠ 1) :
    l1 lit (N δ) fullSentences (.subject m) = Pi.single m 1 := by
  ext m'
  simp only [l1, l1Score_subject m hδ₀ hδ₁, Pi.single_apply]
  split_ifs <;> simp [div_self hδ₀]

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
  deriving DecidableEq, Fintype

/-- The subject sentences, stressed (capitals) or not, and the conjunction. -/
inductive Utterance
  | aliceWent
  | ALICE_went
  | bobWent
  | BOB_went
  | aliceAndBobWent
  deriving DecidableEq, Fintype

/-- Lower-bound literal meanings: "Alice went" is true whenever Alice went. -/
def lit : Utterance → Finset Meaning
  | .aliceWent | .ALICE_went => {.onlyAlice, .both}
  | .bobWent | .BOB_went => {.onlyBob, .both}
  | .aliceAndBobWent => {.both}

/-- Subjects are confused at rate `ε`, halved under stress; the conjunction is safe. -/
noncomputable def rate (ε : ℝ) : Utterance → ℝ
  | .aliceWent | .bobWent => ε
  | .ALICE_went | .BOB_went => ε / 2
  | .aliceAndBobWent => 0

/-- A subject is misheard as the other subject, with its prosody. -/
def slip : Utterance → Option Utterance
  | .aliceWent => some .bobWent
  | .bobWent => some .aliceWent
  | .ALICE_went => some .BOB_went
  | .BOB_went => some .ALICE_went
  | .aliceAndBobWent => none

/-- The subject-confusion channel at rate `ε`. -/
noncomputable abbrev N (ε : ℝ) : Utterance → Utterance → ℝ := slipChannel (rate ε) slip

variable {ε : ℝ}

private theorem sum_univ_utt (f : Utterance → ℝ) :
    ∑ u, f u = f .aliceWent + f .ALICE_went + f .bobWent + f .BOB_went + f .aliceAndBobWent := by
  rw [show (univ : Finset Utterance)
      = {.aliceWent, .ALICE_went, .bobWent, .BOB_went, .aliceAndBobWent} from rfl,
    sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_singleton]
  ring

private theorem sum_univ_mean (f : Meaning → ℝ) :
    ∑ m, f m = f .onlyAlice + f .onlyBob + f .both := by
  rw [show (univ : Finset Meaning) = {.onlyAlice, .onlyBob, .both} from rfl,
    sum_insert (by decide), sum_insert (by decide), sum_singleton]
  ring

/-- The literal posteriors of `onlyBob`: the intact subject sentence at one minus its rate,
the confused one at its rate, each over the two meanings a subject sentence is true of. -/
private theorem l0_onlyBob :
    l0 lit (N ε) .bobWent .onlyBob = (1 - ε) / 2 ∧
    l0 lit (N ε) .aliceWent .onlyBob = ε / 2 ∧
    l0 lit (N ε) .BOB_went .onlyBob = (1 - ε / 2) / 2 ∧
    l0 lit (N ε) .ALICE_went .onlyBob = ε / 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp only [l0, l0Score, sum_univ_utt, sum_univ_mean, lit, N, slipChannel, rate, slip]
      norm_num <;> ring

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

/-- The knowledgeable speaker's scores for the two forms of "Bob went" are the entropy forms of
their rates. -/
theorem s1Score_eq_exp_neg_binEntropy (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    s1Score lit (N ε) .onlyBob .bobWent = exp (-binEntropy ε) / 2 ∧
    s1Score lit (N ε) .onlyBob .BOB_went = exp (-binEntropy (ε / 2)) / 2 := by
  obtain ⟨hb, ha, hB, hA⟩ := l0_onlyBob (ε := ε)
  refine ⟨?_, ?_⟩
  · rw [N, s1Score_slipChannel_of_slip (show slip .bobWent = some .aliceWent from rfl)
      (by decide), hb, ha]
    exact rpow_mul_rpow_eq_exp_neg_binEntropy hε₀ hε₁
  · rw [N, s1Score_slipChannel_of_slip (show slip .BOB_went = some .ALICE_went from rfl)
      (by decide), hB, hA]
    have := rpow_mul_rpow_eq_exp_neg_binEntropy (half_pos hε₀) (by linarith)
    rwa [show ε / 2 / 2 = ε / 4 by ring] at this

/-- A speaker who knows that only Bob went scores "BOB went" above "Bob went": halving the
rate lowers its binary entropy. -/
theorem s1Score_bobWent_lt_BOB_went (hε₀ : 0 < ε) (hε : ε ≤ 1 / 2) :
    s1Score lit (N ε) .onlyBob .bobWent < s1Score lit (N ε) .onlyBob .BOB_went := by
  obtain ⟨hb, hB⟩ := s1Score_eq_exp_neg_binEntropy hε₀ (by linarith)
  rw [hb, hB]
  refine div_lt_div_of_pos_right (exp_lt_exp.2 (neg_lt_neg ?_)) two_pos
  exact binEntropy_strictMonoOn ⟨by linarith, by norm_num; linarith⟩
    ⟨hε₀.le, by norm_num; linarith⟩ (by linarith)

/-- The knowledgeable speaker prefers the stressed form (Fig. 2, right, at depth one). -/
theorem s1_bobWent_lt_BOB_went (hε₀ : 0 < ε) (hε : ε ≤ 1 / 2) :
    s1 lit (N ε) univ .onlyBob .bobWent < s1 lit (N ε) univ .onlyBob .BOB_went := by
  refine div_lt_div_of_pos_right (s1Score_bobWent_lt_BOB_went hε₀ hε) ?_
  rw [sum_univ_utt]
  have hB : 0 < s1Score lit (N ε) .onlyBob .BOB_went := by
    rw [(s1Score_eq_exp_neg_binEntropy hε₀ (by linarith)).2]; positivity
  have hN : ∀ u v, 0 ≤ N ε u v :=
    slipChannel_nonneg (fun u => by cases u <;> simp [rate] <;> linarith)
      (fun u => by cases u <;> simp [rate] <;> linarith)
  have h := fun u => s1Score_nonneg (lit := lit) hN Meaning.onlyBob u
  linarith [h .aliceWent, h .ALICE_went, h .bobWent, h .aliceAndBobWent]

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
      s1 lit (N (1 / 100)) univ .onlyBob u_u < s1 lit (N (1 / 100)) univ .onlyBob u_s :=
  ⟨_, _, rfl, rfl, s1_bobWent_lt_BOB_went (by norm_num) (by norm_num)⟩

end Prosody

end BergenGoodman2015
