import Linglib.Core.Probability.Scores
import Linglib.Pragmatics.RSA.Atoms
import Linglib.Pragmatics.RSA.LatentOperators
import Linglib.Pragmatics.RSA.Operators
import Linglib.Pragmatics.RSA.Channel
import Linglib.Data.Examples.BergenGoodman2015

/-!
# [bergen-goodman-2015]: the strategic use of noise

*Topics in Cognitive Science* 7(2), 336–350. RSA over a noisy channel
P_N(u_p | u_i): the listener reasons about which intended utterance the
perceived one came from (eq. 6), the speaker about which utterances
survive noise (eqs. 7–8).

## Main results

* `l0_fragment_correct` / `l1_fragment_correct`: "Bob" — no literal
  meaning — is interpreted as "Bob went to the movies" (§3 ellipsis):
  noise-deletion reasoning recovers the unique full-sentence source.
* `l0_fragment_robust`: the fragment inference holds for every noise rate
  δ ∈ (0, 1), not just the sampled δ = 1/100.
* `stress_increases_exhaustivity`: at every noise rate ε < 2/3, "BOB
  went" (stressed) is more likely than "Bob went" to mean only-Bob (§4)
  — stress reduces noise on the word it protects.
* `stress_increases_discrimination`: the channel-level mechanism, for
  every ε ∈ (0, 1).

## Implementation notes

Ellipsis is exact ℚ≥0: each meaning has a unique truthful full sentence,
so the eq. 7 softmax is degenerate and eq. 8 reduces to the channel row
(`s1nQ`); listeners are `PMF.ofScores`. Prosody is transcendental — the
eq. 7 utilities are channel-weighted geometric means of literal
posteriors (`xAtom`, `yAtom`) — and fully parametric in ε: the mechanism
theorem `xAtom_lt_yAtom` places the atoms strictly on either side of the
unstressed posterior by the two-factor GM bounds in
`Pragmatics/RSA/Atoms.lean`, and the headline reduces to that ordering
plus algebra. No magnitude certificates.
-/

open BigOperators RSA Real
open scoped NNRat ENNReal

namespace BergenGoodman2015

/-! ### Ellipsis: Sentence Fragments -/

/-! ## Ellipsis (§3)

Three meanings, seven utterances (full sentences plus fragments); only
full sentences have literal meaning, and per-word deletion (rate δ) turns
them into fragments. -/

namespace EllipsisModel

/-- Meanings: who went to the movies. -/
inductive Meaning where
  | aliceWent
  | bobWent
  | nobodyWent
  deriving DecidableEq, Fintype, Repr, Inhabited

/-- Utterances: full sentences and fragments. Fragments arise from
    noise deleting words from full sentences. -/
inductive Utterance where
  | aliceWentToMovies
  | bobWentToMovies
  | nobodyWentToMovies
  | alice
  | bob
  | nobody
  | wentToMovies
  deriving DecidableEq, Fintype, Repr, Inhabited

/-- Literal meaning: only full sentences have truth conditions.
    Fragments have no literal meaning — this is the key to the model. -/
def literalMeaning : Utterance → Meaning → Bool
  | .aliceWentToMovies, .aliceWent => true
  | .bobWentToMovies, .bobWent => true
  | .nobodyWentToMovies, .nobodyWent => true
  | _, _ => false

/-- Prior over utterances (speaker's production probability).
    Only full sentences are in the speaker's production distribution. -/
noncomputable def utterancePrior : Utterance → ℝ
  | .aliceWentToMovies => 1
  | .bobWentToMovies => 1
  | .nobodyWentToMovies => 1
  | _ => 0

/-- Deletion channel: a full sentence survives with probability 1 − δ or
loses its predicate with probability δ (the path relevant to "Bob"). -/
noncomputable def noiseChannel (δ : ℝ) : Utterance → Utterance → ℝ
  | .aliceWentToMovies, .aliceWentToMovies => 1 - δ
  | .aliceWentToMovies, .alice => δ
  | .bobWentToMovies, .bobWentToMovies => 1 - δ
  | .bobWentToMovies, .bob => δ
  | .nobodyWentToMovies, .nobodyWentToMovies => 1 - δ
  | .nobodyWentToMovies, .nobody => δ
  | .alice, .alice => 1
  | .bob, .bob => 1
  | .nobody, .nobody => 1
  | .wentToMovies, .wentToMovies => 1
  | _, _ => 0

/-! ### The ellipsis chain -/

/-- ℚ noise rate (1%; Fig. 1 shows robustness across 10⁻⁵–10⁻¹). -/
def δQ : ℚ≥0 := 1/100

/-- ℚ noise channel (word deletion, mirroring `noiseChannel`). -/
def noiseQ : Utterance → Utterance → ℚ≥0
  | .aliceWentToMovies, .aliceWentToMovies => 1 - δQ
  | .aliceWentToMovies, .alice => δQ
  | .bobWentToMovies, .bobWentToMovies => 1 - δQ
  | .bobWentToMovies, .bob => δQ
  | .nobodyWentToMovies, .nobodyWentToMovies => 1 - δQ
  | .nobodyWentToMovies, .nobody => δQ
  | .alice, .alice => 1
  | .bob, .bob => 1
  | .nobody, .nobody => 1
  | .wentToMovies, .wentToMovies => 1
  | _, _ => 0

/-- ℚ utterance prior (only full sentences are produced). -/
def utterancePriorQ : Utterance → ℚ≥0
  | .aliceWentToMovies => 1
  | .bobWentToMovies => 1
  | .nobodyWentToMovies => 1
  | _ => 0

/-- ℚ noisy literal-listener score (eq. 6 numerator). -/
def noisyMeaningQ (u_p : Utterance) (m : Meaning) : ℚ≥0 :=
  ∑ u_i, (if literalMeaning u_i m then (1 : ℚ≥0) else 0) *
    utterancePriorQ u_i * noiseQ u_i u_p

/-- The unique full sentence expressing each meaning. -/
def fullOf : Meaning → Utterance
  | .aliceWent => .aliceWentToMovies
  | .bobWent => .bobWentToMovies
  | .nobodyWent => .nobodyWentToMovies

/-- The noise-folded pragmatic speaker (eqs. 7–8). Each meaning has exactly
one truthful full sentence, so eq. 7's softmax has singleton support and
the intended-speaker distribution is degenerate at `fullOf m`; eq. 8's fold
then reduces to the channel row of `fullOf m`. -/
def s1nQ (m : Meaning) (u_p : Utterance) : ℚ≥0 := noiseQ (fullOf m) u_p

/-- Literal listener over meanings (eq. 6). -/
noncomputable def l0 (u_p : Utterance) : PMF Meaning :=
  .ofScores .uniform fun m => noisyMeaningQ u_p m

/-- Pragmatic listener over meanings (eq. 8, uniform meaning prior). -/
noncomputable def l1 (u_p : Utterance) : PMF Meaning :=
  .ofScores .uniform fun m => s1nQ m u_p

/-- Noisy L0 meaning (Eq. 6 numerator).

    meaning(u_p, m) = Σ_{u_i} ⟦u_i⟧(m) · P(u_i) · P_N(u_p | u_i)

    The listener considers all intended utterances u_i with meaning m,
    weighted by how likely noise would produce the perceived u_p. -/
noncomputable def noisyMeaning (δ : ℝ) (u_p : Utterance) (m : Meaning) : ℝ :=
  ∑ u_i : Utterance,
    (if literalMeaning u_i m then (1 : ℝ) else 0) *
    utterancePrior u_i * noiseChannel δ u_i u_p

/-! ### Ellipsis Predictions -/

/-- Hearing the fragment "Bob" — no literal meaning — L0 infers "Bob
went": the only full sentence producing "Bob" by deletion. -/
theorem l0_fragment_correct :
    l0 .bob .aliceWent < l0 .bob .bobWent ∧
    l0 .bob .nobodyWent < l0 .bob .bobWent :=
  ⟨PMF.ofScores_lt _ (by decide +kernel), PMF.ofScores_lt _ (by decide +kernel)⟩

/-- The same for the "Nobody" fragment. -/
theorem l0_nobody_correct :
    l0 .nobody .aliceWent < l0 .nobody .nobodyWent ∧
    l0 .nobody .bobWent < l0 .nobody .nobodyWent :=
  ⟨PMF.ofScores_lt _ (by decide +kernel), PMF.ofScores_lt _ (by decide +kernel)⟩

/-- Full sentences are interpreted literally (sanity check). -/
theorem l0_full_sentence_correct :
    l0 .bobWentToMovies .aliceWent < l0 .bobWentToMovies .bobWent ∧
    l0 .bobWentToMovies .nobodyWent < l0 .bobWentToMovies .bobWent :=
  ⟨PMF.ofScores_lt _ (by decide +kernel), PMF.ofScores_lt _ (by decide +kernel)⟩

/-- The pragmatic listener agrees on the fragment. -/
theorem l1_fragment_correct :
    l1 .bob .aliceWent < l1 .bob .bobWent ∧
    l1 .bob .nobodyWent < l1 .bob .bobWent :=
  ⟨PMF.ofScores_lt _ (by decide +kernel), PMF.ofScores_lt _ (by decide +kernel)⟩

/-! ### Parametric Robustness -/

/-! ### Parametric robustness (Fig. 1, left panel) -/

/-- The noisy meaning at "bob" is δ for bobWent and 0 for all others.

    Only "Bob went to the movies" can produce "Bob" via noise deletion,
    and only with meaning bobWent. Therefore L0("bob") = δ/δ = 1. -/
theorem noisyMeaning_bob_bobWent (δ : ℝ) :
    noisyMeaning δ .bob .bobWent = δ := by
  unfold noisyMeaning
  rw [Finset.sum_eq_single .bobWentToMovies]
  · simp [literalMeaning, utterancePrior, noiseChannel]
  · intro u_i _ hu; cases u_i <;> simp_all [literalMeaning, utterancePrior, noiseChannel]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem noisyMeaning_bob_aliceWent (δ : ℝ) :
    noisyMeaning δ .bob .aliceWent = 0 := by
  unfold noisyMeaning
  apply Finset.sum_eq_zero
  intro u_i _; cases u_i <;> simp [literalMeaning, utterancePrior, noiseChannel]

theorem noisyMeaning_bob_nobodyWent (δ : ℝ) :
    noisyMeaning δ .bob .nobodyWent = 0 := by
  unfold noisyMeaning
  apply Finset.sum_eq_zero
  intro u_i _; cases u_i <;> simp [literalMeaning, utterancePrior, noiseChannel]

/-- Fragment interpretation at every noise rate δ > 0 — "this reasoning
will work even if the noise rate is arbitrarily close to 0, so long as it
is positive": "Bob" only arises from "Bob went", so L0 gives it
probability δ/δ = 1. -/
theorem l0_fragment_robust (δ₀ : ℝ) (hδ : δ₀ ≠ 0) :
    noisyMeaning δ₀ .bob .bobWent /
      (noisyMeaning δ₀ .bob .aliceWent + noisyMeaning δ₀ .bob .bobWent +
       noisyMeaning δ₀ .bob .nobodyWent) = 1 := by
  rw [noisyMeaning_bob_bobWent, noisyMeaning_bob_aliceWent, noisyMeaning_bob_nobodyWent]
  simp [div_self hδ]

end EllipsisModel

/-! ### Prosody: Strategic Noise Reduction -/

/-! ## Prosody (§4)

Stress halves the noise rate on the stressed word (§4.1's ε/n at n = 2).
An exhaustive-knowledge speaker must protect "Bob" from mishearing, a
non-exhaustive one need not — so the listener reads stress as
exhaustivity. -/

namespace ProsodyModel

/-- Meanings: who went to the movies (exhaustive vs non-exhaustive). -/
inductive Meaning where
  | onlyAlice
  | onlyBob
  | both
  deriving DecidableEq, Fintype, Repr, Inhabited

/-- Utterances: with and without prosodic stress (CAPS = stress). -/
inductive Utterance where
  | aliceWent
  | ALICE_went
  | bobWent
  | BOB_went
  | aliceAndBobWent
  deriving DecidableEq, Fintype, Repr, Inhabited

/-- Literal meaning: lower-bound semantics.
    "Alice went" is true if Alice went (regardless of others). -/
def literalMeaning : Utterance → Meaning → Bool
  | .aliceWent, .onlyAlice => true
  | .aliceWent, .both => true
  | .ALICE_went, .onlyAlice => true
  | .ALICE_went, .both => true
  | .bobWent, .onlyBob => true
  | .bobWent, .both => true
  | .BOB_went, .onlyBob => true
  | .BOB_went, .both => true
  | .aliceAndBobWent, .both => true
  | _, _ => false

/-- Noise channel with prosody.

    The confusion is between subjects: "Alice" ↔ "Bob".
    - No stress: ε chance of subject confusion
    - With stress: ε/2 chance (stress reduces noise) -/
noncomputable def noiseChannel (ε : ℝ) : Utterance → Utterance → ℝ
  | .aliceWent, .aliceWent => 1 - ε
  | .aliceWent, .bobWent => ε
  | .bobWent, .bobWent => 1 - ε
  | .bobWent, .aliceWent => ε
  | .ALICE_went, .ALICE_went => 1 - ε/2
  | .ALICE_went, .aliceWent => ε/2
  | .BOB_went, .BOB_went => 1 - ε/2
  | .BOB_went, .bobWent => ε/2
  | .aliceAndBobWent, .aliceAndBobWent => 1
  | _, _ => 0

/-- Noisy L0 meaning (Eq. 6 numerator) for the prosody model. -/
noncomputable def noisyMeaning (ε : ℝ) (u_p : Utterance) (m : Meaning) : ℝ :=
  ∑ u_i : Utterance,
    (if literalMeaning u_i m then (1 : ℝ) else 0) *
    noiseChannel ε u_i u_p

/-- Literal listener over meanings given the perceived utterance
(eq. 6, uniform priors). -/
noncomputable def l0 (ε : ℝ) (u_p : Utterance) (m : Meaning) : ℝ :=
  noisyMeaning ε u_p m / ∑ m', noisyMeaning ε u_p m'

private theorem sumMeaningsR (f : Meaning → ℝ) :
    ∑ m, f m = f .onlyAlice + f .onlyBob + f .both := by
  rw [show (Finset.univ : Finset Meaning) = {.onlyAlice, .onlyBob, .both} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

private theorem sumUttsR (f : Utterance → ℝ) :
    ∑ u, f u = f .aliceWent + f .ALICE_went + f .bobWent + f .BOB_went +
      f .aliceAndBobWent := by
  rw [show (Finset.univ : Finset Utterance)
      = {.aliceWent, .ALICE_went, .bobWent, .BOB_went, .aliceAndBobWent} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

section Parametric

variable {ε : ℝ}

/-! The literal posteriors, symbolically in ε: the stressed percept pins
the subject against `both`; the unstressed one mixes in the confusable
subject; the `both` row is identically `1/2` (`1 + ε/2 = (2 + ε)/2`). -/

private theorem l0_B_ob (hε0 : 0 < ε) (hε1 : ε < 1) :
    l0 ε .BOB_went .onlyBob = 1/2 := by
  have hB : (2 : ℝ) - ε ≠ 0 := by linarith
  unfold l0 noisyMeaning
  rw [sumMeaningsR]
  simp only [sumUttsR, literalMeaning, noiseChannel, if_true]
  norm_num
  rw [div_eq_div_iff (ne_of_gt (by linarith)) (ne_of_gt (by linarith))]
  ring

private theorem l0_b_ob (hε0 : 0 < ε) (hε1 : ε < 1) :
    l0 ε .bobWent .onlyBob = (1 - ε/2) / (2 + ε) := by
  have h2 : (2 : ℝ) + ε ≠ 0 := by linarith
  unfold l0 noisyMeaning
  rw [sumMeaningsR]
  simp only [sumUttsR, literalMeaning, noiseChannel, if_true]
  norm_num
  rw [div_eq_div_iff (ne_of_gt (by linarith)) (ne_of_gt (by linarith))]
  ring

private theorem l0_a_ob (hε0 : 0 < ε) (hε1 : ε < 1) :
    l0 ε .aliceWent .onlyBob = ε / (2 + ε) := by
  have h2 : (2 : ℝ) + ε ≠ 0 := by linarith
  unfold l0 noisyMeaning
  rw [sumMeaningsR]
  simp only [sumUttsR, literalMeaning, noiseChannel, if_true]
  norm_num
  rw [div_eq_div_iff (ne_of_gt (by linarith)) (ne_of_gt (by linarith))]
  ring

private theorem l0_values (hε0 : 0 < ε) (hε1 : ε < 1) :
    l0 ε .BOB_went .onlyBob = 1/2 ∧
    l0 ε .bobWent .onlyBob = (1 - ε/2) / (2 + ε) ∧
    l0 ε .aliceWent .onlyBob = ε / (2 + ε) :=
  ⟨l0_B_ob hε0 hε1, l0_b_ob hε0 hε1, l0_a_ob hε0 hε1⟩

/-- Unstressed speaker-utility atom (eq. 7): the channel-weighted geometric
mean of the literal posteriors for uttering "Bob went". -/
noncomputable def xAtom (ε : ℝ) : ℝ :=
  l0 ε .bobWent .onlyBob ^ (1 - ε) * l0 ε .aliceWent .onlyBob ^ ε

/-- Stressed speaker-utility atom (eq. 7) for "BOB went". -/
noncomputable def yAtom (ε : ℝ) : ℝ :=
  l0 ε .BOB_went .onlyBob ^ (1 - ε/2) * l0 ε .bobWent .onlyBob ^ (ε/2)

/-- The paper's mechanism, at every noise rate ε < 2/3: the stressed atom
strictly exceeds the unstressed one. Stress both concentrates the channel
on the informative percept and sharpens that percept's posterior, so the
weighted geometric means separate across the unstressed posterior
`(1 − ε/2)/(2 + ε)` — no magnitude computation involved. -/
theorem xAtom_lt_yAtom (hε0 : 0 < ε) (hε : ε < 2/3) :
    xAtom ε < yAtom ε := by
  obtain ⟨hB, hb, ha⟩ := l0_values hε0 (by linarith)
  have h2 : (0:ℝ) < 2 + ε := by linarith
  have hv : (0:ℝ) < (1 - ε/2) / (2 + ε) := div_pos (by linarith) h2
  have hu : (0:ℝ) < ε / (2 + ε) := div_pos hε0 h2
  have huv : ε / (2 + ε) < (1 - ε/2) / (2 + ε) := by
    apply div_lt_div_of_pos_right _ h2; linarith
  have hvhalf : (1 - ε/2) / (2 + ε) < 1/2 := by
    rw [div_lt_iff₀ h2]; linarith
  calc xAtom ε < (1 - ε/2) / (2 + ε) := by
        rw [xAtom, hb, ha]
        exact RSA.rpow_mul_rpow_lt hu hv hv le_rfl huv (by linarith) hε0
          (by ring)
    _ < yAtom ε := by
        rw [yAtom, hB, hb, mul_comm]
        exact RSA.lt_rpow_mul_rpow hv hvhalf le_rfl (by linarith)
          (by linarith) (by ring)

theorem xAtom_pos (hε0 : 0 < ε) (hε1 : ε < 1) : 0 < xAtom ε := by
  obtain ⟨_, hb, ha⟩ := l0_values hε0 hε1
  rw [xAtom, hb, ha]
  have h2 : (0:ℝ) < 2 + ε := by linarith
  exact mul_pos (Real.rpow_pos_of_pos (div_pos (by linarith) h2) _)
    (Real.rpow_pos_of_pos (div_pos hε0 h2) _)

theorem yAtom_pos (hε0 : 0 < ε) (hε1 : ε < 1) : 0 < yAtom ε := by
  obtain ⟨hB, hb, _⟩ := l0_values hε0 hε1
  rw [yAtom, hB, hb]
  have h2 : (0:ℝ) < 2 + ε := by linarith
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.rpow_pos_of_pos (div_pos (by linarith) h2) _)

/-- The atoms are the paper's exponentiated eq.-7 utilities. -/
theorem xAtom_eq_exp (hε0 : 0 < ε) (hε1 : ε < 1) :
    xAtom ε = Real.exp ((1 - ε) * Real.log (l0 ε .bobWent .onlyBob) +
      ε * Real.log (l0 ε .aliceWent .onlyBob)) := by
  obtain ⟨_, hb, ha⟩ := l0_values hε0 hε1
  have h2 : (0:ℝ) < 2 + ε := by linarith
  have hvpos : (0:ℝ) < l0 ε .bobWent .onlyBob := by
    rw [hb]; exact div_pos (by linarith) h2
  have hupos : (0:ℝ) < l0 ε .aliceWent .onlyBob := by
    rw [ha]; exact div_pos hε0 h2
  rw [xAtom, Real.rpow_def_of_pos hvpos, Real.rpow_def_of_pos hupos,
    ← Real.exp_add]
  ring_nf

/-- Speaker-utility atoms per (meaning, utterance): the truthful subject
utterances carry `xAtom`/`yAtom` (by Alice/Bob symmetry), the `both`
meaning's subject atoms are identically `1/2`, and the conjunction is
noise-free. -/
noncomputable def eAtom (ε : ℝ) : Meaning → Utterance → ℝ
  | .onlyBob, .bobWent => xAtom ε
  | .onlyBob, .BOB_went => yAtom ε
  | .onlyAlice, .aliceWent => xAtom ε
  | .onlyAlice, .ALICE_went => yAtom ε
  | .both, .aliceAndBobWent => 1
  | .both, _ => 1/2
  | _, _ => 0

/-- Pragmatic-listener score (eq. 8): speaker-normalized atoms folded
through the channel. -/
noncomputable def l1Score (ε : ℝ) (u_p : Utterance) (m : Meaning) : ℝ :=
  (∑ u_i, eAtom ε m u_i * noiseChannel ε u_i u_p) / ∑ u_i, eAtom ε m u_i

/-- Pragmatic listener (eq. 8). -/
noncomputable def l1PMF (ε : ℝ) (u_p : Utterance) : PMF Meaning :=
  PMF.normalizeOrUniform fun m => ENNReal.ofReal (l1Score ε u_p m)

private theorem noiseChannel_nonneg (hε0 : 0 < ε) (hε1 : ε < 1)
    (u p : Utterance) : 0 ≤ noiseChannel ε u p := by
  cases u <;> cases p <;> simp only [noiseChannel] <;> linarith

private theorem eAtom_nonneg (hε0 : 0 < ε) (hε1 : ε < 1)
    (m : Meaning) (u : Utterance) : 0 ≤ eAtom ε m u := by
  have hx := (xAtom_pos hε0 hε1).le
  have hy := (yAtom_pos hε0 hε1).le
  cases m <;> cases u <;> simp only [eAtom] <;> first | assumption | norm_num

private theorem l1Score_nonneg (hε0 : 0 < ε) (hε1 : ε < 1)
    (u_p : Utterance) (m : Meaning) : 0 ≤ l1Score ε u_p m :=
  div_nonneg
    (Finset.sum_nonneg fun u _ =>
      mul_nonneg (eAtom_nonneg hε0 hε1 m u) (noiseChannel_nonneg hε0 hε1 u u_p))
    (Finset.sum_nonneg fun u _ => eAtom_nonneg hε0 hε1 m u)

/-- The six score values the headline compares (symbolic in ε). -/
private theorem l1Score_values (hε0 : 0 < ε) (hε1 : ε < 1) :
    l1Score ε .BOB_went .onlyBob
        = yAtom ε * (1 - ε/2) / (xAtom ε + yAtom ε) ∧
    l1Score ε .BOB_went .onlyAlice = 0 ∧
    l1Score ε .BOB_went .both = (1 - ε/2) / 6 ∧
    l1Score ε .bobWent .onlyBob
        = (xAtom ε * (1 - ε) + yAtom ε * (ε/2)) / (xAtom ε + yAtom ε) ∧
    l1Score ε .bobWent .onlyAlice = xAtom ε * ε / (xAtom ε + yAtom ε) ∧
    l1Score ε .bobWent .both = (1 + ε/2) / 6 := by
  have hxy : xAtom ε + yAtom ε ≠ 0 := by
    have := xAtom_pos hε0 hε1; have := yAtom_pos hε0 hε1; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · unfold l1Score
      rw [sumUttsR, sumUttsR]
      simp only [eAtom, noiseChannel]
      norm_num
      try rw [div_eq_div_iff hxy hxy]
      try ring

private theorem sum_pos_BOB (hε0 : 0 < ε) (hε1 : ε < 1) :
    0 < ∑ m, l1Score ε .BOB_went m := by
  obtain ⟨hB_ob, hB_oa, hB_both, _, _, _⟩ := l1Score_values hε0 hε1
  have hx := xAtom_pos hε0 hε1; have hy := yAtom_pos hε0 hε1
  rw [sumMeaningsR, hB_oa, hB_ob, hB_both]
  have : (0:ℝ) < yAtom ε * (1 - ε/2) / (xAtom ε + yAtom ε) := by
    apply div_pos _ (by linarith); nlinarith
  nlinarith

private theorem sum_pos_bob (hε0 : 0 < ε) (hε1 : ε < 1) :
    0 < ∑ m, l1Score ε .bobWent m := by
  obtain ⟨_, _, _, hb_ob, hb_oa, hb_both⟩ := l1Score_values hε0 hε1
  have hx := xAtom_pos hε0 hε1; have hy := yAtom_pos hε0 hε1
  rw [sumMeaningsR, hb_oa, hb_ob, hb_both]
  have h1 : (0:ℝ) ≤ xAtom ε * ε / (xAtom ε + yAtom ε) := by positivity
  have h2 : (0:ℝ) ≤ (xAtom ε * (1 - ε) + yAtom ε * (ε/2)) / (xAtom ε + yAtom ε) := by
    apply div_nonneg _ (by linarith); nlinarith
  nlinarith

/-- Stress increases the exhaustive interpretation, at every noise rate
ε < 2/3: "BOB went" is strictly more likely than "Bob went" to mean only
Bob went (§4). By posterior dominance (`Finset.div_sum_lt_div_sum`), the
comparison is cell-by-cell odds dominance: trivial at `onlyAlice` (the
stressed row is zero there) and `onlyBob`, and the atom ordering
`xAtom < yAtom` — the paper's mechanism — at `both`. -/
theorem stress_increases_exhaustivity (hε0 : 0 < ε) (hε : ε < 2/3) :
    l1PMF ε .bobWent .onlyBob < l1PMF ε .BOB_went .onlyBob := by
  have hε1 : ε < 1 := by linarith
  have hx := xAtom_pos hε0 hε1
  have hxy := xAtom_lt_yAtom hε0 hε
  obtain ⟨hB_ob, hB_oa, hB_both, hb_ob, _, hb_both⟩ := l1Score_values hε0 hε1
  have hboth : l1Score ε .bobWent .onlyBob * l1Score ε .BOB_went .both <
      l1Score ε .BOB_went .onlyBob * l1Score ε .bobWent .both := by
    rw [hb_ob, hB_both, hB_ob, hb_both, div_mul_div_comm, div_mul_div_comm]
    have hy := yAtom_pos hε0 hε1
    exact div_lt_div_of_pos_right (by nlinarith [mul_pos hx hε0]) (by nlinarith)
  rw [l1PMF, l1PMF]
  exact PMF.normalizeOrUniform_ofReal_lt_cross (l1Score_nonneg hε0 hε1 _)
    (l1Score_nonneg hε0 hε1 _) (sum_pos_bob hε0 hε1) (sum_pos_BOB hε0 hε1)
    (Finset.div_sum_lt_div_sum (sum_pos_bob hε0 hε1) (sum_pos_BOB hε0 hε1)
      (fun c => match c with
        | .onlyAlice => by
            rw [hB_oa, mul_zero]
            exact mul_nonneg (l1Score_nonneg hε0 hε1 _ _) (l1Score_nonneg hε0 hε1 _ _)
        | .onlyBob => (mul_comm _ _).le
        | .both => hboth.le)
      ⟨.both, hboth⟩)

end Parametric

/-- The paper's working regime (ε = 1/100) is inside the parametric
theorem's range. -/
example : l1PMF (1/100) .bobWent .onlyBob < l1PMF (1/100) .BOB_went .onlyBob :=
  stress_increases_exhaustivity (by norm_num) (by norm_num)

end ProsodyModel

/-! ### Fragment Interpretation Summary -/

/-!
## Fragment Interpretation

The wh-fragment-answer prediction — "Bob" as answer to "Who went to the
movies?" is correctly interpreted despite having no literal meaning — is
carried by `EllipsisModel.l0_fragment_correct` and
`EllipsisModel.l1_fragment_correct` in §1.

The same mechanism extends to non-question fragments: noise-based inference
is not restricted to question-answer pairs — any context where deletion is
plausible licenses fragment use.
-/

/-! ### Prosody Data -/

/-!
## Prosody data (`Data/Examples/BergenGoodman2015.json`)

The paper's stress/exhaustivity stimuli: "BOB went to the movies" is read
exhaustively (only Bob went), "Bob went to the movies" is not. The model
derives the contrast from noise reduction: stress lowers the noise rate, and
the listener infers that the speaker had reason to protect the stressed word,
implying exhaustive knowledge.
-/

/-- Utterance adapter: a row's `stress` feature as a `ProsodyModel.Utterance`. -/
def uttOf (row : Data.Examples.LinguisticExample) : Option ProsodyModel.Utterance :=
  match row.feature? "stress" with
  | some "subject" => some .BOB_went
  | some "none"    => some .bobWent
  | _              => none

/-- The model's L1 assigns the exhaustive meaning more probability at the
    stressed row's utterance than at the unstressed row's, matching the rows'
    recorded `reading` contrast. -/
theorem model_matches_stress_rows :
    ∃ u_s u_u, uttOf Examples.stressed_subject = some u_s ∧
      uttOf Examples.unstressed_subject = some u_u ∧
      ProsodyModel.l1PMF (1/100) u_u .onlyBob <
        ProsodyModel.l1PMF (1/100) u_s .onlyBob :=
  ⟨_, _, rfl, rfl,
    ProsodyModel.stress_increases_exhaustivity (by norm_num) (by norm_num)⟩

/-- Stress widens the channel's correct-vs-confused gap by exactly ε
(1 − ε stressed versus 1 − 2ε unstressed) — the mechanism behind
`stress_increases_exhaustivity`, at every noise rate. -/
theorem stress_increases_discrimination (ε : ℝ) (hε : 0 < ε) :
    ProsodyModel.noiseChannel ε .BOB_went .BOB_went -
      ProsodyModel.noiseChannel ε .BOB_went .bobWent >
    ProsodyModel.noiseChannel ε .bobWent .bobWent -
      ProsodyModel.noiseChannel ε .bobWent .aliceWent := by
  simp only [ProsodyModel.noiseChannel]
  linarith

end BergenGoodman2015
