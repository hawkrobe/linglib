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
* `stress_increases_exhaustivity`: "BOB went" (stressed) is more likely
  than "Bob went" to mean only-Bob (§4 prosody) — stress reduces noise on
  the word it protects.
* `stress_increases_discrimination`: the channel-level mechanism, for
  every ε ∈ (0, 1).

## Implementation notes

Ellipsis is exact ℚ≥0: each meaning has a unique truthful full sentence,
so the eq. 7 softmax is degenerate and eq. 8 reduces to the channel row
(`s1nQ`); listeners are `PMF.ofScores`. Prosody is transcendental — eq. 7
exponentiates noise-weighted sums of `log l0` — but with ε = 1/100 the
weights have denominator 200, so each utility atom is an `RSA.rootAtom`
of an explicit rational 200th power (`X200`, `Y200`), two-sidedly bounded
by kernel certificates (`Xa_bounds`, `Ya_bounds`), identified with the
paper's exponential form by `Xa_eq_exp`/`Ya_eq_exp`, and the predictions
close by `nlinarith` over the bounds.
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

/-- ℚ noise rate (1%). -/
def εQ : ℚ := 1/100

/-- ℚ noise channel with prosody (stress halves the rate; §4.1). -/
def noiseQ : Utterance → Utterance → ℚ
  | .aliceWent, .aliceWent => 1 - εQ
  | .aliceWent, .bobWent => εQ
  | .bobWent, .bobWent => 1 - εQ
  | .bobWent, .aliceWent => εQ
  | .ALICE_went, .ALICE_went => 1 - εQ/2
  | .ALICE_went, .aliceWent => εQ/2
  | .BOB_went, .BOB_went => 1 - εQ/2
  | .BOB_went, .bobWent => εQ/2
  | .aliceAndBobWent, .aliceAndBobWent => 1
  | _, _ => 0

/-- ℚ noisy literal-listener score (eq. 6 numerator). -/
def noisyMeaningQ (u_p : Utterance) (m : Meaning) : ℚ :=
  ∑ u_i, (if literalMeaning u_i m then (1 : ℚ) else 0) * noiseQ u_i u_p

/-- L0 posterior over meanings (eq. 6). All values are rational; the
relevant column entries are `l0Q .bobWent .onlyBob = 199/402`,
`l0Q .aliceWent .onlyBob = 1/201`, `l0Q .BOB_went .onlyBob = 1/2`, and the
`both` column is constantly `1/2` on subject utterances (`1` on the
conjunction). -/
def l0Q (u_p : Utterance) (m : Meaning) : ℚ :=
  noisyMeaningQ u_p m / ∑ m', noisyMeaningQ u_p m'

/-- 200th power of the speaker utility atom for the single-subject meanings
(eq. 7 exponentiates a `P_N`-weighted sum of `log l0` values; with
ε = 1/100 the exponent weights have denominator 200, so the utility's 200th
power is rational): `exp(U(bobWent | onlyBob))²⁰⁰ = l0(b|ob)¹⁹⁸ · l0(a|ob)²`. -/
def X200 : ℚ := l0Q .bobWent .onlyBob ^ 198 * l0Q .aliceWent .onlyBob ^ 2

/-- 200th power of the stressed-utterance utility atom:
`exp(U(BOB_went | onlyBob))²⁰⁰ = l0(B|ob)¹⁹⁹ · l0(b|ob)`. -/
def Y200 : ℚ := l0Q .BOB_went .onlyBob ^ 199 * l0Q .bobWent .onlyBob

/-- Unstressed speaker-utility atom `exp(U(bobWent | onlyBob))`. -/
noncomputable def Xa : ℝ := RSA.rootAtom (X200 : ℝ) 200

/-- Stressed speaker-utility atom `exp(U(BOB_went | onlyBob))`. -/
noncomputable def Ya : ℝ := RSA.rootAtom (Y200 : ℝ) 200

private theorem l0_b_ob : l0Q .bobWent .onlyBob = 199/402 := by decide +kernel
private theorem l0_a_ob : l0Q .aliceWent .onlyBob = 1/201 := by decide +kernel
private theorem l0_B_ob : l0Q .BOB_went .onlyBob = 1/2 := by decide +kernel

/-- The atoms are the paper's exponentiated utilities (eq. 7): the
`P_N`-weighted geometric means of the literal posteriors. -/
theorem Xa_eq_exp :
    Xa = Real.exp ((1 - (εQ : ℝ)) * Real.log (l0Q .bobWent .onlyBob : ℝ) +
      (εQ : ℝ) * Real.log (l0Q .aliceWent .onlyBob : ℝ)) := by
  rw [Xa, show ((X200 : ℚ) : ℝ) = (l0Q .bobWent .onlyBob : ℝ) ^ (198:ℕ) *
      (l0Q .aliceWent .onlyBob : ℝ) ^ (2:ℕ) by push_cast [X200]; ring,
    RSA.rootAtom_pow_mul_pow (by rw [l0_b_ob]; norm_num) (by rw [l0_a_ob]; norm_num)]
  norm_num [εQ]

theorem Ya_eq_exp :
    Ya = Real.exp ((1 - (εQ : ℝ)/2) * Real.log (l0Q .BOB_went .onlyBob : ℝ) +
      ((εQ : ℝ)/2) * Real.log (l0Q .bobWent .onlyBob : ℝ)) := by
  rw [Ya, show ((Y200 : ℚ) : ℝ) = (l0Q .BOB_went .onlyBob : ℝ) ^ (199:ℕ) *
      (l0Q .bobWent .onlyBob : ℝ) ^ (1:ℕ) by push_cast [Y200]; ring,
    RSA.rootAtom_pow_mul_pow (by rw [l0_B_ob]; norm_num) (by rw [l0_b_ob]; norm_num)]
  norm_num [εQ]

private theorem X200_pos : (0:ℚ) < X200 := by decide +kernel
private theorem Y200_pos : (0:ℚ) < Y200 := by decide +kernel

theorem Xa_pos : 0 < Xa := RSA.rootAtom_pos (by exact_mod_cast X200_pos) _

theorem Ya_pos : 0 < Ya := RSA.rootAtom_pos (by exact_mod_cast Y200_pos) _

/-- Kernel-certified bounds: `(47/100)²⁰⁰ ≤ X200 ≤ (473/1000)²⁰⁰`. -/
theorem Xa_bounds : (47/100 : ℝ) ≤ Xa ∧ Xa ≤ 473/1000 :=
  ⟨RSA.le_rootAtom_of_pow_le (by norm_num) (by norm_num)
      (by rw [show ((47:ℝ)/100) = ((47/100 : ℚ) : ℝ) by norm_num]
          exact_mod_cast (by decide +kernel : (47/100 : ℚ) ^ 200 ≤ X200)),
    RSA.rootAtom_le_of_le_pow (by norm_num) (by exact_mod_cast X200_pos.le)
      (by norm_num)
      (by rw [show ((473:ℝ)/1000) = ((473/1000 : ℚ) : ℝ) by norm_num]
          exact_mod_cast (by decide +kernel : X200 ≤ (473/1000 : ℚ) ^ 200))⟩

/-- Kernel-certified bounds: `(4999/10000)²⁰⁰ ≤ Y200 ≤ (1/2)²⁰⁰`. -/
theorem Ya_bounds : (4999/10000 : ℝ) ≤ Ya ∧ Ya ≤ 1/2 :=
  ⟨RSA.le_rootAtom_of_pow_le (by norm_num) (by norm_num)
      (by rw [show ((4999:ℝ)/10000) = ((4999/10000 : ℚ) : ℝ) by norm_num]
          exact_mod_cast (by decide +kernel : (4999/10000 : ℚ) ^ 200 ≤ Y200)),
    RSA.rootAtom_le_of_le_pow (by norm_num) (by exact_mod_cast Y200_pos.le)
      (by norm_num)
      (by rw [show ((1:ℝ)/2) = ((1/2 : ℚ) : ℝ) by norm_num]
          exact_mod_cast (by decide +kernel : Y200 ≤ (1/2 : ℚ) ^ 200))⟩

/-- Speaker-utility atom per (meaning, intended utterance): `Xa`/`Ya` for the
single-subject meanings (the a ↔ b relabelling fixes the model, so the
`onlyAlice` atoms coincide with the `onlyBob` ones — their 200th powers are
equal rationals), exact `1/2` (and `1` on the conjunction) for `both`
(its literal posteriors are constantly `1/2`, so the geometric mean is
degenerate), and `0` off the truthful support. -/
noncomputable def eAtom : Meaning → Utterance → ℝ
  | .onlyBob, .bobWent => Xa
  | .onlyBob, .BOB_went => Ya
  | .onlyAlice, .aliceWent => Xa
  | .onlyAlice, .ALICE_went => Ya
  | .both, .aliceWent => 1/2
  | .both, .ALICE_went => 1/2
  | .both, .bobWent => 1/2
  | .both, .BOB_went => 1/2
  | .both, .aliceAndBobWent => 1
  | _, _ => 0

private theorem eAtom_nonneg (m : Meaning) (u : Utterance) : 0 ≤ eAtom m u := by
  cases m <;> cases u <;> simp [eAtom, Xa_pos.le, Ya_pos.le]

/-- L1 world score (eq. 8, uniform meaning prior): the normalized
intended-speaker mass pushed through the channel. -/
noncomputable def l1Score (u_p : Utterance) (m : Meaning) : ℝ :=
  (∑ u_i, eAtom m u_i * (noiseQ u_i u_p : ℝ)) / ∑ u_i, eAtom m u_i

private theorem l1Score_nonneg (u_p : Utterance) (m : Meaning) :
    0 ≤ l1Score u_p m := by
  apply div_nonneg
  · exact Finset.sum_nonneg fun u_i _ => mul_nonneg (eAtom_nonneg m u_i)
      (by exact_mod_cast (by cases u_i <;> cases u_p <;> norm_num [noiseQ, εQ] :
        (0:ℚ) ≤ noiseQ u_i u_p))
  · exact Finset.sum_nonneg fun u_i _ => eAtom_nonneg m u_i

/-- Pragmatic listener (eq. 8), dite-total. -/
noncomputable def l1PMF (u_p : Utterance) : PMF Meaning :=
  PMF.normalizeOrUniform fun m => ENNReal.ofReal (l1Score u_p m)

private theorem sumMeanings (f : Meaning → ℝ≥0∞) :
    ∑' m, f m = f .onlyAlice + f .onlyBob + f .both := by
  rw [tsum_fintype,
    show (Finset.univ : Finset Meaning) = {.onlyAlice, .onlyBob, .both} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

private theorem l1PMF_apply (u_p : Utterance)
    (hpos : 0 < ∑ m, l1Score u_p m) (m : Meaning) :
    l1PMF u_p m = ENNReal.ofReal (l1Score u_p m / ∑ m', l1Score u_p m') := by
  have hsum : (∑' m, ENNReal.ofReal (l1Score u_p m))
      = ENNReal.ofReal (∑ m, l1Score u_p m) := by
    rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg fun m _ => l1Score_nonneg u_p m]
  rw [l1PMF, PMF.normalizeOrUniform_apply
      (by rw [hsum, ENNReal.ofReal_ne_zero_iff]; exact hpos)
      (by rw [hsum]; exact ENNReal.ofReal_ne_top),
    hsum, ← ENNReal.ofReal_inv_of_pos hpos,
    ← ENNReal.ofReal_mul (l1Score_nonneg u_p m), div_eq_mul_inv]

private theorem sumUttsR (f : Utterance → ℝ) :
    ∑ u, f u = f .aliceWent + f .ALICE_went + f .bobWent + f .BOB_went +
      f .aliceAndBobWent := by
  rw [show (Finset.univ : Finset Utterance)
      = {.aliceWent, .ALICE_went, .bobWent, .BOB_went, .aliceAndBobWent} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

private theorem sumMeaningsR (f : Meaning → ℝ) :
    ∑ m, f m = f .onlyAlice + f .onlyBob + f .both := by
  rw [show (Finset.univ : Finset Meaning) = {.onlyAlice, .onlyBob, .both} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

/-- Expanded scores (5-term utterance sums; `Z both = 3`). -/
private theorem l1Score_values :
    l1Score .BOB_went .onlyBob = Ya * ((1 : ℝ) - 1/200) / (Xa + Ya) ∧
    l1Score .BOB_went .onlyAlice = 0 ∧
    l1Score .BOB_went .both = ((1 : ℝ) - 1/200) / 6 ∧
    l1Score .bobWent .onlyBob = (Xa * ((1 : ℝ) - 1/100) + Ya * (1/200)) / (Xa + Ya) ∧
    l1Score .bobWent .onlyAlice = Xa * (1/100) / (Xa + Ya) ∧
    l1Score .bobWent .both = ((1 : ℝ) + 1/200) / 6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · unfold l1Score
      rw [sumUttsR, sumUttsR]
      simp only [eAtom]
      push_cast [noiseQ, εQ]
      ring

private theorem sum_pos_BOB : 0 < ∑ m, l1Score .BOB_went m := by
  rw [sumMeaningsR]
  have h := l1Score_values
  rw [h.2.1, h.1, h.2.2.1]
  have := Xa_pos; have := Ya_pos
  positivity

private theorem sum_pos_bob : 0 < ∑ m, l1Score .bobWent m := by
  rw [sumMeaningsR]
  have h := l1Score_values
  rw [h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2]
  have := Xa_pos; have := Ya_pos
  positivity

/-- Stress increases exhaustive interpretation: "BOB went" (stressed) is
strictly more likely to mean "only Bob" than unstressed "Bob went" (§4). -/
theorem stress_increases_exhaustivity :
    l1PMF .bobWent .onlyBob < l1PMF .BOB_went .onlyBob := by
  rw [l1PMF_apply _ sum_pos_bob, l1PMF_apply _ sum_pos_BOB, sumMeaningsR, sumMeaningsR]
  obtain ⟨hB_ob, hB_oa, hB_both, hb_ob, hb_oa, hb_both⟩ := l1Score_values
  rw [hB_ob, hB_oa, hB_both, hb_ob, hb_oa, hb_both]
  have hX := Xa_pos; have hY := Ya_pos
  obtain ⟨hX1, hX2⟩ := Xa_bounds; obtain ⟨hY1, hY2⟩ := Ya_bounds
  have hXY : 0 < Xa + Ya := by linarith
  refine (ENNReal.ofReal_lt_ofReal_iff ?_).mpr ?_
  · positivity
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    field_simp
    nlinarith [mul_pos hX hY, sq_nonneg (Xa - Ya), sq_nonneg (Xa + Ya),
      mul_le_mul_of_nonneg_left hY2 hX.le, mul_le_mul_of_nonneg_left hX2 hY.le,
      mul_le_mul_of_nonneg_left hY1 hX.le, mul_le_mul_of_nonneg_left hX1 hY.le]

/-- "Both went" stays live under stress: it beats `onlyAlice` (which is
channel-incompatible with hearing "BOB went"). -/
theorem stressed_both_positive :
    l1PMF .BOB_went .onlyAlice < l1PMF .BOB_went .both := by
  rw [l1PMF_apply _ sum_pos_BOB, l1PMF_apply _ sum_pos_BOB]
  obtain ⟨_, hB_oa, hB_both, _, _, _⟩ := l1Score_values
  rw [hB_oa, hB_both]
  refine (ENNReal.ofReal_lt_ofReal_iff ?_).mpr ?_
  · exact div_pos (by norm_num) sum_pos_BOB
  · exact div_lt_div_of_pos_right (by norm_num) sum_pos_BOB

/-- "Both went" also beats `onlyAlice` without stress. -/
theorem unstressed_both_positive :
    l1PMF .bobWent .onlyAlice < l1PMF .bobWent .both := by
  rw [l1PMF_apply _ sum_pos_bob, l1PMF_apply _ sum_pos_bob]
  obtain ⟨_, _, _, _, hb_oa, hb_both⟩ := l1Score_values
  rw [hb_oa, hb_both]
  have hX := Xa_pos; have hY := Ya_pos
  obtain ⟨hX1, hX2⟩ := Xa_bounds; obtain ⟨hY1, hY2⟩ := Ya_bounds
  refine (ENNReal.ofReal_lt_ofReal_iff ?_).mpr ?_
  · exact div_pos (by positivity) sum_pos_bob
  · refine div_lt_div_of_pos_right ?_ sum_pos_bob
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith

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
      ProsodyModel.l1PMF u_u .onlyBob < ProsodyModel.l1PMF u_s .onlyBob :=
  ⟨_, _, rfl, rfl, ProsodyModel.stress_increases_exhaustivity⟩

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
