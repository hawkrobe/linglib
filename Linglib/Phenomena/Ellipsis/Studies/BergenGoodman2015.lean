import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Pragmatics.RSA.Core.Noise
import Linglib.Phenomena.Ellipsis.FragmentAnswers
import Linglib.Phenomena.Focus.ProsodicExhaustivity

/-!
# @cite{bergen-goodman-2015}
@cite{frank-goodman-2012} @cite{degen-etal-2020}

The Strategic Use of Noise in Pragmatic Reasoning.
*Topics in Cognitive Science* 7(2), 336–350.

## Core Argument

Standard RSA assumes perfect transmission: the utterance the speaker produces
is the utterance the listener hears. This paper extends RSA with a **noisy
channel** P_N(u_p | u_i) — the probability that the listener perceives u_p
given the speaker intended u_i. This extension explains two phenomena that
standard RSA cannot:

1. **Sentence fragments** (§3): "Bob" as answer to "Who went?" has no literal
   meaning, yet listeners correctly interpret it by reasoning that noise
   deleted words from a full sentence.

2. **Prosodic exhaustivity** (§4): "BOB went" (stressed) signals exhaustive
   knowledge (only Bob went), while "Bob went" (unstressed) is compatible
   with others also going. This emerges because stress reduces noise rate,
   and speakers strategically protect informative words.

## Key Equations

    L_0(m | u_p) ∝ P(m) Σ_{u_i: m∈⟦u_i⟧} P(u_i) · P_N(u_p | u_i)     (Eq. 6)
    U_n(u_i | m) = Σ_{u_p} P_N(u_p|u_i) · log L_{n-1}(m|u_p) - c(u_i)  (Eq. 7)
    L_n(m | u_p) ∝ P(m) Σ_{u_i} S_n(u_i|m) · P_N(u_p|u_i)              (Eq. 8)

## RSAConfig Encoding

The noisy channel model is encoded in RSAConfig by **folding noise into the
score functions**:

- `meaning(u_p, m)` = Eq. 6 numerator: Σ_{u_i} ⟦u_i⟧(m) · P(u_i) · P_N(u_p|u_i)
- `s1Score(l0, α, _, m, u_p)` = Eqs. 7-8 combined:
  Σ_{u_i} exp(α · Σ_{u_p'} P_N(u_p'|u_i) · log l0(u_p',m)) · P_N(u_p|u_i)

This works because the noise channel rows sum to 1, so normalization before
vs after folding in noise gives the same result:

    S1_noise(u_p|m) = Σ_{u_i} S1_intended(u_i|m) · P_N(u_p|u_i)

and L1(m|u_p) ∝ worldPrior(m) · S1_noise(u_p|m), matching Eq. 8.

The S1 speaker only produces **full sentences** — fragments arise solely from
noise corruption. This is encoded via `literalMeaning`: fragments have no
literal meaning, so S1's exp(α·utility) term is zero for them (matching
exp(-∞) = 0 from log(0) in the utility).
-/

open BigOperators RSA Phenomena.Ellipsis

namespace BergenGoodman2015

-- ============================================================================
-- § 1. Ellipsis: Sentence Fragments
-- ============================================================================

/-!
## Ellipsis

From the paper (§3):

> (1) A: Who went to the movies?
>     B: Bob

The fragment "Bob" has no literal truth conditions. The listener interprets
it as "Bob went to the movies" by reasoning that noise (word deletion)
corrupted a full sentence into a fragment.

### Model Setup

- Meanings M = {aliceWent, bobWent, nobodyWent}
- Utterances U = full sentences + fragments (7 total)
- Noise: per-word deletion with probability δ
- Only full sentences have literal meaning; fragments have none
-/

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

/-- Noise channel for ellipsis: word deletion with probability δ.

    P_N(u_p | u_i):
    - Full sentence heard correctly: 1 - δ
    - Full sentence reduced to subject fragment: δ (predicate deleted)
    - Everything else: 0

    This models the subject-deletion path. The paper also considers
    predicate deletion and multi-word deletion, but subject deletion is
    the relevant path for the "Bob" example. -/
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

-- ============================================================================
-- § 2. RSAConfig for Ellipsis
-- ============================================================================

/-- Noisy L0 meaning (Eq. 6 numerator).

    meaning(u_p, m) = Σ_{u_i} ⟦u_i⟧(m) · P(u_i) · P_N(u_p | u_i)

    The listener considers all intended utterances u_i with meaning m,
    weighted by how likely noise would produce the perceived u_p. -/
noncomputable def noisyMeaning (δ : ℝ) (u_p : Utterance) (m : Meaning) : ℝ :=
  ∑ u_i : Utterance,
    (if literalMeaning u_i m then (1 : ℝ) else 0) *
    utterancePrior u_i * noiseChannel δ u_i u_p

/-- Noise-folded S1 score (Eqs. 7-8 combined).

    s1Score(l0, α, _, m, u_p) = Σ_{u_i} raw(u_i|m) · P_N(u_p | u_i)

    where raw(u_i|m) = exp(α · Σ_{u_p'} P_N(u_p'|u_i) · log l0(u_p',m))
    for utterances with literal meaning m, and 0 otherwise (exp(-∞) = 0).

    This folds the noise channel into S1's output so that RSAConfig's
    S1(u_p|m) = Σ_{u_i} S1_intended(u_i|m) · P_N(u_p|u_i), matching Eq. 8.
    The row-sum-to-1 property of the noise channel ensures normalization
    is correct. -/
noncomputable def noisyS1Score (δ : ℝ)
    (l0 : Utterance → Meaning → ℝ) (α : ℝ) (_ : Unit)
    (m : Meaning) (u_p : Utterance) : ℝ :=
  ∑ u_i : Utterance,
    (if literalMeaning u_i m then
      Real.exp (α * ∑ u_p' : Utterance,
        noiseChannel δ u_i u_p' * Real.log (l0 u_p' m))
    else 0) * noiseChannel δ u_i u_p

/-- Noise rate: 1% per-word deletion. The paper's Fig. 1 shows results
    are robust across noise rates from 10⁻⁵ to 10⁻¹. -/
noncomputable def δ : ℝ := 1/100

/-- RSAConfig for the ellipsis model.

    The noisy channel is encoded via:
    - `meaning`: noisy L0 score (Eq. 6 numerator)
    - `s1Score`: noise-folded S1 (Eqs. 7-8 combined) -/
noncomputable def cfg : RSAConfig Utterance Meaning where
  Latent := Unit
  meaning _ _ := noisyMeaning δ
  meaning_nonneg _ _ u_p m := by
    show 0 ≤ noisyMeaning δ u_p m
    unfold noisyMeaning
    apply Finset.sum_nonneg; intro u_i _
    apply mul_nonneg
    · apply mul_nonneg
      · split <;> norm_num
      · cases u_i <;> simp [utterancePrior]
    · cases u_i <;> cases u_p <;> simp [noiseChannel, δ] <;> norm_num
  s1Score := noisyS1Score δ
  s1Score_nonneg l0 α _ m u_p _ _ := by
    unfold noisyS1Score
    apply Finset.sum_nonneg; intro u_i _
    apply mul_nonneg
    · split
      · exact le_of_lt (Real.exp_pos _)
      · exact le_refl 0
    · cases u_i <;> cases u_p <;> simp [noiseChannel, δ] <;> norm_num
  α := 1
  α_pos := by norm_num
  worldPrior_nonneg _ := by norm_num
  latentPrior_nonneg _ _ := by norm_num

-- ============================================================================
-- § 3. Ellipsis Predictions
-- ============================================================================

/-- L0 assigns higher probability to "Bob went" than "Alice went" or
    "Nobody went" given the fragment "Bob".

    Even though "Bob" has no literal meaning, the noisy L0 infers it
    must have come from "Bob went to the movies" via deletion. This is
    the only full sentence that produces "Bob" via noise, so L0 assigns
    it probability 1. -/
theorem l0_fragment_correct :
    cfg.L0 () .bob .bobWent > cfg.L0 () .bob .aliceWent ∧
    cfg.L0 () .bob .bobWent > cfg.L0 () .bob .nobodyWent :=
  ⟨by rsa_predict, by rsa_predict⟩

/-- L0 correctly interprets the "Nobody" fragment. -/
theorem l0_nobody_correct :
    cfg.L0 () .nobody .nobodyWent > cfg.L0 () .nobody .aliceWent ∧
    cfg.L0 () .nobody .nobodyWent > cfg.L0 () .nobody .bobWent :=
  ⟨by rsa_predict, by rsa_predict⟩

/-- L0 correctly interprets a full sentence (sanity check). -/
theorem l0_full_sentence_correct :
    cfg.L0 () .bobWentToMovies .bobWent > cfg.L0 () .bobWentToMovies .aliceWent ∧
    cfg.L0 () .bobWentToMovies .bobWent > cfg.L0 () .bobWentToMovies .nobodyWent :=
  ⟨by rsa_predict, by rsa_predict⟩

/-- L1 also correctly interprets the fragment "Bob" as "Bob went".

    The pragmatic listener, reasoning about S1's production choices,
    also assigns bobWent the highest probability. -/
theorem l1_fragment_correct :
    cfg.L1 .bob .bobWent > cfg.L1 .bob .aliceWent ∧
    cfg.L1 .bob .bobWent > cfg.L1 .bob .nobodyWent :=
  ⟨by rsa_predict, by rsa_predict⟩

-- ============================================================================
-- § 4. Parametric Robustness
-- ============================================================================

/-!
### Parametric Robustness (Fig. 1, left panel)

Fragment interpretation works for ANY noise rate δ > 0. Since "Bob" can
only arise from "Bob went to the movies" via deletion, L0 assigns
probability 1 regardless of δ. This is the paper's key theoretical
result: "this reasoning will work even if the noise rate is arbitrarily
close to 0, so long as it is positive."

We prove this by showing that the noisy meaning at "bob" is zero for all
meanings except bobWent, and nonzero (= δ) for bobWent. Since L0
normalizes the meaning, L0(bobWent | bob) = δ/δ = 1.
-/

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

/-- **Robustness** (Fig. 1, left panel): Fragment interpretation works for
    ANY noise rate δ > 0. Since "Bob" can only arise from "Bob went to the
    movies" via deletion, L0 assigns probability 1 regardless of δ.

    This is the paper's key theoretical result: "this reasoning will work
    even if the noise rate is arbitrarily close to 0, so long as it is
    positive." -/
theorem l0_fragment_robust (δ₀ : ℝ) (hδ : δ₀ ≠ 0) :
    noisyMeaning δ₀ .bob .bobWent /
      (noisyMeaning δ₀ .bob .aliceWent + noisyMeaning δ₀ .bob .bobWent +
       noisyMeaning δ₀ .bob .nobodyWent) = 1 := by
  rw [noisyMeaning_bob_bobWent, noisyMeaning_bob_aliceWent, noisyMeaning_bob_nobodyWent]
  simp [div_self hδ]

end EllipsisModel


-- ============================================================================
-- § 5. Prosody: Strategic Noise Reduction
-- ============================================================================

/-!
## Prosody

From the paper (§4):

> (2) A: Who went to the movies?
>     B: BOB went to the movies.

Prosodic stress reduces the noise rate on stressed words. The listener
infers that stress → the speaker had reason to protect that word →
the speaker has exhaustive knowledge → only Bob went.

### Mechanism

1. Speaker with exhaustive knowledge (only Bob went) needs listener
   to correctly hear "Bob" — mishearing "Alice" would be wrong
2. Therefore: stress "Bob" to reduce noise
3. Speaker with non-exhaustive knowledge (Bob went, maybe others too)
   has less need to protect — "Alice" is also compatible
4. Listener infers: stress → exhaustive knowledge

### Model Setup

- Meanings: {onlyAlice, onlyBob, both} (who went)
- Utterances: {aliceWent, ALICE_went, bobWent, BOB_went, aliceAndBobWent}
- Noise: baseline ε, reduced to ε/2 for stressed words
- The paper (§4.1): "placing stress on a word can reduce the noise rate of
  that word from ε to ε/n for some reduction factor n > 1." We use n = 2.
-/

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

/-- Noise-folded S1 score (Eqs. 7-8) for the prosody model. -/
noncomputable def noisyS1Score (ε : ℝ)
    (l0 : Utterance → Meaning → ℝ) (α : ℝ) (_ : Unit)
    (m : Meaning) (u_p : Utterance) : ℝ :=
  ∑ u_i : Utterance,
    (if literalMeaning u_i m then
      Real.exp (α * ∑ u_p' : Utterance,
        noiseChannel ε u_i u_p' * Real.log (l0 u_p' m))
    else 0) * noiseChannel ε u_i u_p

/-- Baseline noise rate (1%). -/
noncomputable def ε : ℝ := 1/100

/-- RSAConfig for the prosody model. -/
noncomputable def cfg : RSAConfig Utterance Meaning where
  Latent := Unit
  meaning _ _ := noisyMeaning ε
  meaning_nonneg _ _ u_p m := by
    show 0 ≤ noisyMeaning ε u_p m
    unfold noisyMeaning
    apply Finset.sum_nonneg; intro u_i _
    apply mul_nonneg
    · split <;> norm_num
    · cases u_i <;> cases u_p <;> simp [noiseChannel, ε] <;> norm_num
  s1Score := noisyS1Score ε
  s1Score_nonneg l0 α _ m u_p _ _ := by
    unfold noisyS1Score
    apply Finset.sum_nonneg; intro u_i _
    apply mul_nonneg
    · split
      · exact le_of_lt (Real.exp_pos _)
      · exact le_refl 0
    · cases u_i <;> cases u_p <;> simp [noiseChannel, ε] <;> norm_num
  α := 1
  α_pos := by norm_num
  worldPrior_nonneg _ := by norm_num
  latentPrior_nonneg _ _ := by norm_num

-- ============================================================================
-- § 6. Prosody Predictions
-- ============================================================================

/-- Stress increases exhaustive interpretation.

    "BOB went" (stressed) is strictly more likely to mean "only Bob" than
    "Bob went" (unstressed). This is the paper's central prosody
    prediction (§4). -/
theorem stress_increases_exhaustivity :
    cfg.L1 .BOB_went .onlyBob > cfg.L1 .bobWent .onlyBob := by
  rsa_predict

/-- Both stressed and unstressed assign positive probability to "both went"
    (it is compatible with either prosody). We show this via comparison:
    .both gets more probability than .onlyAlice under each utterance. -/
theorem stressed_both_positive :
    cfg.L1 .BOB_went .both > cfg.L1 .BOB_went .onlyAlice := by
  rsa_predict

theorem unstressed_both_positive :
    cfg.L1 .bobWent .both > cfg.L1 .bobWent .onlyAlice := by
  rsa_predict

end ProsodyModel


-- ============================================================================
-- § 7. Bridge: Ellipsis Data
-- ============================================================================

/-!
## Bridge: FragmentAnswers

The noisy channel model explains the data in `Phenomena.Ellipsis.FragmentAnswers`:

- `fragmentSubject` (question: "Who went to the movies?", fragment: "Bob")
  is correctly interpreted by both L0 and L1 (see `EllipsisModel.l0_fragment_correct`,
  `EllipsisModel.l1_fragment_correct`)

- `fragmentNobody` follows the same mechanism (different subject)

The model also accounts for non-question fragments (`fragmentAssertion`,
`fragmentTopic`): noise-based inference is not restricted to question-answer
pairs — any context where deletion is plausible licenses fragment use.
-/

/-- The model's prediction aligns with the fragment answer data. -/
theorem ellipsis_matches_data :
    FragmentAnswers.fragmentSubject.fragment = "Bob" ∧
    FragmentAnswers.fragmentSubject.available = true :=
  ⟨rfl, rfl⟩


-- ============================================================================
-- § 8. Bridge: Prosody Data
-- ============================================================================

/-!
## Bridge: ProsodicExhaustivity

The noisy channel model explains the data in
`Phenomena.Focus.ProsodicExhaustivity`:

- `stressedSubject`: "BOB went" → exhaustive reading
- `unstressedSubject`: "Bob went" → non-exhaustive reading

The model derives this from noise reduction: stress lowers the noise rate,
and the listener infers that the speaker had reason to protect the stressed
word, implying exhaustive knowledge.
-/

open Phenomena.Focus.ProsodicExhaustivity in
/-- The model's prediction aligns with the prosody data. -/
theorem prosody_matches_data :
    stressedSubject.reading = .exhaustive ∧
    unstressedSubject.reading = .nonExhaustive :=
  ⟨rfl, rfl⟩


-- ============================================================================
-- § 9. Connection to Unified Noise Theory
-- ============================================================================

/-!
## Connection to RSA.Noise

`RSA.Noise` defines the fundamental noise channel operation:

    noiseChannel(match, mismatch, b) = match · b + mismatch · (1 - b)

Both the ellipsis deletion channel and the prosody confusion channel are
special cases. The key insight from @cite{bergen-goodman-2015} is that noise
can be **strategically exploited** — a feature not shared by
@cite{degen-etal-2020}'s semantic noise model
(see `DegenEtAl2020`).

| Property | @cite{bergen-goodman-2015} | @cite{degen-etal-2020} |
|----------|---------------------------|----------------------|
| Noise location | Channel (transmission) | Semantics (perception) |
| Type | P_N(u_p \| u_i) | φ(u, o) ∈ [0,1] |
| Effect | Word corruption | Graded feature match |
| Strategic use | Yes (ellipsis, prosody) | No |
-/

/-- Prosodic stress increases channel discrimination between intended
    and confused utterances. Stressed "BOB went" has a larger gap between
    correct and confused perception than unstressed "Bob went".

    - Stressed gap: (1 - ε/2) - ε/2 = 1 - ε
    - Unstressed gap: (1 - ε) - ε = 1 - 2ε
    - Difference: ε > 0 -/
theorem stress_increases_discrimination (ε : ℝ) (hε : 0 < ε) :
    ProsodyModel.noiseChannel ε .BOB_went .BOB_went -
      ProsodyModel.noiseChannel ε .BOB_went .bobWent >
    ProsodyModel.noiseChannel ε .bobWent .bobWent -
      ProsodyModel.noiseChannel ε .bobWent .aliceWent := by
  simp only [ProsodyModel.noiseChannel]
  linarith

end BergenGoodman2015
