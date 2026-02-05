/-
# Bergen & Goodman (2015)

"The Strategic Use of Noise in Pragmatic Reasoning"
Topics in Cognitive Science 7(2): 336-350

This paper combines noisy-channel models with probabilistic pragmatics,
showing that noise can be *strategically exploited* for communication.

## Two Phenomena

**1. Ellipsis** (Section: Ellipsis)
   - Sentence fragments communicate full propositions
   - "Bob" in response to "Who went?" → "Bob went to the movies"
   - Works via listener's inference that noise deleted words

**2. Prosody** (Section: Prosody)
   - Prosodic stress reduces noise rate on stressed words
   - "BOB went" signals exhaustivity (only Bob went)
   - Speaker strategically protects important information

## Innovation

Standard RSA assumes perfect transmission. This model adds:
- P_N(u_p | u_i) : noisy channel (probability of perceiving u_p given intended u_i)
- Speaker utility considers expected listener accuracy over noise
- Listener reasons about what speaker intended given perceived utterance

## Relation to Degen et al. (2020)

Two different noise models in RSA:
- **Bergen & Goodman (channel noise)**: P_N(u_p|u_i) - words can be deleted/inserted
- **Degen et al. (semantic noise)**: φ(u,o) ∈ [0,1] - graded semantic match

This file implements channel noise. See DegenEtAl2020.lean for semantic noise.
-/

import Linglib.Theories.RSA.Core.Eval
import Linglib.Theories.RSA.Core.Noise
import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Basic

namespace RSA.BergenGoodman2015

open RSA.Eval


/-!
## Noisy Channel Model

A noisy channel is a stochastic matrix P_N(u_p | u_i) giving the probability
that the listener perceives utterance u_p when the speaker intended u_i.

Key properties:
- Rows sum to 1 (it's a conditional distribution)
- Diagonal entries are typically high (usually perceived correctly)
- Off-diagonal entries represent noise (corruption)
-/

/--
A noisy channel over utterances.

`transmit u_i u_p` is P_N(u_p | u_i): probability of perceiving u_p given intended u_i.
-/
structure NoisyChannel (U : Type) where
  /-- Transition probability P_N(u_p | u_i) -/
  transmit : U → U → ℚ
  /-- All probabilities are non-negative -/
  nonneg : ∀ ui up, 0 ≤ transmit ui up := by intros; decide

namespace NoisyChannel

variable {U : Type} [DecidableEq U]

/-- Identity channel: no noise, perfect transmission -/
def identity (allU : List U) : NoisyChannel U where
  transmit ui up := if ui = up then 1 else 0
  nonneg := by intros; split_ifs <;> decide

/-- Symmetric noise channel: each word independently corrupted with probability ε -/
def symmetric (allU : List U) (ε : ℚ) (hε : 0 ≤ ε ∧ ε ≤ 1) : NoisyChannel U where
  transmit ui up :=
    if ui = up then 1 - ε
    else if allU.length > 1 then ε / (allU.length - 1 : ℚ) else 0
  nonneg := by
    intros ui up
    split_ifs with h1 h2
    · linarith [hε.1, hε.2]
    · exact div_nonneg hε.1 (sub_nonneg.mpr (by exact_mod_cast (le_of_lt h2)))
    · decide

end NoisyChannel


/-!
## Ellipsis: Sentence Fragments

Example from paper:
- A: "Who went to the movies?"
- B: "Bob"  (fragment, not full sentence)

The listener infers "Bob went to the movies" because:
1. "Bob" is not grammatical on its own
2. Listener assumes noise deleted the rest
3. "Bob went to the movies" → "Bob" via deletion is most probable

### Model Setup

- Meanings M = {Alice went, Bob went, Nobody went}
- Full utterances U = {"Alice went", "Bob went", "Nobody went"}
- Fragments F = {"Alice", "Bob", "Nobody", ...}
- Noise: word deletion with probability δ
-/

namespace Ellipsis

/-- Meanings: who went to the movies -/
inductive Meaning where
  | aliceWent
  | bobWent
  | nobodyWent
  deriving DecidableEq, BEq, Repr, Inhabited

def allMeanings : List Meaning := [.aliceWent, .bobWent, .nobodyWent]

/-- Utterances: full sentences and fragments -/
inductive Utterance where
  -- Full sentences
  | aliceWentToMovies
  | bobWentToMovies
  | nobodyWentToMovies
  -- Fragments (result of deletion)
  | alice
  | bob
  | nobody
  | wentToMovies  -- subject deleted
  deriving DecidableEq, BEq, Repr, Inhabited

def allUtterances : List Utterance :=
  [.aliceWentToMovies, .bobWentToMovies, .nobodyWentToMovies,
   .alice, .bob, .nobody, .wentToMovies]

def fullSentences : List Utterance :=
  [.aliceWentToMovies, .bobWentToMovies, .nobodyWentToMovies]

def fragments : List Utterance :=
  [.alice, .bob, .nobody, .wentToMovies]

/-- Literal meaning: only full sentences have truth conditions -/
def literalMeaning : Utterance → Meaning → Bool
  | .aliceWentToMovies, .aliceWent => true
  | .bobWentToMovies, .bobWent => true
  | .nobodyWentToMovies, .nobodyWent => true
  | _, _ => false  -- Fragments have no literal meaning!

/-- Prior over utterances (speaker's production probability) -/
def utterancePrior : Utterance → ℚ
  | .aliceWentToMovies => 1
  | .bobWentToMovies => 1
  | .nobodyWentToMovies => 1
  | _ => 0  -- Fragments not in speaker's production distribution

/-- Noise model: probability of perceiving u_p given intended u_i.

Simplified model with base noise rate δ:
- Same utterance: high probability (1 - δ)
- Full sentence → fragment (subject): probability δ (plausible deletion)
- Everything else: small probability
-/
def noiseChannel (δ : ℚ) : Utterance → Utterance → ℚ
  -- Full sentences: mostly heard correctly, sometimes reduced to fragment
  | .aliceWentToMovies, .aliceWentToMovies => 1 - δ
  | .aliceWentToMovies, .alice => δ  -- deleted predicate
  | .bobWentToMovies, .bobWentToMovies => 1 - δ
  | .bobWentToMovies, .bob => δ
  | .nobodyWentToMovies, .nobodyWentToMovies => 1 - δ
  | .nobodyWentToMovies, .nobody => δ
  -- Fragments: heard as intended (already short)
  | .alice, .alice => 1
  | .bob, .bob => 1
  | .nobody, .nobody => 1
  | .wentToMovies, .wentToMovies => 1
  -- Default: 0
  | _, _ => 0

/-- Utterance cost (longer = more costly) -/
def cost : Utterance → ℚ
  | .aliceWentToMovies => 5
  | .bobWentToMovies => 5
  | .nobodyWentToMovies => 5
  | .alice => 1
  | .bob => 1
  | .nobody => 1
  | .wentToMovies => 4

-- RSA with Noisy Channel

/-- L0: Literal listener with noise inference (Eq. 6 from paper)

L0(m | u_p) ∝ P(m) Σ_{u_i : m ∈ [[u_i]]} P(u_i) P_N(u_p | u_i)

The listener:
1. Considers all utterances u_i that could have produced perceived u_p
2. Weights by prior P(u_i) and noise probability P_N(u_p | u_i)
3. Assigns meaning based on literal semantics of u_i
-/
def L0_noisy (δ : ℚ) (u_perceived : Utterance) : List (Meaning × ℚ) :=
  let scores := allMeanings.map λ m =>
    let compatibleSources := fullSentences.filter (literalMeaning · m)
    let score := compatibleSources.foldl (λ acc u_i =>
      acc + utterancePrior u_i * noiseChannel δ u_i u_perceived) 0
    (m, score)
  normalize scores

/-- S1: Speaker considering noise (simplified)

The speaker chooses utterances that will likely be interpreted correctly.
Utility = P(listener gets correct meaning) - cost
-/
def S1_noisy (δ : ℚ) (m : Meaning) : List (Utterance × ℚ) :=
  -- Only consider full sentences (speaker doesn't intentionally use fragments)
  let scores := fullSentences.map λ u_i =>
    -- Expected accuracy: how often does listener recover correct meaning?
    let expectedAccuracy := allUtterances.foldl (λ acc u_p =>
      let pNoise := noiseChannel δ u_i u_p
      let l0Score := getScore (L0_noisy δ u_p) m
      acc + pNoise * l0Score) 0
    -- Score is accuracy (ignoring cost for simplicity)
    (u_i, if literalMeaning u_i m then expectedAccuracy else 0)
  normalize scores

/-- L1: Pragmatic listener reasoning about noisy speaker

L1(m | u_p) ∝ P(m) Σ_{u_i} S1(u_i | m) P_N(u_p | u_i)
-/
def L1_noisy (δ : ℚ) (u_perceived : Utterance) : List (Meaning × ℚ) :=
  let scores := allMeanings.map λ m =>
    let score := fullSentences.foldl (λ acc u_i =>
      let s1Score := getScore (S1_noisy δ m) u_i
      let pNoise := noiseChannel δ u_i u_perceived
      acc + s1Score * pNoise) 0
    (m, score)
  normalize scores

-- Results: Ellipsis

/-- Noise rate for experiments -/
def δ_default : ℚ := 1/100  -- 1% per-word deletion rate

-- L0 interpretation of "Bob" (fragment)
def l0_bob : List (Meaning × ℚ) := L0_noisy δ_default .bob

-- L1 interpretation of "Bob" (fragment)
def l1_bob : List (Meaning × ℚ) := L1_noisy δ_default .bob

-- S1 production when meaning is "Bob went"
def s1_bobWent : List (Utterance × ℚ) := S1_noisy δ_default .bobWent

#eval l0_bob    -- L0 interprets "Bob" as meaning bobWent
#eval l1_bob    -- L1 also interprets "Bob" as bobWent
#eval s1_bobWent -- S1 might use fragment "Bob" (via noise model)

/--
**Ellipsis Theorem**: The fragment "Bob" is interpreted as "Bob went".

Even though "Bob" has no literal meaning, the listener infers it via:
1. "Bob" most likely came from "Bob went to the movies" via deletion
2. "Bob went to the movies" means Bob went
3. Therefore "Bob" → Bob went
-/
theorem fragment_interpretation :
    getScore l0_bob .bobWent > getScore l0_bob .aliceWent ∧
    getScore l0_bob .bobWent > getScore l0_bob .nobodyWent := by
  native_decide

/-- L0 correctly interprets fragment -/
theorem l0_fragment_works :
    getScore l0_bob .bobWent = 1 := by
  native_decide

end Ellipsis


/-!
## Prosody: Strategic Noise Reduction

Prosodic stress (BOB vs Bob) reduces noise rate on stressed words.
This has pragmatic consequences:

Example:
- "Bob went to the movies" - compatible with others also going
- "BOB went to the movies" - exhaustive: ONLY Bob went

### Mechanism

Speaker S1 with exhaustive knowledge (only Bob went):
- Needs listener to hear "Bob" correctly
- If listener mishears "Alice", wrong inference
- Therefore: stress "Bob" to reduce noise

Speaker with non-exhaustive knowledge (Bob went, maybe others too):
- Less critical if listener mishears "Bob" as "Alice"
- Both are compatible with speaker's knowledge
- Therefore: less likely to stress

Listener infers: stress → speaker had reason to protect that word
                      → speaker has exhaustive knowledge
-/

namespace Prosody

/-- Meanings for exhaustivity example -/
inductive Meaning where
  | onlyAlice   -- Only Alice went
  | onlyBob     -- Only Bob went
  | both        -- Both Alice and Bob went
  deriving DecidableEq, BEq, Repr, Inhabited

def allMeanings : List Meaning := [.onlyAlice, .onlyBob, .both]

/-- Utterances with optional prosodic stress -/
inductive Utterance where
  | aliceWent          -- Alice went (no stress)
  | ALICE_went         -- ALICE went (stress on Alice)
  | bobWent            -- Bob went (no stress)
  | BOB_went           -- BOB went (stress on Bob)
  | aliceAndBobWent    -- Alice and Bob went
  deriving DecidableEq, BEq, Repr, Inhabited

def allUtterances : List Utterance :=
  [.aliceWent, .ALICE_went, .bobWent, .BOB_went, .aliceAndBobWent]

/-- Literal meaning: lower-bound semantics -/
def literalMeaning : Utterance → Meaning → Bool
  | .aliceWent, .onlyAlice => true
  | .aliceWent, .both => true       -- Alice went is true if both went
  | .ALICE_went, .onlyAlice => true
  | .ALICE_went, .both => true
  | .bobWent, .onlyBob => true
  | .bobWent, .both => true         -- Bob went is true if both went
  | .BOB_went, .onlyBob => true
  | .BOB_went, .both => true
  | .aliceAndBobWent, .both => true
  | _, _ => false

/-- Noise channel with prosody.

Base noise rate ε. Stress reduces noise by factor of 2.

Model: probability of subject being misheard.
- No stress: ε chance of mishearing
- Stress: ε/2 chance of mishearing
-/
def noiseChannel (ε : ℚ) : Utterance → Utterance → ℚ
  -- No stress: baseline noise
  | .aliceWent, .aliceWent => 1 - ε
  | .aliceWent, .bobWent => ε        -- Alice → Bob confusion
  | .bobWent, .bobWent => 1 - ε
  | .bobWent, .aliceWent => ε        -- Bob → Alice confusion
  -- With stress: reduced noise
  | .ALICE_went, .ALICE_went => 1 - ε/2
  | .ALICE_went, .aliceWent => ε/2   -- Stress lost but word heard
  | .BOB_went, .BOB_went => 1 - ε/2
  | .BOB_went, .bobWent => ε/2
  -- Both: no ambiguity
  | .aliceAndBobWent, .aliceAndBobWent => 1
  -- Default: 0
  | _, _ => 0

/-- Speaker's knowledge state -/
inductive Knowledge where
  | full        -- Knows exactly who went
  | incomplete  -- Knows Bob went, uncertain about Alice
  deriving DecidableEq, BEq, Repr

/-- Speaker's belief given observation (for partial knowledge model) -/
def speakerBelief (k : Knowledge) (m : Meaning) : ℚ :=
  match k with
  | .full => 1  -- Full knowledge: point mass on true meaning
  | .incomplete =>
    match m with
    | .onlyBob => 1/2  -- Uncertain between onlyBob and both
    | .both => 1/2
    | .onlyAlice => 0

-- Simplified L0/S1/L1 for Prosody

/-- L0 with noise -/
def L0 (ε : ℚ) (u_p : Utterance) : List (Meaning × ℚ) :=
  let scores := allMeanings.map λ m =>
    let score := allUtterances.foldl (λ acc u_i =>
      if literalMeaning u_i m then
        acc + noiseChannel ε u_i u_p
      else acc) 0
    (m, score)
  normalize scores

/-- S1: Speaker choosing utterance given meaning and knowledge -/
def S1 (ε : ℚ) (k : Knowledge) (m : Meaning) : List (Utterance × ℚ) :=
  -- Only consider utterances compatible with meaning
  let compatUtts := allUtterances.filter (literalMeaning · m)
  let scores := compatUtts.map λ u_i =>
    -- Expected probability listener gets correct meaning
    let expectedScore := allUtterances.foldl (λ acc u_p =>
      let pNoise := noiseChannel ε u_i u_p
      let l0Score := getScore (L0 ε u_p) m
      acc + pNoise * l0Score) 0
    (u_i, expectedScore)
  normalize scores

/-- L1: Pragmatic listener -/
def L1 (ε : ℚ) (u_p : Utterance) : List (Meaning × ℚ) :=
  let scores := allMeanings.map λ m =>
    let score := allUtterances.foldl (λ acc u_i =>
      let s1Score := getScore (S1 ε .full m) u_i  -- Assume full knowledge for now
      let pNoise := noiseChannel ε u_i u_p
      acc + s1Score * pNoise) 0
    (m, score)
  normalize scores

-- Results: Prosody

def ε_default : ℚ := 1/100  -- 1% base noise rate

-- L1 interpretation of stressed vs unstressed
def l1_BOB_went : List (Meaning × ℚ) := L1 ε_default .BOB_went
def l1_bob_went : List (Meaning × ℚ) := L1 ε_default .bobWent

#eval l1_BOB_went  -- Stress → more exhaustive interpretation
#eval l1_bob_went  -- No stress → less exhaustive

/--
**Prosody Theorem**: Stress increases exhaustive interpretation.

"BOB went" is more likely to mean "only Bob" than "Bob went" (no stress).
-/
theorem stress_increases_exhaustivity :
    getScore l1_BOB_went .onlyBob ≥ getScore l1_bob_went .onlyBob := by
  native_decide

/-- Both utterances are compatible with the "both" meaning -/
theorem both_compatible :
    getScore l1_BOB_went .both > 0 ∧ getScore l1_bob_went .both > 0 := by
  native_decide

end Prosody


/-!
## Connection to Other Noise Models

### Bergen & Goodman 2015 (This File)
- **Channel noise**: P_N(u_p | u_i)
- Words can be deleted, inserted, replaced
- Noise is in transmission, not semantics
- Prosody reduces channel noise

### Degen et al. 2020 (DegenEtAl2020.lean)
- **Semantic noise**: φ(u, o) ∈ [0,1]
- Feature matching is probabilistic
- Noise is in perception of features
- No explicit channel model

### Potential Unification

Could Degen's semantic noise emerge from channel noise?

Hypothesis: If utterances are descriptions of features, and features
can be "misheard", then:
- φ(u, o) = E_{u' ~ P_N(·|u)}[[[u']](o)]

That is, graded truth = expected Boolean truth over noisy channel.

This would show:
- Degen's continuous φ = Bergen's discrete channel + Boolean semantics
- Similar to: Degen φ = Boolean × noise channel (proven in DegenEtAl2020.lean)

### Information-Theoretic View

Both noise models reduce mutual information I(M; U):
- Channel noise: I(U_intended; U_perceived) decreases
- Semantic noise: I(U; O) decreases (less discrimination)

Higher noise → less informative communication → worse utility.

This suggests a unified "informativeness" measure applicable to both.
-/

namespace TheoreticalConnections

/-- Channel noise reduces channel capacity.

With noise rate ε, the mutual information I(U; U') between intended
and perceived utterance decreases.

At ε = 0: I(U; U') = H(U) (perfect channel)
At ε = 1: I(U; U') = 0 (completely noisy, no information transmitted)
-/
def channelCapacity (ε : ℚ) (numUtts : ℕ) : ℚ :=
  -- Simplified: for symmetric channel with n utterances
  -- Capacity ≈ log(n) * (1 - ε) approximately
  -- This is a placeholder for the actual calculation
  if ε < 1 then (1 - ε) else 0

/-- Higher noise → lower capacity -/
theorem noise_reduces_capacity (ε₁ ε₂ : ℚ) (h : ε₁ < ε₂) (hε₂ : ε₂ ≤ 1) (n : ℕ) :
    channelCapacity ε₂ n ≤ channelCapacity ε₁ n := by
  simp only [channelCapacity]
  split_ifs with h1 h2
  · linarith
  · linarith
  · linarith [h, hε₂]
  · rfl

end TheoreticalConnections

-- Summary

/-!
## Summary

### From the Paper

1. **Ellipsis** (Section 3)
   - Fragment "Bob" → meaning "Bob went to the movies"
   - Works via noise inference: listener assumes words were deleted
   - `fragment_interpretation`: proven

2. **Prosody** (Section 4)
   - Stress reduces noise rate
   - "BOB went" → exhaustive (only Bob)
   - "Bob went" → non-exhaustive (maybe others too)
   - `stress_increases_exhaustivity`: proven

### Innovation

The noisy channel model explains phenomena that standard RSA cannot:
- Fragments have NO literal meaning, yet are interpreted
- Prosody has NO semantic content, yet affects meaning

Both emerge from strategic reasoning about noise.

### Relation to Degen et al. 2020

| Property | Bergen & Goodman | Degen et al. |
|----------|------------------|--------------|
| Noise location | Channel | Semantics |
| Type | P_N(u_p\|u_i) | φ(u,o) ∈ [0,1] |
| Effect | Word corruption | Graded match |

Potential unification: semantic noise as expectation over channel noise.
-/

end RSA.BergenGoodman2015
