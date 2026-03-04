import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Pragmatics.RSA.Core.Noise

/-!
# @cite{schlotterbeck-wang-2023} — Incremental RSA for Adjective Ordering
@cite{cohn-gordon-goodman-potts-2019} @cite{degen-etal-2020}

Schlotterbeck, F. & Wang, H. (2023). An incremental RSA model for adjective
ordering preferences in referential visual context. *Proceedings of the Society
for Computation in Linguistics (SCiL)* 6, 121–132.

## The Model

The incremental sequence speaker (S1^inc) produces adjective–noun sequences
word-by-word. At each step the utility is the incremental listener's posterior.
The trajectory score accumulates utility across all prefixes:

  S1^inc(w₁,...,wₙ | r) ∝ ∏ₖ U(w₁,...,wₖ; r)

where U(w⃗; r) = exp(β · log L0^inc(r | w⃗)) and the paper sets β = 1 in all
reported simulations. With β = 1, no cost, and uniform language prior, this
simplifies to:

  S1^inc(w₁,...,wₙ | r) = ∏ₖ L0(r | w₁,...,wₖ)

The model uses continuous/noisy semantics (@cite{degen-etal-2020}) where each
word applies with reliability v (correct application) or 1 − v (noise).

**Key insight**: With strictly positive noisy semantics, the prefix meaning
is a product of per-word terms, and multiplication commutes. Therefore the
full-sequence L0 posterior is order-independent:
L0(r | w₁, w₂) = L0(r | w₂, w₁). In the paper's batch-normalized model,
where S1^inc scores are normalized once over all trajectories, the ordering
preference ratio S1^inc(adj₁,adj₂,n|r) / S1^inc(adj₂,adj₁,n|r) reduces
entirely to the first-word L0 posterior ratio L0(r|adj₁) / L0(r|adj₂).

## Formalization

This uses `RSAConfig`'s sequential infrastructure (following
@cite{cohn-gordon-goodman-potts-2019} and @cite{waldon-degen-2021}):

- `Ctx = List Word` — the prefix produced so far
- `transition ctx w = ctx ++ [w]` — append the next word
- `initial = []` — start with empty prefix
- `meaning` uses continuous/noisy semantics (`lexContinuousQ`) with
  scene-dependent reliability parameters

Predictions use `trajectoryProb` for ordering preferences and `S1_at` for
first-word informativity, proved via `rsa_predict`.

## Findings

| # | Finding | Theorem |
|---|---------|---------|
| 1 | Prefix meaning is order-independent | `prefix_meaning_swap` |
| 2 | Size discriminatory → size-first preferred | `size_first_when_size_discriminates` |
| 3 | Equal discrimination + color reliable → color-first | `color_first_when_color_reliable` |
| 4 | Both orderings identify the target (A) | `both_orderings_identify_target_A` |
| 5 | Both orderings identify the target (B) | `both_orderings_identify_target_B` |

## Connections

- **Noise theory**: `lexContinuousQ` instantiates the unified noise channel
  from `RSA.Core.Noise`. See `lexContinuous_as_noiseChannel`.
- **PoE structure**: `prefix_meaning_product` shows two-word prefix meaning
  decomposes as a product of per-word semantics, matching
  @cite{degen-etal-2020}'s Product of Experts.
- **Incremental RSA**: Extends @cite{cohn-gordon-goodman-potts-2019} with
  scene-parameterized continuous semantics.
- **Psychophysics**: The paper's size perception noise is parameterized by
  Weber fractions — the just-noticeable size difference is proportional to
  absolute size (@cite{luce-1959}). `Core.Agent.PsychophysicalChoice`
  derives Weber-like intensity ratios from Stevens power law + JND
  thresholds (`stevens_jndL_intensity_ratio`). A deeper integration could
  derive the `sRel` reliability parameter from a `StevensScale` exponent
  rather than stipulating it, grounding the noise in the psychophysical
  theory layer.

## Simplifications

The paper's full model includes components not formalized here:

1. **Gaussian+binomial perception**: The paper models size via Gaussian
   distributions with Weber fractions and color via binomial noise ε
   (@cite{degen-etal-2020}). `Core.Agent.Psychophysics` formalizes the
   Stevens power law and multidimensional decomposition that underlie
   Weber's law; a future integration could derive size reliability from
   this framework. We currently use a simpler noise model with flat
   reliability parameters sRel and cRel.
2. **Language model P_Lang**: The paper constrains the S1 vocabulary at each
   step to grammatically valid continuations (noun vs adjective). Our S1
   distributes over all 6 words at each step. This does not affect the
   qualitative ordering predictions.
3. **S1^{inc_utt} vs S1^inc**: The paper defines both a word-level speaker
   (S1^inc, used for data fitting with β = 1) and an utterance-level speaker
   (S1^{inc_utt}). We formalize S1^inc.
4. **Bias parameter b**: The paper includes a prior bias b for size-first
   ordering (to account for language-specific defaults). We omit this.

The specific reliability values (sRel, cRel) are chosen to demonstrate the
qualitative predictions — they are not taken from the paper's fitted values.
-/

set_option autoImplicit false

namespace Phenomena.WordOrder.Studies.SchlotterbeckWang2023

open RSA

-- ============================================================================
-- §1. Domain Types
-- ============================================================================

/-- Referents in the reference game. Flat enum with `Fintype` for `RSAConfig`. -/
inductive Referent where
  | bigBlue | bigGreen | smallBlue | smallGreen | smallRed
  deriving DecidableEq, Fintype, BEq, Repr

/-- Words available to the speaker: size adjectives, color adjectives, noun. -/
inductive Word where
  | big | small | blue | green | red | sticker
  deriving DecidableEq, Fintype, BEq, Repr

-- ============================================================================
-- §2. Boolean Semantics
-- ============================================================================

/-- Whether a word is veridically true of a referent. -/
def wordApplies : Word → Referent → Bool
  | .big,     .bigBlue  | .big,     .bigGreen  => true
  | .small,   .smallBlue | .small,  .smallGreen | .small, .smallRed => true
  | .blue,    .bigBlue  | .blue,    .smallBlue  => true
  | .green,   .bigGreen | .green,   .smallGreen => true
  | .red,     .smallRed => true
  | .sticker, _         => true
  | _,        _         => false

-- ============================================================================
-- §3. Continuous Semantics
-- ============================================================================

/-- Perceptual reliability for each word type: size words use `sRel`,
    color words use `cRel`, the noun "sticker" applies universally. -/
def reliabilityQ (sRel cRel : ℚ) : Word → ℚ
  | .big | .small         => sRel
  | .blue | .green | .red => cRel
  | .sticker              => 1

/-- Noisy word meaning: returns reliability if the word truly applies,
    noise floor (1 − reliability) otherwise.
    Simplified from @cite{degen-etal-2020}'s continuous semantics. -/
def lexContinuousQ (sRel cRel : ℚ) (w : Word) (r : Referent) : ℚ :=
  if wordApplies w r then reliabilityQ sRel cRel w else 1 - reliabilityQ sRel cRel w

/-- Prefix meaning: product of noisy word meanings over a word sequence.
    This implements the Product of Experts model from @cite{degen-etal-2020}:
    each word contributes an independent noisy channel value. -/
def prefixMeaningQ (sRel cRel : ℚ) (pfx : List Word) (r : Referent) : ℚ :=
  pfx.foldl (λ acc w => acc * lexContinuousQ sRel cRel w r) 1

private theorem lexContinuousQ_nonneg (sRel cRel : ℚ) (w : Word) (r : Referent)
    (hs : 0 ≤ sRel ∧ sRel ≤ 1) (hc : 0 ≤ cRel ∧ cRel ≤ 1) :
    0 ≤ lexContinuousQ sRel cRel w r := by
  unfold lexContinuousQ
  split
  · cases w <;> simp only [reliabilityQ] <;> linarith [hs.1, hc.1]
  · cases w <;> simp only [reliabilityQ] <;> linarith [hs.2, hc.2]

private theorem prefixMeaningQ_nonneg (sRel cRel : ℚ) (pfx : List Word) (r : Referent)
    (hs : 0 ≤ sRel ∧ sRel ≤ 1) (hc : 0 ≤ cRel ∧ cRel ≤ 1) :
    0 ≤ prefixMeaningQ sRel cRel pfx r := by
  unfold prefixMeaningQ
  suffices ∀ (l : List Word) (init : ℚ), 0 ≤ init →
      0 ≤ l.foldl (λ acc w => acc * lexContinuousQ sRel cRel w r) init by
    exact this pfx 1 one_pos.le
  intro l; induction l with
  | nil => intro init h; exact h
  | cons w ws ih =>
    intro init hinit; simp only [List.foldl]
    exact ih _ (mul_nonneg hinit (lexContinuousQ_nonneg sRel cRel w r hs hc))

/-- Strict positivity: with reliability strictly between 0 and 1, every
    word–referent pair has a strictly positive noisy meaning value. This
    ensures the incremental L0 is well-defined (no zero denominators). -/
theorem lexContinuousQ_pos (sRel cRel : ℚ) (w : Word) (r : Referent)
    (hs : 0 < sRel ∧ sRel < 1) (hc : 0 < cRel ∧ cRel < 1) :
    0 < lexContinuousQ sRel cRel w r := by
  cases w <;> cases r <;>
    simp [lexContinuousQ, wordApplies, reliabilityQ] <;>
    linarith [hs.1, hs.2, hc.1, hc.2]

-- ============================================================================
-- §4. Scenes
-- ============================================================================

/-- **Scene A**: Size-discriminatory scene.
    Objects: {big-blue, small-blue, small-green, small-red}. Target: big-blue.
    "big" uniquely identifies the target (1/4 objects are big). -/
def sceneAMembers : Referent → Bool
  | .bigBlue | .smallBlue | .smallGreen | .smallRed => true
  | _ => false

/-- **Scene B**: Equal-discrimination scene with color more reliable.
    Objects: {big-blue, big-green, small-blue, small-green}. Target: big-blue.
    Both "big" and "blue" narrow to 2/4 referents. -/
def sceneBMembers : Referent → Bool
  | .bigBlue | .bigGreen | .smallBlue | .smallGreen => true
  | _ => false

/-- The target referent in both scenes. -/
def target : Referent := .bigBlue

-- ============================================================================
-- §5. RSAConfig Factory
-- ============================================================================

/-- Incremental RSA for adjective ordering, parameterized by scene and
    perceptual reliability. Uses `RSAConfig`'s sequential infrastructure:
    - L0 uses product-of-experts noisy semantics
    - S1 uses identity scoring (β = 1, no cost)
    - `trajectoryProb` chains word-by-word S1 probabilities -/
noncomputable def mkIncRSA (scene : Referent → Bool) (sRel cRel : ℚ)
    (hs : 0 ≤ sRel ∧ sRel ≤ 1) (hc : 0 ≤ cRel ∧ cRel ≤ 1) :
    RSAConfig Word Referent where
  Ctx := List Word
  meaning ctx _ u w :=
    if scene w then (prefixMeaningQ sRel cRel (ctx ++ [u]) w : ℝ) else 0
  meaning_nonneg _ _ _ w := by
    split
    · exact Rat.cast_nonneg.mpr (prefixMeaningQ_nonneg _ _ _ w hs hc)
    · exact le_refl _
  s1Score l0 _ _ w u := l0 u w
  s1Score_nonneg _ _ _ _ _ hl _ := hl _ _
  α := 1
  α_pos := one_pos
  transition ctx w := ctx ++ [w]
  initial := []
  latentPrior_nonneg _ _ := by norm_num
  worldPrior_nonneg _ := by norm_num

/-- Scene A config: sizeRel = 99/100, colorRel = 95/100. -/
noncomputable def sceneACfg : RSAConfig Word Referent :=
  mkIncRSA sceneAMembers (99/100) (95/100)
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩

/-- Scene B config: sizeRel = 80/100, colorRel = 95/100. -/
noncomputable def sceneBCfg : RSAConfig Word Referent :=
  mkIncRSA sceneBMembers (80/100) (95/100)
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩

-- ============================================================================
-- §6. Utterances
-- ============================================================================

/-- Size-first ordering for the big-blue target. -/
def sizeFirstUtt : List Word := [.big, .blue, .sticker]

/-- Color-first ordering for the big-blue target. -/
def colorFirstUtt : List Word := [.blue, .big, .sticker]

-- ============================================================================
-- §7. Prefix Meaning Properties
-- ============================================================================

/-- Prefix meaning for two words is order-independent. This follows from
    commutativity of ℚ multiplication: foldl(*lex) 1 [a,b] = lex(a)·lex(b)
    = lex(b)·lex(a) = foldl(*lex) 1 [b,a]. -/
theorem prefix_meaning_swap (sRel cRel : ℚ) (a b : Word) (r : Referent) :
    prefixMeaningQ sRel cRel [a, b] r =
    prefixMeaningQ sRel cRel [b, a] r := by
  simp only [prefixMeaningQ, List.foldl]; ring

/-- Prefix meaning for three words is independent of the first two words'
    order. Swapping the adjectives before the noun does not change the
    product semantics. -/
theorem prefix_meaning_swap3 (sRel cRel : ℚ) (a b c : Word) (r : Referent) :
    prefixMeaningQ sRel cRel [a, b, c] r =
    prefixMeaningQ sRel cRel [b, a, c] r := by
  simp only [prefixMeaningQ, List.foldl]; ring

/-- Two-word prefix meaning decomposes as a product of per-word noisy meanings.
    This is the Product of Experts (PoE) structure from @cite{degen-etal-2020}:
    each word contributes an independent noisy channel value. -/
theorem prefix_meaning_product (sRel cRel : ℚ) (a b : Word) (r : Referent) :
    prefixMeaningQ sRel cRel [a, b] r =
    lexContinuousQ sRel cRel a r * lexContinuousQ sRel cRel b r := by
  simp only [prefixMeaningQ, List.foldl, one_mul]

-- ============================================================================
-- §8. Predictions (via trajectoryProb)
-- ============================================================================

set_option maxHeartbeats 16000000 in
/-- **Finding**: When size has high discriminatory power (Scene A),
    S1^inc prefers size-first ordering. -/
theorem size_first_when_size_discriminates :
    sceneACfg.trajectoryProb () target sizeFirstUtt >
    sceneACfg.trajectoryProb () target colorFirstUtt := by
  rsa_predict

set_option maxHeartbeats 16000000 in
/-- **Finding**: When both properties discriminate equally but color is
    more reliable (Scene B), S1^inc prefers color-first ordering. -/
theorem color_first_when_color_reliable :
    sceneBCfg.trajectoryProb () target colorFirstUtt >
    sceneBCfg.trajectoryProb () target sizeFirstUtt := by
  rsa_predict

/-- The ordering preference flips between scenes: Scene A prefers size-first,
    Scene B prefers color-first. This captures @cite{schlotterbeck-wang-2023}'s
    key prediction: the preferred ordering depends on the discriminatory
    structure of the scene, not a fixed ordering rule. -/
theorem ordering_preference_flips :
    sceneACfg.trajectoryProb () target sizeFirstUtt >
    sceneACfg.trajectoryProb () target colorFirstUtt ∧
    sceneBCfg.trajectoryProb () target colorFirstUtt >
    sceneBCfg.trajectoryProb () target sizeFirstUtt :=
  ⟨size_first_when_size_discriminates, color_first_when_color_reliable⟩

-- ============================================================================
-- §9. First-Word Informativity (via S1_at)
-- ============================================================================

set_option maxHeartbeats 16000000 in
/-- In Scene A, "big" is more informative than "blue" about the target. -/
theorem big_more_informative_A :
    sceneACfg.S1_at ([] : List Word) () target .big >
    sceneACfg.S1_at ([] : List Word) () target .blue := by
  rsa_predict

set_option maxHeartbeats 16000000 in
/-- In Scene B, "blue" is more informative than "big" about the target. -/
theorem blue_more_informative_B :
    sceneBCfg.S1_at ([] : List Word) () target .blue >
    sceneBCfg.S1_at ([] : List Word) () target .big := by
  rsa_predict

-- ============================================================================
-- §10. Target Identification
-- ============================================================================

/-- After hearing both adjectives, the meaning function assigns highest
    value to the target among Scene A members. -/
theorem both_orderings_identify_target_A :
    ∀ r : Referent, sceneAMembers r = true → r ≠ target →
      prefixMeaningQ (99/100) (95/100) [.big, .blue] target >
      prefixMeaningQ (99/100) (95/100) [.big, .blue] r := by
  native_decide

/-- After hearing both adjectives, the meaning function assigns highest
    value to the target among Scene B members. -/
theorem both_orderings_identify_target_B :
    ∀ r : Referent, sceneBMembers r = true → r ≠ target →
      prefixMeaningQ (80/100) (95/100) [.big, .blue] target >
      prefixMeaningQ (80/100) (95/100) [.big, .blue] r := by
  native_decide

-- ============================================================================
-- §11. Noise Bridge
-- ============================================================================

private def boolToRat (b : Bool) : ℚ := if b then 1 else 0

/-- `lexContinuousQ` is an instance of the unified noise channel from
    `RSA.Core.Noise`. The continuous lexical semantics is exactly the
    noise channel with onMatch = reliability, onMismatch = 1 − reliability.

    This connects @cite{schlotterbeck-wang-2023} to the @cite{degen-etal-2020}
    parameterization where mismatch = 1 − match. -/
theorem lexContinuous_as_noiseChannel (sRel cRel : ℚ) (w : Word) (r : Referent) :
    lexContinuousQ sRel cRel w r =
    RSA.Noise.noiseChannel (reliabilityQ sRel cRel w) (1 - reliabilityQ sRel cRel w)
      (boolToRat (wordApplies w r)) := by
  simp only [lexContinuousQ, RSA.Noise.noiseChannel, boolToRat]
  split <;> ring

-- ============================================================================
-- §12. Findings & Verification
-- ============================================================================

/-- Qualitative findings from the incremental RSA adjective ordering model. -/
inductive Finding where
  /-- Prefix meaning is order-independent for any two words. -/
  | prefix_order_independent
  /-- When size has high discriminatory power, size-first ordering is
      preferred: trajectoryProb(size-first) > trajectoryProb(color-first). -/
  | size_first_when_size_discriminates
  /-- When both properties discriminate equally but color is more
      reliable, color-first is preferred. -/
  | color_first_when_color_reliable
  /-- The meaning function correctly identifies the target (scene A). -/
  | both_orderings_identify_target_A
  /-- The meaning function correctly identifies the target (scene B). -/
  | both_orderings_identify_target_B
  deriving DecidableEq, BEq, Repr

/-- Map each finding to the model prediction that accounts for it. -/
def formalize : Finding → Prop
  | .prefix_order_independent =>
      ∀ (sRel cRel : ℚ) (a b : Word) (r : Referent),
        prefixMeaningQ sRel cRel [a, b] r =
        prefixMeaningQ sRel cRel [b, a] r
  | .size_first_when_size_discriminates =>
      sceneACfg.trajectoryProb () target sizeFirstUtt >
      sceneACfg.trajectoryProb () target colorFirstUtt
  | .color_first_when_color_reliable =>
      sceneBCfg.trajectoryProb () target colorFirstUtt >
      sceneBCfg.trajectoryProb () target sizeFirstUtt
  | .both_orderings_identify_target_A =>
      ∀ r : Referent, sceneAMembers r = true → r ≠ target →
        prefixMeaningQ (99/100) (95/100) [.big, .blue] target >
        prefixMeaningQ (99/100) (95/100) [.big, .blue] r
  | .both_orderings_identify_target_B =>
      ∀ r : Referent, sceneBMembers r = true → r ≠ target →
        prefixMeaningQ (80/100) (95/100) [.big, .blue] target >
        prefixMeaningQ (80/100) (95/100) [.big, .blue] r

/-- All 5 findings verified. -/
theorem all_findings_verified : ∀ f : Finding, formalize f := by
  intro f; cases f
  · exact prefix_meaning_swap
  · exact size_first_when_size_discriminates
  · exact color_first_when_color_reliable
  · exact both_orderings_identify_target_A
  · exact both_orderings_identify_target_B

end Phenomena.WordOrder.Studies.SchlotterbeckWang2023
