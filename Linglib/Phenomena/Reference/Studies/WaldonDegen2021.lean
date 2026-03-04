import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Pragmatics.RSA.Core.Noise

/-!
# @cite{waldon-degen-2021} — Continuous-Incremental RSA (CI-RSA)
@cite{cohn-gordon-goodman-potts-2019} @cite{degen-etal-2020}

Waldon, B. & Degen, J. (2021). Modeling cross-linguistic production of
referring expressions. *Proceedings of the Society for Computation in
Linguistics (SCiL)* 4, 206–215.

## The Model

CI-RSA synthesizes two RSA extensions:
1. **Incremental RSA** (@cite{cohn-gordon-goodman-potts-2019}): Word-by-word production
   via the chain rule S1(u|r) = ∏ₖ S1(wₖ | [w₁,...,wₖ₋₁], r)
2. **Continuous semantics** (@cite{degen-etal-2020}): Noisy adjective reliability
   L^C(r, i) = v^i if i true of r, else 1 - v^i

The incremental meaning function averages continuous semantics over
grammatical completions of the current prefix:

  X^C(c, i, r) = Σ_{u ⊒ c+i} ⟦u⟧^C(r) / |{u : u ⊒ c+i}|

The utterance set is scene-filtered: only utterances Boolean-true of at
least one scene member are included (Figure 1).

## Formalization

This builds on `RSAConfig`'s sequential infrastructure (following
@cite{cohn-gordon-goodman-potts-2019}), adding:
- Continuous (ℚ-valued) meaning instead of Boolean extension-counting
- `rpow`-based s1Score with α = 7
- Scene-parameterized configs for cross-condition comparisons

The three predictions are trajectory probability comparisons across
different `RSAConfig` instances (language × scene).

## Predictions

| # | Prediction | Status |
|---|-----------|--------|
| 1 | English color/size asymmetry: SS > CS | `rsa_predict` |
| 2 | Cross-linguistic: English SS > Spanish SS | `rsa_predict` |
| 3 | Spanish flip: CS > SS for redundant size | `rsa_predict` |
| 4 | Overall: English total > Spanish total | `rsa_predict` |

## Connections

- **Noise theory**: `lexContinuousQ` instantiates the unified noise channel
  from `RSA.Core.Noise`. See `lexContinuous_as_noiseChannel`.
- **Incremental RSA**: Extends @cite{cohn-gordon-goodman-potts-2019} with
  continuous semantics and cross-linguistic word order variation.
-/

set_option autoImplicit false

namespace Phenomena.Reference.Studies.WaldonDegen2021

open RSA

-- ============================================================================
-- §1. Domain Types
-- ============================================================================

/-- Words available to the incremental speaker: two color adjectives,
    two size adjectives, a noun ("pin"), and an explicit stop token.
    The stop token models the speaker's choice to end the utterance;
    without it, postnominal word orders lack a way to represent the
    stopping decision after the noun (cf. English where "pin" naturally
    terminates utterances). -/
inductive Word where
  | blue | red | big | small | pin | stop
  deriving DecidableEq, Fintype, BEq, Repr

/-- Referents in the 2×2 reference game: big/small × blue/red. -/
inductive Referent where
  | bigBlue | bigRed | smallBlue | smallRed
  deriving DecidableEq, Fintype, Repr

-- ============================================================================
-- §2. Boolean Semantics
-- ============================================================================

/-- Whether a word is veridically true of a referent. -/
def wordApplies : Word → Referent → Bool
  | .blue,  .bigBlue | .blue,  .smallBlue => true
  | .red,   .bigRed  | .red,   .smallRed  => true
  | .big,   .bigBlue | .big,   .bigRed    => true
  | .small, .smallBlue | .small, .smallRed => true
  | .pin,   _          => true
  | .stop,  _          => true
  | _,      _          => false

-- ============================================================================
-- §3. Continuous Semantics
-- ============================================================================

/-- Semantic reliability values v^i. Color adjectives are more reliable
    than size adjectives: v^color = 19/20 (0.95), v^size = 4/5 (0.8). -/
def semanticValueQ : Word → ℚ
  | .blue | .red   => 19/20
  | .big  | .small => 4/5
  | .pin | .stop   => 1

/-- Continuous lexical interpretation L^C(r, i).
    Returns v^i if true, (1 - v^i) if false. -/
def lexContinuousQ (r : Referent) (w : Word) : ℚ :=
  if wordApplies w r then semanticValueQ w else 1 - semanticValueQ w

/-- Continuous utterance meaning ⟦u⟧^C(r) = ∏_{w ∈ u} L^C(r, w). -/
def uttContinuousQ (r : Referent) (u : List Word) : ℚ :=
  u.foldl (fun acc w => acc * lexContinuousQ r w) 1

-- ============================================================================
-- §4. Utterances (Scene-Filtered)
-- ============================================================================

/-- Boolean utterance truth: conjunction of word applicability. -/
def uttBoolTrue (u : List Word) (r : Referent) : Bool :=
  u.all (fun w => wordApplies w r)

/-- All grammatical English (prenominal) utterances, each terminated
    by `.stop`. In English the noun always comes last before stop,
    so "pin" naturally precedes the stopping decision. -/
def allUttsEng : List (List Word) :=
  [[.blue, .pin, .stop], [.red, .pin, .stop],
   [.big, .pin, .stop], [.small, .pin, .stop],
   [.small, .blue, .pin, .stop], [.small, .red, .pin, .stop],
   [.big, .blue, .pin, .stop], [.big, .red, .pin, .stop]]

/-- All grammatical Spanish (postnominal) utterances, each terminated
    by `.stop`. The stop token is critical here: after `[pin, blue]`,
    the S1 chooses between `.stop` (2-word non-redundant) and `.small`
    (continuing to the 3-word redundant utterance). Without `.stop`,
    the model forces continuation whenever valid extensions exist. -/
def allUttsSpn : List (List Word) :=
  [[.pin, .blue, .stop], [.pin, .red, .stop],
   [.pin, .big, .stop], [.pin, .small, .stop],
   [.pin, .blue, .small, .stop], [.pin, .red, .small, .stop],
   [.pin, .blue, .big, .stop], [.pin, .red, .big, .stop]]

/-- Scene-filtered utterances: only those Boolean-true of at least one
    scene member (Figure 1). This yields 7 utterances per scene. -/
def sceneFilter (utts : List (List Word)) (scene : Referent → Bool) :
    List (List Word) :=
  utts.filter fun u =>
    [Referent.bigBlue, .bigRed, .smallBlue, .smallRed].any fun r =>
      scene r && uttBoolTrue u r

-- ============================================================================
-- §5. Production Cost
-- ============================================================================

/-- Per-word production cost (Section 4): each adjective incurs cost 0.1.
    Pin and stop have zero cost (noun and utterance boundary). -/
def wordCostQ : Word → ℚ
  | .pin | .stop => 0
  | _ => 1/10

-- ============================================================================
-- §6. Extension-Based Continuous Meaning
-- ============================================================================

/-- Incremental continuous meaning: average continuous semantics over
    all grammatical completions of prefix.

    X^C(c, i, r) = Σ_{u ⊒ c+i} ⟦u⟧^C(r) / |{u : u ⊒ c+i}| -/
def continuousMeaningQ (utts : List (List Word)) (scene : Referent → Bool)
    (pfx : List Word) (r : Referent) : ℚ :=
  let exts := (sceneFilter utts scene).filter (pfx.isPrefixOf)
  if exts.isEmpty then 0
  else exts.foldl (fun acc u => acc + uttContinuousQ r u) 0 / exts.length

private theorem continuousMeaningQ_nonneg (utts : List (List Word))
    (scene : Referent → Bool) (pfx : List Word) (r : Referent) :
    0 ≤ continuousMeaningQ utts scene pfx r := by
  unfold continuousMeaningQ
  simp only
  split
  · exact le_refl _
  · apply div_nonneg
    · suffices ∀ (l : List (List Word)) (init : ℚ), 0 ≤ init →
          0 ≤ l.foldl (fun acc u => acc + uttContinuousQ r u) init by
        exact this _ 0 (le_refl _)
      intro l; induction l with
      | nil => intro init h; exact h
      | cons u us ih =>
        intro init hinit; simp only [List.foldl]
        apply ih
        apply add_nonneg hinit
        unfold uttContinuousQ
        suffices ∀ (l : List Word) (init : ℚ), 0 ≤ init →
            0 ≤ l.foldl (fun acc w => acc * lexContinuousQ r w) init by
          exact this _ 1 one_pos.le
        intro l2; induction l2 with
        | nil => intro init h; exact h
        | cons w ws ih2 =>
          intro init hinit; simp only [List.foldl]
          exact ih2 _ (mul_nonneg hinit (by
            cases r <;> cases w <;>
              simp [lexContinuousQ, wordApplies, semanticValueQ] <;> norm_num))
    · exact Nat.cast_nonneg _

/-- Real-valued continuous meaning (for RSAConfig). -/
noncomputable def continuousMeaning (utts : List (List Word))
    (scene : Referent → Bool) (pfx : List Word) (r : Referent) : ℝ :=
  (continuousMeaningQ utts scene pfx r : ℝ)

-- ============================================================================
-- §7. Scenes
-- ============================================================================

/-- Size-sufficient scene: {big_blue, big_red, small_blue}.
    Target small_blue is uniquely identified by size alone. -/
def ssScene : Referent → Bool
  | .bigBlue | .bigRed | .smallBlue => true
  | _ => false

/-- Color-sufficient scene: {small_red, big_red, small_blue}.
    Target small_blue is uniquely identified by color alone. -/
def csScene : Referent → Bool
  | .smallRed | .bigRed | .smallBlue => true
  | _ => false

-- ============================================================================
-- §8. RSAConfig (Parameterized by Language and Scene)
-- ============================================================================

/-- CI-RSA configuration parameterized by utterance set and scene.

    - L0 uses extension-based continuous meaning, returning 0 for
      referents outside the scene
    - S1 uses `rpow`-based scoring with α = 7 and per-word cost C(i)
    - S1(i|c,r) ∝ L0(r|c,i)^α · exp(−α · C(i))  (Section 4)

    Note: v^color = 0.95 here, matching the paper's fitted values.
    This differs from the @cite{degen-etal-2020} value of v^color = 0.99
    used in `RSA.Core.Noise`, because the two papers fit different
    experimental datasets. -/
noncomputable def mkCIRSA (utts : List (List Word)) (scene : Referent → Bool) :
    RSAConfig Word Referent where
  Ctx := List Word
  meaning ctx _ u w :=
    if scene w then continuousMeaning utts scene (ctx ++ [u]) w else 0
  meaning_nonneg _ _ _ w := by
    split
    · exact Rat.cast_nonneg.mpr (continuousMeaningQ_nonneg _ _ _ _)
    · exact le_refl _
  s1Score l0 α _ w u := Real.rpow (l0 u w) α * Real.exp (-α * (wordCostQ u : ℝ))
  s1Score_nonneg _ _ _ _ _ hl _ :=
    mul_nonneg (Real.rpow_nonneg (hl _ _) _) (Real.exp_pos _).le
  α := 7
  α_pos := by norm_num
  transition ctx w := ctx ++ [w]
  initial := []
  latentPrior_nonneg _ _ := by norm_num
  worldPrior_nonneg _ := by norm_num

/-- English (prenominal) CI-RSA in size-sufficient scene. -/
noncomputable def englishSS := mkCIRSA allUttsEng ssScene

/-- English (prenominal) CI-RSA in color-sufficient scene. -/
noncomputable def englishCS := mkCIRSA allUttsEng csScene

/-- Spanish (postnominal) CI-RSA in size-sufficient scene. -/
noncomputable def spanishSS := mkCIRSA allUttsSpn ssScene

/-- Spanish (postnominal) CI-RSA in color-sufficient scene. -/
noncomputable def spanishCS := mkCIRSA allUttsSpn csScene

-- ============================================================================
-- §9. Scene-Filter Cardinality
-- ============================================================================

theorem ss_eng_has_7_utts : (sceneFilter allUttsEng ssScene).length = 7 := by native_decide
theorem cs_eng_has_7_utts : (sceneFilter allUttsEng csScene).length = 7 := by native_decide
theorem ss_spn_has_7_utts : (sceneFilter allUttsSpn ssScene).length = 7 := by native_decide
theorem cs_spn_has_7_utts : (sceneFilter allUttsSpn csScene).length = 7 := by native_decide

-- ============================================================================
-- §10. Predictions
-- ============================================================================

-- **Prediction 1**: English color/size asymmetry.
-- P(small blue pin stop | English, SS) > P(small blue pin stop | English, CS)
-- In the size-sufficient scene, color is redundant but speakers use it
-- more than they use redundant size in the color-sufficient scene.
-- This follows from v^color > v^size: the continuous meaning of color
-- words is more informative, so L0 assigns higher probability to the
-- target when color words are used.
set_option maxHeartbeats 8000000 in
theorem prediction1_english_asymmetry :
    englishSS.trajectoryProb () .smallBlue [.small, .blue, .pin, .stop] >
    englishCS.trajectoryProb () .smallBlue [.small, .blue, .pin, .stop] := by
  rsa_predict

-- **Prediction 2**: Cross-linguistic variation.
-- P(small blue pin stop | English, SS) > P(pin blue small stop | Spanish, SS)
-- English prenominal order produces more redundant color than Spanish
-- postnominal order. In English, the adjective comes first and
-- immediately narrows the referent set; in Spanish, the noun comes
-- first and the adjective is less incrementally informative.
set_option maxHeartbeats 8000000 in
theorem prediction2_cross_linguistic :
    englishSS.trajectoryProb () .smallBlue [.small, .blue, .pin, .stop] >
    spanishSS.trajectoryProb () .smallBlue [.pin, .blue, .small, .stop] := by
  rsa_predict

-- **Prediction 3** (novel): Spanish flip.
-- P(pin blue small stop | Spanish, CS) > P(pin blue small stop | Spanish, SS)
-- In Spanish postnominal order, the asymmetry reverses: redundant
-- size (in CS) exceeds redundant color (in SS). The noun is produced
-- first, and post-nominal size in CS is more incrementally informative
-- than post-nominal color in SS due to the earlier noun anchoring
-- different extension sets.
set_option maxHeartbeats 8000000 in
theorem prediction3_spanish_flip :
    spanishCS.trajectoryProb () .smallBlue [.pin, .blue, .small, .stop] >
    spanishSS.trajectoryProb () .smallBlue [.pin, .blue, .small, .stop] := by
  rsa_predict

-- ============================================================================
-- §11. Semantic Properties
-- ============================================================================

/-- Color adjectives have higher reliability than size adjectives.
    This asymmetry drives the redundant modification predictions. -/
theorem color_more_reliable_than_size :
    semanticValueQ .blue > semanticValueQ .big ∧
    semanticValueQ .red > semanticValueQ .small := by
  constructor <;> norm_num [semanticValueQ]

/-- All semantic values are positive (required for valid probability). -/
theorem semantic_values_positive :
    ∀ w : Word, semanticValueQ w > 0 := by
  intro w; cases w <;> norm_num [semanticValueQ]

-- ============================================================================
-- §12. Noise Theory Connection
-- ============================================================================

/-- `lexContinuousQ` is an instance of the unified noise channel from
    `RSA.Core.Noise`. The continuous lexical semantics L^C(r, i) is
    exactly the noise channel with onMatch = v^i, onMismatch = 1 - v^i,
    b = 1 if item i is true of referent r, 0 otherwise.

    This connects @cite{waldon-degen-2021} to the @cite{degen-etal-2020}
    parameterization where mismatch = 1 - match. -/
theorem lexContinuous_as_noiseChannel (r : Referent) (w : Word) :
    lexContinuousQ r w =
    RSA.Noise.noiseChannel (semanticValueQ w) (1 - semanticValueQ w)
      (if wordApplies w r then 1 else 0 : ℚ) := by
  simp only [lexContinuousQ, RSA.Noise.noiseChannel]
  split <;> ring

-- ============================================================================
-- §13. Prediction 4: Overall Cross-Linguistic Redundancy
-- ============================================================================

-- **Prediction 4**: Overall cross-linguistic redundancy (Section 4).
-- Across SS and CS scenes, CI-RSA predicts lower overall redundant
-- modification probability in Spanish-postnom. than in English.
set_option maxHeartbeats 16000000 in
theorem prediction4_overall_redundancy :
    englishSS.trajectoryProb () .smallBlue [.small, .blue, .pin, .stop] +
    englishCS.trajectoryProb () .smallBlue [.small, .blue, .pin, .stop] >
    spanishSS.trajectoryProb () .smallBlue [.pin, .blue, .small, .stop] +
    spanishCS.trajectoryProb () .smallBlue [.pin, .blue, .small, .stop] := by
  rsa_predict

end Phenomena.Reference.Studies.WaldonDegen2021
