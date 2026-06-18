import Linglib.Tactics.RSAPredict
import Linglib.Pragmatics.RSA.Basic
import Linglib.Pragmatics.RSA.Channel
import Linglib.Pragmatics.RSA.Noisy
import Linglib.Pragmatics.RSA.Sequential

/-!
# [schlotterbeck-wang-2023] — Incremental RSA for Adjective Ordering (sanity-check slice)
[cohn-gordon-goodman-potts-2019] [degen-etal-2020] [waldon-degen-2021]

Schlotterbeck, F. & Wang, H. (2023). An incremental RSA model for adjective
ordering preferences in referential visual context. *Proceedings of the Society
for Computation in Linguistics (SCiL)* 6, 121–132.

**SCOPE WARNING.** This file formalizes the *symmetric-PoE
sanity-check slice* of S&W 2023, **not** their main asymmetric model. The
paper documents that with symmetric per-class continuous semantics
the incremental listener's order-independence holds *as a sanity check*; their
predictive results come from the asymmetric semantics + sequence speaker that
this file does not formalize.

What this file *does* formalize: the order-independence headline at the
listener level, plus discrimination-driven ordering preferences at the
speaker level using linglib's `trajectoryProb` (chain-rule product of
per-step normalized softmaxes). Note that linglib's `trajectoryProb` is not
literally S&W's `S1^inc` (which accumulates utilities with a single global
normalization rather than per-step softmaxes). Per-step S1 normalizers are
world-dependent, so speaker chaining and stage-to-stage listener chaining
(`RSA.RSAConfig.composeWithPrior`) generically diverge at the pragmatic
layer ([cohn-gordon-goodman-potts-2019]); they agree at the literal layer,
where iterated Bayesian update equals the PoE posterior.

What this file does **not** formalize:
- Asymmetric per-class semantics (k%-threshold for size dimensions à la
  Schmidt et al. 2009 / Cremers 2022 / Franke et al. 2019, vs binomial-ε
  for color à la [degen-etal-2020])
- The language model `P_Lang` constraining S1's per-step vocabulary to
  grammatical continuations
- The utterance-prior bias `b` for size-first defaults

## The model (formalized slice)

The incremental sequence speaker `S1^inc` produces adjective–noun sequences
word-by-word. With β = 1, no cost, and uniform language prior, the trajectory
score reduces to a per-prefix product of literal-listener posteriors:

  S1^inc(w₁,...,wₙ | r) ∝ ∏ₖ L0(r | w₁,...,wₖ)

The L0 meaning is the Product-of-Experts noisy semantics
([degen-etal-2020]): each word contributes an independent ℚ-valued
factor `lex(w, r)`, and the prefix meaning is their product. With strictly
positive `lex`, the product commutes (`RSA.prefixMeaning_perm`), so the
full-sequence L0 posterior is order-independent.

## Substrate use

This file plugs `RSA.NoisyLex` (`Pragmatics/RSA/Noisy.lean`) into
`RSAConfig`'s sequential machinery. Each scene becomes a `NoisyLex` value
plus a scene predicate; `NoisyLex.toRSAConfigSeq` produces the incremental
RSAConfig. The PoE prefix-product order-independence lemmas live in
`RSA.Sequential` and are inherited (no per-study reproof).

## Variable-name note (α vs β)

S&W's α is the **utterance-level speaker** softmax temperature (Table 1
row 6, varied 5/1/1 across Fig. 3a–c); their β is the **utility/word-level
speaker** temperature (Table 1 row 7, set to 1 in all reported simulations).
This file's `RSAConfig.α` field corresponds to S&W's β = 1. The α-field-name
in the substrate predates S&W and is not renamed here.

## Findings

| # | Finding | Theorem |
|---|---------|---------|
| 1 | Prefix meaning is order-independent | `prefix_meaning_swap` |
| 2 | Size-discriminatory scene → size-first preferred | `size_first_when_size_discriminates` |
| 3 | Equal discrimination + reliable color → color-first | `color_first_when_color_reliable` |
| 4 | Both orderings identify the target (Scene A) | `both_orderings_identify_target_A` |
| 5 | Both orderings identify the target (Scene B) | `both_orderings_identify_target_B` |
-/

namespace SchlotterbeckWang2023

open RSA

/-! ### Domain types -/

/-- Referents in the reference game. -/
inductive Referent where
  | bigBlue | bigGreen | smallBlue | smallGreen | smallRed
  deriving DecidableEq, Fintype, Repr

/-- Words available to the speaker: size adjectives, color adjectives, noun. -/
inductive Word where
  | big | small | blue | green | red | sticker
  deriving DecidableEq, Fintype, Repr

/-! ### Boolean semantics -/

/-- Whether a word is veridically true of a referent. -/
def wordApplies : Word → Referent → Bool
  | .big,     .bigBlue  | .big,     .bigGreen  => true
  | .small,   .smallBlue | .small,  .smallGreen | .small, .smallRed => true
  | .blue,    .bigBlue  | .blue,    .smallBlue  => true
  | .green,   .bigGreen | .green,   .smallGreen => true
  | .red,     .smallRed => true
  | .sticker, _         => true
  | _,        _         => false

/-! ### Noisy lexicon via `RSA.NoisyLex` -/

/-- Per-class perceptual reliability: size words use `sRel`, color words use
    `cRel`, the noun "sticker" applies universally. -/
def reliabilityQ (sRel cRel : ℚ) : Word → ℚ
  | .big | .small         => sRel
  | .blue | .green | .red => cRel
  | .sticker              => 1

/-- Noisy word meaning: returns reliability if the word truly applies,
    `1 − reliability` (noise floor) otherwise. Bernoulli-channel form of
    [degen-etal-2020]'s continuous semantics. -/
def lexQ (sRel cRel : ℚ) (w : Word) (r : Referent) : ℚ :=
  if wordApplies w r then reliabilityQ sRel cRel w
  else 1 - reliabilityQ sRel cRel w

/-- Bundle of noisy lex parameters for the study, packaged as a `NoisyLex`.
    Hypotheses are split into separate lower- and upper-bound arguments per
    mathlib idiom (no destructuring at call sites). -/
def noisyLex (sRel cRel : ℚ) (hs0 : 0 ≤ sRel) (hs1 : sRel ≤ 1)
    (hc0 : 0 ≤ cRel) (hc1 : cRel ≤ 1) : NoisyLex Word Referent where
  lex w r := lexQ sRel cRel w r
  lex_nonneg w r := by
    unfold lexQ
    split
    · cases w <;> simp only [reliabilityQ] <;> linarith
    · cases w <;> simp only [reliabilityQ] <;> linarith

/-! ### Scenes -/

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

/-- Scene A lexicon: sizeRel = 99/100, colorRel = 95/100. -/
def sceneALex : NoisyLex Word Referent :=
  noisyLex (99/100) (95/100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Scene B lexicon: sizeRel = 80/100, colorRel = 95/100. -/
def sceneBLex : NoisyLex Word Referent :=
  noisyLex (80/100) (95/100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ### `RSAConfig` via `NoisyLex.toRSAConfigSeq` -/

/-- Scene A config: `sceneALex` over Scene A members. -/
noncomputable def sceneACfg : RSAConfig Word Referent :=
  sceneALex.toRSAConfigSeq sceneAMembers

/-- Scene B config: `sceneBLex` over Scene B members. -/
noncomputable def sceneBCfg : RSAConfig Word Referent :=
  sceneBLex.toRSAConfigSeq sceneBMembers

/-! ### Utterances -/

/-- Size-first ordering for the big-blue target. -/
def sizeFirstUtt : List Word := [.big, .blue, .sticker]

/-- Color-first ordering for the big-blue target. -/
def colorFirstUtt : List Word := [.blue, .big, .sticker]

/-! ### Prefix-meaning properties -/

/-- Two-word prefix meaning is order-independent. Direct corollary of
    `NoisyLex.prefixMeaning_perm`: ℚ-product commutativity over a list of
    per-word noisy lex values. -/
theorem prefix_meaning_swap (sRel cRel : ℚ) (hs0 : 0 ≤ sRel) (hs1 : sRel ≤ 1)
    (hc0 : 0 ≤ cRel) (hc1 : cRel ≤ 1) (a b : Word) (r : Referent) :
    (noisyLex sRel cRel hs0 hs1 hc0 hc1).prefixMeaning [a, b] r =
      (noisyLex sRel cRel hs0 hs1 hc0 hc1).prefixMeaning [b, a] r :=
  (noisyLex sRel cRel hs0 hs1 hc0 hc1).prefixMeaning_perm (List.Perm.swap b a []) r

/-- Swap of the first two words in any-length prefix. Direct corollary of
    `NoisyLex.prefixMeaning_perm` applied to a head swap. -/
theorem prefix_meaning_swap_head (sRel cRel : ℚ) (hs0 : 0 ≤ sRel) (hs1 : sRel ≤ 1)
    (hc0 : 0 ≤ cRel) (hc1 : cRel ≤ 1) (a b : Word) (rest : List Word) (r : Referent) :
    (noisyLex sRel cRel hs0 hs1 hc0 hc1).prefixMeaning (a :: b :: rest) r =
      (noisyLex sRel cRel hs0 hs1 hc0 hc1).prefixMeaning (b :: a :: rest) r :=
  (noisyLex sRel cRel hs0 hs1 hc0 hc1).prefixMeaning_perm (List.Perm.swap b a rest) r

/-- Two-word prefix meaning decomposes as a product of per-word noisy
    meanings (the Product-of-Experts structure of [degen-etal-2020]). -/
theorem prefix_meaning_product (sRel cRel : ℚ) (hs0 : 0 ≤ sRel) (hs1 : sRel ≤ 1)
    (hc0 : 0 ≤ cRel) (hc1 : cRel ≤ 1) (a b : Word) (r : Referent) :
    (noisyLex sRel cRel hs0 hs1 hc0 hc1).prefixMeaning [a, b] r =
      lexQ sRel cRel a r * lexQ sRel cRel b r := by
  simp only [NoisyLex.prefixMeaning, RSA.prefixMeaning, noisyLex, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one]

/-! ### Predictions via `trajectoryProb` -/

/-- **Finding**: When size has high discriminatory power (Scene A),
    `S1^inc` prefers size-first ordering. -/
theorem size_first_when_size_discriminates :
    sceneACfg.trajectoryProb () target sizeFirstUtt >
    sceneACfg.trajectoryProb () target colorFirstUtt := by
  rsa_predict

/-- **Finding**: When both properties discriminate equally but color is
    more reliable (Scene B), `S1^inc` prefers color-first ordering. -/
theorem color_first_when_color_reliable :
    sceneBCfg.trajectoryProb () target colorFirstUtt >
    sceneBCfg.trajectoryProb () target sizeFirstUtt := by
  rsa_predict

/-- The ordering preference flips between scenes: Scene A prefers size-first,
    Scene B prefers color-first. The preferred ordering depends on the
    discriminatory structure of the scene, not a fixed ordering rule. -/
theorem ordering_preference_flips :
    sceneACfg.trajectoryProb () target sizeFirstUtt >
    sceneACfg.trajectoryProb () target colorFirstUtt ∧
    sceneBCfg.trajectoryProb () target colorFirstUtt >
    sceneBCfg.trajectoryProb () target sizeFirstUtt :=
  ⟨size_first_when_size_discriminates, color_first_when_color_reliable⟩

/-! ### First-word informativity via `S1_at` -/

/-- In Scene A, "big" is more informative than "blue" about the target. -/
theorem big_more_informative_A :
    sceneACfg.S1_at ([] : List Word) () target .big >
    sceneACfg.S1_at ([] : List Word) () target .blue := by
  rsa_predict

/-- In Scene B, "blue" is more informative than "big" about the target. -/
theorem blue_more_informative_B :
    sceneBCfg.S1_at ([] : List Word) () target .blue >
    sceneBCfg.S1_at ([] : List Word) () target .big := by
  rsa_predict

/-! ### Target identification -/

/-- After hearing both adjectives, the meaning function assigns highest
    value to the target among Scene A members. -/
theorem both_orderings_identify_target_A :
    ∀ r : Referent, sceneAMembers r = true → r ≠ target →
      sceneALex.prefixMeaning [.big, .blue] target >
      sceneALex.prefixMeaning [.big, .blue] r := by
  intro r _ hne; cases r
  · exact absurd rfl hne
  all_goals
    (simp only [sceneALex, NoisyLex.prefixMeaning, RSA.prefixMeaning, noisyLex, lexQ,
                wordApplies, reliabilityQ, target, List.map, List.prod_cons,
                List.prod_nil, if_true]; norm_num)

/-- After hearing both adjectives, the meaning function assigns highest
    value to the target among Scene B members. -/
theorem both_orderings_identify_target_B :
    ∀ r : Referent, sceneBMembers r = true → r ≠ target →
      sceneBLex.prefixMeaning [.big, .blue] target >
      sceneBLex.prefixMeaning [.big, .blue] r := by
  intro r _ hne; cases r
  · exact absurd rfl hne
  all_goals
    (simp only [sceneBLex, NoisyLex.prefixMeaning, RSA.prefixMeaning, noisyLex, lexQ,
                wordApplies, reliabilityQ, target, List.map, List.prod_cons,
                List.prod_nil, if_true]; norm_num)

/-! ### Noise-channel bridge -/

/-- `lexQ` is an instance of the unified noise channel from `RSA.Noise`:
    onMatch = `reliabilityQ`, onMismatch = `1 − reliabilityQ`. Connects
    [schlotterbeck-wang-2023] to the [degen-etal-2020]
    parameterization where mismatch = 1 − match. -/
theorem lexQ_as_noiseChannel (sRel cRel : ℚ) (w : Word) (r : Referent) :
    lexQ sRel cRel w r =
      RSA.Noise.noiseChannel (reliabilityQ sRel cRel w)
        (1 - reliabilityQ sRel cRel w)
        (if wordApplies w r then 1 else 0) := by
  simp only [lexQ, RSA.Noise.noiseChannel]
  split <;> ring

end SchlotterbeckWang2023
