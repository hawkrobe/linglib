import Linglib.Pragmatics.RSA.LatentOperators
import Linglib.Pragmatics.RSA.Operators
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
(prior-composition operators) generically diverge at the pragmatic
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

This file plugs `RSA.NoisyLex` (`Pragmatics/RSA/Noisy.lean`) into an
incremental word-by-word chain. Each scene is a `NoisyLex` value plus a
scene predicate; the chain (`l0Q`/`s1Q`/`s1PMF`) is No-Brevity over
PoE-prefix meanings. The order-independence lemmas live in
`RSA.Sequential` and are inherited (no per-study reproof).

## Variable-name note (α vs β)

S&W's α is the **utterance-level speaker** softmax temperature (Table 1
row 6, varied 5/1/1 across Fig. 3a–c); their β is the **utility/word-level
speaker** temperature (Table 1 row 7, set to 1 in all reported simulations).
The chain has no rationality exponent, matching S&W's β = 1. The α-name
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

instance : Nonempty Referent := ⟨.bigBlue⟩

/-- Words available to the speaker: size adjectives, color adjectives, noun. -/
inductive Word where
  | big | small | blue | green | red | sticker
  deriving DecidableEq, Fintype, Repr

instance : Nonempty Word := ⟨.sticker⟩

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

/-! ### Exact-ℚ face (local pending the RSA API pass)

The builder's chain is No-Brevity (`s1Score = l0`, β = 1, no cost) over
PoE-prefix meanings, so every layer is exact ℚ: `l0Q` normalizes the
scene-gated prefix product over referents, `s1Q` renormalizes over words,
and utterance probabilities are chain-rule products. -/

section QFace

/-- Scene-gated ℚ prefix meaning. -/
def meaningQ (lex : NoisyLex Word Referent) (scene : Referent → Bool)
    (ctx : List Word) (u : Word) (r : Referent) : ℚ :=
  if scene r then lex.prefixMeaning (ctx ++ [u]) r else 0

/-- Word-level literal listener value. -/
def l0Q (lex : NoisyLex Word Referent) (scene : Referent → Bool)
    (ctx : List Word) (u : Word) (r : Referent) : ℚ :=
  meaningQ lex scene ctx u r / ∑ r', meaningQ lex scene ctx u r'

/-- Word-level speaker value (β = 1, no cost). -/
def s1Q (lex : NoisyLex Word Referent) (scene : Referent → Bool)
    (ctx : List Word) (r : Referent) (u : Word) : ℚ :=
  l0Q lex scene ctx u r / ∑ u', l0Q lex scene ctx u' r

private theorem meaningQ_nonneg (lex : NoisyLex Word Referent)
    (scene : Referent → Bool) (ctx : List Word) (u : Word) (r : Referent) :
    0 ≤ meaningQ lex scene ctx u r := by
  unfold meaningQ
  split
  · exact lex.prefixMeaning_nonneg _ r
  · exact le_refl 0

private theorem l0Q_nonneg (lex : NoisyLex Word Referent)
    (scene : Referent → Bool) (ctx : List Word) (u : Word) (r : Referent) :
    0 ≤ l0Q lex scene ctx u r :=
  div_nonneg (meaningQ_nonneg lex scene ctx u r)
    (Finset.sum_nonneg fun r' _ => meaningQ_nonneg lex scene ctx u r')

theorem s1Q_nonneg (lex : NoisyLex Word Referent) (scene : Referent → Bool)
    (ctx : List Word) (r : Referent) (u : Word) :
    0 ≤ s1Q lex scene ctx r u :=
  div_nonneg (l0Q_nonneg lex scene ctx u r)
    (Finset.sum_nonneg fun u' _ => l0Q_nonneg lex scene ctx u' r)

open scoped ENNReal

/-- Normalize a rational score vector into a PMF (uniform at zero mass). -/
noncomputable def pmfOfScores {σ : Type*} [Fintype σ] [Nonempty σ]
    (f : σ → ℚ) : PMF σ :=
  if h : (∑' x, ENNReal.ofReal ((f x : ℝ))) ≠ 0 then
    PMF.normalize (fun x => ENNReal.ofReal ((f x : ℝ))) h
      (ENNReal.tsum_ne_top_of_fintype fun _ => ENNReal.ofReal_ne_top)
  else PMF.uniformOfFintype σ

theorem pmfOfScores_apply {σ : Type*} [Fintype σ] [Nonempty σ]
    {f : σ → ℚ} (hf : ∀ x, 0 ≤ f x) (hpos : 0 < ∑ x, f x) (x : σ) :
    pmfOfScores f x = ENNReal.ofReal ((f x / ∑ x', f x' : ℚ) : ℝ) := by
  have hsum : (∑' x, ENNReal.ofReal ((f x : ℝ)))
      = ENNReal.ofReal ((∑ x, f x : ℚ) : ℝ) := by
    rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun x _ => by exact_mod_cast hf x)]
    push_cast
    rfl
  rw [pmfOfScores, dif_pos (by
      rw [hsum, ENNReal.ofReal_ne_zero_iff]; exact_mod_cast hpos),
    PMF.normalize_apply, hsum,
    ← ENNReal.ofReal_inv_of_pos (by exact_mod_cast hpos),
    ← ENNReal.ofReal_mul (by exact_mod_cast hf x)]
  congr 1
  push_cast
  rw [div_eq_mul_inv]

/-- Strict comparison of `pmfOfScores` values via the exact-ℚ scores. -/
theorem pmf_lt_cross {σ τ : Type*} [Fintype σ] [Nonempty σ] [Fintype τ] [Nonempty τ]
    {f : σ → ℚ} {g : τ → ℚ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfp : 0 < ∑ x, f x) (hgp : 0 < ∑ x, g x) {a : σ} {b : τ}
    (hb : 0 < g b / ∑ x, g x) (hab : f a / ∑ x, f x < g b / ∑ x, g x) :
    pmfOfScores f a < pmfOfScores g b := by
  rw [pmfOfScores_apply hf hfp, pmfOfScores_apply hg hgp]
  exact (ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast hb)).mpr
    (by exact_mod_cast hab)

private theorem ofReal_mul3 {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (_hc : 0 ≤ c) :
    ENNReal.ofReal a * ENNReal.ofReal b * ENNReal.ofReal c
      = ENNReal.ofReal (a * b * c) := by
  rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul (mul_nonneg ha hb)]

private theorem valNN (lex : NoisyLex Word Referent) (scene : Referent → Bool)
    (ctx : List Word) (u : Word) (r : Referent) :
    (0:ℝ) ≤ ((l0Q lex scene ctx u r / ∑ u', l0Q lex scene ctx u' r : ℚ) : ℝ) := by
  exact_mod_cast div_nonneg (l0Q_nonneg lex scene ctx u r)
    (Finset.sum_nonneg fun u' _ => l0Q_nonneg lex scene ctx u' r)

/-- Word-by-word speaker at context `ctx` (β = 1, no cost). -/
noncomputable def s1PMF (lex : NoisyLex Word Referent) (scene : Referent → Bool)
    (ctx : List Word) (r : Referent) : PMF Word :=
  pmfOfScores (fun u => l0Q lex scene ctx u r)

end QFace

/-! ### Predictions via `trajectoryProb` -/

/-- **Finding**: When size has high discriminatory power (Scene A),
    `S1^inc` prefers size-first ordering. -/
theorem size_first_when_size_discriminates :
    s1PMF sceneALex sceneAMembers [] target .blue *
      s1PMF sceneALex sceneAMembers [.blue] target .big *
      s1PMF sceneALex sceneAMembers [.blue, .big] target .sticker <
    s1PMF sceneALex sceneAMembers [] target .big *
      s1PMF sceneALex sceneAMembers [.big] target .blue *
      s1PMF sceneALex sceneAMembers [.big, .blue] target .sticker := by
  simp only [s1PMF]
  rw [pmfOfScores_apply (f := fun u => l0Q sceneALex sceneAMembers [] u target) (x := .blue)
      (fun u => l0Q_nonneg sceneALex sceneAMembers [] u target) (by decide +kernel),
    pmfOfScores_apply (f := fun u => l0Q sceneALex sceneAMembers [] u target) (x := .big)
      (fun u => l0Q_nonneg sceneALex sceneAMembers [] u target) (by decide +kernel),
    pmfOfScores_apply (f := fun u => l0Q sceneALex sceneAMembers [.blue] u target)
      (fun u => l0Q_nonneg sceneALex sceneAMembers [.blue] u target) (by decide +kernel),
    pmfOfScores_apply (f := fun u => l0Q sceneALex sceneAMembers [.blue, .big] u target)
      (fun u => l0Q_nonneg sceneALex sceneAMembers [.blue, .big] u target) (by decide +kernel),
    pmfOfScores_apply (f := fun u => l0Q sceneALex sceneAMembers [.big] u target)
      (fun u => l0Q_nonneg sceneALex sceneAMembers [.big] u target) (by decide +kernel),
    pmfOfScores_apply (f := fun u => l0Q sceneALex sceneAMembers [.big, .blue] u target)
      (fun u => l0Q_nonneg sceneALex sceneAMembers [.big, .blue] u target) (by decide +kernel)]
  rw [ofReal_mul3 (valNN sceneALex sceneAMembers [] .blue target)
      (valNN sceneALex sceneAMembers [.blue] .big target)
      (valNN sceneALex sceneAMembers [.blue, .big] .sticker target),
    ofReal_mul3 (valNN sceneALex sceneAMembers [] .big target)
      (valNN sceneALex sceneAMembers [.big] .blue target)
      (valNN sceneALex sceneAMembers [.big, .blue] .sticker target)]
  refine (ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast (by decide +kernel :
    (0:ℚ) < (l0Q sceneALex sceneAMembers [] .big target /
        ∑ u', l0Q sceneALex sceneAMembers [] u' target) *
      (l0Q sceneALex sceneAMembers [.big] .blue target /
        ∑ u', l0Q sceneALex sceneAMembers [.big] u' target) *
      (l0Q sceneALex sceneAMembers [.big, .blue] .sticker target /
        ∑ u', l0Q sceneALex sceneAMembers [.big, .blue] u' target)))).mpr ?_
  exact_mod_cast (by decide +kernel :
    (l0Q sceneALex sceneAMembers [] .blue target /
        ∑ u', l0Q sceneALex sceneAMembers [] u' target) *
      (l0Q sceneALex sceneAMembers [.blue] .big target /
        ∑ u', l0Q sceneALex sceneAMembers [.blue] u' target) *
      (l0Q sceneALex sceneAMembers [.blue, .big] .sticker target /
        ∑ u', l0Q sceneALex sceneAMembers [.blue, .big] u' target) <
    (l0Q sceneALex sceneAMembers [] .big target /
        ∑ u', l0Q sceneALex sceneAMembers [] u' target) *
      (l0Q sceneALex sceneAMembers [.big] .blue target /
        ∑ u', l0Q sceneALex sceneAMembers [.big] u' target) *
      (l0Q sceneALex sceneAMembers [.big, .blue] .sticker target /
        ∑ u', l0Q sceneALex sceneAMembers [.big, .blue] u' target))

/-- **Finding**: When both properties discriminate equally but color is
    more reliable (Scene B), `S1^inc` prefers color-first ordering. -/
theorem color_first_when_color_reliable :
    s1PMF sceneBLex sceneBMembers [] target .big *
      s1PMF sceneBLex sceneBMembers [.big] target .blue *
      s1PMF sceneBLex sceneBMembers [.big, .blue] target .sticker <
    s1PMF sceneBLex sceneBMembers [] target .blue *
      s1PMF sceneBLex sceneBMembers [.blue] target .big *
      s1PMF sceneBLex sceneBMembers [.blue, .big] target .sticker := by
  simp only [s1PMF]
  rw [pmfOfScores_apply (f := fun u => l0Q sceneBLex sceneBMembers [] u target) (x := .big)
      (fun u => l0Q_nonneg sceneBLex sceneBMembers [] u target) (by decide +kernel),
    pmfOfScores_apply (f := fun u => l0Q sceneBLex sceneBMembers [] u target) (x := .blue)
      (fun u => l0Q_nonneg sceneBLex sceneBMembers [] u target) (by decide +kernel),
    pmfOfScores_apply (f := fun u => l0Q sceneBLex sceneBMembers [.big] u target)
      (fun u => l0Q_nonneg sceneBLex sceneBMembers [.big] u target) (by decide +kernel),
    pmfOfScores_apply (f := fun u => l0Q sceneBLex sceneBMembers [.big, .blue] u target)
      (fun u => l0Q_nonneg sceneBLex sceneBMembers [.big, .blue] u target) (by decide +kernel),
    pmfOfScores_apply (f := fun u => l0Q sceneBLex sceneBMembers [.blue] u target)
      (fun u => l0Q_nonneg sceneBLex sceneBMembers [.blue] u target) (by decide +kernel),
    pmfOfScores_apply (f := fun u => l0Q sceneBLex sceneBMembers [.blue, .big] u target)
      (fun u => l0Q_nonneg sceneBLex sceneBMembers [.blue, .big] u target) (by decide +kernel)]
  rw [ofReal_mul3 (valNN sceneBLex sceneBMembers [] .big target)
      (valNN sceneBLex sceneBMembers [.big] .blue target)
      (valNN sceneBLex sceneBMembers [.big, .blue] .sticker target),
    ofReal_mul3 (valNN sceneBLex sceneBMembers [] .blue target)
      (valNN sceneBLex sceneBMembers [.blue] .big target)
      (valNN sceneBLex sceneBMembers [.blue, .big] .sticker target)]
  refine (ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast (by decide +kernel :
    (0:ℚ) < (l0Q sceneBLex sceneBMembers [] .blue target /
        ∑ u', l0Q sceneBLex sceneBMembers [] u' target) *
      (l0Q sceneBLex sceneBMembers [.blue] .big target /
        ∑ u', l0Q sceneBLex sceneBMembers [.blue] u' target) *
      (l0Q sceneBLex sceneBMembers [.blue, .big] .sticker target /
        ∑ u', l0Q sceneBLex sceneBMembers [.blue, .big] u' target)))).mpr ?_
  exact_mod_cast (by decide +kernel :
    (l0Q sceneBLex sceneBMembers [] .big target /
        ∑ u', l0Q sceneBLex sceneBMembers [] u' target) *
      (l0Q sceneBLex sceneBMembers [.big] .blue target /
        ∑ u', l0Q sceneBLex sceneBMembers [.big] u' target) *
      (l0Q sceneBLex sceneBMembers [.big, .blue] .sticker target /
        ∑ u', l0Q sceneBLex sceneBMembers [.big, .blue] u' target) <
    (l0Q sceneBLex sceneBMembers [] .blue target /
        ∑ u', l0Q sceneBLex sceneBMembers [] u' target) *
      (l0Q sceneBLex sceneBMembers [.blue] .big target /
        ∑ u', l0Q sceneBLex sceneBMembers [.blue] u' target) *
      (l0Q sceneBLex sceneBMembers [.blue, .big] .sticker target /
        ∑ u', l0Q sceneBLex sceneBMembers [.blue, .big] u' target))

/-- The ordering preference flips between scenes: Scene A prefers size-first,
    Scene B prefers color-first. The preferred ordering depends on the
    discriminatory structure of the scene, not a fixed ordering rule. -/
theorem ordering_preference_flips :
    (s1PMF sceneALex sceneAMembers [] target .blue *
        s1PMF sceneALex sceneAMembers [.blue] target .big *
        s1PMF sceneALex sceneAMembers [.blue, .big] target .sticker <
      s1PMF sceneALex sceneAMembers [] target .big *
        s1PMF sceneALex sceneAMembers [.big] target .blue *
        s1PMF sceneALex sceneAMembers [.big, .blue] target .sticker) ∧
    (s1PMF sceneBLex sceneBMembers [] target .big *
        s1PMF sceneBLex sceneBMembers [.big] target .blue *
        s1PMF sceneBLex sceneBMembers [.big, .blue] target .sticker <
      s1PMF sceneBLex sceneBMembers [] target .blue *
        s1PMF sceneBLex sceneBMembers [.blue] target .big *
        s1PMF sceneBLex sceneBMembers [.blue, .big] target .sticker) :=
  ⟨size_first_when_size_discriminates, color_first_when_color_reliable⟩

/-! ### First-word informativity via `S1_at` -/

/-- In Scene A, "big" is more informative than "blue" about the target. -/
theorem big_more_informative_A :
    s1PMF sceneALex sceneAMembers [] target .blue <
    s1PMF sceneALex sceneAMembers [] target .big :=
  pmf_lt_cross (fun u => l0Q_nonneg sceneALex sceneAMembers [] u target)
    (fun u => l0Q_nonneg sceneALex sceneAMembers [] u target)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- In Scene B, "blue" is more informative than "big" about the target. -/
theorem blue_more_informative_B :
    s1PMF sceneBLex sceneBMembers [] target .big <
    s1PMF sceneBLex sceneBMembers [] target .blue :=
  pmf_lt_cross (fun u => l0Q_nonneg sceneBLex sceneBMembers [] u target)
    (fun u => l0Q_nonneg sceneBLex sceneBMembers [] u target)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

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
