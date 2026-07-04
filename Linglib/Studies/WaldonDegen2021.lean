import Linglib.Pragmatics.RSA.LatentOperators
import Linglib.Pragmatics.RSA.Operators
import Mathlib.Analysis.Complex.ExponentialBounds
import Linglib.Pragmatics.RSA.Channel
import Linglib.Pragmatics.RSA.Noisy
import Linglib.Pragmatics.RSA.Sequential

/-!
# [waldon-degen-2021] — Continuous-Incremental RSA (CI-RSA)
[cohn-gordon-goodman-potts-2019] [degen-etal-2020]

Waldon, B. & Degen, J. (2021). Modeling cross-linguistic production of
referring expressions. *Proceedings of the Society for Computation in
Linguistics (SCiL)* 4, 206–215.

## The Model

CI-RSA synthesizes two RSA extensions:
1. **Incremental RSA** ([cohn-gordon-goodman-potts-2019]): Word-by-word production
   via the chain rule S1(u|r) = ∏ₖ S1(wₖ | [w₁,...,wₖ₋₁], r)
2. **Continuous semantics** ([degen-etal-2020]): Noisy adjective reliability
   L^C(r, i) = v^i if i true of r, else 1 - v^i

The incremental meaning function averages continuous semantics over
grammatical completions of the current prefix:

  X^C(c, i, r) = Σ_{u ⊒ c+i} ⟦u⟧^C(r) / |{u : u ⊒ c+i}|

The utterance set is scene-filtered: only utterances Boolean-true of at
least one scene member are included (Figure 1).

## Formalization

This builds on the incremental word-by-word chain (following
[cohn-gordon-goodman-potts-2019]), adding:
- Continuous (ℚ-valued) meaning instead of Boolean extension-counting
- `rpow`-based s1Score with α = 7
- Scene-parameterized configs for cross-condition comparisons

The three predictions are trajectory probability comparisons across
different (language × scene) configurations of the same chain.

## Predictions

| # | Prediction | Status |
|---|-----------|--------|
| 1 | English color/size asymmetry: SS > CS | `prediction1_english_asymmetry` |
| 2 | Cross-linguistic: English SS > Spanish SS | `prediction2_cross_linguistic` |
| 3 | Spanish flip: CS > SS for redundant size | `prediction3_spanish_flip` |
| 4 | Overall: English total > Spanish total | `prediction4_overall_redundancy` |

## Connections

- **Noise theory**: `lexContinuousQ` instantiates the unified noise channel
  from `RSA.Core.Noise`. See `lexContinuous_as_noiseChannel`.
- **Incremental RSA**: Extends [cohn-gordon-goodman-potts-2019] with
  continuous semantics and cross-linguistic word order variation.
-/

namespace WaldonDegen2021

open RSA

/-! ### Domain Types -/

/-- Words available to the incremental speaker: two color adjectives,
    two size adjectives, a noun ("pin"), and an explicit stop token.
    The stop token models the speaker's choice to end the utterance;
    without it, postnominal word orders lack a way to represent the
    stopping decision after the noun (cf. English where "pin" naturally
    terminates utterances). -/
inductive Word where
  | blue | red | big | small | pin | stop
  deriving DecidableEq, Fintype, Repr

instance : Nonempty Word := ⟨.pin⟩

/-- Referents in the 2×2 reference game: big/small × blue/red. -/
inductive Referent where
  | bigBlue | bigRed | smallBlue | smallRed
  deriving DecidableEq, Fintype, Repr

/-! ### Boolean Semantics -/

/-- Whether a word is veridically true of a referent. -/
def wordApplies : Word → Referent → Bool
  | .blue,  .bigBlue | .blue,  .smallBlue => true
  | .red,   .bigRed  | .red,   .smallRed  => true
  | .big,   .bigBlue | .big,   .bigRed    => true
  | .small, .smallBlue | .small, .smallRed => true
  | .pin,   _          => true
  | .stop,  _          => true
  | _,      _          => false

/-! ### Continuous Semantics -/

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

/-! ### Utterances (Scene-Filtered) -/

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

/-! ### Production Cost -/

/-- Per-word production cost (Section 4): each adjective incurs cost 0.1.
    Pin and stop have zero cost (noun and utterance boundary). -/
def wordCostQ : Word → ℚ
  | .pin | .stop => 0
  | _ => 1/10

/-! ### Extension-Based Continuous Meaning -/

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

/-! ### Scenes -/

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

/-! ### Exact-ℚ face and the cost atom (local pending the RSA API pass) -/

/-! With α = 7 the informativity factor `L0^α` is exact ℚ; the only
transcendental ingredient is the per-adjective cost factor
`cAtom = exp(−α·C) = exp(−7/10)`, bounded two-sidedly below via
`cAtom¹⁰ · e⁷ = 1` and kernel arithmetic on `e`-bounds. Every prediction
trajectory reduces to `K · cAtom / (A + B · cAtom)` with kernel-certified
rational constants, so the comparisons are linear (the sum comparison
quadratic) in the atom. -/

section QFace

/-- L0 policy value: scene-gated continuous meaning normalized over
referents (all rational). -/
def l0Q (utts : List (List Word)) (scene : Referent → Bool)
    (ctx : List Word) (u : Word) (r : Referent) : ℚ :=
  (if scene r then continuousMeaningQ utts scene (ctx ++ [u]) r else 0) /
    ∑ r', (if scene r' then continuousMeaningQ utts scene (ctx ++ [u]) r' else 0)

/-- Informativity factor of the S1 score (α = 7). -/
def s1BaseQ (utts : List (List Word)) (scene : Referent → Bool)
    (tgt : Referent) (ctx : List Word) (u : Word) : ℚ :=
  l0Q utts scene ctx u tgt ^ 7

/-- Cost exponent: one `cAtom` factor per adjective (C = 1/10, α = 7). -/
def costExp : Word → ℕ
  | .pin | .stop => 0
  | _ => 1

private theorem l0Q_nonneg (utts : List (List Word)) (scene : Referent → Bool)
    (ctx : List Word) (u : Word) (r : Referent) : 0 ≤ l0Q utts scene ctx u r := by
  apply div_nonneg
  · split
    · exact continuousMeaningQ_nonneg _ _ _ _
    · exact le_refl 0
  · exact Finset.sum_nonneg fun r' _ => by
      split
      · exact continuousMeaningQ_nonneg _ _ _ _
      · exact le_refl 0

private theorem s1BaseQ_nonneg (utts : List (List Word)) (scene : Referent → Bool)
    (tgt : Referent) (ctx : List Word) (u : Word) :
    0 ≤ s1BaseQ utts scene tgt ctx u :=
  pow_nonneg (l0Q_nonneg utts scene ctx u tgt) 7

end QFace

section CostAtom

/-- The per-adjective cost factor `exp(−α·C) = exp(−7/10)`. -/
noncomputable def cAtom : ℝ := Real.exp (-(7/10 : ℝ))

theorem cAtom_pos : 0 < cAtom := Real.exp_pos _

private theorem cAtom_pow10 : cAtom ^ (10:ℕ) * Real.exp 7 = 1 := by
  rw [cAtom, ← Real.exp_nat_mul, ← Real.exp_add]
  norm_num

private theorem e7_bounds :
    (1096.633 : ℝ) < Real.exp 7 ∧ Real.exp 7 < 1096.634 := by
  have h : Real.exp 7 = Real.exp 1 ^ (7:ℕ) := by
    rw [← Real.exp_nat_mul]; norm_num
  constructor
  · calc (1096.633 : ℝ) < 2.7182818283 ^ (7:ℕ) := by norm_num
      _ < Real.exp 1 ^ (7:ℕ) :=
        pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
      _ = Real.exp 7 := h.symm
  · calc Real.exp 7 = Real.exp 1 ^ (7:ℕ) := h
      _ < 2.7182818286 ^ (7:ℕ) :=
        pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
      _ < 1096.634 := by norm_num

/-- Kernel-certified atom bounds: `(4965/10000)¹⁰·e⁷ < 1 < (4967/10000)¹⁰·e⁷`. -/
theorem cAtom_bounds : (4965/10000 : ℝ) < cAtom ∧ cAtom < 4967/10000 := by
  obtain ⟨he1, he2⟩ := e7_bounds
  have h10 := cAtom_pow10
  have hc := cAtom_pos
  constructor
  · have : (4965/10000 : ℝ) ^ (10:ℕ) < cAtom ^ (10:ℕ) := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 10 hc.le this
  · have : cAtom ^ (10:ℕ) < (4967/10000 : ℝ) ^ (10:ℕ) := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 10 (by norm_num) this

end CostAtom

section SpeakerFace

open scoped ENNReal

/-- Incremental CI-RSA speaker at context `ctx` (S1 ∝ L0⁷·exp(−7·C)),
dite-total. -/
noncomputable def s1PMF (utts : List (List Word)) (scene : Referent → Bool)
    (tgt : Referent) (ctx : List Word) : PMF Word :=
  if h : (∑' u, ENNReal.ofReal ((s1BaseQ utts scene tgt ctx u : ℝ) *
      cAtom ^ costExp u)) ≠ 0 then
    PMF.normalize _ h
      (ENNReal.tsum_ne_top_of_fintype fun _ => ENNReal.ofReal_ne_top)
  else PMF.uniformOfFintype Word

private theorem sumWordsE (f : Word → ℝ≥0∞) :
    ∑ u, f u = f .blue + f .red + f .big + f .small + f .pin + f .stop := by
  rw [show (Finset.univ : Finset Word)
      = {.blue, .red, .big, .small, .pin, .stop} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- Generic step-value lemma: with kernel-certified numerator and
κ-partitioned normalizer constants, the speaker's step probability is
`N·cAtomᵏ / (A + B·cAtom)`. -/
private theorem s1PMF_step (utts : List (List Word)) (scene : Referent → Bool)
    (tgt : Referent) (ctx : List Word) (step : Word) {N A B : ℚ}
    (hN : s1BaseQ utts scene tgt ctx step = N)
    (hA : s1BaseQ utts scene tgt ctx .pin + s1BaseQ utts scene tgt ctx .stop = A)
    (hB : s1BaseQ utts scene tgt ctx .blue + s1BaseQ utts scene tgt ctx .red +
      s1BaseQ utts scene tgt ctx .big + s1BaseQ utts scene tgt ctx .small = B)
    (hApos : 0 ≤ A) (hBpos : 0 ≤ B) (hABpos : 0 < A + B) :
    s1PMF utts scene tgt ctx step
      = ENNReal.ofReal ((N : ℝ) * cAtom ^ costExp step /
          ((A : ℝ) + (B : ℝ) * cAtom)) := by
  have hc := cAtom_pos
  have hc1 : cAtom < 1 := by have := cAtom_bounds.2; linarith
  have hden : (0:ℝ) < (A : ℝ) + (B : ℝ) * cAtom := by
    rcases eq_or_lt_of_le hApos with hA0 | hA0
    · have hB0 : (0:ℚ) < B := by rw [← hA0] at hABpos; simpa using hABpos
      have : (0:ℝ) < (B : ℝ) * cAtom := mul_pos (by exact_mod_cast hB0) hc
      rw [← hA0]; push_cast; linarith
    · have : (0:ℝ) ≤ (B : ℝ) * cAtom :=
        mul_nonneg (by exact_mod_cast hBpos) hc.le
      have : (0:ℝ) < (A : ℝ) := by exact_mod_cast hA0
      linarith [mul_nonneg (show (0:ℝ) ≤ (B:ℝ) from by exact_mod_cast hBpos) hc.le]
  have hnn : ∀ u, 0 ≤ (s1BaseQ utts scene tgt ctx u : ℝ) * cAtom ^ costExp u :=
    fun u => mul_nonneg (by exact_mod_cast s1BaseQ_nonneg utts scene tgt ctx u)
      (pow_nonneg hc.le _)
  have hZ : (∑' u, ENNReal.ofReal ((s1BaseQ utts scene tgt ctx u : ℝ) *
      cAtom ^ costExp u)) = ENNReal.ofReal ((A : ℝ) + (B : ℝ) * cAtom) := by
    rw [tsum_fintype, sumWordsE]
    rw [← ENNReal.ofReal_add (hnn _) (hnn _), ← ENNReal.ofReal_add
        (add_nonneg (hnn _) (hnn _)) (hnn _),
      ← ENNReal.ofReal_add (add_nonneg (add_nonneg (hnn _) (hnn _)) (hnn _)) (hnn _),
      ← ENNReal.ofReal_add
        (add_nonneg (add_nonneg (add_nonneg (hnn _) (hnn _)) (hnn _)) (hnn _)) (hnn _),
      ← ENNReal.ofReal_add
        (add_nonneg (add_nonneg (add_nonneg (add_nonneg (hnn _) (hnn _)) (hnn _))
          (hnn _)) (hnn _)) (hnn _)]
    congr 1
    have hb : ((s1BaseQ utts scene tgt ctx .blue : ℝ) + s1BaseQ utts scene tgt ctx .red +
        s1BaseQ utts scene tgt ctx .big + s1BaseQ utts scene tgt ctx .small) = (B : ℝ) := by
      exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) hB
    have ha : ((s1BaseQ utts scene tgt ctx .pin : ℝ) + s1BaseQ utts scene tgt ctx .stop)
        = (A : ℝ) := by
      exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) hA
    simp only [costExp, pow_one, pow_zero, mul_one]
    linear_combination cAtom * hb + ha
  rw [s1PMF, dif_pos (by
      rw [hZ, ENNReal.ofReal_ne_zero_iff]; exact hden),
    PMF.normalize_apply, hZ, hN,
    ← ENNReal.ofReal_inv_of_pos hden,
    ← ENNReal.ofReal_mul (mul_nonneg (by exact_mod_cast
      (hN ▸ s1BaseQ_nonneg utts scene tgt ctx step)) (pow_nonneg hc.le _))]
  rw [div_eq_mul_inv]


end SpeakerFace

/-! ### Scene-Filter Cardinality -/

theorem ss_eng_has_7_utts : (sceneFilter allUttsEng ssScene).length = 7 := by decide
theorem cs_eng_has_7_utts : (sceneFilter allUttsEng csScene).length = 7 := by decide
theorem ss_spn_has_7_utts : (sceneFilter allUttsSpn ssScene).length = 7 := by decide
theorem cs_spn_has_7_utts : (sceneFilter allUttsSpn csScene).length = 7 := by decide

/-! ### Predictions -/

section Predictions

open scoped ENNReal

private theorem ofReal_mul4 {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (_hd : 0 ≤ d) :
    ENNReal.ofReal a * ENNReal.ofReal b * ENNReal.ofReal c * ENNReal.ofReal d
      = ENNReal.ofReal (a * b * c * d) := by
  rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul (mul_nonneg ha hb),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg ha hb) hc)]

private theorem stepNN {N A B : ℝ} (hN : 0 ≤ N) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (k : ℕ) : 0 ≤ N * cAtom ^ k / (A + B * cAtom) :=
  div_nonneg (mul_nonneg hN (pow_nonneg cAtom_pos.le k))
    (add_nonneg hA (mul_nonneg hB cAtom_pos.le))

private theorem cpow_bounds :
    (4965/10000 : ℝ)^2 < cAtom^2 ∧ cAtom^2 < (4967/10000 : ℝ)^2 ∧
    (4965/10000 : ℝ)^3 < cAtom^3 ∧ cAtom^3 < (4967/10000 : ℝ)^3 := by
  obtain ⟨h1, h2⟩ := cAtom_bounds
  have hc := cAtom_pos
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    first
      | exact pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
      | exact pow_lt_pow_left₀ h2 hc.le (by norm_num)

/-- **Prediction 1** (English color/size asymmetry): redundant color in the
size-sufficient scene beats redundant size in the color-sufficient scene,
because v^color > v^size makes color words more informative. -/
theorem prediction1_english_asymmetry :
    s1PMF allUttsEng csScene .smallBlue [] .small *
      s1PMF allUttsEng csScene .smallBlue [.small] .blue *
      s1PMF allUttsEng csScene .smallBlue [.small, .blue] .pin *
      s1PMF allUttsEng csScene .smallBlue [.small, .blue, .pin] .stop <
    s1PMF allUttsEng ssScene .smallBlue [] .small *
      s1PMF allUttsEng ssScene .smallBlue [.small] .blue *
      s1PMF allUttsEng ssScene .smallBlue [.small, .blue] .pin *
      s1PMF allUttsEng ssScene .smallBlue [.small, .blue, .pin] .stop := by
  have hc := cAtom_pos
  obtain ⟨hb1, hb2⟩ := cAtom_bounds
  obtain ⟨hp2l, hp2u, hp3l, hp3u⟩ := cpow_bounds
  rw [s1PMF_step allUttsEng csScene .smallBlue [] .small
      (N := 16384/4782969) (A := 0)
        (B := 86342264515924592972880295/172780993362485219401138176) (by decide +kernel)
          (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsEng csScene .smallBlue [.small] .blue
      (N := 14645194571776/22876792454961) (A := 16384/4782969)
        (B := 285393411026834849792/445803966501334805331) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsEng csScene .smallBlue [.small, .blue] .pin
      (N := 14645194571776/22876792454961) (A := 14645194571776/22876792454961)
        (B := 0) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsEng csScene .smallBlue [.small, .blue, .pin] .stop
      (N := 14645194571776/22876792454961) (A := 14645194571776/22876792454961)
        (B := 0) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsEng ssScene .smallBlue [] .small
      (N := 62748517/612220032) (A := 0)
        (B := 1149559329210952155893/10545714926909498254464) (by decide +kernel)
          (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsEng ssScene .smallBlue [.small] .blue
      (N := 893871739/4586471424) (A := 128/2187)
        (B := 893871739/4586471424) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsEng ssScene .smallBlue [.small, .blue] .pin
      (N := 893871739/4586471424) (A := 893871739/4586471424)
        (B := 0) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsEng ssScene .smallBlue [.small, .blue, .pin] .stop
      (N := 893871739/4586471424) (A := 893871739/4586471424)
        (B := 0) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    ofReal_mul4 (stepNN (by norm_num) (by norm_num) (by norm_num) _) (stepNN (by norm_num)
      (by norm_num) (by norm_num) _) (stepNN (by norm_num) (by norm_num) (by norm_num) _) (stepNN
        (by norm_num) (by norm_num) (by norm_num) _),
    ofReal_mul4 (stepNN (by norm_num) (by norm_num) (by norm_num) _) (stepNN (by norm_num)
      (by norm_num) (by norm_num) _) (stepNN (by norm_num) (by norm_num) (by norm_num) _) (stepNN
        (by norm_num) (by norm_num) (by norm_num) _)]
  refine (ENNReal.ofReal_lt_ofReal_iff ?_).mpr ?_
  · positivity
  · rw [div_mul_div_comm, div_mul_div_comm, div_mul_div_comm,
      div_mul_div_comm, div_mul_div_comm, div_mul_div_comm,
      div_lt_div_iff₀ (by positivity) (by positivity)]
    simp only [costExp, pow_one, pow_zero, mul_one]
    ring_nf
    nlinarith [hb1, hb2, hc, hp2l, hp2u, hp3l, hp3u]

/-- **Prediction 2** (cross-linguistic): English prenominal order produces
more redundant color than Spanish postnominal order. -/
theorem prediction2_cross_linguistic :
    s1PMF allUttsSpn ssScene .smallBlue [] .pin *
      s1PMF allUttsSpn ssScene .smallBlue [.pin] .blue *
      s1PMF allUttsSpn ssScene .smallBlue [.pin, .blue] .small *
      s1PMF allUttsSpn ssScene .smallBlue [.pin, .blue, .small] .stop <
    s1PMF allUttsEng ssScene .smallBlue [] .small *
      s1PMF allUttsEng ssScene .smallBlue [.small] .blue *
      s1PMF allUttsEng ssScene .smallBlue [.small, .blue] .pin *
      s1PMF allUttsEng ssScene .smallBlue [.small, .blue, .pin] .stop := by
  have hc := cAtom_pos
  obtain ⟨hb1, hb2⟩ := cAtom_bounds
  obtain ⟨hp2l, hp2u, hp3l, hp3u⟩ := cpow_bounds
  rw [s1PMF_step allUttsSpn ssScene .smallBlue [] .pin
      (N := 12151280273024/24160660561265139) (A := 12151280273024/24160660561265139)
        (B := 0) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsSpn ssScene .smallBlue [.pin] .blue
      (N := 893871739/137231006679) (A := 0)
        (B := 537060784578032731240015/8257201619310755345796003) (by decide +kernel)
          (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsSpn ssScene .smallBlue [.pin, .blue] .small
      (N := 893871739/4586471424) (A := 893871739/137231006679)
        (B := 38097296322228514331/195468270849383989248) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsSpn ssScene .smallBlue [.pin, .blue, .small] .stop
      (N := 893871739/4586471424) (A := 893871739/4586471424)
        (B := 0) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsEng ssScene .smallBlue [] .small
      (N := 62748517/612220032) (A := 0)
        (B := 1149559329210952155893/10545714926909498254464) (by decide +kernel)
          (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsEng ssScene .smallBlue [.small] .blue
      (N := 893871739/4586471424) (A := 128/2187)
        (B := 893871739/4586471424) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsEng ssScene .smallBlue [.small, .blue] .pin
      (N := 893871739/4586471424) (A := 893871739/4586471424)
        (B := 0) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsEng ssScene .smallBlue [.small, .blue, .pin] .stop
      (N := 893871739/4586471424) (A := 893871739/4586471424)
        (B := 0) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    ofReal_mul4 (stepNN (by norm_num) (by norm_num) (by norm_num) _) (stepNN (by norm_num)
      (by norm_num) (by norm_num) _) (stepNN (by norm_num) (by norm_num) (by norm_num) _) (stepNN
        (by norm_num) (by norm_num) (by norm_num) _),
    ofReal_mul4 (stepNN (by norm_num) (by norm_num) (by norm_num) _) (stepNN (by norm_num)
      (by norm_num) (by norm_num) _) (stepNN (by norm_num) (by norm_num) (by norm_num) _) (stepNN
        (by norm_num) (by norm_num) (by norm_num) _)]
  refine (ENNReal.ofReal_lt_ofReal_iff ?_).mpr ?_
  · positivity
  · rw [div_mul_div_comm, div_mul_div_comm, div_mul_div_comm,
      div_mul_div_comm, div_mul_div_comm, div_mul_div_comm,
      div_lt_div_iff₀ (by positivity) (by positivity)]
    simp only [costExp, pow_one, pow_zero, mul_one]
    ring_nf
    nlinarith [hb1, hb2, hc, hp2l, hp2u, hp3l, hp3u]

/-- **Prediction 3** (novel, Spanish flip): postnominally, redundant size in
CS exceeds redundant color in SS — the early noun anchors the extension sets
differently. -/
theorem prediction3_spanish_flip :
    s1PMF allUttsSpn ssScene .smallBlue [] .pin *
      s1PMF allUttsSpn ssScene .smallBlue [.pin] .blue *
      s1PMF allUttsSpn ssScene .smallBlue [.pin, .blue] .small *
      s1PMF allUttsSpn ssScene .smallBlue [.pin, .blue, .small] .stop <
    s1PMF allUttsSpn csScene .smallBlue [] .pin *
      s1PMF allUttsSpn csScene .smallBlue [.pin] .blue *
      s1PMF allUttsSpn csScene .smallBlue [.pin, .blue] .small *
      s1PMF allUttsSpn csScene .smallBlue [.pin, .blue, .small] .stop := by
  have hc := cAtom_pos
  obtain ⟨hb1, hb2⟩ := cAtom_bounds
  obtain ⟨hp2l, hp2u, hp3l, hp3u⟩ := cpow_bounds
  rw [s1PMF_step allUttsSpn ssScene .smallBlue [] .pin
      (N := 12151280273024/24160660561265139) (A := 12151280273024/24160660561265139)
        (B := 0) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsSpn ssScene .smallBlue [.pin] .blue
      (N := 893871739/137231006679) (A := 0)
        (B := 537060784578032731240015/8257201619310755345796003) (by decide +kernel)
          (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsSpn ssScene .smallBlue [.pin, .blue] .small
      (N := 893871739/4586471424) (A := 893871739/137231006679)
        (B := 38097296322228514331/195468270849383989248) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsSpn ssScene .smallBlue [.pin, .blue, .small] .stop
      (N := 893871739/4586471424) (A := 893871739/4586471424)
        (B := 0) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsSpn csScene .smallBlue [] .pin
      (N := 138338874920368361/395848262635768037376)
        (A := 138338874920368361/395848262635768037376)
        (B := 0) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsSpn csScene .smallBlue [.pin] .blue
      (N := 1954897493193/3521614606208) (A := 0)
        (B := 295168158416140658615676439/528460903635888342130944192) (by decide +kernel)
          (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsSpn csScene .smallBlue [.pin, .blue] .small
      (N := 14645194571776/22876792454961) (A := 893871739/1801088541)
        (B := 14645194571776/22876792454961) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsSpn csScene .smallBlue [.pin, .blue, .small] .stop
      (N := 14645194571776/22876792454961) (A := 14645194571776/22876792454961)
        (B := 0) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    ofReal_mul4 (stepNN (by norm_num) (by norm_num) (by norm_num) _) (stepNN (by norm_num)
      (by norm_num) (by norm_num) _) (stepNN (by norm_num) (by norm_num) (by norm_num) _) (stepNN
        (by norm_num) (by norm_num) (by norm_num) _),
    ofReal_mul4 (stepNN (by norm_num) (by norm_num) (by norm_num) _) (stepNN (by norm_num)
      (by norm_num) (by norm_num) _) (stepNN (by norm_num) (by norm_num) (by norm_num) _) (stepNN
        (by norm_num) (by norm_num) (by norm_num) _)]
  refine (ENNReal.ofReal_lt_ofReal_iff ?_).mpr ?_
  · positivity
  · rw [div_mul_div_comm, div_mul_div_comm, div_mul_div_comm,
      div_mul_div_comm, div_mul_div_comm, div_mul_div_comm,
      div_lt_div_iff₀ (by positivity) (by positivity)]
    simp only [costExp, pow_one, pow_zero, mul_one]
    ring_nf
    nlinarith [hb1, hb2, hc, hp2l, hp2u, hp3l, hp3u]

end Predictions

/-! ### Semantic Properties -/

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

/-! ### Noise Theory Connection + Substrate Bridge -/

/-- `lexContinuousQ` is an instance of the unified noise channel from
    `RSA.Core.Noise`. The continuous lexical semantics L^C(r, i) is
    exactly the noise channel with onMatch = v^i, onMismatch = 1 - v^i,
    b = 1 if item i is true of referent r, 0 otherwise.

    This connects [waldon-degen-2021] to the [degen-etal-2020]
    parameterization where mismatch = 1 - match. -/
theorem lexContinuous_as_noiseChannel (r : Referent) (w : Word) :
    lexContinuousQ r w =
    RSA.Noise.noiseChannel (semanticValueQ w) (1 - semanticValueQ w)
      (if wordApplies w r then 1 else 0 : ℚ) := by
  simp only [lexContinuousQ, RSA.Noise.noiseChannel]
  split <;> ring

/-- `lexContinuousQ` packaged as a `RSA.NoisyLex` bundle. The bundle is
    the substrate this study and [schlotterbeck-wang-2023] share —
    each provides its own `lex` and reliability parameters; the PoE
    prefix-product machinery (`RSA.prefixMeaning` and friends) is reused. -/
def noisyLex : RSA.NoisyLex Word Referent where
  lex w r := lexContinuousQ r w
  lex_nonneg w r := by
    cases w <;> cases r <;>
      (unfold lexContinuousQ; simp only [wordApplies, semanticValueQ];
       split_ifs <;> norm_num)

/-- `uttContinuousQ` is the `NoisyLex.prefixMeaning` of the bundled lex
    (modulo argument order). Substrate-bridge analogue of S&W's
    `prefix_meaning_product` for the W&D extension-averaging context.

    Uses the polymorphic `RSA.prefixMeaning_eq_foldl_mul` from
    `Sequential.lean` — no need for a study-local foldl helper. -/
theorem uttContinuousQ_eq_prefixMeaning (r : Referent) (u : List Word) :
    uttContinuousQ r u = noisyLex.prefixMeaning u r := by
  unfold uttContinuousQ NoisyLex.prefixMeaning
  rw [RSA.prefixMeaning_eq_foldl_mul]
  rfl

/-! ### Prediction 4: Overall Cross-Linguistic Redundancy -/

/-- Extended atom-power bounds for the sum comparison. -/
private theorem cpow_bounds' :
    ∀ k ∈ ({2, 3, 4, 5, 6} : Finset ℕ),
      (4965/10000 : ℝ)^k < cAtom^k ∧ cAtom^k < (4967/10000 : ℝ)^k := by
  intro k hk
  obtain ⟨h1, h2⟩ := cAtom_bounds
  exact ⟨pow_lt_pow_left₀ h1 (by norm_num) (by fin_cases hk <;> norm_num),
    pow_lt_pow_left₀ h2 cAtom_pos.le (by fin_cases hk <;> norm_num)⟩

set_option maxHeartbeats 1600000 in
/-- **Prediction 4** (overall cross-linguistic redundancy): summed across
scenes, English redundant modification exceeds Spanish. -/
theorem prediction4_overall_redundancy :
    s1PMF allUttsSpn ssScene .smallBlue [] .pin *
        s1PMF allUttsSpn ssScene .smallBlue [.pin] .blue *
        s1PMF allUttsSpn ssScene .smallBlue [.pin, .blue] .small *
        s1PMF allUttsSpn ssScene .smallBlue [.pin, .blue, .small] .stop +
      (s1PMF allUttsSpn csScene .smallBlue [] .pin *
        s1PMF allUttsSpn csScene .smallBlue [.pin] .blue *
        s1PMF allUttsSpn csScene .smallBlue [.pin, .blue] .small *
        s1PMF allUttsSpn csScene .smallBlue [.pin, .blue, .small] .stop) <
    s1PMF allUttsEng ssScene .smallBlue [] .small *
        s1PMF allUttsEng ssScene .smallBlue [.small] .blue *
        s1PMF allUttsEng ssScene .smallBlue [.small, .blue] .pin *
        s1PMF allUttsEng ssScene .smallBlue [.small, .blue, .pin] .stop +
      (s1PMF allUttsEng csScene .smallBlue [] .small *
        s1PMF allUttsEng csScene .smallBlue [.small] .blue *
        s1PMF allUttsEng csScene .smallBlue [.small, .blue] .pin *
        s1PMF allUttsEng csScene .smallBlue [.small, .blue, .pin] .stop) := by
  have hc := cAtom_pos
  obtain ⟨hb1, hb2⟩ := cAtom_bounds
  have h2 := cpow_bounds' 2 (by norm_num)
  have h3 := cpow_bounds' 3 (by norm_num)
  have h4 := cpow_bounds' 4 (by norm_num)
  have h5 := cpow_bounds' 5 (by norm_num)
  have h6 := cpow_bounds' 6 (by norm_num)
  rw [s1PMF_step allUttsSpn ssScene .smallBlue [] .pin
      (N := 12151280273024/24160660561265139) (A := 12151280273024/24160660561265139)
        (B := 0) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsSpn ssScene .smallBlue [.pin] .blue
      (N := 893871739/137231006679) (A := 0)
        (B := 537060784578032731240015/8257201619310755345796003) (by decide +kernel)
          (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsSpn ssScene .smallBlue [.pin, .blue] .small
      (N := 893871739/4586471424) (A := 893871739/137231006679)
        (B := 38097296322228514331/195468270849383989248) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsSpn ssScene .smallBlue [.pin, .blue, .small] .stop
      (N := 893871739/4586471424) (A := 893871739/4586471424)
        (B := 0) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsSpn csScene .smallBlue [] .pin
      (N := 138338874920368361/395848262635768037376)
        (A := 138338874920368361/395848262635768037376)
        (B := 0) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsSpn csScene .smallBlue [.pin] .blue
      (N := 1954897493193/3521614606208) (A := 0)
        (B := 295168158416140658615676439/528460903635888342130944192) (by decide +kernel)
          (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsSpn csScene .smallBlue [.pin, .blue] .small
      (N := 14645194571776/22876792454961) (A := 893871739/1801088541)
        (B := 14645194571776/22876792454961) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsSpn csScene .smallBlue [.pin, .blue, .small] .stop
      (N := 14645194571776/22876792454961) (A := 14645194571776/22876792454961)
        (B := 0) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsEng ssScene .smallBlue [] .small
      (N := 62748517/612220032) (A := 0)
        (B := 1149559329210952155893/10545714926909498254464) (by decide +kernel)
          (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsEng ssScene .smallBlue [.small] .blue
      (N := 893871739/4586471424) (A := 128/2187)
        (B := 893871739/4586471424) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsEng ssScene .smallBlue [.small, .blue] .pin
      (N := 893871739/4586471424) (A := 893871739/4586471424)
        (B := 0) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsEng ssScene .smallBlue [.small, .blue, .pin] .stop
      (N := 893871739/4586471424) (A := 893871739/4586471424)
        (B := 0) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsEng csScene .smallBlue [] .small
      (N := 16384/4782969) (A := 0)
        (B := 86342264515924592972880295/172780993362485219401138176) (by decide +kernel)
          (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsEng csScene .smallBlue [.small] .blue
      (N := 14645194571776/22876792454961) (A := 16384/4782969)
        (B := 285393411026834849792/445803966501334805331) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsEng csScene .smallBlue [.small, .blue] .pin
      (N := 14645194571776/22876792454961) (A := 14645194571776/22876792454961)
        (B := 0) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    s1PMF_step allUttsEng csScene .smallBlue [.small, .blue, .pin] .stop
      (N := 14645194571776/22876792454961) (A := 14645194571776/22876792454961)
        (B := 0) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by norm_num) (by norm_num) (by norm_num),
    ofReal_mul4 (stepNN (by norm_num) (by norm_num) (by norm_num) _) (stepNN (by norm_num)
      (by norm_num) (by norm_num) _) (stepNN (by norm_num) (by norm_num) (by norm_num) _) (stepNN
        (by norm_num) (by norm_num) (by norm_num) _), ofReal_mul4 (stepNN (by norm_num)
        (by norm_num) (by norm_num) _) (stepNN (by norm_num) (by norm_num) (by norm_num) _) (stepNN
        (by norm_num) (by norm_num) (by norm_num) _) (stepNN (by norm_num) (by norm_num)
        (by norm_num) _), ofReal_mul4 (stepNN (by norm_num) (by norm_num) (by norm_num) _) (stepNN
        (by norm_num) (by norm_num) (by norm_num) _) (stepNN (by norm_num) (by norm_num)
        (by norm_num) _) (stepNN (by norm_num) (by norm_num) (by norm_num) _), ofReal_mul4 (stepNN
        (by norm_num) (by norm_num) (by norm_num) _) (stepNN (by norm_num) (by norm_num)
        (by norm_num) _) (stepNN (by norm_num) (by norm_num) (by norm_num) _) (stepNN (by norm_num)
        (by norm_num) (by norm_num) _),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr ?_
  rw [div_mul_div_comm, div_mul_div_comm, div_mul_div_comm, div_mul_div_comm,
    div_mul_div_comm, div_mul_div_comm, div_mul_div_comm, div_mul_div_comm,
    div_mul_div_comm, div_mul_div_comm, div_mul_div_comm, div_mul_div_comm,
    div_add_div _ _ (by positivity) (by positivity),
    div_add_div _ _ (by positivity) (by positivity),
    div_lt_div_iff₀ (by positivity) (by positivity)]
  simp only [costExp, pow_one, pow_zero, mul_one]
  ring_nf
  nlinarith [hb1, hb2, hc, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2, h6.1, h6.2]

end WaldonDegen2021
