import Linglib.Pragmatics.RSA.LatentOperators
import Linglib.Pragmatics.RSA.Operators
import Linglib.Pragmatics.RSA.Incremental
import Linglib.Processing.VisualWorld
import Linglib.Studies.SedivyEtAl1999

/-!
# [cohn-gordon-goodman-potts-2019] — Incremental Iterated Response Model

Cohn-Gordon, R., Goodman, N. D., & Potts, C. (2019). An Incremental Iterated
Response Model of Pragmatics. *Proceedings of the Society for Computation in
Linguistics (SCiL)* 2, 81–90.

## The Model

The incremental RSA model extends the standard RSA framework to word-by-word
production. The speaker produces referring expressions incrementally, choosing
each word to maximize the listener's posterior probability for the target:

  S1^WORD(wₖ | [w₁,...,wₖ₋₁], r) ∝ L0(r | w₁,...,wₖ)^α

The full utterance probability factors via the chain rule:

  S1^UTT-IP(w₁,...,wₙ | r) = ∏ₖ S1^WORD(wₖ | [w₁,...,wₖ₋₁], r)

L0 uses **extension-based incremental semantics** (§2.2): given prefix c,

  ⟦c⟧(w) = |{u ∈ U : c ⊑ u ∧ ⟦u⟧(w) = 1}| / |{u ∈ U : c ⊑ u ∧ ∃w'. ⟦u⟧(w') = 1}|

where U is the set of complete utterances and ⊑ is the prefix relation.

## Formalization via the `IncrementalSemantics` bundle

Each scene in this file is a single value of `RSA.IncrementalSemantics U W`
(in `Pragmatics/RSA/Incremental.lean`), specifying just the lexicon
(`wordApplies`), the closed set of complete utterances, and the world set.
The bundle's `toRSAConfig` builder produces the full `RSAConfig` with chain-
rule speaker, α = 1, no cost, uniform priors, and extension-based L0 — so
the three scenes (Figure 1, the [sedivy-2007] reference game, the
[rubio-fernandez-2016] display) share machinery rather than duplicating it.

The bundle exposes a single deep theorem, `l0Utt_ge_inv_card`, proving
the §2.4 weakly-informative bound generically: any complete utterance true
of `r ∈ worlds` yields a literal posterior at least `1 / worlds.length`.
The Figure 1 application (`greedyUnroll_weakly_informative`) below
discharges only the `r ∈ worlds` and `uttSem utt r = true` premises;
the bound follows.

## Main results

* `adj_first_for_target` / `noun_after_adj` / `noun_only_for_r2` /
  `adj_only_for_r3`: the Figure 1c word-by-word speaker rows.
* `uniform_after_red_for_r2`: the §2.2 dead-end fallback (Figure 1c's
  R2 row: 0, ½, ½ over words with viable continuations).
* `listener_anticipation`: hearing "red", L1 favours R3 at 7/11
  (Figure 1d) — the anticipatory implicature.
* `incremental_prefers_bare_noun`: the chain-rule product prefers bare
  "dress" (3/7) over "red dress" (8/21) for R1 (Figure 1e), diverging from
  `global_prefers_red_dress` — the paper's central architectural wedge.
* `sedivy_contrast_inference` / `cgSedivyLooks_satisfy_contrast_reduces_competitor`:
  the §3.2 contrastive-inference reanalysis, discharging the visual-world
  paradigm contract under the Bayesian posterior linking hypothesis.

## Implementation notes

The bundle's extension counts are natural numbers, so the whole No-Brevity
chain is exact ℚ (`incSemQ` … `s1Q`), with PMF agents via `pmfOfScores` and
kernel-verified comparisons. The §2.2 dead-end fallback distributes over
words with viable continuations, gated to scene referents (out-of-scene
referents keep the substrate's zero row). Utterance-level probabilities are
chain-rule products of `s1PMF` values (eq. 7).
-/

namespace CohnGordonEtAl2019

open RSA

/-! ### Domain Types (Figure 1a) -/

/-- Words available to the incremental speaker (Figure 1a). -/
inductive Word where
  | red | dress | object
  deriving DecidableEq, Fintype, Repr

instance : Nonempty Word := ⟨.red⟩

/-- Referents in the reference game scene (Figure 1a).

    Scene: {red dress (R1), blue dress (R2), red hat (R3)} -/
inductive Referent where
  | redDress | blueDress | redHat
  deriving DecidableEq, Fintype, Repr

instance : Nonempty Referent := ⟨.redDress⟩

/-! ### The Figure 1 bundle -/

/-- The Figure 1 reference scene as an `IncrementalSemantics` bundle:
    three words ("red", "dress", "object"), three complete utterances
    ("dress", "red dress", "red object"), three referents (R1, R2, R3). -/
def figureOne : IncrementalSemantics Word Referent where
  wordApplies
    | .red,    .redDress  => true
    | .red,    .redHat    => true
    | .dress,  .redDress  => true
    | .dress,  .blueDress => true
    | .object, _          => true
    | _,       _          => false
  completeUtterances :=
    [[.dress], [.red, .dress], [.red, .object]]
  worlds := [.redDress, .blueDress, .redHat]

/-! ### Exact-ℚ face over a bundle (local pending the RSA API pass) -/

/-! The bundle's extension counts are natural numbers, so the whole
No-Brevity chain (eqs. 4–6, zero cost, α = 1) is exact-ℚ: `l0Q` normalizes
the extension semantics over referents, `s1Q` renormalizes over words, and
utterance-level probabilities are chain-rule products (eq. 7). PMF speakers
and listeners are `pmfOfScores` of these values. -/

section QFace

open RSA

variable {U W : Type} [DecidableEq U]

/-- ℚ extension semantics ⟦pfx⟧(r) (§2.2), mirroring
`IncrementalSemantics.incrementalSem`. -/
def incSemQ (sem : IncrementalSemantics U W) (pfx : List U) (r : W) : ℚ :=
  (sem.trueExtCount pfx r : ℚ) / (sem.viableExtCount pfx : ℚ)

private theorem incSemQ_nonneg (sem : IncrementalSemantics U W) (pfx : List U)
    (r : W) : 0 ≤ incSemQ sem pfx r :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

variable [Fintype W]

/-- Word-level literal listener value (eq. 4). -/
def l0Q (sem : IncrementalSemantics U W) (ctx : List U) (u : U) (r : W) : ℚ :=
  incSemQ sem (ctx ++ [u]) r / ∑ r', incSemQ sem (ctx ++ [u]) r'

private theorem l0Q_nonneg (sem : IncrementalSemantics U W) (ctx : List U)
    (u : U) (r : W) : 0 ≤ l0Q sem ctx u r :=
  div_nonneg (incSemQ_nonneg sem _ r)
    (Finset.sum_nonneg fun r' _ => incSemQ_nonneg sem _ r')

variable [DecidableEq W] [Fintype U]


/-- Word-level speaker score at context `ctx` (eq. 5, zero cost, α = 1).
At dead-end cells — no word makes the referent reachable — probability is
"evenly distributed" over the words with viable continuations (§2.2,
Figure 1c's R2 row: 0, ½, ½). -/
def s1ScoreQ (sem : IncrementalSemantics U W) (ctx : List U) (r : W) (u : U) : ℚ :=
  if (∑ u', sem.trueExtCount (ctx ++ [u']) r) = 0 then
    (if 0 < (sem.worlds.filter (fun r' => decide (r' = r))).length *
          sem.viableExtCount (ctx ++ [u]) then 1 else 0)
  else l0Q sem ctx u r

/-- Normalized word-level speaker value. -/
def s1Q (sem : IncrementalSemantics U W) (ctx : List U) (r : W) (u : U) : ℚ :=
  s1ScoreQ sem ctx r u / ∑ u', s1ScoreQ sem ctx r u'


theorem s1ScoreQ_nonneg (sem : IncrementalSemantics U W) (ctx : List U) (r : W)
    (u : U) : 0 ≤ s1ScoreQ sem ctx r u := by
  unfold s1ScoreQ
  split
  · split <;> norm_num
  · exact l0Q_nonneg sem ctx u r

theorem s1Q_nonneg (sem : IncrementalSemantics U W) (ctx : List U) (r : W)
    (u : U) : 0 ≤ s1Q sem ctx r u :=
  div_nonneg (s1ScoreQ_nonneg sem ctx r u)
    (Finset.sum_nonneg fun u' _ => s1ScoreQ_nonneg sem ctx r u')

open scoped ENNReal

variable [Nonempty U] [Nonempty W]

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

/-- Word-by-word speaker at context `ctx` (eq. 5). -/
noncomputable def s1PMF (sem : IncrementalSemantics U W) (ctx : List U)
    (r : W) : PMF U :=
  pmfOfScores (s1ScoreQ sem ctx r)

/-- Pragmatic listener upon the first word (eq. 6, uniform priors). -/
noncomputable def l1PMF (sem : IncrementalSemantics U W) (u : U) : PMF W :=
  pmfOfScores (fun r => s1Q sem [] r u)

end QFace

/-! ### RSAConfig -/

/-! ### Findings -/

/-- Qualitative findings from the incremental RSA model. -/
inductive Finding where
  /-- The incremental speaker prefers the adjective "red" first when
      referring to the target R1 (red dress). -/
  | adj_first_for_target
  /-- After producing "red", the speaker prefers the type noun "dress"
      over the generic "object". -/
  | noun_after_adj
  /-- For R2 (blue dress), the speaker must start with "dress" —
      "red" has zero incremental semantics for R2. -/
  | noun_only_for_r2
  /-- For R3 (red hat), the speaker must start with "red" —
      "dress" has zero incremental semantics for R3. -/
  | adj_only_for_r3
  /-- After "red" for R2, no extension is true — the speaker is
      indifferent between "dress" and "object" (uniform fallback). -/
  | uniform_after_red_for_r2
  /-- After hearing "red", L1 infers the target is more likely R3
      (red hat) than R1 (red dress) — an anticipatory implicature. -/
  | listener_anticipation
  /-- At the utterance level, the incremental model assigns higher
      probability to "dress" than to "red dress" for R1 — diverging
      from the global model which prefers "red dress". -/
  | incremental_prefers_bare_noun
  deriving DecidableEq, Repr

/-! ### Predictions -/

-- ---------- Figure 1c: S1^WORD incremental speaker ----------

/-- **Finding 1** (Figure 1c): The incremental speaker prefers "red" first
    when referring to R1 (red dress).

    S1(red | [], R1) = 4/7 ≈ 0.57 > S1(dress | [], R1) = 3/7 ≈ 0.43

    Mechanism: "red" narrows the extension set to {red dress, red object},
    both true of R1 (trueExtCount = 2, viableExtCount = 2 → meaning = 1).
    "dress" narrows to {dress}, true of R1 (meaning = 1) but the L0
    posterior for R1 is lower because "dress" also applies to R2. -/
theorem adj_first_for_target :
    s1PMF figureOne [] .redDress .dress < s1PMF figureOne [] .redDress .red :=
  pmf_lt_cross (s1ScoreQ_nonneg figureOne [] .redDress) (s1ScoreQ_nonneg figureOne [] .redDress)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **Finding 2** (Figure 1c): After producing "red", the speaker prefers
    "dress" over "object" for R1.

    S1(dress | [red], R1) = 2/3 ≈ 0.67 > S1(object | [red], R1) = 1/3 ≈ 0.33

    "red dress" uniquely identifies R1 (only R1 is a red dress), while
    "red object" is ambiguous between R1 and R3. -/
theorem noun_after_adj :
    s1PMF figureOne [.red] .redDress .object < s1PMF figureOne [.red] .redDress .dress :=
  pmf_lt_cross (s1ScoreQ_nonneg figureOne _ .redDress) (s1ScoreQ_nonneg figureOne _ .redDress)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **Finding 3** (Figure 1c): For R2 (blue dress), the speaker must start
    with "dress" — "red" never applies to R2 (it's a blue dress), so all
    extensions of "red" have zero semantics for R2.

    S1(dress | [], R2) > S1(red | [], R2) -/
theorem noun_only_for_r2 :
    s1PMF figureOne [] .blueDress .red < s1PMF figureOne [] .blueDress .dress :=
  pmf_lt_cross (s1ScoreQ_nonneg figureOne [] .blueDress) (s1ScoreQ_nonneg figureOne [] .blueDress)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **Finding 4** (Figure 1c): For R3 (red hat), the speaker must start
    with "red" — "dress" never applies to R3 (it's a hat), so the only
    extension of "dress" (= "dress" itself) has zero semantics for R3.

    S1(red | [], R3) > S1(dress | [], R3) -/
theorem adj_only_for_r3 :
    s1PMF figureOne [] .redHat .dress < s1PMF figureOne [] .redHat .red :=
  pmf_lt_cross (s1ScoreQ_nonneg figureOne [] .redHat) (s1ScoreQ_nonneg figureOne [] .redHat)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **Finding 5** (§2.2, uniform fallback): After "red" for R2, no complete
    utterance extension of "red" is true of R2 (blue dress). The paper
    states: "probability is evenly distributed over all choices of word."

    S1(dress | [red], R2) = S1(object | [red], R2)

    Both equal 1/2 because the meaning function returns 0 for all R2
    extensions of "red", yielding uniform L0 → uniform S1. -/
theorem uniform_after_red_for_r2 (w : Word) (hw : w ≠ .red) :
    s1PMF figureOne [.red] .blueDress .dress =
    s1PMF figureOne [.red] .blueDress w := by
  cases w with
  | red => exact absurd rfl hw
  | dress => rfl
  | object =>
      rw [s1PMF, pmfOfScores_apply (s1ScoreQ_nonneg figureOne _ .blueDress)
          (by decide +kernel),
        pmfOfScores_apply (s1ScoreQ_nonneg figureOne _ .blueDress)
          (by decide +kernel)]
      congr 1

-- ---------- Figure 1d: L1^WORD pragmatic listener ----------

/-- **Finding 6** (Figure 1d): After hearing "red", the pragmatic listener L1
    infers that the target is more likely R3 (red hat) than R1 (red dress).

    L1(R3 | red) = 7/11 ≈ 0.64 > L1(R1 | red) = 4/11 ≈ 0.36

    This is an anticipatory implicature: "red" is the ONLY word available
    for R3 (S1(red|[],R3) = 1), so hearing "red" raises R3's probability.
    For R1, the speaker could have said "dress" instead, so "red" is less
    diagnostic. We pick this up below as a structural foreshadowing of
    [sedivy-etal-1999]'s contrastive-inference findings; CommonGround themselves
    cite [sedivy-2007] for the same effect. -/
theorem listener_anticipation :
    l1PMF figureOne .red .redDress < l1PMF figureOne .red .redHat :=
  pmf_lt_cross (fun r => s1Q_nonneg figureOne [] r .red)
    (fun r => s1Q_nonneg figureOne [] r .red)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

-- ---------- Figure 1e: S1^UTT-IP utterance-level ----------

open scoped ENNReal in
/-- **Finding 7** (Figure 1e): The incremental model prefers "dress" over
    "red dress" for R1 — the key divergence from the global RSA model.

    S1^UTT-IP(dress | R1) = 3/7 ≈ 0.43 > S1^UTT-IP(red dress | R1) = 8/21 ≈ 0.38

    The global model prefers "red dress" (more informative). The incremental
    model prefers "dress" because it is produced in one step with probability
    3/7, while "red dress" requires two steps: S1(red|[],R1) · S1(dress|[red],R1)
    = 4/7 · 2/3 = 8/21 < 9/21 = 3/7. -/
theorem incremental_prefers_bare_noun :
    s1PMF figureOne [] .redDress .red * s1PMF figureOne [.red] .redDress .dress <
    s1PMF figureOne [] .redDress .dress := by
  rw [s1PMF, s1PMF,
    pmfOfScores_apply (s1ScoreQ_nonneg figureOne [] .redDress) (by decide +kernel),
    pmfOfScores_apply (s1ScoreQ_nonneg figureOne [.red] .redDress) (by decide +kernel),
    pmfOfScores_apply (s1ScoreQ_nonneg figureOne [] .redDress) (by decide +kernel),
    ← ENNReal.ofReal_mul (by
      exact_mod_cast div_nonneg (s1ScoreQ_nonneg figureOne [] .redDress .red)
        (Finset.sum_nonneg fun u' _ => s1ScoreQ_nonneg figureOne [] .redDress u'))]
  refine (ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast (by decide +kernel :
    (0:ℚ) < s1ScoreQ figureOne [] .redDress .dress /
      ∑ u', s1ScoreQ figureOne [] .redDress u'))).mpr ?_
  exact_mod_cast (by decide +kernel :
    (s1ScoreQ figureOne [] .redDress .red / ∑ u', s1ScoreQ figureOne [] .redDress u') *
      (s1ScoreQ figureOne [.red] .redDress .dress /
        ∑ u', s1ScoreQ figureOne [.red] .redDress u') <
    s1ScoreQ figureOne [] .redDress .dress /
      ∑ u', s1ScoreQ figureOne [] .redDress u')

/-! ### Verification -/

/-- Map each finding to the model prediction that accounts for it. -/
def formalize : Finding → Prop
  | .adj_first_for_target =>
      s1PMF figureOne [] .redDress .dress < s1PMF figureOne [] .redDress .red
  | .noun_after_adj =>
      s1PMF figureOne [.red] .redDress .object < s1PMF figureOne [.red] .redDress .dress
  | .noun_only_for_r2 =>
      s1PMF figureOne [] .blueDress .red < s1PMF figureOne [] .blueDress .dress
  | .adj_only_for_r3 =>
      s1PMF figureOne [] .redHat .dress < s1PMF figureOne [] .redHat .red
  | .uniform_after_red_for_r2 =>
      ∀ w, w ≠ .red →
        s1PMF figureOne [.red] .blueDress .dress = s1PMF figureOne [.red] .blueDress w
  | .listener_anticipation =>
      l1PMF figureOne .red .redDress < l1PMF figureOne .red .redHat
  | .incremental_prefers_bare_noun =>
      s1PMF figureOne [] .redDress .red * s1PMF figureOne [.red] .redDress .dress <
        s1PMF figureOne [] .redDress .dress

/-- All 7 findings verified. -/
theorem all_findings_verified : ∀ f : Finding, formalize f := by
  intro f; cases f
  · exact adj_first_for_target
  · exact noun_after_adj
  · exact noun_only_for_r2
  · exact adj_only_for_r3
  · exact fun w hw => uniform_after_red_for_r2 w hw
  · exact listener_anticipation
  · exact incremental_prefers_bare_noun

/-! ### §2.4 Weakly-Informative Greedy Unrolling -/

/-! [cohn-gordon-goodman-potts-2019] §2.4 establishes a *weakly
informative* lower bound on greedy unrolling: even though the
incremental speaker has no global view of the utterance space, the
greedy choice at each step yields a complete utterance under which the
literal listener's posterior for the target is at least 1 / |W|. The
bound itself — `l0Utt_ge_inv_card` — is proved generically over the
`IncrementalSemantics` bundle in `Pragmatics/RSA/Incremental.lean`.
What's left for this study is to (i) define the greedy unroller for
Figure 1's three referents and (ii) verify that each output is a complete
utterance true of the target; the §2.4 bound then follows. -/

/-- Greedy unrolling for Figure 1's scene: at each step pick the word
    maximizing L0(r | ctx ++ [w]); stop when ctx is a complete utterance.
    Tabulated by case for the three Figure 1 referents. -/
def greedyUnroll : Referent → List Word
  | .redDress  => [.red, .dress]
  | .blueDress => [.dress]
  | .redHat    => [.red, .object]

/-- §2.4 weakly informative bound, instantiated for Figure 1.

    Each of the three greedy outputs is a complete utterance true of its
    target referent, so the generic `l0Utt_ge_inv_card` theorem from
    `Incremental.lean` immediately gives the 1/|worlds| = 1/3 bound. The
    actual values for this scene are 1, 1/2, 1/2 — the bound is loose here
    by design: it certifies architectural sanity, not optimality. -/
theorem greedyUnroll_weakly_informative (r : Referent) :
    figureOne.l0Utt (greedyUnroll r) r ≥ 1 / 3 := by
  have hlen_nat : figureOne.worlds.length = 3 := by decide
  have hlen : (figureOne.worlds.length : ℝ) = 3 := by exact_mod_cast hlen_nat
  have hr_mem : r ∈ figureOne.worlds := by cases r <;> decide
  have htrue : figureOne.uttSem (greedyUnroll r) r = true := by
    cases r <;> decide
  calc figureOne.l0Utt (greedyUnroll r) r
      ≥ 1 / (figureOne.worlds.length : ℝ) :=
        figureOne.l0Utt_ge_inv_card _ _ hr_mem htrue
    _ = 1 / 3 := by rw [hlen]

/-! ### Global RSA Model + Divergence (§2.4) -/

/-! The global RSA model treats each complete utterance as an atomic
option, normalizing over the whole utterance space rather than chaining
word-by-word. The divergence between global and incremental predictions
for R1 is a central result of [cohn-gordon-goodman-potts-2019] §2.4:
the global model prefers the more-informative "red dress" over the bare
"dress" (standard RSA Q-implicature), but the incremental model prefers
"dress" because chain-rule products penalize longer trajectories
(Finding 7, `incremental_prefers_bare_noun`). -/

/-- The three complete utterances of Figure 1, treated as atomic options
    for the global RSA model. -/
inductive Utterance where
  | dress | redDress | redObject
  deriving DecidableEq, Fintype, Repr

instance : Nonempty Utterance := ⟨.dress⟩

/-- Boolean truth of a complete utterance for a referent. -/
def uttApplies : Utterance → Referent → Bool
  | .dress,     .redDress  => true
  | .dress,     .blueDress => true
  | .redDress,  .redDress  => true
  | .redObject, .redDress  => true
  | .redObject, .redHat    => true
  | _,          _          => false

/-- Global literal listener value (eq. 1): indicator over referents. -/
def globalL0Q (u : Utterance) (r : Referent) : ℚ :=
  (if uttApplies u r then 1 else 0) /
    (∑ r', if uttApplies u r' then (1 : ℚ) else 0)

private theorem globalL0Q_nonneg (u : Utterance) (r : Referent) :
    0 ≤ globalL0Q u r :=
  div_nonneg (by split <;> norm_num)
    (Finset.sum_nonneg fun _ _ => by split <;> norm_num)

/-- Global speaker (eq. 2 at zero cost, α = 1): renormalizes L0 over the
three atomic utterances. -/
noncomputable def globalS1PMF (r : Referent) : PMF Utterance :=
  pmfOfScores (fun u => globalL0Q u r)

/-- **Divergence from incremental** (§2.4): the global RSA prefers the
    fully-modified "red dress" over the bare "dress" for R1, because
    "red dress" uniquely identifies R1 while "dress" leaves R1/R2
    ambiguous. Compare Finding 7 (`incremental_prefers_bare_noun`),
    where the incremental trajectory probability has the opposite
    preference: chain-rule products discount longer trajectories enough
    to flip the ordering. This is the central empirical wedge between
    the two architectures the paper articulates. -/
theorem global_prefers_red_dress :
    globalS1PMF .redDress .dress < globalS1PMF .redDress .redDress :=
  pmf_lt_cross (globalL0Q_nonneg · .redDress) (globalL0Q_nonneg · .redDress)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### Sedivy §3.2 Bridge (Anticipatory Contrastive Inference) -/

/-! [cohn-gordon-goodman-potts-2019] §3.2 reanalyses
[sedivy-2007]'s review of contrastive-inference findings within the
incremental RSA framework. The scene contains a target tall cup, a
contrasting short cup (same category, opposite scale pole), a tall
pitcher (cross-category competitor at the same scale pole), and an
unrelated key. After the listener hears just "tall", the pragmatic
listener L1 prefers the tall cup over the tall pitcher — even though
extension semantics treats both as equally compatible — because a
speaker referring to the pitcher would have said "pitcher" alone (no
need for "tall" to disambiguate from the only other pitcher: there
isn't one). The "tall" is therefore diagnostic of the cup with a
same-category contrast.

The original empirical effect is from [sedivy-etal-1999]; CommonGround cite
the [sedivy-2007] review article that summarizes it.

This file formalises both contrast cells. The contrast scene is the
five-word, four-referent `sedivyBundle` from CommonGround's text. The no-contrast
scene is a four-word, three-referent companion bundle
(`SedivyScene_NoContrast.bundle`) — `.short` is omitted because the
shortCup referent it would describe is absent from the display, leaving
the speaker with no scene-anchored use for the word. The two scenes
share a `Referent` type so a single Cell-typed
`LookProportion SedivyEtAl1999.Cell ℝ` projection can read off both. -/

namespace SedivyScene

/-- Sedivy scene words: scalar adjectives (tall, short) and category
    nouns (cup, pitcher, key). -/
inductive Word where
  | tall | short | cup | pitcher | key
  deriving DecidableEq, Fintype, Repr

instance : Nonempty Word := ⟨.tall⟩

/-- Sedivy scene referents: the four objects in the visual display. -/
inductive Referent where
  | tallCup | shortCup | tallPitcher | key
  deriving DecidableEq, Fintype, Repr

instance : Nonempty Referent := ⟨.tallCup⟩

/-- The Sedivy scene as an `IncrementalSemantics` bundle: 5 words,
    6 complete utterances (3 adj+noun phrases + 3 bare nouns; the
    bare-noun option is essential — without it "tall" is no longer
    diagnostic of the cup), 4 referents. -/
def sedivyBundle : IncrementalSemantics Word Referent where
  wordApplies
    | .tall,    .tallCup     => true
    | .tall,    .tallPitcher => true
    | .short,   .shortCup    => true
    | .cup,     .tallCup     => true
    | .cup,     .shortCup    => true
    | .pitcher, .tallPitcher => true
    | .key,     .key         => true
    | _,        _            => false
  completeUtterances :=
    [[.tall, .cup], [.short, .cup], [.tall, .pitcher],
     [.cup], [.pitcher], [.key]]
  worlds := [.tallCup, .shortCup, .tallPitcher, .key]

end SedivyScene

/-! ### No-contrast companion scene -/

/-! **No-contrast variant** of the Sedivy scene, sharing
`SedivyScene.Referent` but with a smaller word inventory. Empirically
this is the no-contrast cell of [sedivy-etal-1999]'s 2 × 2 × 2
design: the same-category contrast object (the short cup) is removed
from the visual display.

The companion bundle drops `.short` from `Word` and the `[short, cup]`
utterance from `completeUtterances`. Justification: with no shortCup
in the display, a cooperative speaker has no scene-anchored use for
`.short`, and CommonGround's `IncrementalSemantics` is a *scene-specific*
production model rather than a lexicon-wide one. (The listener's
standing mental lexicon still contains `short`; the bundle here is a
model of speaker production for *this scene*, not of mental
inventories.)

Why the fresh `Word` type rather than a `{sedivyBundle with worlds := …}`
update? Keeping `.short` in the lexicon while removing all of its
referents leaves `incrementalSem [.short] _ = 0/0`, which mathlib treats
as `0` but which the `rsa_predict` reflection evaluator cannot reduce.
The fresh type sidesteps the divide-by-zero pattern at the cost of mild
bundle duplication. -/

namespace SedivyScene_NoContrast

inductive Word where
  | tall | cup | pitcher | key
  deriving DecidableEq, Fintype, Repr

instance : Nonempty Word := ⟨.tall⟩

def bundle : IncrementalSemantics Word SedivyScene.Referent where
  wordApplies
    | .tall,    .tallCup     => true
    | .tall,    .tallPitcher => true
    | .cup,     .tallCup     => true
    | .pitcher, .tallPitcher => true
    | .key,     .key         => true
    | _,        _            => false
  completeUtterances :=
    [[.tall, .cup], [.tall, .pitcher], [.cup], [.pitcher], [.key]]
  worlds := [.tallCup, .tallPitcher, .key]

end SedivyScene_NoContrast

open SedivyScene in
/-- **Cohn-Gordon §3.2 prediction**: after hearing "tall", L1 favours
    the tall cup over the tall pitcher (3/5 vs 2/5). The mechanism is
    the contrastive inference: a speaker referring to the pitcher would
    use "pitcher" alone (S1(pitcher | tallPitcher) = 2/3); the only
    referent for which "tall" is the speaker's preferred first word is
    the tall cup, where "cup" alone leaves shortCup ambiguous.

    This formalises [sedivy-2007]'s anticipatory contrast effect
    within the incremental RSA framework (and indirectly captures the
    [sedivy-etal-1999] empirical pattern Sedivy 2007 reviews).
    The paradigm-level statement (Sedivy Pattern 2,
    `VisualWorld.ContrastReducesCompetitorLooks`) requires a
    contrast vs no-contrast comparison; this theorem captures the
    contrast-condition direction only. -/
theorem sedivy_contrast_inference :
    l1PMF SedivyScene.sedivyBundle .tall .tallPitcher <
    l1PMF SedivyScene.sedivyBundle .tall .tallCup :=
  pmf_lt_cross (fun r => s1Q_nonneg SedivyScene.sedivyBundle [] r .tall)
    (fun r => s1Q_nonneg SedivyScene.sedivyBundle [] r .tall)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

open VisualWorld SedivyEtAl1999 in
open scoped ENNReal in
/-- **Cell-typed look projection** for the Sedivy paradigm under the
    incremental-RSA model.

    ## Linking hypothesis (load-bearing, editorial)

    The incremental RSA model produces a *posterior* over referents,
    `L1 : Word → Referent → ℝ`. Visual-world data are *fixation
    proportions*. Mapping the former to the latter requires a linking
    hypothesis. This file makes the simplest one explicit:

      *Bayesian posterior linking hypothesis* — the proportion of looks
      to an object equals the listener's posterior probability of that
      object being the referent at the same point in the unfolding
      utterance.

    [cohn-gordon-goodman-potts-2019] do not state this assumption;
    they discuss the contrastive-inference effect at the level of L1
    posteriors and treat empirical contact with [sedivy-2007]'s
    look data informally. The Bayesian linking hypothesis used here is
    the strongest natural choice given a single normalised posterior.
    A weaker alternative would be a Luce-choice rule over a
    monotone-in-posterior activation; that weakening preserves the
    qualitative inequality patterns this file proves. If a second linking hypothesis enters the codebase, the
    paradigm contract should grow a typed `LinkingHypothesis` API and
    the bridge theorem statement should mention which hypothesis is
    in force.

    ## Construction

    `cgSedivyLooks role c` selects the appropriate scene config based on
    `c.contrast` (`incRSA_sedivy` for the contrast cell;
    `SedivyScene_NoContrast.incRSA_sedivy_noContrast` for the no-contrast
    cell) and reads off `L1 .tall ·` at the referent corresponding to
    `role`. Other factors of the cell (typicality, task) are ignored —
    the incremental RSA model has no internal representation of
    typicality or task, so the projection is constant in those factors.

    Cells in the contrast condition cover four roles; cells in the
    no-contrast condition omit `.contrastingObject` (no shortCup is on
    display) and so collapse to `0` for that role. -/
noncomputable def cgSedivyLooks : LookProportion SedivyEtAl1999.Cell ℝ≥0∞ :=
  fun role c =>
    match c.contrast, role with
    | .contrast,   .target                  => l1PMF SedivyScene.sedivyBundle .tall .tallCup
    | .contrast,   .crossCategoryCompetitor => l1PMF SedivyScene.sedivyBundle .tall .tallPitcher
    | .contrast,   .contrastingObject       => l1PMF SedivyScene.sedivyBundle .tall .shortCup
    | .contrast,   .distractor              => l1PMF SedivyScene.sedivyBundle .tall .key
    | .noContrast, .target                  =>
        l1PMF SedivyScene_NoContrast.bundle .tall .tallCup
    | .noContrast, .crossCategoryCompetitor =>
        l1PMF SedivyScene_NoContrast.bundle .tall .tallPitcher
    | .noContrast, .distractor              =>
        l1PMF SedivyScene_NoContrast.bundle .tall .key
    | _,           _                        => 0

open VisualWorld SedivyEtAl1999 in
open scoped ENNReal in
/-- **Paradigm Pattern 2 verified** for Cohn-Gordon's incremental RSA:
    swapping the contrast factor from `contrast` to `noContrast`
    strictly increases looks to the cross-category competitor (the tall
    pitcher), under the Bayesian posterior linking hypothesis stated on
    `cgSedivyLooks`.

    Mechanism: in the contrast scene, `L1(.tall, tallPitcher) = 2/5`
    because a speaker referring to the pitcher would prefer "pitcher"
    alone (the shortCup distractor pulls "tall" toward the cup). In
    the no-contrast scene there is no shortCup, "tall" is uninformative
    between the two extant scale-pole objects, and `L1(.tall, tallPitcher)
    = 1/2`.

    Discharges
    `SedivyEtAl1999.SatisfiesSedivyPattern.contrast_reduces_competitor_looks`
    for this model. The proof reduces — via the `HasContrastCondition`
    lens applied to a destructured cell — to the per-cell L1 inequality,
    dispatched by `rsa_predict`. -/
theorem cgSedivyLooks_satisfy_contrast_reduces_competitor :
    ContrastReducesCompetitorLooks (Cell := SedivyEtAl1999.Cell) (R := ℝ≥0∞) cgSedivyLooks := by
  intro c
  obtain ⟨_, _, _⟩ := c
  show l1PMF SedivyScene.sedivyBundle .tall .tallPitcher <
       l1PMF SedivyScene_NoContrast.bundle .tall .tallPitcher
  exact pmf_lt_cross (fun r => s1Q_nonneg SedivyScene.sedivyBundle [] r .tall)
    (fun r => s1Q_nonneg SedivyScene_NoContrast.bundle [] r .tall)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-! ### Rubio-Fernández §3.1 Bridge (English Over-Modification, STOP token) -/

/-! [cohn-gordon-goodman-potts-2019] §3.1 reanalyses
[rubio-fernandez-2016]'s finding that English speakers
over-modify (saying "the red dress" when "the dress" suffices in a
display with one dress). The mechanism: an explicit `STOP` token
marks the end of the utterance, so trajectories of different lengths
(`[dress, STOP]` vs `[red, dress, STOP]`) become directly comparable
under the chain rule. Without `STOP`, the chain rule penalizes longer
trajectories monotonically (Finding 7); with `STOP` and a per-word
cost the over-modification preference can emerge in the right cost
regime.

This formalisation establishes the model's lexicon and complete-
utterance set with `STOP`, and proves the structural invariants
(every complete utterance ends in `STOP`; `STOP` does not apply
mid-utterance). The cost-dependent comparison theorem
`S1^UTT-IP(red dress, STOP | R1) > S1^UTT-IP(dress, STOP | R1)` is
left as future work — formalising it requires `Real.exp` over a cost
schedule and a quantitative argument that does not reduce via
`rsa_predict`. -/

namespace RubioFernandezScene

/-- English lexicon for the Rubio-Fernández display: type nouns and
    colour adjectives, plus a `stop` token marking utterance termination. -/
inductive Word where
  | dress | hat | red | blue | stop
  deriving DecidableEq, Fintype, Repr

/-- Display referents: a red dress and a blue hat, the canonical
    minimal pair from [rubio-fernandez-2016]'s display. -/
inductive Referent where
  | redDress | blueHat
  deriving DecidableEq, Fintype, Repr

/-- The Rubio-Fernández scene as an `IncrementalSemantics` bundle:
    five words including `stop`, four complete utterances all ending
    in `stop`, two referents. `stop` does not apply to any referent —
    it is a structural marker, not a content word. -/
def rfBundle : IncrementalSemantics Word Referent where
  wordApplies
    | .dress, .redDress => true
    | .hat,   .blueHat  => true
    | .red,   .redDress => true
    | .blue,  .blueHat  => true
    | _,      _         => false
  completeUtterances :=
    [[.dress, .stop], [.red, .dress, .stop],
     [.hat, .stop],   [.blue, .hat, .stop]]
  worlds := [.redDress, .blueHat]

/-- Every complete utterance terminates with `stop`. This is the
    structural invariant the STOP machinery enforces. -/
theorem completeUtterances_terminate_in_stop :
    ∀ u ∈ rfBundle.completeUtterances, u.getLast? = some .stop := by
  decide

/-- `stop` never applies to any referent — it is a structural marker,
    not a content word. This is what makes a STOP-augmented utterance
    `u ++ [.stop]` veridically equivalent to the underlying content
    sequence `u`. -/
theorem stop_never_applies :
    ∀ r : Referent, rfBundle.wordApplies .stop r = false := by
  decide

end RubioFernandezScene

end CohnGordonEtAl2019
