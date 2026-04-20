import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Incremental
import Linglib.Paradigms.VisualWorld
import Linglib.Phenomena.Reference.Studies.SedivyEtAl1999

/-!
# @cite{cohn-gordon-goodman-potts-2019} — Incremental Iterated Response Model

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
(in `Theories/Pragmatics/RSA/Incremental.lean`), specifying just the lexicon
(`wordApplies`), the closed set of complete utterances, and the world set.
The bundle's `toRSAConfig` builder produces the full `RSAConfig` with chain-
rule speaker, α = 1, no cost, uniform priors, and extension-based L0 — so
the three scenes (Figure 1, the @cite{sedivy-2007} reference game, the
@cite{rubio-fernandez-2016} display) share machinery rather than duplicating it.

The bundle exposes a single deep theorem, `l0Utt_ge_inv_card`, proving
the §2.4 weakly-informative bound generically: any complete utterance true
of `r ∈ worlds` yields a literal posterior at least `1 / worlds.length`.
The Figure 1 application (`greedyUnroll_weakly_informative`) below
discharges only the `r ∈ worlds` and `uttSem utt r = true` premises;
the bound follows.

## Findings

| # | Finding | Status |
|---|---------|--------|
| 1 | Adjective-first preferred for target R1 (Figure 1c) | `rsa_predict` |
| 2 | Noun preferred after adjective for R1 (Figure 1c) | `rsa_predict` |
| 3 | R2 must start with "dress" (Figure 1c) | `rsa_predict` |
| 4 | R3 must start with "red" (Figure 1c) | `rsa_predict` |
| 5 | Uniform fallback after "red" for R2 (§2.2) | `cases w <;> rsa_predict` |
| 6 | L1 anticipatory implicature: "red" → R3 (Figure 1d) | `rsa_predict` |
| 7 | Incremental model prefers bare noun over modified NP (Figure 1e) | `rsa_predict` |
-/

set_option autoImplicit false

namespace CohnGordonEtAl2019

open RSA

-- ============================================================================
-- §1. Domain Types (Figure 1a)
-- ============================================================================

/-- Words available to the incremental speaker (Figure 1a). -/
inductive Word where
  | red | dress | object
  deriving DecidableEq, Fintype, Repr

/-- Referents in the reference game scene (Figure 1a).

    Scene: {red dress (R1), blue dress (R2), red hat (R3)} -/
inductive Referent where
  | redDress | blueDress | redHat
  deriving DecidableEq, Fintype, Repr

-- ============================================================================
-- §2. The Figure 1 bundle
-- ============================================================================

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

-- ============================================================================
-- §3. RSAConfig
-- ============================================================================

/-- Incremental RSA for the Figure 1 reference game.

    Built directly from `figureOne` via the bundle's `toRSAConfig` builder.
    Produces a sequential `RSAConfig` with `Ctx = List Word`, chain-rule
    speaker (`s1Score = L0`, α = 1, no cost), and extension-based L0
    meaning (§2.2). -/
noncomputable def incRSA : RSAConfig Word Referent := figureOne.toRSAConfig

-- ============================================================================
-- §4. Findings
-- ============================================================================

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

-- ============================================================================
-- §5. Predictions
-- ============================================================================

-- ---------- Figure 1c: S1^WORD incremental speaker ----------

/-- **Finding 1** (Figure 1c): The incremental speaker prefers "red" first
    when referring to R1 (red dress).

    S1(red | [], R1) = 4/7 ≈ 0.57 > S1(dress | [], R1) = 3/7 ≈ 0.43

    Mechanism: "red" narrows the extension set to {red dress, red object},
    both true of R1 (trueExtCount = 2, viableExtCount = 2 → meaning = 1).
    "dress" narrows to {dress}, true of R1 (meaning = 1) but the L0
    posterior for R1 is lower because "dress" also applies to R2. -/
theorem adj_first_for_target :
    incRSA.S1_at ([] : List Word) () .redDress .red >
    incRSA.S1_at ([] : List Word) () .redDress .dress := by
  rsa_predict

/-- **Finding 2** (Figure 1c): After producing "red", the speaker prefers
    "dress" over "object" for R1.

    S1(dress | [red], R1) = 2/3 ≈ 0.67 > S1(object | [red], R1) = 1/3 ≈ 0.33

    "red dress" uniquely identifies R1 (only R1 is a red dress), while
    "red object" is ambiguous between R1 and R3. -/
theorem noun_after_adj :
    incRSA.S1_at ([Word.red] : List Word) () .redDress .dress >
    incRSA.S1_at ([Word.red] : List Word) () .redDress .object := by
  rsa_predict

/-- **Finding 3** (Figure 1c): For R2 (blue dress), the speaker must start
    with "dress" — "red" never applies to R2 (it's a blue dress), so all
    extensions of "red" have zero semantics for R2.

    S1(dress | [], R2) > S1(red | [], R2) -/
theorem noun_only_for_r2 :
    incRSA.S1_at ([] : List Word) () .blueDress .dress >
    incRSA.S1_at ([] : List Word) () .blueDress .red := by
  rsa_predict

/-- **Finding 4** (Figure 1c): For R3 (red hat), the speaker must start
    with "red" — "dress" never applies to R3 (it's a hat), so the only
    extension of "dress" (= "dress" itself) has zero semantics for R3.

    S1(red | [], R3) > S1(dress | [], R3) -/
theorem adj_only_for_r3 :
    incRSA.S1_at ([] : List Word) () .redHat .red >
    incRSA.S1_at ([] : List Word) () .redHat .dress := by
  rsa_predict

/-- **Finding 5** (§2.2, uniform fallback): After "red" for R2, no complete
    utterance extension of "red" is true of R2 (blue dress). The paper
    states: "probability is evenly distributed over all choices of word."

    S1(dress | [red], R2) = S1(object | [red], R2)

    Both equal 1/2 because the meaning function returns 0 for all R2
    extensions of "red", yielding uniform L0 → uniform S1. -/
theorem uniform_after_red_for_r2 (w : Word) (hw : w ≠ .red) :
    incRSA.S1_at ([Word.red] : List Word) () .blueDress .dress =
    incRSA.S1_at ([Word.red] : List Word) () .blueDress w := by
  cases w with
  | red => exact absurd rfl hw
  | _ => rsa_predict

-- ---------- Figure 1d: L1^WORD pragmatic listener ----------

/-- **Finding 6** (Figure 1d): After hearing "red", the pragmatic listener L1
    infers that the target is more likely R3 (red hat) than R1 (red dress).

    L1(R3 | red) = 7/11 ≈ 0.64 > L1(R1 | red) = 4/11 ≈ 0.36

    This is an anticipatory implicature: "red" is the ONLY word available
    for R3 (S1(red|[],R3) = 1), so hearing "red" raises R3's probability.
    For R1, the speaker could have said "dress" instead, so "red" is less
    diagnostic. We pick this up below as a structural foreshadowing of
    @cite{sedivy-etal-1999}'s contrastive-inference findings; CG themselves
    cite @cite{sedivy-2007} for the same effect. -/
theorem listener_anticipation :
    incRSA.L1 .red .redHat > incRSA.L1 .red .redDress := by
  rsa_predict

-- ---------- Figure 1e: S1^UTT-IP utterance-level ----------

/-- **Finding 7** (Figure 1e): The incremental model prefers "dress" over
    "red dress" for R1 — the key divergence from the global RSA model.

    S1^UTT-IP(dress | R1) = 3/7 ≈ 0.43 > S1^UTT-IP(red dress | R1) = 8/21 ≈ 0.38

    The global model prefers "red dress" (more informative). The incremental
    model prefers "dress" because it is produced in one step with probability
    3/7, while "red dress" requires two steps: S1(red|[],R1) · S1(dress|[red],R1)
    = 4/7 · 2/3 = 8/21 < 9/21 = 3/7. -/
theorem incremental_prefers_bare_noun :
    incRSA.trajectoryProb () .redDress [.dress] >
    incRSA.trajectoryProb () .redDress [.red, .dress] := by
  rsa_predict

-- ============================================================================
-- §6. Verification
-- ============================================================================

/-- Map each finding to the model prediction that accounts for it. -/
def formalize : Finding → Prop
  | .adj_first_for_target =>
      incRSA.S1_at ([] : List Word) () .redDress .red >
      incRSA.S1_at ([] : List Word) () .redDress .dress
  | .noun_after_adj =>
      incRSA.S1_at ([Word.red] : List Word) () .redDress .dress >
      incRSA.S1_at ([Word.red] : List Word) () .redDress .object
  | .noun_only_for_r2 =>
      incRSA.S1_at ([] : List Word) () .blueDress .dress >
      incRSA.S1_at ([] : List Word) () .blueDress .red
  | .adj_only_for_r3 =>
      incRSA.S1_at ([] : List Word) () .redHat .red >
      incRSA.S1_at ([] : List Word) () .redHat .dress
  | .uniform_after_red_for_r2 =>
      ∀ w, w ≠ .red →
        incRSA.S1_at ([Word.red] : List Word) () .blueDress .dress =
        incRSA.S1_at ([Word.red] : List Word) () .blueDress w
  | .listener_anticipation =>
      incRSA.L1 .red .redHat > incRSA.L1 .red .redDress
  | .incremental_prefers_bare_noun =>
      incRSA.trajectoryProb () .redDress [.dress] >
      incRSA.trajectoryProb () .redDress [.red, .dress]

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

-- ============================================================================
-- §6b. §2.4 Weakly-Informative Greedy Unrolling
-- ============================================================================

/-! @cite{cohn-gordon-goodman-potts-2019} §2.4 establishes a *weakly
informative* lower bound on greedy unrolling: even though the
incremental speaker has no global view of the utterance space, the
greedy choice at each step yields a complete utterance under which the
literal listener's posterior for the target is at least 1 / |W|. The
bound itself — `l0Utt_ge_inv_card` — is proved generically over the
`IncrementalSemantics` bundle in `Theories/Pragmatics/RSA/Incremental.lean`.
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

-- ============================================================================
-- §7. Global RSA Model + Divergence (§2.4)
-- ============================================================================

/-! The global RSA model treats each complete utterance as an atomic
option, normalizing over the whole utterance space rather than chaining
word-by-word. The divergence between global and incremental predictions
for R1 is a central result of @cite{cohn-gordon-goodman-potts-2019} §2.4:
the global model prefers the more-informative "red dress" over the bare
"dress" (standard RSA Q-implicature), but the incremental model prefers
"dress" because chain-rule products penalize longer trajectories
(Finding 7, `incremental_prefers_bare_noun`). -/

/-- The three complete utterances of Figure 1, treated as atomic options
    for the global RSA model. -/
inductive Utterance where
  | dress | redDress | redObject
  deriving DecidableEq, Fintype, Repr

/-- Boolean truth of a complete utterance for a referent. -/
def uttApplies : Utterance → Referent → Bool
  | .dress,     .redDress  => true
  | .dress,     .blueDress => true
  | .redDress,  .redDress  => true
  | .redObject, .redDress  => true
  | .redObject, .redHat    => true
  | _,          _          => false

/-- Global RSA model for the Figure 1 reference game: U = full utterances,
    one-shot normalization, α = 1 with no cost term. The same model class
    @cite{frank-goodman-2012} would write for a non-incremental speaker. -/
noncomputable def globalRSA : RSAConfig Utterance Referent where
  meaning _ _ u r := if uttApplies u r then 1 else 0
  meaning_nonneg _ _ u r := by split <;> norm_num
  s1Score l0 _ _ w u := l0 u w
  s1Score_nonneg _ _ _ _ _ hl _ := hl _ _
  α := 1
  α_pos := one_pos
  latentPrior_nonneg _ _ := by norm_num
  worldPrior_nonneg _ := by norm_num

/-- **Divergence from incremental** (§2.4): the global RSA prefers the
    fully-modified "red dress" over the bare "dress" for R1, because
    "red dress" uniquely identifies R1 while "dress" leaves R1/R2
    ambiguous. Compare Finding 7 (`incremental_prefers_bare_noun`),
    where the incremental trajectory probability has the opposite
    preference: chain-rule products discount longer trajectories enough
    to flip the ordering. This is the central empirical wedge between
    the two architectures the paper articulates. -/
theorem global_prefers_red_dress :
    globalRSA.S1 () .redDress .redDress > globalRSA.S1 () .redDress .dress := by
  rsa_predict

-- ============================================================================
-- §8. Sedivy §3.2 Bridge (Anticipatory Contrastive Inference)
-- ============================================================================

/-! @cite{cohn-gordon-goodman-potts-2019} §3.2 reanalyses
@cite{sedivy-2007}'s review of contrastive-inference findings within the
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

The original empirical effect is from @cite{sedivy-etal-1999}; CG cite
the @cite{sedivy-2007} review article that summarizes it.

This file formalises both contrast cells. The contrast scene is the
five-word, four-referent `sedivyBundle` from CG's text. The no-contrast
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

/-- Sedivy scene referents: the four objects in the visual display. -/
inductive Referent where
  | tallCup | shortCup | tallPitcher | key
  deriving DecidableEq, Fintype, Repr

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

/-- Incremental RSA on the Sedivy scene, derived from `sedivyBundle`. -/
noncomputable def incRSA_sedivy : RSAConfig Word Referent := sedivyBundle.toRSAConfig

end SedivyScene

-- ============================================================================
-- §8b. No-contrast companion scene
-- ============================================================================

/-! **No-contrast variant** of the Sedivy scene, sharing
`SedivyScene.Referent` but with a smaller word inventory. Empirically
this is the no-contrast cell of @cite{sedivy-etal-1999}'s 2 × 2 × 2
design: the same-category contrast object (the short cup) is removed
from the visual display.

The companion bundle drops `.short` from `Word` and the `[short, cup]`
utterance from `completeUtterances`. Justification: with no shortCup
in the display, a cooperative speaker has no scene-anchored use for
`.short`, and CG's `IncrementalSemantics` is a *scene-specific*
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

noncomputable def incRSA_sedivy_noContrast : RSAConfig Word SedivyScene.Referent :=
  bundle.toRSAConfig

end SedivyScene_NoContrast

open SedivyScene in
/-- **Cohn-Gordon §3.2 prediction**: after hearing "tall", L1 favours
    the tall cup over the tall pitcher (3/5 vs 2/5). The mechanism is
    the contrastive inference: a speaker referring to the pitcher would
    use "pitcher" alone (S1(pitcher | tallPitcher) = 2/3); the only
    referent for which "tall" is the speaker's preferred first word is
    the tall cup, where "cup" alone leaves shortCup ambiguous.

    This formalises @cite{sedivy-2007}'s anticipatory contrast effect
    within the incremental RSA framework (and indirectly captures the
    @cite{sedivy-etal-1999} empirical pattern Sedivy 2007 reviews).
    The paradigm-level statement (Sedivy Pattern 2,
    `Paradigms.VisualWorld.ContrastReducesCompetitorLooks`) requires a
    contrast vs no-contrast comparison; this theorem captures the
    contrast-condition direction only. -/
theorem sedivy_contrast_inference :
    SedivyScene.incRSA_sedivy.L1 .tall .tallCup >
    SedivyScene.incRSA_sedivy.L1 .tall .tallPitcher := by
  rsa_predict

open Paradigms.VisualWorld SedivyEtAl1999 in
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

    @cite{cohn-gordon-goodman-potts-2019} do not state this assumption;
    they discuss the contrastive-inference effect at the level of L1
    posteriors and treat empirical contact with @cite{sedivy-2007}'s
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
noncomputable def cgSedivyLooks : LookProportion SedivyEtAl1999.Cell ℝ :=
  fun role c =>
    match c.contrast, role with
    | .contrast,   .target                  => SedivyScene.incRSA_sedivy.L1 .tall .tallCup
    | .contrast,   .crossCategoryCompetitor => SedivyScene.incRSA_sedivy.L1 .tall .tallPitcher
    | .contrast,   .contrastingObject       => SedivyScene.incRSA_sedivy.L1 .tall .shortCup
    | .contrast,   .distractor              => SedivyScene.incRSA_sedivy.L1 .tall .key
    | .noContrast, .target                  =>
        SedivyScene_NoContrast.incRSA_sedivy_noContrast.L1 .tall .tallCup
    | .noContrast, .crossCategoryCompetitor =>
        SedivyScene_NoContrast.incRSA_sedivy_noContrast.L1 .tall .tallPitcher
    | .noContrast, .distractor              =>
        SedivyScene_NoContrast.incRSA_sedivy_noContrast.L1 .tall .key
    | _,           _                        => 0

open Paradigms.VisualWorld SedivyEtAl1999 in
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
    ContrastReducesCompetitorLooks (Cell := SedivyEtAl1999.Cell) (R := ℝ) cgSedivyLooks := by
  intro c
  obtain ⟨_, _, _⟩ := c
  show SedivyScene_NoContrast.incRSA_sedivy_noContrast.L1 .tall .tallPitcher >
       SedivyScene.incRSA_sedivy.L1 .tall .tallPitcher
  rsa_predict


-- ============================================================================
-- §9. Rubio-Fernández §3.1 Bridge (English Over-Modification, STOP token)
-- ============================================================================

/-! @cite{cohn-gordon-goodman-potts-2019} §3.1 reanalyses
@cite{rubio-fernandez-2016}'s finding that English speakers
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
    minimal pair from @cite{rubio-fernandez-2016}'s display. -/
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
