import Linglib.Core.Discourse.InformationStructure
import Linglib.Theories.Syntax.DependencyGrammar.Formal.DependencyLength

/-!
# Heaviness vs. Newness in Constituent Ordering
@cite{arnold-wasow-losongco-ginstrom-2000}

A corpus analysis and an elicitation experiment disentangle two confounded
predictors of English constituent ordering:

1. **Heaviness** — structural complexity, measured by relative word count
2. **Newness** — discourse status: given/inferable vs. new

These factors are naturally confounded: new referents require more descriptive
material, so they tend to be heavier. Arnold et al. use logistic regression
to show that in **both** constructions studied — dative alternation and heavy
NP shift — both weight and newness independently predict construction choice.

## Studies

- **Corpus analysis** (§2): Aligned-Hansard corpus (Canadian parliament debates).
  Examines dative alternation (verb *give*, N=269) and heavy NP shift
  (*bring...to* N=223, *take...into account* N=167). Both heaviness and newness
  significantly predict ordering in both constructions; no interactions.

- **Give experiment** (§3): Elicitation experiment, 48 participants (24 pairs),
  Stanford community. Dative alternation only (*give*), N=1684 instructions
  post-exclusion. Both factors significant, plus a significant interaction:
  heaviness has the largest effect when both constituents share newness status.

## Constructions

- **Double Object (DO)**: V Recipient Theme — "give Mary the book"
- **Prepositional Dative (PD)**: V Theme to-Recipient — "give the book to Mary"
- **Nonshifted (HNPS)**: V DO PP — "bring the news to the committee"
- **Shifted (HNPS)**: V PP DO — "bring to the committee the news that..."

The "heavy/new last" principle: speakers place heavier and newer constituents
later. In DA, DO puts the theme last; PD puts the recipient last. In HNPS,
shifting puts the direct object after the PP (later position).

## Central Finding

Both heaviness and newness independently contribute to ordering in both
constructions. Neither factor can be reduced to the other. The interaction
between them (significant only in the experiment) shows they function as
competing constraints: each factor's effect is larger when the other is
less constraining.

## Bridges

- `Core.InformationStructure.DiscourseStatus`: Arnold et al. collapse
  @cite{prince-1981}'s three-way given/inferable/new into two categories.
  Their "given" (given + inferable) is coarser than
  @cite{kratzer-selkirk-2020}'s partition.
- `DependencyLength.lean`: the "heavy last" effect is DLM's short-before-long
  (Behaghel's Gesetz der wachsenden Glieder). But DLM cannot model the
  independent newness effect that Arnold et al. demonstrate.
-/

namespace Phenomena.WordOrder.Studies.ArnoldEtAl2000

open Core.InformationStructure

-- ============================================================================
-- §1: Corpus Analysis — Aligned-Hansard (§2 of paper)
-- ============================================================================

/-- Constructions studied in the corpus analysis. -/
inductive Construction where
  /-- Dative alternation with "give": DO (V Rec Theme) vs. PD (V Theme to-Rec). -/
  | dativeAlternation
  /-- Heavy NP shift: nonshifted (V DO PP) vs. shifted (V PP DO).
      Uses "bring...to" and "take...into account." -/
  | heavyNPShift
  deriving DecidableEq, BEq, Repr

/-- Corpus verb token counts (Table 1). -/
structure VerbData where
  verb : String
  construction : Construction
  n : Nat
  deriving Repr

def bringTo : VerbData :=
  { verb := "bring...to", construction := .heavyNPShift, n := 223 }

def takeIntoAccount : VerbData :=
  { verb := "take...into account", construction := .heavyNPShift, n := 167 }

def giveCorpus : VerbData :=
  { verb := "give", construction := .dativeAlternation, n := 269 }

/-- Total corpus examples: 659 (Table 1). -/
theorem corpus_total :
    bringTo.n + takeIntoAccount.n + giveCorpus.n = 659 := by native_decide

/-- HNPS subcorpus: 390 examples. -/
theorem hnps_total :
    bringTo.n + takeIntoAccount.n = 390 := by native_decide

-- ============================================================================
-- §2: Heaviness Categories and Cell Sizes
-- ============================================================================

/-- Heaviness categories for dative alternation (Table 2).
    Measured as relative length: theme NP length − goal NP length. -/
inductive DAHeaviness where
  /-- Theme shorter: theme − goal ≤ −2 -/
  | themeShorter
  /-- Theme ≈ goal: theme − goal between −1 and 1 -/
  | themeEqualGoal
  /-- Theme longer: theme − goal ≥ 2 -/
  | themeLonger
  deriving DecidableEq, BEq, Repr

/-- Heaviness categories for heavy NP shift (Table 3).
    Measured as relative length: DO length − PP length. -/
inductive HNPSHeaviness where
  /-- DO ≪ PP: DO − PP ≤ −4 -/
  | doMuchShorter
  /-- DO < PP: DO − PP between −3 and −1 -/
  | doShorter
  /-- DO = PP: DO − PP = 0 -/
  | doEqual
  /-- DO > PP: DO − PP between 1 and 3 -/
  | doLonger
  /-- DO ≫ PP: DO − PP ≥ 4 -/
  | doMuchLonger
  deriving DecidableEq, BEq, Repr

/-- Figure 1 cell sizes: "give" dative corpus, by heaviness category. -/
def fig1n : DAHeaviness → Nat
  | .themeShorter  => 26
  | .themeEqualGoal => 89
  | .themeLonger   => 154

/-- Figure 1 cell sizes sum to the give corpus total. -/
theorem fig1_sums_to_give :
    fig1n .themeShorter + fig1n .themeEqualGoal + fig1n .themeLonger =
    giveCorpus.n := by native_decide

/-- Most DA items have theme longer than goal (57%): English datives
    typically have longer themes, consistent with the heavy-last tendency. -/
theorem da_skews_theme_heavy :
    fig1n .themeLonger > fig1n .themeShorter + fig1n .themeEqualGoal := by
  native_decide

/-- Figure 2 cell sizes: HNPS corpus, by heaviness category. -/
def fig2n : HNPSHeaviness → Nat
  | .doMuchShorter => 48
  | .doShorter     => 114
  | .doEqual       => 38
  | .doLonger      => 57
  | .doMuchLonger  => 133

/-- Figure 2 cell sizes sum to the HNPS total. -/
theorem fig2_sums_to_hnps :
    fig2n .doMuchShorter + fig2n .doShorter + fig2n .doEqual +
    fig2n .doLonger + fig2n .doMuchLonger =
    bringTo.n + takeIntoAccount.n := by native_decide

/-- The DO ≫ PP category is the largest single cell (133/390 = 34%),
    reflecting the prevalence of heavy direct objects in shifted constructions. -/
theorem hnps_doMuchLonger_largest :
    fig2n .doMuchLonger > fig2n .doMuchShorter ∧
    fig2n .doMuchLonger > fig2n .doShorter ∧
    fig2n .doMuchLonger > fig2n .doEqual ∧
    fig2n .doMuchLonger > fig2n .doLonger := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

-- ============================================================================
-- §3: Give Experiment (§3 of paper)
-- ============================================================================

/-- 48 participants (24 pairs), 42 sessions included post-exclusion,
    1684 instructions in final analysis. -/
def exp_participants : Nat := 48
def exp_pairs : Nat := 24
def exp_sessions_included : Nat := 42
def exp_n : Nat := 1684

/-- Newness conditions in the experiment. -/
inductive ExpNewness where
  /-- Theme is given (= goal is new) -/
  | themeGiven
  /-- Both constituents are given -/
  | bothGiven
  /-- Goal is given (= theme is new) -/
  | goalGiven
  deriving DecidableEq, BEq, Repr

/-- Figure 8 cell sizes by newness condition. -/
def fig8n : ExpNewness → Nat
  | .themeGiven => 808
  | .bothGiven  => 27
  | .goalGiven  => 849

/-- Figure 8 cell sizes sum to experiment total. -/
theorem fig8_sums_to_exp :
    fig8n .themeGiven + fig8n .bothGiven + fig8n .goalGiven = exp_n := by
  native_decide

/-- "Both given" is extremely rare (< 2%), confirming the experiment
    successfully manipulated newness as a between-constituent contrast. -/
theorem both_given_rare :
    fig8n .bothGiven * 100 / exp_n < 2 := by native_decide

-- ============================================================================
-- §4: Logistic Regression Results
-- ============================================================================

/-- Which factors were selected by the logistic regression for each analysis. -/
structure RegressionResult where
  label : String
  /-- Heaviness is a significant predictor -/
  heavinessSig : Bool
  /-- Newness is a significant predictor -/
  newnessSig : Bool
  /-- Newness × heaviness interaction is significant -/
  interactionSig : Bool
  deriving Repr, DecidableEq, BEq

/-- Corpus DA: both heaviness and newness significant, no interaction. -/
def daCorpusResult : RegressionResult :=
  { label := "DA corpus (give)"
    heavinessSig := true
    newnessSig := true
    interactionSig := false }

/-- Corpus HNPS: heaviness, newness, AND verb significant, no interactions.
    (Verb effect: *take into account* has higher shifting rate than *bring to*,
    likely because it is an opaque collocation.) -/
def hnpsCorpusResult : RegressionResult :=
  { label := "HNPS corpus (bring to + take into account)"
    heavinessSig := true
    newnessSig := true
    interactionSig := false }

/-- Experiment DA: heaviness, newness, AND their interaction significant.
    (Production difficulty also significant but omitted from structure.) -/
def daExperimentResult : RegressionResult :=
  { label := "DA experiment (give)"
    heavinessSig := true
    newnessSig := true
    interactionSig := true }

/-- **Central finding**: BOTH factors significantly predict ordering in ALL
    analyses. Neither can be reduced to the other. -/
theorem both_factors_in_all_analyses :
    daCorpusResult.heavinessSig ∧ daCorpusResult.newnessSig ∧
    hnpsCorpusResult.heavinessSig ∧ hnpsCorpusResult.newnessSig ∧
    daExperimentResult.heavinessSig ∧ daExperimentResult.newnessSig :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- No interaction in either corpus analysis: heaviness and newness contribute
    independently. -/
theorem corpus_no_interactions :
    !daCorpusResult.interactionSig ∧ !hnpsCorpusResult.interactionSig :=
  ⟨rfl, rfl⟩

/-- The experiment finds a significant interaction: heaviness has the largest
    effect when both constituents share newness status, and vice versa. -/
theorem experiment_has_interaction :
    daExperimentResult.interactionSig := rfl

-- ============================================================================
-- §5: Effect Size Comparison
-- ============================================================================

/-- −2 × Log Likelihood Ratio values (× 10 for integer encoding) from the
    paper's logistic regressions. Larger values = stronger predictor. -/

-- Corpus DA
def daCorpus_heavinessLR : Nat := 995   -- −2*Log LR = 99.5, p < .001
def daCorpus_newnessLR   : Nat := 70    -- −2*Log LR = 7.0, p < .01

-- Corpus HNPS
def hnpsCorpus_heavinessLR : Nat := 1209  -- −2*Log LR = 120.9, p < .001
def hnpsCorpus_newnessLR   : Nat := 235   -- −2*Log LR = 23.5, p < .001
def hnpsCorpus_verbLR      : Nat := 314   -- −2*Log LR = 31.4, p < .001

-- Experiment DA
def daExp_newnessLR    : Nat := 2980  -- −2*Log LR = 298, p < .001
def daExp_heavinessLR  : Nat := 95    -- −2*Log LR = 9.5, p < .005
def daExp_interactionLR : Nat := 200  -- −2*Log LR = 20, p < .001

/-- In the corpus, heaviness has a far larger effect size than newness
    in both constructions. -/
theorem corpus_heaviness_dominates :
    daCorpus_heavinessLR > daCorpus_newnessLR ∧
    hnpsCorpus_heavinessLR > hnpsCorpus_newnessLR := by
  constructor <;> native_decide

/-- In the experiment, newness dominates: its effect is 30× larger than
    heaviness. This reversal reflects the narrower heaviness range in the
    experiment (Table 6: range −8 to 20 words) vs. corpus (−29 to 35). -/
theorem experiment_newness_dominates :
    daExp_newnessLR > daExp_heavinessLR := by native_decide

/-- Heaviness effect is stronger in the corpus than in the experiment,
    consistent with the wider weight range in naturally occurring data. -/
theorem heaviness_stronger_in_corpus :
    daCorpus_heavinessLR > daExp_heavinessLR := by native_decide

/-- Newness effect is stronger in the experiment than in the corpus,
    consistent with the experiment's more controlled newness manipulation
    (immediate mention vs. within-agenda-item mention). -/
theorem newness_stronger_in_experiment :
    daExp_newnessLR > daCorpus_newnessLR := by native_decide

-- ============================================================================
-- §6: Table 6 — Heaviness Range Comparison
-- ============================================================================

/-- Average difference in NP length (phrase 1 − phrase 2, × 10) for each
    heaviness category, from Table 6. Shows the actual weight contrasts
    across the three data sets.

    For DA: phrase 1 = theme NP, phrase 2 = goal NP.
    For HNPS: phrase 1 = direct object NP, phrase 2 = prepositional phrase. -/
structure LengthDiffRange where
  label : String
  rangeMin : Int   -- minimum raw difference in words
  rangeMax : Int   -- maximum raw difference in words
  deriving Repr

def hnpsRange : LengthDiffRange :=
  { label := "HNPS corpus", rangeMin := -21, rangeMax := 44 }

def daCorpusRange : LengthDiffRange :=
  { label := "DA corpus", rangeMin := -29, rangeMax := 35 }

def daExpRange : LengthDiffRange :=
  { label := "DA experiment", rangeMin := -8, rangeMax := 20 }

/-- The corpus data spans a far wider heaviness range than the experiment.
    This explains why heaviness dominates in the corpus but not the experiment:
    with less variation in weight, there is less for the weight factor to
    predict. -/
theorem corpus_wider_range :
    daCorpusRange.rangeMax - daCorpusRange.rangeMin >
    daExpRange.rangeMax - daExpRange.rangeMin := by native_decide

/-- HNPS has the widest heaviness range overall, spanning 65 words of
    difference between the lightest and heaviest items. -/
theorem hnps_widest_range :
    hnpsRange.rangeMax - hnpsRange.rangeMin >
    daCorpusRange.rangeMax - daCorpusRange.rangeMin ∧
    hnpsRange.rangeMax - hnpsRange.rangeMin >
    daExpRange.rangeMax - daExpRange.rangeMin := by
  constructor <;> native_decide

-- ============================================================================
-- §7: Bridge — Discourse Status Classification
-- ============================================================================

/-- Arnold et al.'s "given" (previously mentioned or inferable from something
    mentioned within the current agenda item in the corpus; established by
    question or mention in the immediately preceding utterance in the
    experiment) maps to `DiscourseStatus.given`.

    Their classification collapses @cite{prince-1981}'s three-way
    given/inferable/new into two categories: inferables are grouped with
    given. -/
def arnoldGiven : DiscourseStatus := .given

/-- Arnold et al.'s "new" (not previously mentioned and not inferable) maps
    to `DiscourseStatus.new`. This is broader than
    @cite{kratzer-selkirk-2020}'s `.new` — it includes material that K&S
    would mark as `.focused` ([FoC]-marked, contrasted). -/
def arnoldNew : DiscourseStatus := .new

theorem given_aligns : arnoldGiven = DiscourseStatus.given := rfl
theorem new_aligns   : arnoldNew   = DiscourseStatus.new   := rfl

-- ============================================================================
-- §8: Bridge — DLM: Correct on Weight, Blind to Discourse
-- ============================================================================

open DepGrammar DepGrammar.DependencyLength

/-!
## DLM: Correct on weight, blind to discourse

`totalDepLength` is defined over `Dependency` = `(headIdx × depIdx × DepRel)`.
The function never accesses `t.words`, so no property of the words — form,
category, features, discourse status — enters the computation.

Arnold et al.'s finding that newness significantly predicts ordering in BOTH
constructions (even after controlling for heaviness) means DLM alone is
insufficient as a complete account of constituent ordering.
-/

/-- **DLM word-invariance.** `totalDepLength` yields the same value for any
two trees sharing the same dependency structure, regardless of the words. -/
theorem totalDepLength_word_invariant (deps : List Dependency) (rootIdx : Nat)
    (words1 words2 : List Word) :
    totalDepLength { words := words1, deps := deps, rootIdx := rootIdx } =
    totalDepLength { words := words2, deps := deps, rootIdx := rootIdx } := by
  rfl

/-- DLM assigns identical cost to trees differing only in whether NPs are
discourse-given or discourse-new. -/
theorem dlm_discourse_blind
    (deps : List Dependency) (rootIdx : Nat)
    (givenWords newWords : List Word) :
    totalDepLength { words := givenWords, deps := deps, rootIdx := rootIdx } =
    totalDepLength { words := newWords, deps := deps, rootIdx := rootIdx } :=
  totalDepLength_word_invariant deps rootIdx givenWords newWords

/-- Even at the single-dependency level, `depLength` ignores the grammatical
relation. The cost is purely `|headIdx - depIdx|`. -/
theorem depLength_ignores_relation (h d : Nat) (r1 r2 : UD.DepRel) :
    depLength ⟨h, d, r1⟩ = depLength ⟨h, d, r2⟩ := by
  rfl

/-- DLM correctly predicts the weight direction: heavy NP shift reduces
dependency length. -/
theorem dlm_predicts_heavy_shift :
    totalDepLength heavyNPShiftOptimal < totalDepLength heavyNPShiftSuboptimal := by
  native_decide

-- ============================================================================
-- §9: Minimal Adequate Model
-- ============================================================================

/-- A pure-discourse ordering model: the preference for placing a constituent
in late position is determined solely by its discourse status. -/
structure PureDiscourseModel where
  latePref : DiscourseStatus → Nat
  /-- The core given-before-new claim. -/
  new_after_given : latePref .new > latePref .given

/-- A pure-discourse model is weight-blind by type: for a fixed discourse
status, it assigns the same preference regardless of constituent length. -/
theorem pure_discourse_weight_blind (m : PureDiscourseModel)
    (s : DiscourseStatus) (_weight1 _weight2 : Nat) :
    m.latePref s = m.latePref s := rfl

/-- Arnold et al.'s corpus results refute pure-discourse accounts:
heaviness is significant in BOTH constructions even after controlling
for newness. A weight-blind model cannot explain these results. -/
theorem heaviness_refutes_pure_discourse :
    daCorpusResult.heavinessSig ∧ hnpsCorpusResult.heavinessSig :=
  ⟨rfl, rfl⟩

/-- The minimal adequate model type: a function of both weight and discourse
status, encoding Arnold et al.'s central finding. -/
abbrev OrderingModel := Nat → DiscourseStatus → Nat

end Phenomena.WordOrder.Studies.ArnoldEtAl2000
