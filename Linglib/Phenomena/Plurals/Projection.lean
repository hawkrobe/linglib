import Linglib.Core.Logic.Truth3
import Linglib.Data.Examples.Schema

/-!
# Phenomena.Plurals.Projection — Test-suite hub for homogeneity projection

Cross-paper test substrate for how the homogeneity gap of plural definites
projects under embedding quantifiers and operators. The pattern's empirical
literature spans @cite{lobner-2000}, @cite{gajewski-2005},
@cite{spector-2013}, @cite{magri-2014}, @cite{kriz-chemla-2015},
@cite{kriz-2016}, @cite{bar-lev-2021}, @cite{augurzky-etal-2023},
@cite{kriz-spector-2021}, and @cite{haslinger-2025-diss}; the empirical
generalisation predates any one formal account, justifying a `Phenomena/`
(theory-neutral) anchor.

## Main declarations

* `EmbeddingOperator` — operator labels recurring across the literature.
* `GapScenario` — scenario classification used by the C-series experiments
  (TRUE / FALSE / GAP / GAP? / GAP??).
* `ProjectionPredict` — the shared signature any account of homogeneity
  projection must satisfy; given an `(operator, scenario)` pair, predict a
  trivalent `Truth3` value.
* `ProjectionDatum` — typed empirical datum; lifted from the raw
  `LinguisticExample` rows by `fromExample`.
* `Examples` (generator-managed) — pooled stimulus rows from each paper
  that contributes projection-relevant data; per-paper JSON inputs live in
  `Linglib/Data/Examples/<Paper>.json` and route here via per-paper
  `.target` sidecars (see `scripts/gen_examples.py`).
* `allData` — the test pool: every `LinguisticExample` whose
  `paperFeatures` carry the keys this hub recognises.

Studies files (e.g. [[KrizChemla2015]], [[AugurzkyEtAl2023]]) retrieve their
paper-specific slice by filtering `Examples.all` (option-B per-paper
accessor pattern).

## Implementation notes

This file is the entry point for cross-account testing of homogeneity
projection. The shape is: a `ProjectionPredict` signature each account
implements; a `ProjectionDatum` carrying observed outcomes; decidable
theorems comparing each account's prediction to each datum, including
*divergence* theorems where two accounts disagree.

The substrate is restricted to the smallest set of operator cases that
closes the current ≥2-consumer graduation criterion: `every` / `no`
(every major contribution tests these), `exactlyTwo` (introduced by
@cite{kriz-chemla-2015} Exps. A3/B3/C3/C4), and `notEvery` (the
no/notEvery asymmetry from @cite{augurzky-etal-2023}). Extend as new
consumers land.

There is deliberately *no* projector-stipulated `monotonicity :
EmbeddingOperator → ContextPolarity` function — the classical mapping
(`notEvery ↦ downward` by De Morgan) disagrees with the empirical
observation that `notEvery` patterns with `every` rather than `no` in
QUD-manipulation acceptance (@cite{augurzky-etal-2023}), so any single
mapping would be wrong for at least one consumer.

## Todo

* Wire `ProjectionPredict` implementations from each rival account: the
  scalar-implicature/exhaustification accounts (@cite{magri-2014},
  @cite{bar-lev-2021}), the supervaluation/trivalence accounts
  (@cite{spector-2013}, @cite{kriz-2016}, @cite{kriz-spector-2021}), and
  the presupposition account (@cite{gajewski-2005} + Schwarzschild 1994 —
  no linglib study file yet).
* Prove decidable per-datum predictions and cross-account divergence
  theorems once those implementations land.
* Add a denotation hook `EmbeddingOperator → ∀ α, Core.Quantification.GQ α`
  once accounts derive predictions structurally rather than dispatch on
  label (per @cite{peters-westerstahl-2006} discipline).
-/

namespace Phenomena.Plurals.Projection

open Core.Duality (Truth3)
open Data.Examples (LinguisticExample SourceRef)

/-! ### Substrate -/

/--
Quantifier-operator labels for plural-definite embedding environments,
restricted to operators actually consumed by linglib's homogeneity-
projection study files.
-/
inductive EmbeddingOperator where
  | every
  | no
  | exactlyTwo
  | notEvery
  deriving Repr, DecidableEq

/--
Scenario classification used by the trivalent-judgment paradigm
(@cite{kriz-chemla-2015}). The first three are the canonical TRUE / FALSE
/ GAP triad; `gapQ` and `gapQQ` are the `exactly N` refinements that
isolate the at-least-reading from genuine homogeneity projection.
-/
inductive GapScenario where
  | trueScenario   -- all-positive baseline
  | falseScenario  -- all-negative baseline
  | gap            -- standard mixed scenario (homogeneity violated)
  | gapQ           -- at-least reading possible (exactly-only)
  | gapQQ          -- at-least reading ruled out (exactly-only)
  deriving Repr, DecidableEq

/-! ### Test-suite schema -/

/--
Theoretical-prediction signature any account of homogeneity projection
must satisfy: given an embedder label and a scenario, predict the
trivalent `Truth3` value the account commits to.
-/
abbrev ProjectionPredict := EmbeddingOperator → GapScenario → Truth3

/--
Empirical datum derived from a paper-anchored `LinguisticExample`.
`observed` is the trivalent value the paper's findings commit to in this
`(operator, scenario)` cell; `source` is the originating paper.
-/
structure ProjectionDatum where
  operator : EmbeddingOperator
  scenario : GapScenario
  observed : Truth3
  source   : SourceRef
  deriving Repr, DecidableEq

/-! ### `LinguisticExample` adapter -/

/--
Read an `EmbeddingOperator` from a string value of the `paperFeatures`
`"operator"` key. `none` for unrecognised labels.
-/
def parseOperator : String → Option EmbeddingOperator
  | "every"      => some .every
  | "no"         => some .no
  | "exactlyTwo" => some .exactlyTwo
  | "notEvery"   => some .notEvery
  | _            => none

/--
Read a `GapScenario` from a string value of the `paperFeatures`
`"condition"` key. `none` for unrecognised labels.
-/
def parseScenario : String → Option GapScenario
  | "TRUE"  => some .trueScenario
  | "FALSE" => some .falseScenario
  | "GAP"   => some .gap
  | "GAP?"  => some .gapQ
  | "GAP??" => some .gapQQ
  | _       => none

/--
Compute the observed `Truth3` value for a `(scenario, gapDetected)` cell.

Baseline conditions are unambiguous: `TRUE → .true`, `FALSE → .false`.
For gap-bearing scenarios, gap detection means the empirical distribution
peaks on the trivalent middle (`.indet`); a non-detection on a
gap-bearing scenario means an alternative reading (typically an at-least
reading for non-monotonic embedders) rendered the sentence non-gappy.
-/
def observedTruth (scenario : GapScenario) (gapDetected : Bool) : Truth3 :=
  match scenario, gapDetected with
  | .trueScenario,  _    => .true
  | .falseScenario, _    => .false
  | _,              true => .indet
  | _,              false => .true

/--
Lift a `LinguisticExample` to a `ProjectionDatum`, reading the
`operator`, `condition`, and `gap_detected` keys from `paperFeatures`.
Returns `none` for rows whose `paperFeatures` lack the recognised tags —
those rows are not part of this hub's pool.
-/
def fromExample (e : LinguisticExample) : Option ProjectionDatum :=
  match e.paperFeatures.lookup "operator", e.paperFeatures.lookup "condition" with
  | some opStr, some condStr =>
    match parseOperator opStr, parseScenario condStr with
    | some op, some sc =>
      let gapDetected := (e.paperFeatures.lookup "gap_detected").getD "false" == "true"
      some { operator := op, scenario := sc,
             observed := observedTruth sc gapDetected,
             source := e.source }
    | _, _ => none
  | _, _ => none

-- BEGIN GENERATED EXAMPLES
-- (Generated from Linglib/Data/Examples/KrizChemla2015.json by scripts/gen_examples.py.
-- Do not edit between markers; re-run the generator after editing the JSON.)

namespace Examples
open Data.Examples

def every_C2_gap : LinguisticExample :=
  { id := "krizchemla2015_every_C2_gap"
    source := ⟨"kriz-chemla-2015", "Exp. C2, (19) E-every+GAP"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every boy found his presents."
    discourseSegments := []
    glossedTokens := [("Every", "every"), ("boy", "boy"), ("found", "find.PST"), ("his", "3SG.M.POSS"), ("presents", "present.PL")]
    translation := "Every boy found his presents."
    context := "Four boys, each with nine presents to find; every boy found some but not all of his."
    judgment := .acceptable
    alternatives := []
    readings := [("strong/maximal", .acceptable), ("weak/non-maximal", .marginal)]
    paperFeatures := [("operator", "every"), ("embedding", "E-every"), ("condition", "GAP"), ("experiment", "C2"), ("gap_detected", "true")]
    comment := "C2 target condition. All three gap diagnostics significant (Table 9): Diag.1 β=6.7 χ²=26.7 p<10⁻⁶; Diag.2 β=7.7 χ²=35.1 p<10⁻⁸; Diag.3 β=4.9 χ²=4.0 p=.046. The 'weak/non-maximal' reading would interpret the sentence as 'every boy found some of his presents'; the paper finds this reading is marginal-to-rare in target-stimulus presentation, motivating the gap finding."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def no_C2_gap : LinguisticExample :=
  { id := "krizchemla2015_no_C2_gap"
    source := ⟨"kriz-chemla-2015", "Exp. C2, (20) E-no+GAP"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No boy found his presents."
    discourseSegments := []
    glossedTokens := [("No", "no"), ("boy", "boy"), ("found", "find.PST"), ("his", "3SG.M.POSS"), ("presents", "present.PL")]
    translation := "No boy found his presents."
    context := "Four boys, each with nine presents; some boys found some of their presents, but no boy found all of his."
    judgment := .acceptable
    alternatives := []
    readings := [("strong/no-any", .acceptable), ("weak/no-all", .marginal)]
    paperFeatures := [("operator", "no"), ("embedding", "E-no"), ("condition", "GAP"), ("experiment", "C2"), ("gap_detected", "true"), ("gap_size", "small_but_robust")]
    comment := "C2 corrects the apparent null result from A2/B2 (which used the accidentally-ungrammatical 'In none of the cells...' stimulus, per fn. 10 and fn. 14). C2's grammatical 'No boy found his presents.' yields a small-but-robust gap on all three diagnostics (Table 9): Diag.1 β=1.3 χ²=8.2 p=.004; Diag.2 β=1.1 χ²=5.2 p=.022; Diag.3 β=1.6 χ²=7.8 p=.005. Quoting §5.2.3: 'this time, E-no does show a gap, which, albeit small, is robust.' This is the empirical finding the file records — not the pre-C2 null."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def exactlyTwo_C3_gap : LinguisticExample :=
  { id := "krizchemla2015_exactlyTwo_C3_gap"
    source := ⟨"kriz-chemla-2015", "Exp. C3, (24) E-exactly+GAP"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Exactly 2 of the 4 boys found their presents."
    discourseSegments := []
    glossedTokens := [("Exactly", "exactly"), ("2", "two"), ("of", "of"), ("the", "DEF"), ("4", "four"), ("boys", "boy.PL"), ("found", "find.PST"), ("their", "3PL.POSS"), ("presents", "present.PL")]
    translation := "Exactly 2 of the 4 boys found their presents."
    context := "Four boys; exactly two of them found at least some of their presents, but in at most one of those two cells did the boy find all of his presents."
    judgment := .acceptable
    alternatives := []
    readings := [("exactly/maximal", .acceptable), ("exactly/non-maximal", .marginal)]
    paperFeatures := [("operator", "exactlyTwo"), ("embedding", "E-exactly"), ("condition", "GAP"), ("experiment", "C3"), ("gap_detected", "true")]
    comment := "C3 proper-GAP condition: target stimulus designed so that the literal exactly-2-found-all reading and the exactly-2-found-some reading yield different truth values, isolating homogeneity projection in the non-monotonic embedded scope. All three gap diagnostics significant (Table 10): Diag.1 β=3.9 χ²=21.0 p<10⁻⁵; Diag.2 β=7.7 χ²=38.8 p<10⁻⁹; Diag.3 β=6.6 χ²=13.5 p=.0002."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def exactlyTwo_C3_gap_q : LinguisticExample :=
  { id := "krizchemla2015_exactlyTwo_C3_gap_q"
    source := ⟨"kriz-chemla-2015", "Exp. C3, (24) E-exactly+GAP?"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Exactly 2 of the 4 boys found their presents."
    discourseSegments := []
    glossedTokens := [("Exactly", "exactly"), ("2", "two"), ("of", "of"), ("the", "DEF"), ("4", "four"), ("boys", "boy.PL"), ("found", "find.PST"), ("their", "3PL.POSS"), ("presents", "present.PL")]
    translation := "Exactly 2 of the 4 boys found their presents."
    context := "Four boys; one boy found all his presents; two boys each found some (not all) of theirs; one boy found none."
    judgment := .acceptable
    alternatives := []
    readings := [("exactly/maximal", .questionable), ("at-least-2/some", .acceptable)]
    paperFeatures := [("operator", "exactlyTwo"), ("embedding", "E-exactly"), ("condition", "GAP?"), ("experiment", "C3"), ("gap_detected", "false"), ("interpretation", "at_least_reading_emerges")]
    comment := "C3 GAP? condition does NOT yield a gap (Diag.1 p=.23, Diag.2 p=.15, Diag.3 p=.88 — Table 10). Theoretically load-bearing null: per §3.4 the result follows if 'exactly N' admits an at-least reading in this configuration (Marty, Chemla & Spector 2014 for parallel modified-numeral evidence), so what looks like a missing homogeneity gap is actually the at-least-reading rendering the sentence true. This null distinguishes supervaluation accounts (which would predict a gap) from exhaustification accounts (which allow the at-least reading)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def exactlyTwo_C4_gap_qq : LinguisticExample :=
  { id := "krizchemla2015_exactlyTwo_C4_gap_qq"
    source := ⟨"kriz-chemla-2015", "Exp. C4, (24) E-exactly+GAP??"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Exactly 2 of the 4 boys found their presents."
    discourseSegments := []
    glossedTokens := [("Exactly", "exactly"), ("2", "two"), ("of", "of"), ("the", "DEF"), ("4", "four"), ("boys", "boy.PL"), ("found", "find.PST"), ("their", "3PL.POSS"), ("presents", "present.PL")]
    translation := "Exactly 2 of the 4 boys found their presents."
    context := "Four boys; exactly two boys each found all their presents; a third boy found some (not all) of his; the fourth found none. The at-least-reading is false here (since three boys found some), so the only way to judge 'true' is via the homogeneity-bridged exactly-reading."
    judgment := .acceptable
    alternatives := []
    readings := [("exactly/maximal", .marginal), ("at-least-2/some", .unacceptable)]
    paperFeatures := [("operator", "exactlyTwo"), ("embedding", "E-exactly"), ("condition", "GAP??"), ("experiment", "C4"), ("gap_detected", "true")]
    comment := "C4 extends the C3 GAP? configuration to one where the at-least reading is false, ruling out the explanation that nulled GAP?. All three gap diagnostics significant (Table 11): Diag.1 β=4.4 χ²=13.4 p=.0002; Diag.2 β=7.6 χ²=49.4 p<10⁻¹¹; Diag.3 β=7.0 χ²=11.5 p=.0007. Combined with the GAP? null, this confirms that homogeneity *does* project from under 'exactly N', but only in configurations the at-least reading cannot rescue."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [every_C2_gap, no_C2_gap, exactlyTwo_C3_gap, exactlyTwo_C3_gap_q, exactlyTwo_C4_gap_qq]

end Examples
-- END GENERATED EXAMPLES

/-! ### Pool -/

/--
Cross-paper pool of projection-relevant data, derived from the generated
`Examples.all` by `fromExample`. Each entry carries its originating
`SourceRef` for provenance. Rival theories of projection should pass
their `ProjectionPredict` implementations against this pool.
-/
def allData : List ProjectionDatum := Examples.all.filterMap fromExample

end Phenomena.Plurals.Projection
