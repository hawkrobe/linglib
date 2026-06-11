import Linglib.Data.Examples.Schema

/-!
# `KrizChemla2015` — typed example data

Auto-generated from `Linglib/Data/Examples/KrizChemla2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace KrizChemla2015.Examples`.
-/

namespace KrizChemla2015.Examples

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

end KrizChemla2015.Examples
