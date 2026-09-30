module

public import Linglib.Data.Examples.Schema

/-!
# `KrizChemla2015` — typed example data

Auto-generated from `Linglib/Data/Examples/KrizChemla2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace KrizChemla2015.Examples`.
-/

@[expose] public section

namespace KrizChemla2015.Examples

open Data.Examples

def every_C2_gap : LinguisticExample :=
  { id := "krizchemla2015_every_C2_gap"
    source := ⟨"kriz-chemla-2015", "Exp. C2, (19) E-every+GAP"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every boy found his presents."
    glossedTokens := [("Every", "every"), ("boy", "boy"), ("found", "find.PST"), ("his", "3SG.M.POSS"), ("presents", "present.PL")]
    context := "Four boys, each with nine presents to find; three boys found all their presents, one boy found some but not all (Table 13 gap displays, e.g. 9929)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("operator", "every"), ("embedding", "E-every"), ("condition", "GAP"), ("experiment", "C2"), ("gap_detected", "true"), ("display", "9929")] }

def no_C2_gap : LinguisticExample :=
  { id := "krizchemla2015_no_C2_gap"
    source := ⟨"kriz-chemla-2015", "Exp. C2, (20) E-no+GAP"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No boy found his presents."
    glossedTokens := [("No", "no"), ("boy", "boy"), ("found", "find.PST"), ("his", "3SG.M.POSS"), ("presents", "present.PL")]
    context := "Four boys, each with nine presents; one boy found some but not all of his presents, the others found none (Table 13 gap displays, e.g. 0070)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("operator", "no"), ("embedding", "E-no"), ("condition", "GAP"), ("experiment", "C2"), ("gap_detected", "true"), ("gap_size", "small_but_robust"), ("display", "0070")] }

def every_C2_true : LinguisticExample :=
  { id := "krizchemla2015_every_C2_true"
    source := ⟨"kriz-chemla-2015", "Exp. C2, (19) E-every+true condition"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every boy found his presents."
    glossedTokens := [("Every", "every"), ("boy", "boy"), ("found", "find.PST"), ("his", "3SG.M.POSS"), ("presents", "present.PL")]
    context := "Four boys, each with nine presents; every boy found all nine of his (Table 13 display 9999)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("operator", "every"), ("embedding", "E-every"), ("condition", "TRUE"), ("experiment", "C2"), ("display", "9999")] }

def every_C2_false : LinguisticExample :=
  { id := "krizchemla2015_every_C2_false"
    source := ⟨"kriz-chemla-2015", "Exp. C2, (19) E-every+false condition"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every boy found his presents."
    glossedTokens := [("Every", "every"), ("boy", "boy"), ("found", "find.PST"), ("his", "3SG.M.POSS"), ("presents", "present.PL")]
    context := "Four boys; one boy found none of his presents, and two others found some but not all (Table 13 false displays, e.g. 9770)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("operator", "every"), ("embedding", "E-every"), ("condition", "FALSE"), ("experiment", "C2"), ("display", "9770")] }

def no_C2_true : LinguisticExample :=
  { id := "krizchemla2015_no_C2_true"
    source := ⟨"kriz-chemla-2015", "Exp. C2, (20) E-no+true condition"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No boy found his presents."
    glossedTokens := [("No", "no"), ("boy", "boy"), ("found", "find.PST"), ("his", "3SG.M.POSS"), ("presents", "present.PL")]
    context := "Four boys; no boy found any of his presents (Table 13 display 0000)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("operator", "no"), ("embedding", "E-no"), ("condition", "TRUE"), ("experiment", "C2"), ("display", "0000")] }

def no_C2_false : LinguisticExample :=
  { id := "krizchemla2015_no_C2_false"
    source := ⟨"kriz-chemla-2015", "Exp. C2, (20) E-no+false condition"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No boy found his presents."
    glossedTokens := [("No", "no"), ("boy", "boy"), ("found", "find.PST"), ("his", "3SG.M.POSS"), ("presents", "present.PL")]
    context := "Four boys; one boy found all nine of his presents, another found five (Table 13 replacement displays, e.g. 5009)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("operator", "no"), ("embedding", "E-no"), ("condition", "FALSE"), ("experiment", "C2"), ("display", "5009")] }

def exactlyTwo_C3_gap : LinguisticExample :=
  { id := "krizchemla2015_exactlyTwo_C3_gap"
    source := ⟨"kriz-chemla-2015", "Exp. C3, (24) E-exactly+GAP"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Exactly 2 of the 4 boys found their presents."
    glossedTokens := [("Exactly", "exactly"), ("2", "two"), ("of", "of"), ("the", "DEF"), ("4", "four"), ("boys", "boy.PL"), ("found", "find.PST"), ("their", "3PL.POSS"), ("presents", "present.PL")]
    context := "Four boys; exactly two of them found some of their presents (in at most one case all of them), the other two found none (Table 13 gap displays, e.g. 9200, 3300)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("operator", "exactlyTwo"), ("embedding", "E-exactly"), ("condition", "GAP"), ("experiment", "C3"), ("gap_detected", "true"), ("display", "9200")] }

def exactlyTwo_C3_gap_q : LinguisticExample :=
  { id := "krizchemla2015_exactlyTwo_C3_gap_q"
    source := ⟨"kriz-chemla-2015", "Exp. C3, (24) E-exactly+GAP?"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Exactly 2 of the 4 boys found their presents."
    glossedTokens := [("Exactly", "exactly"), ("2", "two"), ("of", "of"), ("the", "DEF"), ("4", "four"), ("boys", "boy.PL"), ("found", "find.PST"), ("their", "3PL.POSS"), ("presents", "present.PL")]
    context := "Four boys; one boy found all his presents; two boys each found some (not all) of theirs; one boy found none (Table 13 gap? displays, e.g. 9202)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("operator", "exactlyTwo"), ("embedding", "E-exactly"), ("condition", "GAP?"), ("experiment", "C3"), ("gap_detected", "false"), ("classical_value", "false"), ("display", "9202")] }

def exactlyTwo_C4_gap_qq : LinguisticExample :=
  { id := "krizchemla2015_exactlyTwo_C4_gap_qq"
    source := ⟨"kriz-chemla-2015", "Exp. C4, (24) E-exactly+GAP??"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Exactly 2 of the 4 boys found their presents."
    glossedTokens := [("Exactly", "exactly"), ("2", "two"), ("of", "of"), ("the", "DEF"), ("4", "four"), ("boys", "boy.PL"), ("found", "find.PST"), ("their", "3PL.POSS"), ("presents", "present.PL")]
    context := "Four boys; exactly two boys each found all their presents; a third boy found some (not all) of his; the fourth found none (Table 13 gap?? displays, e.g. 9209)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("operator", "exactlyTwo"), ("embedding", "E-exactly"), ("condition", "GAP??"), ("experiment", "C4"), ("gap_detected", "true"), ("display", "9209")] }

def exactlyTwo_C3_true : LinguisticExample :=
  { id := "krizchemla2015_exactlyTwo_C3_true"
    source := ⟨"kriz-chemla-2015", "Exp. C3, (24) E-exactly+true condition"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Exactly 2 of the 4 boys found their presents."
    glossedTokens := [("Exactly", "exactly"), ("2", "two"), ("of", "of"), ("the", "DEF"), ("4", "four"), ("boys", "boy.PL"), ("found", "find.PST"), ("their", "3PL.POSS"), ("presents", "present.PL")]
    context := "Four boys; exactly two boys found all nine of their presents, the other two found none (Table 13 displays, e.g. 9900)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("operator", "exactlyTwo"), ("embedding", "E-exactly"), ("condition", "TRUE"), ("experiment", "C3"), ("display", "9900")] }

def exactlyTwo_C3_false : LinguisticExample :=
  { id := "krizchemla2015_exactlyTwo_C3_false"
    source := ⟨"kriz-chemla-2015", "Exp. C3, (24) E-exactly+false condition"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Exactly 2 of the 4 boys found their presents."
    glossedTokens := [("Exactly", "exactly"), ("2", "two"), ("of", "of"), ("the", "DEF"), ("4", "four"), ("boys", "boy.PL"), ("found", "find.PST"), ("their", "3PL.POSS"), ("presents", "present.PL")]
    context := "Four boys; one boy found some but not all of his presents, the others found none (Table 13 false displays, e.g. 4000)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("operator", "exactlyTwo"), ("embedding", "E-exactly"), ("condition", "FALSE"), ("experiment", "C3"), ("display", "4000")] }

def pos_A1_all : LinguisticExample :=
  { id := "krizchemla2015_pos_A1_all"
    source := ⟨"kriz-chemla-2015", "Exp. A1, the+E-∅, 9/9 target-color display"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The triangles are blue."
    glossedTokens := [("The", "DEF"), ("triangles", "triangle.PL"), ("are", "COP.PL"), ("blue", "blue")]
    context := "Nine triangles in the display; all nine are blue."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("condition", "ALL"), ("embedding", "unembedded")] }

def pos_A1_none : LinguisticExample :=
  { id := "krizchemla2015_pos_A1_none"
    source := ⟨"kriz-chemla-2015", "Exp. A1, the+E-∅, 0/9 target-color display"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The triangles are blue."
    glossedTokens := [("The", "DEF"), ("triangles", "triangle.PL"), ("are", "COP.PL"), ("blue", "blue")]
    context := "Nine triangles in the display; none is blue."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("condition", "NONE"), ("embedding", "unembedded")] }

def pos_A1_gap : LinguisticExample :=
  { id := "krizchemla2015_pos_A1_gap"
    source := ⟨"kriz-chemla-2015", "Exp. A1, the+E-∅, mixed display"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The triangles are blue."
    glossedTokens := [("The", "DEF"), ("triangles", "triangle.PL"), ("are", "COP.PL"), ("blue", "blue")]
    context := "Nine triangles in the display; four are blue, five are another color."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("condition", "GAP"), ("embedding", "unembedded"), ("gap_detected", "true")] }

def neg_A1_all : LinguisticExample :=
  { id := "krizchemla2015_neg_A1_all"
    source := ⟨"kriz-chemla-2015", "Exp. A1, the+E-neg, 9/9 target-color display"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The triangles aren't blue."
    glossedTokens := [("The", "DEF"), ("triangles", "triangle.PL"), ("aren't", "COP.PL.NEG"), ("blue", "blue")]
    context := "Nine triangles in the display; all nine are blue."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("condition", "ALL"), ("embedding", "unembedded")] }

def neg_A1_none : LinguisticExample :=
  { id := "krizchemla2015_neg_A1_none"
    source := ⟨"kriz-chemla-2015", "Exp. A1, the+E-neg, 0/9 target-color display"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The triangles aren't blue."
    glossedTokens := [("The", "DEF"), ("triangles", "triangle.PL"), ("aren't", "COP.PL.NEG"), ("blue", "blue")]
    context := "Nine triangles in the display; none is blue."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("condition", "NONE"), ("embedding", "unembedded")] }

def neg_A1_gap : LinguisticExample :=
  { id := "krizchemla2015_neg_A1_gap"
    source := ⟨"kriz-chemla-2015", "Exp. A1, the+E-neg, mixed display"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The triangles aren't blue."
    glossedTokens := [("The", "DEF"), ("triangles", "triangle.PL"), ("aren't", "COP.PL.NEG"), ("blue", "blue")]
    context := "Nine triangles in the display; four are blue, five are another color."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("condition", "GAP"), ("embedding", "unembedded"), ("gap_detected", "true")] }

def all : List LinguisticExample := [every_C2_gap, no_C2_gap, every_C2_true, every_C2_false, no_C2_true, no_C2_false, exactlyTwo_C3_gap, exactlyTwo_C3_gap_q, exactlyTwo_C4_gap_qq, exactlyTwo_C3_true, exactlyTwo_C3_false, pos_A1_all, pos_A1_none, pos_A1_gap, neg_A1_all, neg_A1_none, neg_A1_gap]

end KrizChemla2015.Examples
