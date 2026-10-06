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

def ex_14a : Datum :=
  { id := "krizchemla2015_14a"
    source := ⟨"kriz-chemla-2015", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In all the cells, the symbols are green."
    glossedTokens := [("In", "in"), ("all", "all"), ("the", "DEF"), ("cells", "cell.PL"), ("the", "DEF"), ("symbols", "symbol.PL"), ("are", "COP.PL"), ("green", "green")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("embedding", "E-all")] }

def ex_15 : Datum :=
  { id := "krizchemla2015_15"
    source := ⟨"kriz-chemla-2015", "(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In none of the cells, the symbols are green."
    glossedTokens := [("In", "in"), ("none", "none"), ("of", "of"), ("the", "DEF"), ("cells", "cell.PL"), ("the", "DEF"), ("symbols", "symbol.PL"), ("are", "COP.PL"), ("green", "green")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("embedding", "E-no")] }

def ex_16b : Datum :=
  { id := "krizchemla2015_16b"
    source := ⟨"kriz-chemla-2015", "(16b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In none of the cells are all the symbols green."
    glossedTokens := [("In", "in"), ("none", "none"), ("of", "of"), ("the", "DEF"), ("cells", "cell.PL"), ("are", "COP.PL"), ("all", "all"), ("the", "DEF"), ("symbols", "symbol.PL"), ("green", "green")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("embedding", "E-no")] }

def ex_19 : Datum :=
  { id := "krizchemla2015_19"
    source := ⟨"kriz-chemla-2015", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every boy found his presents."
    glossedTokens := [("Every", "every"), ("boy", "boy"), ("found", "find.PST"), ("his", "3SG.M.POSS"), ("presents", "present.PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("embedding", "E-all")] }

def ex_20 : Datum :=
  { id := "krizchemla2015_20"
    source := ⟨"kriz-chemla-2015", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No boy found his presents."
    glossedTokens := [("No", "no"), ("boy", "boy"), ("found", "find.PST"), ("his", "3SG.M.POSS"), ("presents", "present.PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("embedding", "E-no")] }

def ex_23 : Datum :=
  { id := "krizchemla2015_23"
    source := ⟨"kriz-chemla-2015", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All the boys found their presents."
    glossedTokens := [("All", "all"), ("the", "DEF"), ("boys", "boy.PL"), ("found", "find.PST"), ("their", "3PL.POSS"), ("presents", "present.PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("embedding", "E-all")] }

def ex_24 : Datum :=
  { id := "krizchemla2015_24"
    source := ⟨"kriz-chemla-2015", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Exactly 2 of the 4 boys found their presents."
    glossedTokens := [("Exactly", "exactly"), ("2", "two"), ("of", "of"), ("the", "DEF"), ("4", "four"), ("boys", "boy.PL"), ("found", "find.PST"), ("their", "3PL.POSS"), ("presents", "present.PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("embedding", "E-exactly")] }

def pos_A1_all : Datum :=
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

def pos_A1_none : Datum :=
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

def pos_A1_gap : Datum :=
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

def neg_A1_all : Datum :=
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

def neg_A1_none : Datum :=
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

def neg_A1_gap : Datum :=
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

def all : List Datum := [ex_14a, ex_15, ex_16b, ex_19, ex_20, ex_23, ex_24, pos_A1_all, pos_A1_none, pos_A1_gap, neg_A1_all, neg_A1_none, neg_A1_gap]

end KrizChemla2015.Examples
