import Linglib.Data.Examples.Schema

/-!
# `BeaverCondoravdi2003` — typed example data

Auto-generated from `Linglib/Data/Examples/BeaverCondoravdi2003.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BeaverCondoravdi2003.Examples`.
-/

namespace BeaverCondoravdi2003.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "beavercondoravdi2003_1"
    source := ⟨"beaver-condoravdi-2003", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Cleo left Europe before David did."
    discourseSegments := []
    glossedTokens := []
    translation := "Cleo left Europe before David did."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "before")]
    comment := "True iff (2) is — the intuition behind converseness; implies David did in fact leave Europe."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2 : LinguisticExample :=
  { id := "beavercondoravdi2003_2"
    source := ⟨"beaver-condoravdi-2003", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "David left Europe after Cleo did."
    discourseSegments := []
    glossedTokens := []
    translation := "David left Europe after Cleo did."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "after")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3 : LinguisticExample :=
  { id := "beavercondoravdi2003_3"
    source := ⟨"beaver-condoravdi-2003", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Cleo was in America before David was in America."
    discourseSegments := []
    glossedTokens := []
    translation := "Cleo was in America before David was in America."
    context := "Cleo's stay starts before David's; their stays overlap."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "before"), ("phenomenon", "antisymmetry")]
    comment := "True iff (4) is false: before is antisymmetric."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5 : LinguisticExample :=
  { id := "beavercondoravdi2003_5"
    source := ⟨"beaver-condoravdi-2003", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Cleo was in America after David was in America."
    discourseSegments := []
    glossedTokens := []
    translation := "Cleo was in America after David was in America."
    context := "Cleo's stay starts before David's; their stays overlap."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "after"), ("phenomenon", "antisymmetry")]
    comment := "Can be true together with (6) in the overlap situation (7): after is not antisymmetric."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_9 : LinguisticExample :=
  { id := "beavercondoravdi2003_9"
    source := ⟨"beaver-condoravdi-2003", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fred was dancing after Ginger was."
    discourseSegments := []
    glossedTokens := []
    translation := "Fred was dancing after Ginger was."
    context := "Ginger dances continuously; Fred dances in the middle; Delores does a quick routine after Fred stops, while Ginger still dances."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "after"), ("phenomenon", "transitivity")]
    comment := "Judged true in situation (8)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10 : LinguisticExample :=
  { id := "beavercondoravdi2003_10"
    source := ⟨"beaver-condoravdi-2003", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Ginger was dancing after Delores was."
    discourseSegments := []
    glossedTokens := []
    translation := "Ginger was dancing after Delores was."
    context := "Same situation (8)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "after"), ("phenomenon", "transitivity")]
    comment := "Judged true in situation (8)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_11 : LinguisticExample :=
  { id := "beavercondoravdi2003_11"
    source := ⟨"beaver-condoravdi-2003", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fred was dancing after Delores was."
    discourseSegments := []
    glossedTokens := []
    translation := "Fred was dancing after Delores was."
    context := "Same situation (8)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "after"), ("phenomenon", "transitivity")]
    comment := "Judged false in situation (8): after is not transitive."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12 : LinguisticExample :=
  { id := "beavercondoravdi2003_12"
    source := ⟨"beaver-condoravdi-2003", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Delores was dancing before Ginger was."
    discourseSegments := []
    glossedTokens := []
    translation := "Delores was dancing before Ginger was."
    context := "Same situation (8)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "before"), ("phenomenon", "converseness")]
    comment := "Not judged true in situation (8), though (10) is — the direct counterexample to sentential converseness."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_15 : LinguisticExample :=
  { id := "beavercondoravdi2003_15"
    source := ⟨"beaver-condoravdi-2003", "(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Cleo leapt into action before David moved a muscle."
    discourseSegments := []
    glossedTokens := []
    translation := "Cleo leapt into action before David moved a muscle."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "before"), ("phenomenon", "npi-licensing")]
    comment := "Before licenses NPIs in its clause; also with 'could say a word'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_16 : LinguisticExample :=
  { id := "beavercondoravdi2003_16"
    source := ⟨"beaver-condoravdi-2003", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Cleo leapt into action after David moved a muscle."
    discourseSegments := []
    glossedTokens := []
    translation := "Cleo leapt into action after David moved a muscle."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "after"), ("phenomenon", "npi-licensing")]
    comment := "After does not license NPIs; main clauses license none regardless of connective ((17), (18))."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_22 : LinguisticExample :=
  { id := "beavercondoravdi2003_22"
    source := ⟨"beaver-condoravdi-2003", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "On Dec. 9, the U.S. Supreme Court stopped the hand count before it was completed."
    discourseSegments := []
    glossedTokens := []
    translation := "On Dec. 9, the U.S. Supreme Court stopped the hand count before it was completed."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "before"), ("phenomenon", "veridicality"), ("reading", "counterfactual")]
    comment := "Uncounted votes: the before-clause is not instantiated."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23 : LinguisticExample :=
  { id := "beavercondoravdi2003_23"
    source := ⟨"beaver-condoravdi-2003", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Another booby-trapped bicycle and a bomb hidden in a supermarket cart were discovered and defused by police before they exploded."
    discourseSegments := []
    glossedTokens := []
    translation := "Another booby-trapped bicycle and a bomb hidden in a supermarket cart were discovered and defused by police before they exploded."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "before"), ("phenomenon", "veridicality"), ("reading", "counterfactual")]
    comment := "No explosion."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_24 : LinguisticExample :=
  { id := "beavercondoravdi2003_24"
    source := ⟨"beaver-condoravdi-2003", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mozart died before he finished the Requiem and it was completed by his student, Franz Xavier Suessmayr."
    discourseSegments := []
    glossedTokens := []
    translation := "Mozart died before he finished the Requiem and it was completed by his student, Franz Xavier Suessmayr."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "before"), ("phenomenon", "veridicality"), ("reading", "counterfactual")]
    comment := "Unfinished Requiem; simplified as (40), which implies (41): if Mozart had not died when he did, he might/would have finished it."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_25 : LinguisticExample :=
  { id := "beavercondoravdi2003_25"
    source := ⟨"beaver-condoravdi-2003", "(25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mozart died after he finished the Requiem."
    discourseSegments := []
    glossedTokens := []
    translation := "Mozart died after he finished the Requiem."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "after"), ("phenomenon", "veridicality")]
    comment := "Requiem finished: after-clauses stay veridical under any toying with the examples."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_26 : LinguisticExample :=
  { id := "beavercondoravdi2003_26"
    source := ⟨"beaver-condoravdi-2003", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mozart finished the Requiem after he died."
    discourseSegments := []
    glossedTokens := []
    translation := "Mozart finished the Requiem after he died."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "after"), ("phenomenon", "veridicality")]
    comment := "Requiem finished post mortem: both clauses veridical."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_32 : LinguisticExample :=
  { id := "beavercondoravdi2003_32"
    source := ⟨"beaver-condoravdi-2003", "(32)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "David ate lots of ketchup before he made a clean sweep of all the gold medals in the Sydney Olympics."
    discourseSegments := []
    glossedTokens := []
    translation := "David ate lots of ketchup before he made a clean sweep of all the gold medals in the Sydney Olympics."
    context := "David never won a gold medal at anything."
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("connective", "before"), ("phenomenon", "overgeneration")]
    comment := "Predicted true by the classical rendering whenever the before-clause is empty; odd because no context with common-sense assumptions makes the win reasonably probable."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_34 : LinguisticExample :=
  { id := "beavercondoravdi2003_34"
    source := ⟨"beaver-condoravdi-2003", "(34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Cleo left exactly 5 seconds before David sang."
    discourseSegments := []
    glossedTokens := []
    translation := "Cleo left exactly 5 seconds before David sang."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "before"), ("phenomenon", "measure-phrase")]
    comment := "A universal rendering of the before-clause would require leaving exactly 5 seconds before every singing time."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_42 : LinguisticExample :=
  { id := "beavercondoravdi2003_42"
    source := ⟨"beaver-condoravdi-2003", "(42)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The police defused the bomb before it exploded."
    discourseSegments := []
    glossedTokens := []
    translation := "The police defused the bomb before it exploded."
    context := "It is taken for granted that there was a bomb ticking which ended up not exploding."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "before"), ("phenomenon", "veridicality"), ("reading", "counterfactual")]
    comment := "New information: the bomb did not explode because the police defused it before the time it would have exploded."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_43 : LinguisticExample :=
  { id := "beavercondoravdi2003_43"
    source := ⟨"beaver-condoravdi-2003", "(43)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I left the party before there was any trouble."
    discourseSegments := []
    glossedTokens := []
    translation := "I left the party before there was any trouble."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "before"), ("phenomenon", "veridicality"), ("reading", "non-committal")]
    comment := "No commitment to there having been trouble, but trouble seemed likely shortly before the departure."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1, ex_2, ex_3, ex_5, ex_9, ex_10, ex_11, ex_12, ex_15, ex_16, ex_22, ex_23, ex_24, ex_25, ex_26, ex_32, ex_34, ex_42, ex_43]

end BeaverCondoravdi2003.Examples
