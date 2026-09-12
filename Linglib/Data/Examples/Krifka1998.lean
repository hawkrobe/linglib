import Linglib.Data.Examples.Schema

/-!
# `Krifka1998` — typed example data

Auto-generated from `Linglib/Data/Examples/Krifka1998.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Krifka1998.Examples`.
-/

namespace Krifka1998.Examples

open Data.Examples

def ex11a : LinguisticExample :=
  { id := "krifka1998_ex11a"
    source := ⟨"krifka-1998", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "two kilograms of apples"
    discourseSegments := []
    glossedTokens := []
    translation := "two kilograms of apples"
    context := "Nominal measure construction with an extensive measure function."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("measureFunction", "extensive")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex11b : LinguisticExample :=
  { id := "krifka1998_ex11b"
    source := ⟨"krifka-1998", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "two bags of money"
    discourseSegments := []
    glossedTokens := []
    translation := "two bags of money"
    context := "A container used as an extensive measure function."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("measureFunction", "extensive")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex11c : LinguisticExample :=
  { id := "krifka1998_ex11c"
    source := ⟨"krifka-1998", "(11c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "sixty degree Celsius of water"
    discourseSegments := []
    glossedTokens := []
    translation := "sixty degree Celsius of water"
    context := "Nominal measure construction with a non-extensive measure function."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("measureFunction", "nonExtensive")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex11d : LinguisticExample :=
  { id := "krifka1998_ex11d"
    source := ⟨"krifka-1998", "(11d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "eighteen carats of gold"
    discourseSegments := []
    glossedTokens := []
    translation := "eighteen carats of gold"
    context := "Nominal measure construction with a non-extensive measure function."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("measureFunction", "nonExtensive")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex12c : LinguisticExample :=
  { id := "krifka1998_ex12c"
    source := ⟨"krifka-1998", "(12c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "hundred grams of five hundred meters of wool"
    discourseSegments := []
    glossedTokens := []
    translation := "hundred grams of five hundred meters of wool"
    context := "A measure phrase applied to a predicate that is already quantized; contrast (12a) hundred grams of wool and (12b) five hundred meters of wool."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("measureFunction", "extensive")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex58 : LinguisticExample :=
  { id := "krifka1998_ex58"
    source := ⟨"krifka-1998", "(58)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is an incredibly fast eater. Yesterday she ate peanuts in 0.43 seconds!"
    discourseSegments := []
    glossedTokens := []
    translation := "Mary is an incredibly fast eater. Yesterday she ate peanuts in 0.43 seconds!"
    context := "An interval adverbial with a non-quantized but temporally atomic predicate."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adverbial", "in")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex60a : LinguisticExample :=
  { id := "krifka1998_ex60a"
    source := ⟨"krifka-1998", "(60a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary wrote something in 10 minutes."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary wrote something in 10 minutes."
    context := "A non-quantized object that nevertheless yields a telic predicate; the paper gives the indefinite wide scope over the adverbial."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adverbial", "in")]
    comment := "The paper credits the observation to White (1994), Mittwoch (1982) and White and Zucchi (1996)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex60b : LinguisticExample :=
  { id := "krifka1998_ex60b"
    source := ⟨"krifka-1998", "(60b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary ate more than three apples in an hour."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary ate more than three apples in an hour."
    context := "A non-quantized, cumulative object that nevertheless yields a telic predicate."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adverbial", "in")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex60c : LinguisticExample :=
  { id := "krifka1998_ex60c"
    source := ⟨"krifka-1998", "(60c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary ate a quantity of porridge in an hour."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary ate a quantity of porridge in an hour."
    context := "A non-quantized, cumulative object that nevertheless yields a telic predicate."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adverbial", "in")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex66a : LinguisticExample :=
  { id := "krifka1998_ex66a"
    source := ⟨"krifka-1998", "(66a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Juan se tomó una copa de vino anoche antes de acostarse."
    discourseSegments := []
    glossedTokens := []
    translation := "Juan drank a glass of wine last night before going to bed"
    context := "The reflexive clitic se with a telic predicate."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clitic", "se")]
    comment := "The paper credits the observation to Nishida (1994)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex66b : LinguisticExample :=
  { id := "krifka1998_ex66b"
    source := ⟨"krifka-1998", "(66b)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Juan se tomó vino anoche antes de acostarse."
    discourseSegments := []
    glossedTokens := []
    translation := "Juan drank wine last night before going to bed"
    context := "The reflexive clitic se with an atelic predicate; without se the sentence is fine."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("clitic", "se")]
    comment := "The paper credits the observation to Nishida (1994)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex74 : LinguisticExample :=
  { id := "krifka1998_ex74"
    source := ⟨"krifka-1998", "(74)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary walked from the university to the capitol."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary walked from the university to the capitol."
    context := "A movement with a specified source and goal; telic, so it takes in an hour."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("path", "sourceGoal")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex75 : LinguisticExample :=
  { id := "krifka1998_ex75"
    source := ⟨"krifka-1998", "(75)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary walked from the university towards the capitol."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary walked from the university towards the capitol."
    context := "A movement with a specified source and direction, read as an initial part of a movement to the goal; not telic."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("path", "sourceDirection")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex75_in : LinguisticExample :=
  { id := "krifka1998_ex75_in"
    source := ⟨"krifka-1998", "(75)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "walk from the university towards the capitol in an hour"
    discourseSegments := []
    glossedTokens := []
    translation := "walk from the university towards the capitol in an hour"
    context := "An interval adverbial with a directed but goalless movement."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("path", "sourceDirection"), ("adverbial", "in")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex77a_in : LinguisticExample :=
  { id := "krifka1998_ex77a_in"
    source := ⟨"krifka-1998", "(77a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary baked the lobster till half done in an hour."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary baked the lobster till half done in an hour."
    context := "A change on the scale of doneness with an explicitly specified goal."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("goal", "specified"), ("adverbial", "in")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex77a_for : LinguisticExample :=
  { id := "krifka1998_ex77a_for"
    source := ⟨"krifka-1998", "(77a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary baked the lobster till half done for an hour."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary baked the lobster till half done for an hour."
    context := "A change on the scale of doneness with an explicitly specified goal."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("goal", "specified"), ("adverbial", "for")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex77b_in : LinguisticExample :=
  { id := "krifka1998_ex77b_in"
    source := ⟨"krifka-1998", "(77b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary whipped the cream stiff in an hour."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary whipped the cream stiff in an hour."
    context := "A resultative adjective specifying the goal of the change."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("goal", "specified"), ("adverbial", "in")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex77b_for : LinguisticExample :=
  { id := "krifka1998_ex77b_for"
    source := ⟨"krifka-1998", "(77b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary whipped the cream stiff for an hour."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary whipped the cream stiff for an hour."
    context := "A resultative adjective specifying the goal of the change."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("goal", "specified"), ("adverbial", "for")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex77c : LinguisticExample :=
  { id := "krifka1998_ex77c"
    source := ⟨"krifka-1998", "(77c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary baked the lobster in an hour / for an hour."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary baked the lobster in an hour / for an hour."
    context := "Ambiguous between a change to the natural end state, which takes in an hour, and the bare process, which takes for an hour."
    judgment := .acceptable
    alternatives := []
    readings := [("goal reached (in an hour)", .acceptable), ("process only (for an hour)", .acceptable)]
    paperFeatures := [("goal", "implicit")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex78 : LinguisticExample :=
  { id := "krifka1998_ex78"
    source := ⟨"krifka-1998", "(78)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary arrived in London."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary arrived in London."
    context := "An achievement, read as the minimal final part of a movement to London."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("path", "goal")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex11a, ex11b, ex11c, ex11d, ex12c, ex58, ex60a, ex60b, ex60c, ex66a, ex66b, ex74, ex75, ex75_in, ex77a_in, ex77a_for, ex77b_in, ex77b_for, ex77c, ex78]

end Krifka1998.Examples
