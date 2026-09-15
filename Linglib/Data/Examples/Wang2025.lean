import Linglib.Data.Examples.Schema

/-!
# `Wang2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Wang2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Wang2025.Examples`.
-/

namespace Wang2025.Examples

open Data.Examples

def ex_3_4 : LinguisticExample :=
  { id := "wang2025_3_4"
    source := ⟨"wang-2025", "Ch. 3 (4)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhangsan ye zai jichang chi le wanfan."
    discourseSegments := []
    glossedTokens := [("Zhangsan", "Zhangsan"), ("ye", "also"), ("zai", "at"), ("jichang", "airport"), ("chi", "eat"), ("le", "LE"), ("wanfan", "dinner")]
    translation := "Zhangsan also had dinner at the airport."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "ye"), ("focus", "Zhangsan")]
    comment := "The antecedent must be salient, a focus alternative of the host, and distinct from it."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3_39 : LinguisticExample :=
  { id := "wang2025_3_39"
    source := ⟨"wang-2025", "Ch. 3 (39)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhangsan mei lai. Lisi fan'er lai le."
    discourseSegments := []
    glossedTokens := [("Zhangsan", "Zhangsan"), ("mei", "not"), ("lai", "come"), ("Lisi", "Lisi"), ("fan'er", "instead"), ("lai", "come"), ("le", "LE")]
    translation := "Zhangsan didn't come. Lisi came instead."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "fan'er"), ("focus", "Lisi")]
    comment := "fan'er presupposes the falsity of a salient alternative, the mirror image of ye."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3_40 : LinguisticExample :=
  { id := "wang2025_3_40"
    source := ⟨"wang-2025", "Ch. 3 (40)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Lisi mei qu gongyuan. Ta fan'er qu le xuexiao."
    discourseSegments := []
    glossedTokens := [("Lisi", "Lisi"), ("mei", "not"), ("qu", "go"), ("gongyuan", "park"), ("Ta", "he"), ("fan'er", "instead"), ("qu", "go"), ("le", "LE"), ("xuexiao", "school")]
    translation := "Lisi didn't go to the park. He went to school instead."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "fan'er"), ("focus", "xuexiao")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4_35a : LinguisticExample :=
  { id := "wang2025_4_35a"
    source := ⟨"wang-2025", "Ch. 4 (35a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Yaome Zhangsan chi le binggan, yaome ta chi le dangao."
    discourseSegments := []
    glossedTokens := [("Yaome", "or"), ("Zhangsan", "Zhangsan"), ("chi", "eat"), ("le", "LE"), ("binggan", "cookie"), ("yaome", "or"), ("ta", "he"), ("chi", "eat"), ("le", "LE"), ("dangao", "cake")]
    translation := "Either Zhangsan ate a cookie or a cake."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "yaome-yaome")]
    comment := "Infers that Zhangsan did not eat both: the either-or construction enforces exhaustification of each disjunct."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4_35b : LinguisticExample :=
  { id := "wang2025_4_35b"
    source := ⟨"wang-2025", "Ch. 4 (35b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Ni yaome keyi chi binggan, yaome keyi chi dangao."
    discourseSegments := []
    glossedTokens := [("Ni", "you"), ("yaome", "or"), ("keyi", "can"), ("chi", "eat"), ("binggan", "cookie"), ("yaome", "or"), ("keyi", "can"), ("chi", "eat"), ("dangao", "cake")]
    translation := "You either can eat a cookie or can eat a cake."
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("construction", "yaome-yaome"), ("modal", "above disjunction")]
    comment := "Marked ?? in the dissertation: the disjunction is dispreferred above the possibility modal."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4_35c : LinguisticExample :=
  { id := "wang2025_4_35c"
    source := ⟨"wang-2025", "Ch. 4 (35c)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Ni keyi yaome chi binggan, yaome chi dangao."
    discourseSegments := []
    glossedTokens := [("Ni", "you"), ("keyi", "can"), ("yaome", "or"), ("chi", "eat"), ("binggan", "cookie"), ("yaome", "or"), ("chi", "eat"), ("dangao", "cake")]
    translation := "You can either eat a cookie or eat a cake."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "yaome-yaome"), ("modal", "below disjunction")]
    comment := "The disjunction inside the scope of the modal, as the embedded exhaustification requires."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4_36 : LinguisticExample :=
  { id := "wang2025_4_36"
    source := ⟨"wang-2025", "Ch. 4 (36)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhangsan yexu qu le. Lisi qu le."
    discourseSegments := []
    glossedTokens := [("Zhangsan", "Zhangsan"), ("yexu", "maybe"), ("qu", "go"), ("le", "LE"), ("Lisi", "Lisi"), ("qu", "go"), ("le", "LE")]
    translation := "Zhangsan maybe went. Lisi went."
    context := "A: Who went skiing? Did Zhangsan go?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "positive evidence"), ("trigger", "ye omitted")]
    comment := "Exhaustifying the target sentence yields the implicature that Zhangsan did not go, which contradicts the positive evidence; the additive is therefore obligatory, Table 4.4."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4_42 : LinguisticExample :=
  { id := "wang2025_4_42"
    source := ⟨"wang-2025", "Ch. 4 (42)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhangsan yexu qu le. Lisi qu le."
    discourseSegments := []
    glossedTokens := [("Zhangsan", "Zhangsan"), ("yexu", "possibly"), ("qu", "go"), ("le", "LE"), ("Lisi", "Lisi"), ("qu", "go"), ("le", "LE")]
    translation := "Zhangsan possibly went. Lisi went."
    context := "A: Who went skiing? Did Zhangsan go?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "positive evidence"), ("focus", "yexu")]
    comment := "With focus on the possibility modal the first sentence carries an ignorance implicature, and exhaustification above the belief operator makes the trigger unnecessary."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4_45 : LinguisticExample :=
  { id := "wang2025_4_45"
    source := ⟨"wang-2025", "Ch. 4 (45)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhangsan yexu yiqian zong chuchai. Xianzai ta buzai jingchang chuchai le."
    discourseSegments := []
    glossedTokens := [("Zhangsan", "Zhangsan"), ("yexu", "possibly"), ("yiqian", "past"), ("zong", "frequently"), ("chuchai", "on.business.trip"), ("Xianzai", "now"), ("ta", "he"), ("buzai", "not.anymore"), ("jingchang", "often"), ("chuchai", "on.business.trip"), ("le", "LE")]
    translation := "Zhangsan possibly went on business trips frequently in the past. Now he does not often go on business trips anymore."
    context := "A: Did Zhangsan often go on business trips?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "buzai"), ("context", "positive evidence"), ("contrast", "polarity and time")]
    comment := "The double contrast yields two maximal consistent subsets of alternatives, so the cessative trigger is optional, Tables 4.7 and 4.9."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_3_4, ex_3_39, ex_3_40, ex_4_35a, ex_4_35b, ex_4_35c, ex_4_36, ex_4_42, ex_4_45]

end Wang2025.Examples
