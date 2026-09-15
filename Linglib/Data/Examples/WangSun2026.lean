import Linglib.Data.Examples.Schema

/-!
# `WangSun2026` — typed example data

Auto-generated from `Linglib/Data/Examples/WangSun2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace WangSun2026.Examples`.
-/

namespace WangSun2026.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "wangsun2026_1"
    source := ⟨"wang-sun-2026", "(4c)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "yī hěn cōngmíng de gè xuéshēng"
    discourseSegments := []
    glossedTokens := [("yī", "one"), ("hěn", "very"), ("cōngmíng", "clever"), ("de", "DE"), ("gè", "CL"), ("xuéshēng", "student")]
    translation := "a very clever student"
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "degree"), ("position", "Num _ Cl")]
    comment := "A degree-modified adjective between the numeral and the classifier."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2 : LinguisticExample :=
  { id := "wangsun2026_2"
    source := ⟨"wang-sun-2026", "(8a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "yī gè cōngmíng (de) xuéshēng"
    discourseSegments := []
    glossedTokens := [("yī", "one"), ("gè", "CL"), ("cōngmíng", "clever"), ("(de)", "(DE)"), ("xuéshēng", "student")]
    translation := "a clever student"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "bare"), ("position", "Cl _ N")]
    comment := "The adjective follows the classifier."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3 : LinguisticExample :=
  { id := "wangsun2026_3"
    source := ⟨"wang-sun-2026", "(29a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "yī hěn dà (de) zhāng zhuōzi"
    discourseSegments := []
    glossedTokens := [("yī", "one"), ("hěn", "very"), ("dà", "big"), ("(de)", "(DE)"), ("zhāng", "CL"), ("zhuōzi", "table")]
    translation := "a very big table"
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "degree"), ("position", "Num _ Cl")]
    comment := "A degree-modified adjective between the numeral and the classifier."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4 : LinguisticExample :=
  { id := "wangsun2026_4"
    source := ⟨"wang-sun-2026", "(29b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "yī dà zhāng zhuōzi"
    discourseSegments := []
    glossedTokens := [("yī", "one"), ("dà", "big"), ("zhāng", "CL"), ("zhuōzi", "table")]
    translation := "a big table"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "bare"), ("position", "Num _ Cl")]
    comment := "A bare size adjective before the classifier, spelled out with Q."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5 : LinguisticExample :=
  { id := "wangsun2026_5"
    source := ⟨"wang-sun-2026", "(28a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "yī zhāng hěn dà de zhuōzi"
    discourseSegments := []
    glossedTokens := [("yī", "one"), ("zhāng", "CL"), ("hěn", "very"), ("dà", "big"), ("de", "DE"), ("zhuōzi", "table")]
    translation := "a very big table"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "degree"), ("position", "Cl _ N")]
    comment := "A degree-modified adjective after the classifier."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6 : LinguisticExample :=
  { id := "wangsun2026_6"
    source := ⟨"wang-sun-2026", "(5c)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Gè píngguǒ, Zhāngsān chī-le sān"
    discourseSegments := []
    glossedTokens := [("Gè", "CL"), ("píngguǒ", "apple"), ("Zhāngsān", "Zhangsan"), ("chī-le", "eat-PFV"), ("sān", "three")]
    translation := "As to apples, Zhangsan ate three."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("dislocation", "Cl N")]
    comment := "Classifier and noun topicalized together, stranding the numeral."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7 : LinguisticExample :=
  { id := "wangsun2026_7"
    source := ⟨"wang-sun-2026", "(13b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Píngguǒ, Zhāngsān chī-le sān gè"
    discourseSegments := []
    glossedTokens := [("Píngguǒ", "apple"), ("Zhāngsān", "Zhangsan"), ("chī-le", "eat-PFV"), ("sān", "three"), ("gè", "CL")]
    translation := "As to apples, Zhangsan ate three."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dislocation", "N")]
    comment := "The noun topicalized alone."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8 : LinguisticExample :=
  { id := "wangsun2026_8"
    source := ⟨"wang-sun-2026", "(14a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Sān gè, Zhāngsān chī-le píngguǒ"
    discourseSegments := []
    glossedTokens := [("Sān", "three"), ("gè", "CL"), ("Zhāngsān", "Zhangsan"), ("chī-le", "eat-PFV"), ("píngguǒ", "apple")]
    translation := "Zhangsan ate three apples."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("dislocation", "Num Cl")]
    comment := "Numeral and classifier topicalized without the noun."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_9 : LinguisticExample :=
  { id := "wangsun2026_9"
    source := ⟨"wang-sun-2026", "(39a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhāngsān mǎi-le jǐ zhāng hěn dà de zhuōzi?"
    discourseSegments := []
    glossedTokens := [("Zhāngsān", "Zhangsan"), ("mǎi-le", "buy-PFV"), ("jǐ", "how.many"), ("zhāng", "CL"), ("hěn", "very"), ("dà", "big"), ("de", "DE"), ("zhuōzi", "table")]
    translation := "How many very big tables did Zhangsan buy?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("wh", "numeral"), ("modifier", "post-classifier")]
    comment := "The wh-numeral precedes a post-classifier modifier."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10 : LinguisticExample :=
  { id := "wangsun2026_10"
    source := ⟨"wang-sun-2026", "(39b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhāngsān mǎi-le hěn dà de jǐ zhāng zhuōzi?"
    discourseSegments := []
    glossedTokens := [("Zhāngsān", "Zhangsan"), ("mǎi-le", "buy-PFV"), ("hěn", "very"), ("dà", "big"), ("de", "DE"), ("jǐ", "how.many"), ("zhāng", "CL"), ("zhuōzi", "table")]
    translation := "How many very big tables did Zhangsan buy?"
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("wh", "numeral"), ("modifier", "pre-nominal")]
    comment := "The wh-numeral follows a pre-nominal modifier in D's second dimension."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_11 : LinguisticExample :=
  { id := "wangsun2026_11"
    source := ⟨"wang-sun-2026", "(33a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "sān bēi jiǔ"
    discourseSegments := []
    glossedTokens := [("sān", "three"), ("bēi", "glass"), ("jiǔ", "liquor")]
    translation := "three glasses of liquor"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "none"), ("reading", "sortal")]
    comment := "Without de the container classifier denotes real glasses: the sortal reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12 : LinguisticExample :=
  { id := "wangsun2026_12"
    source := ⟨"wang-sun-2026", "(33b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "sān bēi de jiǔ"
    discourseSegments := []
    glossedTokens := [("sān", "three"), ("bēi", "glass"), ("de", "DE"), ("jiǔ", "liquor")]
    translation := "three glassfuls of liquor"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "de"), ("reading", "mensural")]
    comment := "With de the classifier denotes an abstract unit: the mensural reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_12]

end WangSun2026.Examples
