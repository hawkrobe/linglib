module

public import Linglib.Data.Examples.Schema

/-!
# `WangSun2026` — typed example data

Auto-generated from `Linglib/Data/Examples/WangSun2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace WangSun2026.Examples`.
-/

@[expose] public section

namespace WangSun2026.Examples

open Data.Examples

def ex_1 : Datum :=
  { id := "wangsun2026_1"
    source := ⟨"wang-sun-2026", "(4c)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "yī hěn cōngmíng de gè xuéshēng"
    glossedTokens := [("yī", "one"), ("hěn", "very"), ("cōngmíng", "clever"), ("de", "DE"), ("gè", "CL"), ("xuéshēng", "student")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "degree"), ("position", "Num _ Cl")] }

def ex_2 : Datum :=
  { id := "wangsun2026_2"
    source := ⟨"wang-sun-2026", "(8a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "yī gè cōngmíng (de) xuéshēng"
    glossedTokens := [("yī", "one"), ("gè", "CL"), ("cōngmíng", "clever"), ("(de)", "(DE)"), ("xuéshēng", "student")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "bare"), ("position", "Cl _ N")] }

def ex_3 : Datum :=
  { id := "wangsun2026_3"
    source := ⟨"wang-sun-2026", "(29a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "yī hěn dà (de) zhāng zhuōzi"
    glossedTokens := [("yī", "one"), ("hěn", "very"), ("dà", "big"), ("(de)", "(DE)"), ("zhāng", "CL"), ("zhuōzi", "table")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "degree"), ("position", "Num _ Cl")] }

def ex_4 : Datum :=
  { id := "wangsun2026_4"
    source := ⟨"wang-sun-2026", "(29b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "yī dà zhāng zhuōzi"
    glossedTokens := [("yī", "one"), ("dà", "big"), ("zhāng", "CL"), ("zhuōzi", "table")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "bare"), ("position", "Num _ Cl")] }

def ex_5 : Datum :=
  { id := "wangsun2026_5"
    source := ⟨"wang-sun-2026", "(28a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "yī zhāng hěn dà de zhuōzi"
    glossedTokens := [("yī", "one"), ("zhāng", "CL"), ("hěn", "very"), ("dà", "big"), ("de", "DE"), ("zhuōzi", "table")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "degree"), ("position", "Cl _ N")] }

def ex_6 : Datum :=
  { id := "wangsun2026_6"
    source := ⟨"wang-sun-2026", "(5c)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Gè píngguǒ, Zhāngsān chī-le sān"
    glossedTokens := [("Gè", "CL"), ("píngguǒ", "apple"), ("Zhāngsān", "Zhangsan"), ("chī-le", "eat-PFV"), ("sān", "three")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("dislocation", "Cl N")] }

def ex_7 : Datum :=
  { id := "wangsun2026_7"
    source := ⟨"wang-sun-2026", "(13b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Píngguǒ, Zhāngsān chī-le sān gè"
    glossedTokens := [("Píngguǒ", "apple"), ("Zhāngsān", "Zhangsan"), ("chī-le", "eat-PFV"), ("sān", "three"), ("gè", "CL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dislocation", "N")] }

def ex_8 : Datum :=
  { id := "wangsun2026_8"
    source := ⟨"wang-sun-2026", "(14a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Sān gè, Zhāngsān chī-le píngguǒ"
    glossedTokens := [("Sān", "three"), ("gè", "CL"), ("Zhāngsān", "Zhangsan"), ("chī-le", "eat-PFV"), ("píngguǒ", "apple")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("dislocation", "Num Cl")] }

def ex_9 : Datum :=
  { id := "wangsun2026_9"
    source := ⟨"wang-sun-2026", "(39a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhāngsān mǎi-le jǐ zhāng hěn dà de zhuōzi?"
    glossedTokens := [("Zhāngsān", "Zhangsan"), ("mǎi-le", "buy-PFV"), ("jǐ", "how.many"), ("zhāng", "CL"), ("hěn", "very"), ("dà", "big"), ("de", "DE"), ("zhuōzi", "table")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("wh", "numeral"), ("modifier", "post-classifier")] }

def ex_10 : Datum :=
  { id := "wangsun2026_10"
    source := ⟨"wang-sun-2026", "(39b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Zhāngsān mǎi-le hěn dà de jǐ zhāng zhuōzi?"
    glossedTokens := [("Zhāngsān", "Zhangsan"), ("mǎi-le", "buy-PFV"), ("hěn", "very"), ("dà", "big"), ("de", "DE"), ("jǐ", "how.many"), ("zhāng", "CL"), ("zhuōzi", "table")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("wh", "numeral"), ("modifier", "pre-nominal")] }

def ex_11 : Datum :=
  { id := "wangsun2026_11"
    source := ⟨"wang-sun-2026", "(33a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "sān bēi jiǔ"
    glossedTokens := [("sān", "three"), ("bēi", "glass"), ("jiǔ", "liquor")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "none"), ("reading", "sortal")] }

def ex_12 : Datum :=
  { id := "wangsun2026_12"
    source := ⟨"wang-sun-2026", "(33b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "sān bēi de jiǔ"
    glossedTokens := [("sān", "three"), ("bēi", "glass"), ("de", "DE"), ("jiǔ", "liquor")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "de"), ("reading", "mensural")] }

def ex_13 : Datum :=
  { id := "wangsun2026_13"
    source := ⟨"wang-sun-2026", "(31)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "nà hěn dà de yī zhāng zhuōzi"
    glossedTokens := [("nà", "that"), ("hěn", "very"), ("dà", "big"), ("de", "DE"), ("yī", "one"), ("zhāng", "CL"), ("zhuōzi", "table")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "de-marked"), ("position", "D _ Num")] }

def ex_14 : Datum :=
  { id := "wangsun2026_14"
    source := ⟨"wang-sun-2026", "(37a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "hěn míngguì de sān gè bēizi de jiǔ"
    glossedTokens := [("hěn", "very"), ("míngguì", "expensive"), ("de", "DE"), ("sān", "three"), ("gè", "CL"), ("bēizi", "glass"), ("de", "DE"), ("jiǔ", "liquor")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "two de-marked"), ("target", "D")] }

def ex_15 : Datum :=
  { id := "wangsun2026_15"
    source := ⟨"wang-sun-2026", "(37b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "hěn dà de sān gè bēizi de jiǔ"
    glossedTokens := [("hěn", "very"), ("dà", "big"), ("de", "DE"), ("sān", "three"), ("gè", "CL"), ("bēizi", "glass"), ("de", "DE"), ("jiǔ", "liquor")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modifier", "nested de-marked")] }

def ex_16 : Datum :=
  { id := "wangsun2026_16"
    source := ⟨"wang-sun-2026", "(43a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Sān gè píngguǒ, Zhāngsān chī-le."
    glossedTokens := [("Sān", "three"), ("gè", "CL"), ("píngguǒ", "apple"), ("Zhāngsān", "Zhangsan"), ("chī-le", "eat-PFV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topicalisation", "D")] }

def ex_17 : Datum :=
  { id := "wangsun2026_17"
    source := ⟨"wang-sun-2026", "(44a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Píngguǒ, Zhāngsān chī-le sān gè hěn dà de."
    glossedTokens := [("Píngguǒ", "apple"), ("Zhāngsān", "Zhangsan"), ("chī-le", "eat-PFV"), ("sān", "three"), ("gè", "CL"), ("hěn", "very"), ("dà", "big"), ("de", "DE")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topicalisation", "N"), ("modifier", "2-part of Cl")] }

def ex_18 : Datum :=
  { id := "wangsun2026_18"
    source := ⟨"wang-sun-2026", "(44b)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Píngguǒ, Zhāngsān chī-le hěn dà de sān gè."
    glossedTokens := [("Píngguǒ", "apple"), ("Zhāngsān", "Zhangsan"), ("chī-le", "eat-PFV"), ("hěn", "very"), ("dà", "big"), ("de", "DE"), ("sān", "three"), ("gè", "CL")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("topicalisation", "N"), ("modifier", "2-part of D")] }

def ex_19 : Datum :=
  { id := "wangsun2026_19"
    source := ⟨"wang-sun-2026", "(45a)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "Píngguǒ bǐ yīngtáo duō sān kē."
    glossedTokens := [("Píngguǒ", "apple"), ("bǐ", "than"), ("yīngtáo", "cherry"), ("duō", "much"), ("sān", "three"), ("kē", "CL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "measure"), ("noun", "absent")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14, ex_15, ex_16, ex_17, ex_18, ex_19]

end WangSun2026.Examples
