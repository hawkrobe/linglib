module

public import Linglib.Data.Examples.Schema

/-!
# `Hewett2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Hewett2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Hewett2026.Examples`.
-/

@[expose] public section

namespace Hewett2026.Examples

def ex1a : Datum :=
  { id := "hewett2026_ex1a"
    source := ⟨"hewett-2026", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They apologized for/*to/*of their behavior."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("root", "apologi"), ("category", "V"), ("prep", "for")] }

def ex1b : Datum :=
  { id := "hewett2026_ex1b"
    source := ⟨"hewett-2026", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Their apology for/*to/*of their behavior was half-hearted."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("root", "apologi"), ("category", "N"), ("prep", "for")] }

def ex1c : Datum :=
  { id := "hewett2026_ex1c"
    source := ⟨"hewett-2026", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They are apologetic for/*to/*of their behavior."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("root", "apologi"), ("category", "A"), ("prep", "for")] }

def ex2a : Datum :=
  { id := "hewett2026_ex2a"
    source := ⟨"hewett-2026", "(2a)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "bftaxir b-/*ʕala/*min zakaʔ-i."
    glossedTokens := [("bftaxir", "be.proud.1.SG"), ("b-/*ʕala/*min", "in-/*over/*from"), ("zakaʔ-i", "intelligence-my")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("root", "fxr"), ("category", "V"), ("prep", "b-")] }

def ex2b : Datum :=
  { id := "hewett2026_ex2b"
    source := ⟨"hewett-2026", "(2b)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "ʕand-i faxr b-/*ʕala/*min zakaʔ-i."
    glossedTokens := [("ʕand-i", "at-me"), ("faxr", "pride"), ("b-/*ʕala/*min", "in-/*over/*from"), ("zakaʔ-i", "intelligence-my")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("root", "fxr"), ("category", "N"), ("prep", "b-")] }

def ex2c : Datum :=
  { id := "hewett2026_ex2c"
    source := ⟨"hewett-2026", "(2c)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "ʔana faxur b-/*ʕala/*min zakaʔ-i."
    glossedTokens := [("ʔana", "I"), ("faxur", "proud"), ("b-/*ʕala/*min", "in-/*over/*from"), ("zakaʔ-i", "intelligence-my")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("root", "fxr"), ("category", "A"), ("prep", "b-")] }

def ex5a : Datum :=
  { id := "hewett2026_ex5a"
    source := ⟨"hewett-2026", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She prides herself on/*in/*of her thoroughness."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("root", "prd"), ("category", "V"), ("prep", "on")] }

def ex5b : Datum :=
  { id := "hewett2026_ex5b"
    source := ⟨"hewett-2026", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Her pride in/*on/*of her thoroughness is understandable."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("root", "prd"), ("category", "N"), ("prep", "in")] }

def ex5c : Datum :=
  { id := "hewett2026_ex5c"
    source := ⟨"hewett-2026", "(5c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is proud of/*on/*in her thoroughness."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("root", "prd"), ("category", "A"), ("prep", "of")] }

def ex6a : Datum :=
  { id := "hewett2026_ex6a"
    source := ⟨"hewett-2026", "(6a)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "barako-ni b-/*ʕa(la) l-walad."
    glossedTokens := [("barako-ni", "congratulated.3.PL-me"), ("b-/*ʕa(la)", "in-/*over"), ("l-walad", "the-baby")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("root", "brk"), ("category", "V"), ("prep", "b-")] }

def ex6b : Datum :=
  { id := "hewett2026_ex6b"
    source := ⟨"hewett-2026", "(6b)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "baʕtu-li mbarake ʕa(la)/*b- l-walad."
    glossedTokens := [("baʕtu-li", "sent.3.PL-to.me"), ("mbarake", "congratulations"), ("ʕa(la)/*b-", "over/*in-"), ("l-walad", "the-baby")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("root", "brk"), ("category", "N"), ("prep", "ʕala")] }

def ex11a : Datum :=
  { id := "hewett2026_ex11a"
    source := ⟨"hewett-2026", "(11a)"⟩
    reportedIn := none
    language := "tuni1259"
    primaryText := "xaf min l-ʔasad."
    glossedTokens := [("xaf", "feared.3.M.SG"), ("min", "from"), ("l-ʔasad", "the-lion")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("root", "xwf"), ("template", "XaYaZ"), ("prep", "min")] }

def ex11b : Datum :=
  { id := "hewett2026_ex11b"
    source := ⟨"hewett-2026", "(11b)"⟩
    reportedIn := none
    language := "tuni1259"
    primaryText := "xawwəf-u min l-ʔasad."
    glossedTokens := [("xawwəf-u", "made.afraid.3.M.SG-him"), ("min", "from"), ("l-ʔasad", "the-lion")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("root", "xwf"), ("template", "XaYYaZ"), ("prep", "min")] }

def ex13ai : Datum :=
  { id := "hewett2026_ex13ai"
    source := ⟨"hewett-2026", "(13a.i)"⟩
    reportedIn := none
    language := "tuni1259"
    primaryText := "kraht (*fi) Sami."
    glossedTokens := [("kraht", "hate.1.SG"), ("(*fi)", "(*in)"), ("Sami", "Sami")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "krh"), ("template", "XaYaZ"), ("prep", "none")] }

def ex13aii : Datum :=
  { id := "hewett2026_ex13aii"
    source := ⟨"hewett-2026", "(13a.ii)"⟩
    reportedIn := none
    language := "tuni1259"
    primaryText := "karraht-ha *(fi) Sami."
    glossedTokens := [("karraht-ha", "made.hate.1.SG-her"), ("*(fi)", "*(in)"), ("Sami", "Sami")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "krh"), ("template", "XaYYaZ"), ("prep", "fi")] }

def ex13bi : Datum :=
  { id := "hewett2026_ex13bi"
    source := ⟨"hewett-2026", "(13b.i)"⟩
    reportedIn := none
    language := "tuni1259"
    primaryText := "l-ħnaʃ daːr biː-/*ʕliː-k."
    glossedTokens := [("l-ħnaʃ", "the-snake"), ("daːr", "encircled.3.M.SG"), ("biː-/*ʕliː-k", "in-/*over-you")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "dwr"), ("template", "XaYaZ"), ("prep", "bi-")] }

def ex13bii : Datum :=
  { id := "hewett2026_ex13bii"
    source := ⟨"hewett-2026", "(13b.ii)"⟩
    reportedIn := none
    language := "tuni1259"
    primaryText := "dawwart l-ħnaʃ ʕliː-/*biː-k."
    glossedTokens := [("dawwart", "encircled.1.SG"), ("l-ħnaʃ", "the-snake"), ("ʕliː-/*biː-k", "over-/*in-you")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "dwr"), ("template", "XaYYaZ"), ("prep", "ʕla")] }

def ex14a : Datum :=
  { id := "hewett2026_ex14a"
    source := ⟨"hewett-2026", "(14a)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "ħakam ʕalej-o b-s-siʤn."
    glossedTokens := [("ħakam", "sentenced.3.M.SG"), ("ʕalej-o", "over-him"), ("b-s-siʤn", "in-the-jail")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "ħkm"), ("template", "XaYaZ"), ("prep", "ʕala")] }

def ex14b : Datum :=
  { id := "hewett2026_ex14b"
    source := ⟨"hewett-2026", "(14b)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "ħakkam (*ʕala/*b-) (l-mubaːreː)."
    glossedTokens := [("ħakkam", "refereed.3.M.SG"), ("(*ʕala/*b-)", "(*over/*in-)"), ("(l-mubaːreː)", "(the-match)")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "ħkm"), ("template", "XaYYaZ"), ("prep", "none")] }

def ex15a_active : Datum :=
  { id := "hewett2026_ex15a_active"
    source := ⟨"hewett-2026", "(15a)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "wasaʔ b- NP"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "wsʔ"), ("template", "XaYaZ"), ("prep", "b-")] }

def ex15a_nonactive : Datum :=
  { id := "hewett2026_ex15a_nonactive"
    source := ⟨"hewett-2026", "(15a)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "nwasaʔ b- NP"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "wsʔ"), ("template", "nXaYaZ"), ("prep", "b-")] }

def ex15b_active : Datum :=
  { id := "hewett2026_ex15b_active"
    source := ⟨"hewett-2026", "(15b)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "ʤaðab NP1 la-/ʕala NP2"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "ʤðb"), ("template", "XaYaZ"), ("prep", "la-/ʕala")] }

def ex15b_nonactive : Datum :=
  { id := "hewett2026_ex15b_nonactive"
    source := ⟨"hewett-2026", "(15b)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "nʤaðab la-/??ʕala NP2"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "ʤðb"), ("template", "nXaYaZ"), ("prep", "la-")] }

def ex15c_active : Datum :=
  { id := "hewett2026_ex15c_active"
    source := ⟨"hewett-2026", "(15c)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "ʃaka NP1 la- NP2"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "ʃkw"), ("template", "XaYaZ"), ("prep", "la-")] }

def ex15c_nonactive : Datum :=
  { id := "hewett2026_ex15c_nonactive"
    source := ⟨"hewett-2026", "(15c)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "nʃaka ʕala NP"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "ʃkw"), ("template", "nXaYaZ"), ("prep", "ʕala")] }

def ex16a_active : Datum :=
  { id := "hewett2026_ex16a_active"
    source := ⟨"hewett-2026", "(16a)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "dawwar ʕala NP"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "dwr"), ("template", "XaYYaZ"), ("prep", "ʕala")] }

def ex16a_nonactive : Datum :=
  { id := "hewett2026_ex16a_nonactive"
    source := ⟨"hewett-2026", "(16a)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "ddawwar ʕala NP"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "dwr"), ("template", "tXaYYaZ"), ("prep", "ʕala")] }

def ex16b_active : Datum :=
  { id := "hewett2026_ex16b_active"
    source := ⟨"hewett-2026", "(16b)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "ʃawwaʔ NP2 ʕala/*la- NP1"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "ʃwq"), ("template", "XaYYaZ"), ("prep", "ʕala")] }

def ex16b_nonactive : Datum :=
  { id := "hewett2026_ex16b_nonactive"
    source := ⟨"hewett-2026", "(16b)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "tʃawwaʔ ʕala/la- NP1"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "ʃwq"), ("template", "tXaYYaZ"), ("prep", "ʕala/la-")] }

def ex16c_active : Datum :=
  { id := "hewett2026_ex16c_active"
    source := ⟨"hewett-2026", "(16c)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "ħakkam"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "ħkm"), ("template", "XaYYaZ"), ("prep", "none")] }

def ex16c_nonactive : Datum :=
  { id := "hewett2026_ex16c_nonactive"
    source := ⟨"hewett-2026", "(16c)"⟩
    reportedIn := none
    language := "nort3139"
    primaryText := "tħakkam b- NP"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "ħkm"), ("template", "tXaYYaZ"), ("prep", "b-")] }

def ex17a : Datum :=
  { id := "hewett2026_ex17a"
    source := ⟨"hewett-2026", "(17a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "tipel be- NP1"
    glossedTokens := [("tipel", "treated"), ("be-", "in-"), ("NP1", "NP1")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "tpl"), ("template", "XiYeZ"), ("prep", "be-")] }

def ex17b : Datum :=
  { id := "hewett2026_ex17b"
    source := ⟨"hewett-2026", "(17b)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "NP1 tupal (al jedej NP2)"
    glossedTokens := [("NP1", "NP1"), ("tupal", "was.treated"), ("(al jedej NP2)", "(by NP2)")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "tpl"), ("template", "XuYaZ"), ("prep", "none")] }

def ex18a : Datum :=
  { id := "hewett2026_ex18a"
    source := ⟨"hewett-2026", "(18a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "hiʃpia al NP1"
    glossedTokens := [("hiʃpia", "influenced"), ("al", "over"), ("NP1", "NP1")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "ʃpʕ"), ("template", "hiXYiZ"), ("prep", "al")] }

def ex18b : Datum :=
  { id := "hewett2026_ex18b"
    source := ⟨"hewett-2026", "(18b)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "NP1 huʃpa (al jedej NP2)"
    glossedTokens := [("NP1", "NP1"), ("huʃpa", "was.influenced"), ("(al jedej NP2)", "(by NP2)")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "ʃpʕ"), ("template", "huXYaZ"), ("prep", "none")] }

def ex19a : Datum :=
  { id := "hewett2026_ex19a"
    source := ⟨"hewett-2026", "(19a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "serev le- NP1"
    glossedTokens := [("serev", "rejected"), ("le-", "to-"), ("NP1", "NP1")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "srb"), ("template", "XiYeZ"), ("prep", "le-")] }

def ex19b : Datum :=
  { id := "hewett2026_ex19b"
    source := ⟨"hewett-2026", "(19b)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "*NP1 surav (al jedej NP2)"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "srb"), ("template", "XuYaZ")] }

def ex20a : Datum :=
  { id := "hewett2026_ex20a"
    source := ⟨"hewett-2026", "(20a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "hirbic le- NP1"
    glossedTokens := [("hirbic", "hit"), ("le-", "to-"), ("NP1", "NP1")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "rbc"), ("template", "hiXYiZ"), ("prep", "le-")] }

def ex20b : Datum :=
  { id := "hewett2026_ex20b"
    source := ⟨"hewett-2026", "(20b)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "*NP1 hurbac (al jedej NP2)"
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "rbc"), ("template", "huXYaZ")] }

def ex21a : Datum :=
  { id := "hewett2026_ex21a"
    source := ⟨"hewett-2026", "(21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That kind of tumor can be operated on by experienced doctors."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "oper"), ("construction", "pseudopassive")] }

def ex21b : Datum :=
  { id := "hewett2026_ex21b"
    source := ⟨"hewett-2026", "(21b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That kind of tumor is operable (*on) (*by experienced doctors)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "oper"), ("construction", "-able")] }

def ex21c : Datum :=
  { id := "hewett2026_ex21c"
    source := ⟨"hewett-2026", "(21c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "*That kind of tumor operates on easily/quickly (by experienced doctors)."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "oper"), ("construction", "middle")] }

def ex22a : Datum :=
  { id := "hewett2026_ex22a"
    source := ⟨"hewett-2026", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That kind of tumor can be treated by experienced doctors."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "treat"), ("construction", "passive")] }

def ex22b : Datum :=
  { id := "hewett2026_ex22b"
    source := ⟨"hewett-2026", "(22b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That kind of tumor is treatable by experienced doctors."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "treat"), ("construction", "-able")] }

def ex22c : Datum :=
  { id := "hewett2026_ex22c"
    source := ⟨"hewett-2026", "(22c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(?)That kind of tumor treats easily/quickly (*by experienced doctors)."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("root", "treat"), ("construction", "middle")] }

def all : List Datum := [ex1a, ex1b, ex1c, ex2a, ex2b, ex2c, ex5a, ex5b, ex5c, ex6a, ex6b, ex11a, ex11b, ex13ai, ex13aii, ex13bi, ex13bii, ex14a, ex14b, ex15a_active, ex15a_nonactive, ex15b_active, ex15b_nonactive, ex15c_active, ex15c_nonactive, ex16a_active, ex16a_nonactive, ex16b_active, ex16b_nonactive, ex16c_active, ex16c_nonactive, ex17a, ex17b, ex18a, ex18b, ex19a, ex19b, ex20a, ex20b, ex21a, ex21b, ex21c, ex22a, ex22b, ex22c]

end Hewett2026.Examples
