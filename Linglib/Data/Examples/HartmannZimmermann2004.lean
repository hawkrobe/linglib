module

public import Linglib.Data.Examples.Schema

/-!
# `HartmannZimmermann2004` — typed example data

Auto-generated from `Linglib/Data/Examples/HartmannZimmermann2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HartmannZimmermann2004.Examples`.
-/

@[expose] public section

namespace HartmannZimmermann2004.Examples

open Data.Examples

def ex17b : LinguisticExample :=
  { id := "hartmannzimmermann2004_ex17b"
    source := ⟨"hartmann-zimmermann-2004", "(17b)"⟩
    reportedIn := none
    language := "nucl1696"
    primaryText := "múdúd-gó nó̰?"
    glossedTokens := [("múdúd-gó", "die-PERF"), ("nó̰", "who")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focused", "subject"), ("aspect", "perfective"), ("strategy", "postposing")] }

def ex24a : LinguisticExample :=
  { id := "hartmannzimmermann2004_ex24a"
    source := ⟨"hartmann-zimmermann-2004", "(24a)"⟩
    reportedIn := none
    language := "nucl1696"
    primaryText := "Fátíma wur-go."
    glossedTokens := [("Fátíma", "Fatima"), ("wur-go", "laugh-PERF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focused", "allNew"), ("aspect", "perfective"), ("strategy", "unmarked")] }

def ex24b : LinguisticExample :=
  { id := "hartmannzimmermann2004_ex24b"
    source := ⟨"hartmann-zimmermann-2004", "(24b)"⟩
    reportedIn := none
    language := "nucl1696"
    primaryText := "Mbáastám wur-gó-i."
    glossedTokens := [("Mbáastám", "she"), ("wur-gó-i", "laugh-PERF-FOC")]
    context := "Answer to: Mairo yaa-gó ná̰? 'What did Mairo do?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focused", "vp"), ("aspect", "perfective"), ("strategy", "suffixI"), ("transitive", "false")] }

def ex25a : LinguisticExample :=
  { id := "hartmannzimmermann2004_ex25a"
    source := ⟨"hartmann-zimmermann-2004", "(25a)"⟩
    reportedIn := none
    language := "nucl1696"
    primaryText := "Lak wai-gó lánda"
    glossedTokens := [("Lak", "Laku"), ("wai-gó", "sell-PERF"), ("lánda", "dress")]
    context := "Answer to: What did Laku sell?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focused", "object"), ("aspect", "perfective"), ("strategy", "boundary"), ("transitive", "true")] }

def ex25b : LinguisticExample :=
  { id := "hartmannzimmermann2004_ex25b"
    source := ⟨"hartmann-zimmermann-2004", "(25b)"⟩
    reportedIn := none
    language := "nucl1696"
    primaryText := "Lak wai-gó lánda"
    glossedTokens := [("Lak", "Laku"), ("wai-gó", "sell-PERF"), ("lánda", "dress")]
    context := "Answer to: What did Laku do?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focused", "vp"), ("aspect", "perfective"), ("strategy", "boundary"), ("transitive", "true")] }

def ex25c : LinguisticExample :=
  { id := "hartmannzimmermann2004_ex25c"
    source := ⟨"hartmann-zimmermann-2004", "(25c)"⟩
    reportedIn := none
    language := "nucl1696"
    primaryText := "Lak wai-gó lánda"
    glossedTokens := [("Lak", "Laku"), ("wai-gó", "sell-PERF"), ("lánda", "dress")]
    context := "Answer to: What did Laku do at the market? Did she buy a dress or did she sell a dress?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focused", "verb"), ("aspect", "perfective"), ("strategy", "boundary"), ("transitive", "true")] }

def ex31 : LinguisticExample :=
  { id := "hartmannzimmermann2004_ex31"
    source := ⟨"hartmann-zimmermann-2004", "(31)"⟩
    reportedIn := none
    language := "nucl1696"
    primaryText := "Lakú n ball wasíika"
    glossedTokens := [("Lakú", "Laku"), ("n", "PROG"), ("ball", "writing"), ("wasíika", "letter")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focused", "allNew"), ("aspect", "progressive"), ("strategy", "unmarked")] }

def ex32a : LinguisticExample :=
  { id := "hartmannzimmermann2004_ex32a"
    source := ⟨"hartmann-zimmermann-2004", "(32a)"⟩
    reportedIn := none
    language := "nucl1696"
    primaryText := "Lakú n ball wasíika"
    glossedTokens := [("Lakú", "Laku"), ("n", "PROG"), ("ball", "writing"), ("wasíika", "letter")]
    context := "Answer to: Lakú n ball ná̰? 'What is Laku writing?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focused", "object"), ("aspect", "progressive"), ("strategy", "unmarked")] }

def ex32b : LinguisticExample :=
  { id := "hartmannzimmermann2004_ex32b"
    source := ⟨"hartmann-zimmermann-2004", "(32b)"⟩
    reportedIn := none
    language := "nucl1696"
    primaryText := "Lakú n ball wasíika"
    glossedTokens := [("Lakú", "Laku"), ("n", "PROG"), ("ball", "writing"), ("wasíika", "letter")]
    context := "Answer to: Lakú n yaaj ná̰? 'What is Laku doing?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focused", "vp"), ("aspect", "progressive"), ("strategy", "unmarked")] }

def ex32c : LinguisticExample :=
  { id := "hartmannzimmermann2004_ex32c"
    source := ⟨"hartmann-zimmermann-2004", "(32c)"⟩
    reportedIn := none
    language := "nucl1696"
    primaryText := "Lakú n ball wasíika"
    glossedTokens := [("Lakú", "Laku"), ("n", "PROG"), ("ball", "writing"), ("wasíika", "letter")]
    context := "Answer to: Lakú n ball wasíika yá mad wasíika? 'Is Laku WRITING a letter or READING a letter?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focused", "verb"), ("aspect", "progressive"), ("strategy", "unmarked")] }

def ex36a : LinguisticExample :=
  { id := "hartmannzimmermann2004_ex36a"
    source := ⟨"hartmann-zimmermann-2004", "(36a)"⟩
    reportedIn := none
    language := "nucl1696"
    primaryText := "N fad-go núm littáfi-i, n fad-ug wam gáayi-m"
    glossedTokens := [("N", "I"), ("fad-go", "buy-PERF"), ("núm", "only"), ("littáfi-i", "book-the"), ("n", "I"), ("fad-ug", "buy-PERF"), ("wam gáayi-m", "s.th.else-NEG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focused", "object"), ("aspect", "perfective"), ("association", "object")] }

def ex36b : LinguisticExample :=
  { id := "hartmannzimmermann2004_ex36b"
    source := ⟨"hartmann-zimmermann-2004", "(36b)"⟩
    reportedIn := none
    language := "nucl1696"
    primaryText := "N fad-go núm littáfi-i, n yaa-g wamgáayi-m"
    glossedTokens := [("N", "I"), ("fad-go", "buy-PERF"), ("núm", "only"), ("littáfi-i", "book-the"), ("n", "I"), ("yaa-g", "do-PERF"), ("wamgáayi-m", "s.th.else-NEG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focused", "vp"), ("aspect", "perfective"), ("association", "vp")] }

def ex36c : LinguisticExample :=
  { id := "hartmannzimmermann2004_ex36c"
    source := ⟨"hartmann-zimmermann-2004", "(36c)"⟩
    reportedIn := none
    language := "nucl1696"
    primaryText := "N fad-go núm littáfi-i, fon di n mad-go-m"
    glossedTokens := [("N", "I"), ("fad-go", "buy-PERF"), ("núm", "only"), ("littáfi-i", "book-the"), ("fon di", "but yet"), ("n", "I"), ("mad-go-m", "read-PERF-NEG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focused", "verb"), ("aspect", "perfective"), ("association", "verb")] }

def all : List LinguisticExample := [ex17b, ex24a, ex24b, ex25a, ex25b, ex25c, ex31, ex32a, ex32b, ex32c, ex36a, ex36b, ex36c]

end HartmannZimmermann2004.Examples
