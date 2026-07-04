import Linglib.Data.Examples.Schema

/-!
# `HartmannZimmermann2004` — typed example data

Auto-generated from `Linglib/Data/Examples/HartmannZimmermann2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HartmannZimmermann2004.Examples`.
-/

namespace HartmannZimmermann2004.Examples

open Data.Examples

def ex17b : LinguisticExample :=
  { id := "hartmannzimmermann2004_ex17b"
    source := ⟨"hartmann-zimmermann-2004", "(17b)"⟩
    reportedIn := none
    language := "tang1336"
    primaryText := "múdúd-gó nó̰?"
    discourseSegments := []
    glossedTokens := [("múdúd-gó", "die-PERF"), ("nó̰", "who")]
    translation := "Who died?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focused", "subject"), ("aspect", "perfective"), ("strategy", "postposing")]
    comment := "Wh-subjects, like focused subjects, obligatorily move to a postverbal position (§4.1.1)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex24a : LinguisticExample :=
  { id := "hartmannzimmermann2004_ex24a"
    source := ⟨"hartmann-zimmermann-2004", "(24a)"⟩
    reportedIn := none
    language := "tang1336"
    primaryText := "Fátíma wur-go."
    discourseSegments := []
    glossedTokens := [("Fátíma", "Fatima"), ("wur-go", "laugh-PERF")]
    translation := "Fatima laughed."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focused", "allNew"), ("aspect", "perfective"), ("strategy", "unmarked")]
    comment := "Neutral all-new sentence: no focus suffix."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex24b : LinguisticExample :=
  { id := "hartmannzimmermann2004_ex24b"
    source := ⟨"hartmann-zimmermann-2004", "(24b)"⟩
    reportedIn := none
    language := "tang1336"
    primaryText := "Mbáastám wur-gó-i."
    discourseSegments := []
    glossedTokens := [("Mbáastám", "she"), ("wur-gó-i", "laugh-PERF-FOC")]
    translation := "She LAUGHED."
    context := "Answer to: Mairo yaa-gó ná̰? 'What did Mairo do?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focused", "vp"), ("aspect", "perfective"), ("strategy", "suffixI"), ("transitive", "false")]
    comment := "Morphological focus marking with the suffix -i, reserved for (some) intransitive verbal predicates (§5.2.1, their fn. 6)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex25a : LinguisticExample :=
  { id := "hartmannzimmermann2004_ex25a"
    source := ⟨"hartmann-zimmermann-2004", "(25a)"⟩
    reportedIn := none
    language := "tang1336"
    primaryText := "Lak wai-gó lánda"
    discourseSegments := []
    glossedTokens := [("Lak", "Laku"), ("wai-gó", "sell-PERF"), ("lánda", "dress")]
    translation := "Laku sold A DRESS."
    context := "Answer to: What did Laku sell?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focused", "object"), ("aspect", "perfective"), ("strategy", "boundary"), ("transitive", "true")]
    comment := "Prosodic phrase boundary after the verb: vowel elision and left line delinking are blocked (non-elided wai-gó with its H-tone intact)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex25b : LinguisticExample :=
  { id := "hartmannzimmermann2004_ex25b"
    source := ⟨"hartmann-zimmermann-2004", "(25b)"⟩
    reportedIn := none
    language := "tang1336"
    primaryText := "Lak wai-gó lánda"
    discourseSegments := []
    glossedTokens := [("Lak", "Laku"), ("wai-gó", "sell-PERF"), ("lánda", "dress")]
    translation := "Laku [sold A DRESS]F."
    context := "Answer to: What did Laku do?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focused", "vp"), ("aspect", "perfective"), ("strategy", "boundary"), ("transitive", "true")]
    comment := "String-identical to (25a): the boundary marks V-, VP-, and OBJ-focus alike; the §5.3 pitch study finds no further prosodic cue."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex25c : LinguisticExample :=
  { id := "hartmannzimmermann2004_ex25c"
    source := ⟨"hartmann-zimmermann-2004", "(25c)"⟩
    reportedIn := none
    language := "tang1336"
    primaryText := "Lak wai-gó lánda"
    discourseSegments := []
    glossedTokens := [("Lak", "Laku"), ("wai-gó", "sell-PERF"), ("lánda", "dress")]
    translation := "Laku [SOLD]F a dress."
    context := "Answer to: What did Laku do at the market? Did she buy a dress or did she sell a dress?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focused", "verb"), ("aspect", "perfective"), ("strategy", "boundary"), ("transitive", "true")]
    comment := "Third member of the string-identical (25) triple."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex31 : LinguisticExample :=
  { id := "hartmannzimmermann2004_ex31"
    source := ⟨"hartmann-zimmermann-2004", "(31)"⟩
    reportedIn := none
    language := "tang1336"
    primaryText := "Lakú n ball wasíika"
    discourseSegments := []
    glossedTokens := [("Lakú", "Laku"), ("n", "PROG"), ("ball", "writing"), ("wasíika", "letter")]
    translation := "Laku is writing a letter."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focused", "allNew"), ("aspect", "progressive"), ("strategy", "unmarked")]
    comment := "Neutral progressive: vowel elision applies obligatorily (balli > ball)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex32a : LinguisticExample :=
  { id := "hartmannzimmermann2004_ex32a"
    source := ⟨"hartmann-zimmermann-2004", "(32a)"⟩
    reportedIn := none
    language := "tang1336"
    primaryText := "Lakú n ball wasíika"
    discourseSegments := []
    glossedTokens := [("Lakú", "Laku"), ("n", "PROG"), ("ball", "writing"), ("wasíika", "letter")]
    translation := "Laku is writing A LETTER."
    context := "Answer to: Lakú n ball ná̰? 'What is Laku writing?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focused", "object"), ("aspect", "progressive"), ("strategy", "unmarked")]
    comment := "No discernible difference from neutral (31): VE applies as usual — contra Kidda 1993:127 (their fn. 12)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex32b : LinguisticExample :=
  { id := "hartmannzimmermann2004_ex32b"
    source := ⟨"hartmann-zimmermann-2004", "(32b)"⟩
    reportedIn := none
    language := "tang1336"
    primaryText := "Lakú n ball wasíika"
    discourseSegments := []
    glossedTokens := [("Lakú", "Laku"), ("n", "PROG"), ("ball", "writing"), ("wasíika", "letter")]
    translation := "Laku is [writing A LETTER]F."
    context := "Answer to: Lakú n yaaj ná̰? 'What is Laku doing?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focused", "vp"), ("aspect", "progressive"), ("strategy", "unmarked")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex32c : LinguisticExample :=
  { id := "hartmannzimmermann2004_ex32c"
    source := ⟨"hartmann-zimmermann-2004", "(32c)"⟩
    reportedIn := none
    language := "tang1336"
    primaryText := "Lakú n ball wasíika"
    discourseSegments := []
    glossedTokens := [("Lakú", "Laku"), ("n", "PROG"), ("ball", "writing"), ("wasíika", "letter")]
    translation := "Laku is [WRITING]F a letter."
    context := "Answer to: Lakú n ball wasíika yá mad wasíika? 'Is Laku WRITING a letter or READING a letter?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focused", "verb"), ("aspect", "progressive"), ("strategy", "unmarked")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex36a : LinguisticExample :=
  { id := "hartmannzimmermann2004_ex36a"
    source := ⟨"hartmann-zimmermann-2004", "(36a)"⟩
    reportedIn := none
    language := "tang1336"
    primaryText := "N fad-go núm littáfi-i, n fad-ug wam gáayi-m"
    discourseSegments := []
    glossedTokens := [("N", "I"), ("fad-go", "buy-PERF"), ("núm", "only"), ("littáfi-i", "book-the"), ("n", "I"), ("fad-ug", "buy-PERF"), ("wam gáayi-m", "s.th.else-NEG")]
    translation := "I bought only THE BOOK, I bought nothing else."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focused", "object"), ("aspect", "perfective"), ("association", "object")]
    comment := "núm is syntactically fixed to DP expressions (like Hausa sái) but associates semantically with OBJ, VP, or V focus (§6.3); pitch tracks show no prosodic difference across (36a-c)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex36b : LinguisticExample :=
  { id := "hartmannzimmermann2004_ex36b"
    source := ⟨"hartmann-zimmermann-2004", "(36b)"⟩
    reportedIn := none
    language := "tang1336"
    primaryText := "N fad-go núm littáfi-i, n yaa-g wamgáayi-m"
    discourseSegments := []
    glossedTokens := [("N", "I"), ("fad-go", "buy-PERF"), ("núm", "only"), ("littáfi-i", "book-the"), ("n", "I"), ("yaa-g", "do-PERF"), ("wamgáayi-m", "s.th.else-NEG")]
    translation := "I only bought THE BOOK, I did nothing else."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focused", "vp"), ("aspect", "perfective"), ("association", "vp")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex36c : LinguisticExample :=
  { id := "hartmannzimmermann2004_ex36c"
    source := ⟨"hartmann-zimmermann-2004", "(36c)"⟩
    reportedIn := none
    language := "tang1336"
    primaryText := "N fad-go núm littáfi-i, fon di n mad-go-m"
    discourseSegments := []
    glossedTokens := [("N", "I"), ("fad-go", "buy-PERF"), ("núm", "only"), ("littáfi-i", "book-the"), ("fon di", "but yet"), ("n", "I"), ("mad-go-m", "read-PERF-NEG")]
    translation := "I only BOUGHT the book, but I have not read (it) yet."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focused", "verb"), ("aspect", "perfective"), ("association", "verb")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex17b, ex24a, ex24b, ex25a, ex25b, ex25c, ex31, ex32a, ex32b, ex32c, ex36a, ex36b, ex36c]

end HartmannZimmermann2004.Examples
