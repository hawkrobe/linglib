import Linglib.Data.Examples.Schema

/-!
# `Belnap1982` — typed example data

Auto-generated from `Linglib/Data/Examples/Belnap1982.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Belnap1982.Examples`.
-/

namespace Belnap1982.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "belnap1982_1"
    source := ⟨"belnap-1982", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which person kicked Sam?"
    discourseSegments := []
    glossedTokens := []
    translation := "Which person kicked Sam?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("answers: John / It was John / The person who kicked Sam was John", .acceptable), ("non-answers: *He / *Sam kicked John / *China is populous", .unacceptable), ("responses but not answers: I don't know / Ask Sam", .acceptable)]
    paperFeatures := [("claim", "answerhood is as entrenched as sentencehood")]
    comment := "The battery grounding Q1: linguistic theory should describe the question-answer relationship."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def gas : LinguisticExample :=
  { id := "belnap1982_gas"
    source := ⟨"belnap-1982", "p. 172"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Where is a place at which I can get gas on a Sunday?"
    discourseSegments := []
    glossedTokens := []
    translation := "Where is a place at which I can get gas on a Sunday?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "Unique Answer Fallacy"), ("answers", "multiple, each full and complete and true")]
    comment := "A mention-some question: any open station is a complete true answer."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def prime : LinguisticExample :=
  { id := "belnap1982_prime"
    source := ⟨"belnap-1982", "p. 174"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What's an example of a prime between 10 and 20?"
    discourseSegments := []
    glossedTokens := []
    translation := "What's an example of a prime between 10 and 20?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "Unique Answer Fallacy"), ("target", "Karttunen-style unique denotations")]
    comment := "A foundation on which every question has one answer cannot even state a language that asks for examples."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def unicorns : LinguisticExample :=
  { id := "belnap1982_unicorns"
    source := ⟨"belnap-1982", "§3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John wonders where two unicorns live."
    discourseSegments := []
    glossedTokens := []
    translation := "John wonders where two unicorns live."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("for each of two actual unicorns, John wonders where it lives", .acceptable), ("John wonders where the single place is at which two unicorns live", .acceptable), ("quantifier between wonder and the wh: each unicorn possibly living in a different place", .acceptable)]
    paperFeatures := [("phenomenon", "quantifying into questions")]
    comment := "The third reading needs the quantifier scoped inside wonder but over where."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def grades : LinguisticExample :=
  { id := "belnap1982_grades"
    source := ⟨"belnap-1982", "§3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What the average grade is depends only on what grade each student receives."
    discourseSegments := []
    glossedTokens := []
    translation := "What the average grade is depends only on what grade each student receives."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "quantifying into questions"), ("embedding", "depend")]
    comment := "Each cannot scope over the whole declarative nor inside the wh: the quantified indirect question is a closed unit."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def king : LinguisticExample :=
  { id := "belnap1982_king"
    source := ⟨"belnap-1982", "§3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "whether the king of France is bald"
    discourseSegments := []
    glossedTokens := []
    translation := "whether the king of France is bald"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "quantifying into a whether"), ("status", "no true answers")]
    comment := "With the quantifier scoped in, an answer must answer for the present king of France; there being none, the question has no true answers."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def china : LinguisticExample :=
  { id := "belnap1982_china"
    source := ⟨"belnap-1982", "p. 177"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Peter knows that China is populous but he doesn't know which person kicked Sam."
    discourseSegments := []
    glossedTokens := []
    translation := "Peter knows that China is populous but he doesn't know which person kicked Sam."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "Distributivity Test"), ("verdict", "consistent, so not an answer")]
    comment := "Consistency of the know-P-but-not-IQ report rules P out as an answer."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def john : LinguisticExample :=
  { id := "belnap1982_john"
    source := ⟨"belnap-1982", "p. 177"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Peter knows that the person who kicked Sam is John but Peter doesn't know who kicked Sam."
    discourseSegments := []
    glossedTokens := []
    translation := "Peter knows that the person who kicked Sam is John but Peter doesn't know who kicked Sam."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "Distributivity Test"), ("verdict", "inconsistent — likely an answer, not guaranteed")]
    comment := "The test is a necessary condition only: passing it does not certify answerhood."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1, gas, prime, unicorns, grades, king, china, john]

end Belnap1982.Examples
