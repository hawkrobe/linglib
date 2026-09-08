import Linglib.Data.Examples.Schema

/-!
# `BhattTakahashi2011` — typed example data

Auto-generated from `Linglib/Data/Examples/BhattTakahashi2011.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BhattTakahashi2011.Examples`.
-/

namespace BhattTakahashi2011.Examples

open Data.Examples

def ex11a : LinguisticExample :=
  { id := "bhatttakahashi2011_ex11a"
    source := ⟨"bhatt-takahashi-2011", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "More people introduced him_i to Mary than to John_i's mother."
    discourseSegments := []
    glossedTokens := []
    translation := "More people introduced him to Mary than to John's mother."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "binding"), ("pron_c_commands_associate", "yes")]
    comment := "The pronoun c-commands the associate and cannot corefer with an R-expression inside the standard; control: More people introduced John_i to Mary than to his_i mother."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex11b : LinguisticExample :=
  { id := "bhatttakahashi2011_ex11b"
    source := ⟨"bhatt-takahashi-2011", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary introduced him_i to more people than John_i's mother."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary introduced him to more people than John's mother."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "binding"), ("pron_c_commands_associate", "no")]
    comment := "The pronoun does not c-command the associate; coreference into the standard is possible."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex12a : LinguisticExample :=
  { id := "bhatttakahashi2011_ex12a"
    source := ⟨"bhatt-takahashi-2011", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "More people talked to him_i about Sally than about Peter_i's sister."
    discourseSegments := []
    glossedTokens := []
    translation := "More people talked to him about Sally than about Peter's sister."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "binding"), ("pron_c_commands_associate", "yes")]
    comment := "Control: More people talked to Peter_i about Sally than about his_i sister."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex12b : LinguisticExample :=
  { id := "bhatttakahashi2011_ex12b"
    source := ⟨"bhatt-takahashi-2011", "(12b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "More people talked to Sally about him_i than to Peter_i's sister."
    discourseSegments := []
    glossedTokens := []
    translation := "More people talked to Sally about him than to Peter's sister."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "binding"), ("pron_c_commands_associate", "no")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex13a : LinguisticExample :=
  { id := "bhatttakahashi2011_ex13a"
    source := ⟨"bhatt-takahashi-2011", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "More people expect him_i to overtake Sally than Peter_i's sister."
    discourseSegments := []
    glossedTokens := []
    translation := "More people expect him to overtake Sally than Peter's sister."
    context := "Peter, Peter's sister, and Sally are taking part in a race; people are betting on their prospects."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "binding"), ("pron_c_commands_associate", "yes")]
    comment := "Control: More people expect Peter_i to overtake Sally than his_i sister."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex13b : LinguisticExample :=
  { id := "bhatttakahashi2011_ex13b"
    source := ⟨"bhatt-takahashi-2011", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "More people expect Sally to overtake him_i than Peter_i's sister."
    discourseSegments := []
    glossedTokens := []
    translation := "More people expect Sally to overtake him than Peter's sister."
    context := "Peter, Peter's sister, and Sally are taking part in a race; people are betting on their prospects."
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "binding"), ("pron_c_commands_associate", "no")]
    comment := "Marginal for some speakers (fn. 5), in the coreference-licit direction."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex35 : LinguisticExample :=
  { id := "bhatttakahashi2011_ex35"
    source := ⟨"bhatt-takahashi-2011", "(35)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "Atif-ne Ravi-kii behen-kii foto-se us-ko Mohan-kii behen-kii foto zyaadaa baar dikhaa-ii."
    discourseSegments := []
    glossedTokens := [("Atif-ne", "Atif-ERG"), ("Ravi-kii", "Ravi-GEN"), ("behen-kii", "sister-GEN"), ("foto-se", "picture-than"), ("us-ko", "he-DAT"), ("Mohan-kii", "Mohan-GEN"), ("behen-kii", "sister-GEN"), ("foto", "picture"), ("zyaadaa", "more"), ("baar", "times"), ("dikhaa-ii", "show-PFV.F")]
    translation := "Atif showed Mohan's sister's picture to him more times than Ravi's sister's picture."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "binding"), ("pron_c_commands_associate", "yes")]
    comment := "The pronoun follows the standard and precedes the associate, so it c-commands the associate, yet corefers with the R-expression inside the standard: the standard is an external PP."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex43a : LinguisticExample :=
  { id := "bhatttakahashi2011_ex43a"
    source := ⟨"bhatt-takahashi-2011", "(43a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Craige assigned every first year student more papers than every second year student."
    discourseSegments := []
    glossedTokens := []
    translation := "Craige assigned every first year student more papers than every second year student."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "scope"), ("qp_base_c_commands_degree_trace", "yes"), ("than_internal_scope", "unavailable")]
    comment := "The quantifier's base position c-commands the than-phrase-internal degree trace, so it must scope out."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex43b : LinguisticExample :=
  { id := "bhatttakahashi2011_ex43b"
    source := ⟨"bhatt-takahashi-2011", "(43b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Craige assigned more students every paper by Hellan than every paper by Klein."
    discourseSegments := []
    glossedTokens := []
    translation := "Craige assigned more students every paper by Hellan than every paper by Klein."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "scope"), ("qp_base_c_commands_degree_trace", "no"), ("than_internal_scope", "available")]
    comment := "The base position does not c-command the degree trace, so than-phrase-internal scope is possible."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex40 : LinguisticExample :=
  { id := "bhatttakahashi2011_ex40"
    source := ⟨"bhatt-takahashi-2011", "(40)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "har syntax paper har semantics paper-se zyaadaa logõ-ne par.h-aa."
    discourseSegments := []
    glossedTokens := [("har", "every"), ("syntax", "syntax"), ("paper", "paper"), ("har", "every"), ("semantics", "semantics"), ("paper-se", "paper-than"), ("zyaadaa", "more"), ("logõ-ne", "people-ERG"), ("par.h-aa", "read-PFV")]
    translation := "More people read every syntax paper than every semantics paper."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "scope"), ("qp_base_c_commands_degree_trace", "no"), ("than_internal_scope", "unavailable")]
    comment := "Only the external scope reading, every > -er, is available; the than-phrase-internal reading needs the clausal comparative (41)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex11a, ex11b, ex12a, ex12b, ex13a, ex13b, ex35, ex43a, ex43b, ex40]

end BhattTakahashi2011.Examples
