module

public import Linglib.Data.Examples.Schema

/-!
# `Ostrove2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Ostrove2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Ostrove2026.Examples`.
-/

@[expose] public section

namespace Ostrove2026.Examples

def ex_9a_completive : Datum :=
  { id := "ostrove2026_9a_completive"
    source := ⟨"ostrove-2026", "(9a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ká'án =ì xìin Ana iin be'e"
    glossedTokens := [("Ká'án", "think:CONT"), ("=ì", "=I"), ("xìin", "buy:COMP"), ("Ana", "Ana"), ("iin", "one"), ("be'e", "house")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ka'án"), ("clauseType", "finite"), ("diagnostic", "aspect"), ("aspect", "completive")] }

def ex_9a_continuous : Datum :=
  { id := "ostrove2026_9a_continuous"
    source := ⟨"ostrove-2026", "(9a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ká'án =ì xíin Ana iin be'e"
    glossedTokens := [("Ká'án", "think:CONT"), ("=ì", "=I"), ("xíin", "buy:CONT"), ("Ana", "Ana"), ("iin", "one"), ("be'e", "house")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ka'án"), ("clauseType", "finite"), ("diagnostic", "aspect"), ("aspect", "continuous")] }

def ex_9a_irrealis : Datum :=
  { id := "ostrove2026_9a_irrealis"
    source := ⟨"ostrove-2026", "(9a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ká'án =ì kwiin Ana iin be'e"
    glossedTokens := [("Ká'án", "think:CONT"), ("=ì", "=I"), ("kwiin", "buy:IRR"), ("Ana", "Ana"), ("iin", "one"), ("be'e", "house")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ka'án"), ("clauseType", "finite"), ("diagnostic", "aspect"), ("aspect", "irrealis")] }

def ex_9b_completive : Datum :=
  { id := "ostrove2026_9b_completive"
    source := ⟨"ostrove-2026", "(9b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Nì- kà'àn Maria kìxi kwé'e =ñá"
    glossedTokens := [("Nì-", "COMP-"), ("kà'àn", "say"), ("Maria", "Maria"), ("kìxi", "sleep:COMP"), ("kwé'e", "much"), ("=ñá", "=she")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "kà'àn"), ("clauseType", "finite"), ("diagnostic", "aspect"), ("aspect", "completive")] }

def ex_9b_continuous : Datum :=
  { id := "ostrove2026_9b_continuous"
    source := ⟨"ostrove-2026", "(9b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Nì- kà'àn Maria kíxi kwé'e =ñá"
    glossedTokens := [("Nì-", "COMP-"), ("kà'àn", "say"), ("Maria", "Maria"), ("kíxi", "sleep:CONT"), ("kwé'e", "much"), ("=ñá", "=she")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "kà'àn"), ("clauseType", "finite"), ("diagnostic", "aspect"), ("aspect", "continuous")] }

def ex_9b_irrealis : Datum :=
  { id := "ostrove2026_9b_irrealis"
    source := ⟨"ostrove-2026", "(9b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Nì- kà'àn Maria kusi kwé'e =ñá"
    glossedTokens := [("Nì-", "COMP-"), ("kà'àn", "say"), ("Maria", "Maria"), ("kusi", "sleep:IRR"), ("kwé'e", "much"), ("=ñá", "=she")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "kà'àn"), ("clauseType", "finite"), ("diagnostic", "aspect"), ("aspect", "irrealis")] }

def ex_9c_completive : Datum :=
  { id := "ostrove2026_9c_completive"
    source := ⟨"ostrove-2026", "(9c)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kùsijǐ ini =rà nì- nì'ǐ =rà ña'á"
    glossedTokens := [("Kùsijǐ", "be.happy:COMP"), ("ini", "in"), ("=rà", "=he"), ("nì-", "COMP-"), ("nì'ǐ", "get"), ("=rà", "=he"), ("ña'á", "thing")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "kusijǐ ini"), ("clauseType", "finite"), ("diagnostic", "aspect"), ("aspect", "completive")] }

def ex_9c_continuous : Datum :=
  { id := "ostrove2026_9c_continuous"
    source := ⟨"ostrove-2026", "(9c)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kùsijǐ ini =rà nî'ǐ =rà ña'á"
    glossedTokens := [("Kùsijǐ", "be.happy:COMP"), ("ini", "in"), ("=rà", "=he"), ("nî'ǐ", "get:CONT"), ("=rà", "=he"), ("ña'á", "thing")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "kusijǐ ini"), ("clauseType", "finite"), ("diagnostic", "aspect"), ("aspect", "continuous")] }

def ex_9c_irrealis : Datum :=
  { id := "ostrove2026_9c_irrealis"
    source := ⟨"ostrove-2026", "(9c)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kùsijǐ ini =rà ni'ǐ =rà ña'á"
    glossedTokens := [("Kùsijǐ", "be.happy:COMP"), ("ini", "in"), ("=rà", "=he"), ("ni'ǐ", "get:IRR"), ("=rà", "=he"), ("ña'á", "thing")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "kusijǐ ini"), ("clauseType", "finite"), ("diagnostic", "aspect"), ("aspect", "irrealis")] }

def ex_13a_completive : Datum :=
  { id := "ostrove2026_13a_completive"
    source := ⟨"ostrove-2026", "(13a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntátu =rà xòná =rà ña'á"
    glossedTokens := [("Ntátu", "hope:CONT"), ("=rà", "=he"), ("xòná", "open:COMP"), ("=rà", "he"), ("ña'á", "thing")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ntatu"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "aspect"), ("aspect", "completive")] }

def ex_13a_continuous : Datum :=
  { id := "ostrove2026_13a_continuous"
    source := ⟨"ostrove-2026", "(13a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntátu =rà xóná =rà ña'á"
    glossedTokens := [("Ntátu", "hope:CONT"), ("=rà", "=he"), ("xóná", "open:CONT"), ("=rà", "he"), ("ña'á", "thing")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ntatu"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "aspect"), ("aspect", "continuous")] }

def ex_13a_irrealis : Datum :=
  { id := "ostrove2026_13a_irrealis"
    source := ⟨"ostrove-2026", "(13a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntátu =rà koná =rà ña'á"
    glossedTokens := [("Ntátu", "hope:CONT"), ("=rà", "=he"), ("koná", "open:IRR"), ("=rà", "he"), ("ña'á", "thing")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ntatu"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "aspect"), ("aspect", "irrealis")] }

def ex_13b_completive : Datum :=
  { id := "ostrove2026_13b_completive"
    source := ⟨"ostrove-2026", "(13b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kôni =ì xòná =ì mí yùye'e"
    glossedTokens := [("Kôni", "want:CONT"), ("=ì", "=I"), ("xòná", "open:COMP"), ("=ì", "=I"), ("mí", "the"), ("yùye'e", "door")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "kòni"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "aspect"), ("aspect", "completive")] }

def ex_13b_continuous : Datum :=
  { id := "ostrove2026_13b_continuous"
    source := ⟨"ostrove-2026", "(13b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kôni =ì xóxá =ì mí yùye'e"
    glossedTokens := [("Kôni", "want:CONT"), ("=ì", "=I"), ("xóxá", "open:CONT"), ("=ì", "=I"), ("mí", "the"), ("yùye'e", "door")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "kòni"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "aspect"), ("aspect", "continuous")] }

def ex_13b_irrealis : Datum :=
  { id := "ostrove2026_13b_irrealis"
    source := ⟨"ostrove-2026", "(13b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kôni =ì koná =ì mí yùye'e"
    glossedTokens := [("Kôni", "want:CONT"), ("=ì", "=I"), ("koná", "open:IRR"), ("=ì", "=I"), ("mí", "the"), ("yùye'e", "door")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "kòni"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "aspect"), ("aspect", "irrealis")] }

def ex_13c_completive : Datum :=
  { id := "ostrove2026_13c_completive"
    source := ⟨"ostrove-2026", "(13c)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntùkú Ana xìxi kwa'ǎ =ñá ntstika"
    glossedTokens := [("Ntùkú", "try:COMP"), ("Ana", "Ana"), ("xìxi", "eat:COMP"), ("kwa'ǎ", "more"), ("=ñá", "=she"), ("ntstika", "banana")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ntukú"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "aspect"), ("aspect", "completive")] }

def ex_13c_continuous : Datum :=
  { id := "ostrove2026_13c_continuous"
    source := ⟨"ostrove-2026", "(13c)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntùkú Ana xíxi kwa'ǎ =ñá ntstika"
    glossedTokens := [("Ntùkú", "try:COMP"), ("Ana", "Ana"), ("xíxi", "eat:CONT"), ("kwa'ǎ", "more"), ("=ñá", "=she"), ("ntstika", "banana")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ntukú"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "aspect"), ("aspect", "continuous")] }

def ex_13c_irrealis : Datum :=
  { id := "ostrove2026_13c_irrealis"
    source := ⟨"ostrove-2026", "(13c)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntùkú Ana kuxi kwa'ǎ =ñá ntstika"
    glossedTokens := [("Ntùkú", "try:COMP"), ("Ana", "Ana"), ("kuxi", "eat:IRR"), ("kwa'ǎ", "more"), ("=ñá", "=she"), ("ntstika", "banana")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ntukú"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "aspect"), ("aspect", "irrealis")] }

def ex_13d_completive : Datum :=
  { id := "ostrove2026_13d_completive"
    source := ⟨"ostrove-2026", "(13d)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Xíniñu'u =ì xì'i kwa'ǎ =ì tskwǐì"
    glossedTokens := [("Xíniñu'u", "need:COMP"), ("=ì", "=I"), ("xì'i", "drink:COMP"), ("kwa'ǎ", "more"), ("=ì", "=I"), ("tskwǐì", "water")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "xiniñu'u"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "aspect"), ("aspect", "completive")] }

def ex_13d_continuous : Datum :=
  { id := "ostrove2026_13d_continuous"
    source := ⟨"ostrove-2026", "(13d)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Xíniñu'u =ì xí'ì kwa'ǎ =ì tskwǐì"
    glossedTokens := [("Xíniñu'u", "need:COMP"), ("=ì", "=I"), ("xí'ì", "drink:CONT"), ("kwa'ǎ", "more"), ("=ì", "=I"), ("tskwǐì", "water")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "xiniñu'u"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "aspect"), ("aspect", "continuous")] }

def ex_13d_irrealis : Datum :=
  { id := "ostrove2026_13d_irrealis"
    source := ⟨"ostrove-2026", "(13d)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Xíniñu'u =ì ko'o kwa'ǎ =ì tskwǐì"
    glossedTokens := [("Xíniñu'u", "need:COMP"), ("=ì", "=I"), ("ko'o", "drink:IRR"), ("kwa'ǎ", "more"), ("=ì", "=I"), ("tskwǐì", "water")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "xiniñu'u"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "aspect"), ("aspect", "irrealis")] }

def ex_10a : Datum :=
  { id := "ostrove2026_10a"
    source := ⟨"ostrove-2026", "(10a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Bitsìn kâ'àn Maria xìin =ñá iin be'e xàa koni"
    glossedTokens := [("Bitsìn", "now"), ("kâ'àn", "say:CONT"), ("Maria", "Maria"), ("xìin", "buy:COMP"), ("=ñá", "=she"), ("iin", "one"), ("be'e", "house"), ("xàa", "new"), ("koni", "yesterday")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "kà'àn"), ("clauseType", "finite"), ("diagnostic", "tense")] }

def ex_10b : Datum :=
  { id := "ostrove2026_10b"
    source := ⟨"ostrove-2026", "(10b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Itsyààn ka'án Raúl xí'i kwé'e =rà bitsìn"
    glossedTokens := [("Itsyààn", "tomorrow"), ("ka'án", "think:IRR"), ("Raúl", "Raul"), ("xí'i", "drink:CONT"), ("kwé'e", "a.lot"), ("=rà", "=he"), ("bitsìn", "now")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ka'án"), ("clauseType", "finite"), ("diagnostic", "tense")] }

def ex_16a : Datum :=
  { id := "ostrove2026_16a"
    source := ⟨"ostrove-2026", "(16a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Bitsìn ntátu =ì kusi bà'a =ì itsyààn"
    glossedTokens := [("Bitsìn", "today"), ("ntátu", "hope:CONT"), ("=ì", "=I"), ("kusi", "sleep:IRR"), ("bà'a", "well"), ("=ì", "=I"), ("itsyààn", "tomorrow")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ntatu"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "tense")] }

def ex_16b : Datum :=
  { id := "ostrove2026_16b"
    source := ⟨"ostrove-2026", "(16b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Koni kò nì- kòni Maria ku'ún =ñá tienda bitsìn"
    glossedTokens := [("Koni", "yesterday"), ("kò", "NEG"), ("nì-", "COMP-"), ("kòni", "want"), ("Maria", "Maria"), ("ku'ún", "go:IRR"), ("=ñá", "=she"), ("tienda", "store"), ("bitsìn", "today")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "kòni"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "tense")] }

def ex_17a : Datum :=
  { id := "ostrove2026_17a"
    source := ⟨"ostrove-2026", "(17a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Bitsìn nákú'ún ini Maria ku'ún =ñá tienda itsyààn"
    glossedTokens := [("Bitsìn", "today"), ("nákú'ún", "remember:CONT"), ("ini", "in"), ("Maria", "Maria"), ("ku'ún", "go:IRR"), ("=ñá", "=she"), ("tienda", "market"), ("itsyààn", "tomorrow")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "nakú'ún ini"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "tense")] }

def ex_17b : Datum :=
  { id := "ostrove2026_17b"
    source := ⟨"ostrove-2026", "(17b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Koni ntùkú Juân ka'ani =rà iin ntsìbá'yi itsyààn"
    glossedTokens := [("Koni", "yesterday"), ("ntùkú", "try:COMP"), ("Juân", "Juan"), ("ka'ani", "kill:IRR"), ("=rà", "=he"), ("iin", "one"), ("ntsìbá'yi", "coyote"), ("itsyààn", "tomorrow")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ntukú"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "tense")] }

def ex_12a : Datum :=
  { id := "ostrove2026_12a"
    source := ⟨"ostrove-2026", "(12a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Káchi Raúl xí'in Pablo xìxi kwé'e =rà ndùchì koni"
    glossedTokens := [("Káchi", "say:COMP"), ("Raúl", "Raul"), ("xí'in", "with"), ("Pablo", "Pablo"), ("xìxi", "eat:COMP"), ("kwé'e", "many"), ("=rà", "=he"), ("ndùchì", "bean"), ("koni", "yesterday")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("controlled", .acceptable), ("free", .acceptable)]
    paperFeatures := [("verb", "káchi"), ("clauseType", "finite"), ("diagnostic", "subject")] }

def ex_12b : Datum :=
  { id := "ostrove2026_12b"
    source := ⟨"ostrove-2026", "(12b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kúsijǐ ini Eva kèba'a =ñá carrera"
    glossedTokens := [("Kúsijǐ", "be.happy:CONT"), ("ini", "in"), ("Eva", "Eva"), ("kèba'a", "win:COMP"), ("=ñá", "=she"), ("carrera", "race")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("controlled", .acceptable), ("free", .acceptable)]
    paperFeatures := [("verb", "kusijǐ ini"), ("clauseType", "finite"), ("diagnostic", "subject")] }

def ex_18a : Datum :=
  { id := "ostrove2026_18a"
    source := ⟨"ostrove-2026", "(18a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kôni Maria kusi =ñá"
    glossedTokens := [("Kôni", "want:CONT"), ("Maria", "Maria"), ("kusi", "sleep:IRR"), ("=ñá", "=she")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("controlled", .acceptable), ("free", .unacceptable)]
    paperFeatures := [("verb", "kòni"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "subject")] }

def ex_18b : Datum :=
  { id := "ostrove2026_18b"
    source := ⟨"ostrove-2026", "(18b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kôni Maria ná kusi =ñá"
    glossedTokens := [("Kôni", "want:CONT"), ("Maria", "Maria"), ("ná", "NÁ"), ("kusi", "sleep:IRR"), ("=ñá", "=she")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("controlled", .unacceptable), ("free", .acceptable)]
    paperFeatures := [("verb", "kòni"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "subject")] }

def ex_18c : Datum :=
  { id := "ostrove2026_18c"
    source := ⟨"ostrove-2026", "(18c)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kôni Maria kusi =rí"
    glossedTokens := [("Kôni", "want:CONT"), ("Maria", "Maria"), ("kusi", "sleep:IRR"), ("=rí", "=it.AML")]
    context := ""
    judgment := .acceptable
    alternatives := [("Kôni Maria ná kusi =rí", .acceptable)]
    readings := [("free", .acceptable)]
    paperFeatures := [("verb", "kòni"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "subject")] }

def ex_18d : Datum :=
  { id := "ostrove2026_18d"
    source := ⟨"ostrove-2026", "(18d)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kôni Maria kusi lěe =ñá"
    glossedTokens := [("Kôni", "want:CONT"), ("Maria", "Maria"), ("kusi", "sleep:IRR"), ("lěe", "baby"), ("=ñá", "=her")]
    context := ""
    judgment := .acceptable
    alternatives := [("Kôni Maria ná kusi lěe =ñá", .acceptable)]
    readings := [("free", .acceptable)]
    paperFeatures := [("verb", "kòni"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "subject"), ("embeddedSubject", "lexical")] }

def ex_19a : Datum :=
  { id := "ostrove2026_19a"
    source := ⟨"ostrove-2026", "(19a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntùkú Maria ku'un =rà tienda"
    glossedTokens := [("Ntùkú", "try:COMP"), ("Maria", "Maria"), ("ku'un", "go:IRR"), ("=rà", "=he"), ("tienda", "store")]
    context := ""
    judgment := .ungrammatical
    alternatives := [("Ntùkú Maria ná ku'un =rà tienda", .ungrammatical), ("Ntùkú Maria ná ku'un =ñá tienda", .ungrammatical)]
    readings := [("free", .ungrammatical)]
    paperFeatures := [("verb", "ntukú"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "subject")] }

def ex_19b : Datum :=
  { id := "ostrove2026_19b"
    source := ⟨"ostrove-2026", "(19b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Nàkú'ún ini Maria kata bà'a =rà"
    glossedTokens := [("Nàkú'ún", "remember:CONT"), ("ini", "in"), ("Maria", "Maria"), ("kata", "sing:IRR"), ("bà'a", "well"), ("=rà", "=he")]
    context := ""
    judgment := .ungrammatical
    alternatives := [("Nàkú'ún ini Maria ná kata bà'a =rà", .ungrammatical), ("Nàkú'ún ini Maria ná kata bà'a =ñá", .ungrammatical)]
    readings := [("free", .ungrammatical)]
    paperFeatures := [("verb", "nakú'ún ini"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "subject")] }

def ex_40a : Datum :=
  { id := "ostrove2026_40a"
    source := ⟨"ostrove-2026", "(40a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Xíniñu'u Maria kwiin =rà iin koto xàá"
    glossedTokens := [("Xíniñu'u", "need:CONT"), ("Maria", "Maria"), ("kwiin", "buy:IRR"), ("=rà", "=he"), ("iin", "one"), ("koto", "shirt"), ("xàá", "new")]
    context := ""
    judgment := .ungrammatical
    alternatives := [("Xíniñu'u Maria ná kwiin =rà iin koto xàá", .ungrammatical), ("Xíniñu'u Maria ná kwiin =ñá iin koto xàá", .ungrammatical)]
    readings := [("free", .ungrammatical)]
    paperFeatures := [("verb", "xiniñu'u"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "subject")] }

def ex_40b : Datum :=
  { id := "ostrove2026_40b"
    source := ⟨"ostrove-2026", "(40b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kìxǎ Maria kata bà'a =rà"
    glossedTokens := [("Kìxǎ", "start:CONT"), ("Maria", "Maria"), ("kata", "sing:IRR"), ("bà'a", "well"), ("=rà", "=he")]
    context := ""
    judgment := .ungrammatical
    alternatives := [("Kìxǎ Maria ná kata bà'a =rà", .ungrammatical), ("Kìxǎ Maria ná kata bà'a =ñá", .ungrammatical)]
    readings := [("free", .ungrammatical)]
    paperFeatures := [("verb", "kixǎ"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "subject")] }

def ex_41a : Datum :=
  { id := "ostrove2026_41a"
    source := ⟨"ostrove-2026", "(41a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntátu Maria bà'a ná kusi ìjǐ =ñá"
    glossedTokens := [("Ntátu", "hope:CONT"), ("Maria", "Maria"), ("bà'a", "well"), ("ná", "NÁ"), ("kusi", "sleep:IRR"), ("ìjǐ", "husband"), ("=ñá", "=her")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("free", .acceptable)]
    paperFeatures := [("verb", "ntatu"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "subject"), ("embeddedSubject", "lexical")] }

def ex_41b : Datum :=
  { id := "ostrove2026_41b"
    source := ⟨"ostrove-2026", "(41b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Xíniñu'u Maria kwiin Juân iin koto xàá"
    glossedTokens := [("Xíniñu'u", "need:CONT"), ("Maria", "Maria"), ("kwiin", "buy:IRR"), ("Juân", "Juan"), ("iin", "one"), ("koto", "shirt"), ("xàá", "new")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := [("free", .ungrammatical)]
    paperFeatures := [("verb", "xiniñu'u"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "subject"), ("embeddedSubject", "lexical")] }

def ex_20a : Datum :=
  { id := "ostrove2026_20a"
    source := ⟨"ostrove-2026", "(20a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kwa'ǎ carro ndàtǔ'un Maria nàkatsya Pedro"
    glossedTokens := [("Kwa'ǎ", "many"), ("carro", "car"), ("ndàtǔ'un", "talk:COMP"), ("Maria", "Maria"), ("nàkatsya", "wash:COMP"), ("Pedro", "Pedro")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ntatǔ'un"), ("clauseType", "finite"), ("diagnostic", "fronting"), ("fronting", "out")] }

def ex_20b : Datum :=
  { id := "ostrove2026_20b"
    source := ⟨"ostrove-2026", "(20b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ni'iin =nà ká'á =rà doctor kò kú'u"
    glossedTokens := [("Ni'iin", "no"), ("=nà", "=they"), ("ká'á", "think:CONT"), ("=rà", "=he"), ("doctor", "doctor"), ("kò", "NEG"), ("kú'u", "be.sick:CONT")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ka'án"), ("clauseType", "finite"), ("diagnostic", "fronting"), ("fronting", "out")] }

def ex_21a : Datum :=
  { id := "ostrove2026_21a"
    source := ⟨"ostrove-2026", "(21a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Káchi Maria kòjmǐ xìta xìxi =ñá"
    glossedTokens := [("Káchi", "say:COMP"), ("Maria", "Maria"), ("kòjmǐ", "four"), ("xìta", "tortilla"), ("xìxi", "eat:COMP"), ("=ñá", "=she")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "káchi"), ("clauseType", "finite"), ("diagnostic", "fronting"), ("fronting", "within")] }

def ex_21b : Datum :=
  { id := "ostrove2026_21b"
    source := ⟨"ostrove-2026", "(21b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kúntàà ini =ì ntsikû mí tsǐnà ntá'yi"
    glossedTokens := [("Kúntàà", "believe:CONT"), ("ini", "in"), ("=ì", "=I"), ("ntsikû", "all"), ("mí", "the"), ("tsǐnà", "dog"), ("ntá'yi", "cry:CONT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "kuntàà ini"), ("clauseType", "finite"), ("diagnostic", "fronting"), ("fronting", "within")] }

def ex_22a : Datum :=
  { id := "ostrove2026_22a"
    source := ⟨"ostrove-2026", "(22a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntsi'i carro ntátu Pedro nakatsya =rà"
    glossedTokens := [("Ntsi'i", "every"), ("carro", "car"), ("ntátu", "hope:CONT"), ("Pedro", "Pedro"), ("nakatsya", "wash:IRR"), ("=rà", "=he")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ntatu"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "fronting"), ("fronting", "out")] }

def ex_22b : Datum :=
  { id := "ostrove2026_22b"
    source := ⟨"ostrove-2026", "(22b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kwa'ǎ yà'a í'ní chìkàà ini Juân kaxi =rà"
    glossedTokens := [("Kwa'ǎ", "many"), ("yà'a", "chili"), ("í'ní", "hot"), ("chìkàà", "put.in:COMP"), ("ini", "in"), ("Juân", "Juan"), ("kaxi", "eat:IRR"), ("=rà", "=he")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "chikàà ini"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "fronting"), ("fronting", "out")] }

def ex_23a : Datum :=
  { id := "ostrove2026_23a"
    source := ⟨"ostrove-2026", "(23a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntátu =rà lo'o ntsi'i ña'á koná =rà"
    glossedTokens := [("Ntátu", "hope:CONT"), ("=rà", "=he"), ("lo'o", "little"), ("ntsi'i", "every"), ("ña'á", "thing"), ("koná", "open:IRR"), ("=rà", "=he")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ntatu"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "fronting"), ("fronting", "within")] }

def ex_23b : Datum :=
  { id := "ostrove2026_23b"
    source := ⟨"ostrove-2026", "(23b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Chìkàà ini Juân kwa'ǎ yà'ǎ í'ní kaxi =rà"
    glossedTokens := [("Chìkàà", "put.in:COMP"), ("ini", "in"), ("Juân", "Juan"), ("kwa'ǎ", "many"), ("yà'ǎ", "chili"), ("í'ní", "hot"), ("kaxi", "eat:IRR"), ("=rà", "=he")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "chikàà ini"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "fronting"), ("fronting", "within")] }

def ex_24a : Datum :=
  { id := "ostrove2026_24a"
    source := ⟨"ostrove-2026", "(24a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kwa'ǎ ko'ǒ nàntǒso Mateo nakatsya =rà"
    glossedTokens := [("Kwa'ǎ", "many"), ("ko'ǒ", "plate"), ("nàntǒso", "forget:COMP"), ("Mateo", "Mateo"), ("nakatsya", "wash:IRR"), ("=rà", "=he")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "nantǒso"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "fronting"), ("fronting", "out")] }

def ex_24b : Datum :=
  { id := "ostrove2026_24b"
    source := ⟨"ostrove-2026", "(24b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kòjmǐ yà'ǎ ntùkú Maria kaxi =ñá"
    glossedTokens := [("Kòjmǐ", "four"), ("yà'ǎ", "chili"), ("ntùkú", "try:COMP"), ("Maria", "Maria"), ("kaxi", "eat:IRR"), ("=ñá", "=she")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ntukú"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "fronting"), ("fronting", "out")] }

def ex_25a : Datum :=
  { id := "ostrove2026_25a"
    source := ⟨"ostrove-2026", "(25a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Nàntǒso Mateo kwa'ǎ ko'ǒ nakatsya =rà"
    glossedTokens := [("Nàntǒso", "forget:COMP"), ("Mateo", "Mateo"), ("kwa'ǎ", "many"), ("ko'ǒ", "plate"), ("nakatsya", "wash:IRR"), ("=rà", "=he")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "nantǒso"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "fronting"), ("fronting", "within")] }

def ex_25b : Datum :=
  { id := "ostrove2026_25b"
    source := ⟨"ostrove-2026", "(25b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntùkú Maria kòjmǐ yà'ǎ kaxi =ñá"
    glossedTokens := [("Ntùkú", "try:COMP"), ("Maria", "Maria"), ("kòjmǐ", "four"), ("yà'ǎ", "chili"), ("kaxi", "eat:IRR"), ("=ñá", "=she")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ntukú"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "fronting"), ("fronting", "within")] }

def ex_109 : Datum :=
  { id := "ostrove2026_109"
    source := ⟨"ostrove-2026", "(109)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Iin dragón kôni =rà tsyàja ka'ani =rà"
    glossedTokens := [("Iin", "one"), ("dragón", "dragon"), ("kôni", "want:CONT"), ("=rà", "=he"), ("tsyàja", "man"), ("ka'ani", "kill:IRR"), ("=rà", "=he")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "kòni"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "fronting"), ("fronting", "out")] }

def ex_30a : Datum :=
  { id := "ostrove2026_30a"
    source := ⟨"ostrove-2026", "(30a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Káchi Julia bà'a kwé'e xìjnǐ =ñá, sǎ =ti Mateo =ba"
    glossedTokens := [("Káchi", "say:COMP"), ("Julia", "Julia"), ("bà'a", "good"), ("kwé'e", "very"), ("xìjnǐ", "head"), ("=ñá", "=she"), ("sǎ", "so"), ("=ti", "=too"), ("Mateo", "Mateo"), ("=ba", "=EMPH")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("sloppy", .acceptable), ("strict", .acceptable)]
    paperFeatures := [("verb", "káchi"), ("clauseType", "finite"), ("diagnostic", "ellipsis")] }

def ex_30b : Datum :=
  { id := "ostrove2026_30b"
    source := ⟨"ostrove-2026", "(30b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kà'án Juan ni'í xìnu =rà, sǎ =ti Sergio =ba"
    glossedTokens := [("Kà'án", "think:COMP"), ("Juan", "Juan"), ("ni'í", "fast"), ("xìnu", "run:COMP"), ("=rà", "=he"), ("sǎ", "so"), ("=ti", "=too"), ("Sergio", "Sergio"), ("=ba", "=EMPH")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("sloppy", .acceptable), ("strict", .acceptable)]
    paperFeatures := [("verb", "ka'án"), ("clauseType", "finite"), ("diagnostic", "ellipsis")] }

def ex_32a : Datum :=
  { id := "ostrove2026_32a"
    source := ⟨"ostrove-2026", "(32a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kôni Marco keba'a =rà carrera, sǎ =ti Maria =ba"
    glossedTokens := [("Kôni", "want:CONT"), ("Marco", "Marco"), ("keba'a", "win:IRR"), ("=rà", "=he"), ("carrera", "race"), ("sǎ", "so"), ("=ti", "=too"), ("Maria", "Maria"), ("=ba", "=EMPH")]
    context := "Maria is not in the race, but she wants Marco to win."
    judgment := .acceptable
    alternatives := []
    readings := [("sloppy", .acceptable), ("strict", .acceptable)]
    paperFeatures := [("verb", "kòni"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "ellipsis")] }

def ex_32b : Datum :=
  { id := "ostrove2026_32b"
    source := ⟨"ostrove-2026", "(32b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntátu Raúl ku'ún =rà Olímpico, sǎ =ti nána =rà =ba"
    glossedTokens := [("Ntátu", "hope:CONT"), ("Raúl", "Raul"), ("ku'ún", "go:IRR"), ("=rà", "=he"), ("Olímpico", "Olympics"), ("sǎ", "so"), ("=ti", "=too"), ("nána", "mother"), ("=rà", "=his"), ("=ba", "=EMPH")]
    context := "Raul's mother is not an athlete, but she hopes her son will go to the Olympics."
    judgment := .acceptable
    alternatives := []
    readings := [("sloppy", .acceptable), ("strict", .acceptable)]
    paperFeatures := [("verb", "ntatu"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "ellipsis")] }

def ex_33a : Datum :=
  { id := "ostrove2026_33a"
    source := ⟨"ostrove-2026", "(33a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Xînì Ana ixutsya =ñá, sǎ =ti Laura =ba"
    glossedTokens := [("Xînì", "know:CONT"), ("Ana", "Ana"), ("ixutsya", "swim:IRR"), ("=ñá", "=she"), ("sǎ", "so"), ("=ti", "=too"), ("Laura", "Laura"), ("=ba", "=EMPH")]
    context := "Laura cannot swim, but she knows that Ana can."
    judgment := .acceptable
    alternatives := []
    readings := [("sloppy", .acceptable), ("strict", .unacceptable)]
    paperFeatures := [("verb", "kònì"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "ellipsis")] }

def ex_33b : Datum :=
  { id := "ostrove2026_33b"
    source := ⟨"ostrove-2026", "(33b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Nàkú'ún ini Maria ku'ún =ñá tienda, sǎ =ti Juân =ba"
    glossedTokens := [("Nàkú'ún", "remember:COMP"), ("ini", "in"), ("Maria", "Maria"), ("ku'ún", "go:IRR"), ("=ñá", "=she"), ("tienda", "store"), ("sǎ", "so"), ("=ti", "=too"), ("Juân", "Juan"), ("=ba", "=EMPH")]
    context := "Juan did not go to the store, but he remembers Maria did."
    judgment := .acceptable
    alternatives := []
    readings := [("sloppy", .acceptable), ("strict", .unacceptable)]
    paperFeatures := [("verb", "nakú'ún ini"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "ellipsis")] }

def ex_37a : Datum :=
  { id := "ostrove2026_37a"
    source := ⟨"ostrove-2026", "(37a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Nàntǒso =rà patrón nakitá'àn =nà kâ uxi iin"
    glossedTokens := [("Nàntǒso", "forget:COMP"), ("=rà", "=he"), ("patrón", "boss"), ("nakitá'àn", "meet:IRR"), ("=nà", "=they"), ("kâ", "hour"), ("uxi", "ten"), ("iin", "one")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "nantǒso"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "partialControl")] }

def ex_37b : Datum :=
  { id := "ostrove2026_37b"
    source := ⟨"ostrove-2026", "(37b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Xíniñu'u Maria ku'ún ntíbi =nà bìjkǒ"
    glossedTokens := [("Xíniñu'u", "need:CONT"), ("Maria", "Maria"), ("ku'ún", "go:IRR"), ("ntíbi", "together"), ("=nà", "=they"), ("bìjkǒ", "party")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "xiniñu'u"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "partialControl")] }

def ex_43a : Datum :=
  { id := "ostrove2026_43a"
    source := ⟨"ostrove-2026", "(43a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kôni nána Julio ná keba'a =rà mí carrera"
    glossedTokens := [("Kôni", "want:CONT"), ("nána", "mother"), ("Julio", "Julio"), ("ná", "NÁ"), ("keba'a", "win:IRR"), ("=rà", "=he"), ("mí", "the"), ("carrera", "race")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "kòni"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "cCommand"), ("antecedent", "nonCCommanding")] }

def ex_43b : Datum :=
  { id := "ostrove2026_43b"
    source := ⟨"ostrove-2026", "(43b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntátu amiga ña'à Marco ná ku'u =rà mí Olimpico"
    glossedTokens := [("Ntátu", "hope:CONT"), ("amiga", "friend.FEM"), ("ña'à", "POSS"), ("Marco", "Marco"), ("ná", "NÁ"), ("ku'u", "go:IRR"), ("=rà", "=he"), ("mí", "the"), ("Olimpico", "Olympics")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ntatu"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "cCommand"), ("antecedent", "nonCCommanding")] }

def ex_44a : Datum :=
  { id := "ostrove2026_44a"
    source := ⟨"ostrove-2026", "(44a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Nàntǒso táta Maria ku'un =ñá tienda"
    glossedTokens := [("Nàntǒso", "forget:COMP"), ("táta", "father"), ("Maria", "Maria"), ("ku'un", "go:IRR"), ("=ñá", "=she"), ("tienda", "store")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "nantǒso"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "cCommand"), ("antecedent", "nonCCommanding")] }

def ex_44b : Datum :=
  { id := "ostrove2026_44b"
    source := ⟨"ostrove-2026", "(44b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Xíniñu'u nána Julio kwiin =rà iin koto xàá"
    glossedTokens := [("Xíniñu'u", "need:CONT"), ("nána", "mother"), ("Julio", "Julio"), ("kwiin", "buy:IRR"), ("=rà", "=he"), ("iin", "one"), ("koto", "shirt"), ("xàá", "new")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "xiniñu'u"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "cCommand"), ("antecedent", "nonCCommanding")] }

def ex_45a : Datum :=
  { id := "ostrove2026_45a"
    source := ⟨"ostrove-2026", "(45a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Bìjkǒ ña'à Marco xìndatu Ana kaxi =rà yù'u =ñá"
    glossedTokens := [("Bìjkǒ", "party"), ("ña'à", "POSS"), ("Marco", "Marco"), ("xìndatu", "hope:IMP:COMP"), ("Ana", "Ana"), ("kaxi", "eat:IRR"), ("=rà", "=he"), ("yù'u", "mouth"), ("=ñá", "=her")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ntatu"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "cCommand"), ("antecedent", "nonCCommanding")] }

def ex_45b : Datum :=
  { id := "ostrove2026_45b"
    source := ⟨"ostrove-2026", "(45b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Bìjkǒ ña'à Marco kòni Ana kaxi =rà yù'u =ñá"
    glossedTokens := [("Bìjkǒ", "party"), ("ña'à", "POSS"), ("Marco", "Marco"), ("kòni", "want:COMP"), ("Ana", "Ana"), ("kaxi", "eat:IRR"), ("=rà", "=he"), ("yù'u", "mouth"), ("=ñá", "=her")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "kòni"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "cCommand"), ("antecedent", "nonCCommanding")] }

def ex_46a : Datum :=
  { id := "ostrove2026_46a"
    source := ⟨"ostrove-2026", "(46a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Bìjkǒ ña'à Marco xìniñu'u Ana kaxi =rà yù'u =ñá"
    glossedTokens := [("Bìjkǒ", "party"), ("ña'à", "POSS"), ("Marco", "Marco"), ("xìniñu'u", "need:COMP"), ("Ana", "Ana"), ("kaxi", "eat:IRR"), ("=rà", "=he"), ("yù'u", "mouth"), ("=ñá", "=her")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "xiniñu'u"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "cCommand"), ("antecedent", "nonCCommanding")] }

def ex_46b : Datum :=
  { id := "ostrove2026_46b"
    source := ⟨"ostrove-2026", "(46b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Bìjkǒ ña'à Marco ntùkú Ana kaxi =rà yù'u =ñá"
    glossedTokens := [("Bìjkǒ", "party"), ("ña'à", "POSS"), ("Marco", "Marco"), ("ntùkú", "try:COMP"), ("Ana", "Ana"), ("kaxi", "eat:IRR"), ("=rà", "=he"), ("yù'u", "mouth"), ("=ñá", "=her")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ntukú"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "cCommand"), ("antecedent", "nonCCommanding")] }

def ex_67a : Datum :=
  { id := "ostrove2026_67a"
    source := ⟨"ostrove-2026", "(67a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Saá nántǒso =ndó koná ndó'ó yùye'e"
    glossedTokens := [("Saá", "always"), ("nántǒso", "forget:CONT"), ("=ndó", "=you.PL"), ("koná", "open:IRR"), ("ndó'ó", "you"), ("yùye'e", "door")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "nantǒso"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "clitic"), ("embeddedSubject", "nonclitic")] }

def ex_67b : Datum :=
  { id := "ostrove2026_67b"
    source := ⟨"ostrove-2026", "(67b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Xíni Marco ixutsya mí =rà"
    glossedTokens := [("Xíni", "know:CONT"), ("Marco", "Marco"), ("ixutsya", "swim:IRR"), ("mí", "the"), ("=rà", "=he")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "kònì"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "clitic"), ("embeddedSubject", "nonclitic")] }

def ex_67c : Datum :=
  { id := "ostrove2026_67c"
    source := ⟨"ostrove-2026", "(67c)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kìxǎ mí leso taxá'á rí kani"
    glossedTokens := [("Kìxǎ", "start:COMP"), ("mí", "the"), ("leso", "rabbit"), ("taxá'á", "dance:IRR"), ("rí", "it.AML"), ("kani", "there")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "kixǎ"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "clitic"), ("embeddedSubject", "nonclitic")] }

def ex_68a : Datum :=
  { id := "ostrove2026_68a"
    source := ⟨"ostrove-2026", "(68a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kôni Jûan keba'a mí =rà carrera"
    glossedTokens := [("Kôni", "want:CONT"), ("Jûan", "Juan"), ("keba'a", "win:IRR"), ("mí", "the"), ("=rà", "=he"), ("carrera", "race")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "kòni"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "clitic"), ("embeddedSubject", "nonclitic")] }

def ex_68b : Datum :=
  { id := "ostrove2026_68b"
    source := ⟨"ostrove-2026", "(68b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ntátu Maria ku'ún mí =ñá yòjo"
    glossedTokens := [("Ntátu", "hope:CONT"), ("Maria", "Maria"), ("ku'ún", "go:IRR"), ("mí", "the"), ("=ñá", "=she"), ("yòjo", "moon")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "ntatu"), ("clauseType", "tensedSubjunctive"), ("diagnostic", "clitic"), ("embeddedSubject", "nonclitic")] }

def ex_75a : Datum :=
  { id := "ostrove2026_75a"
    source := ⟨"ostrove-2026", "(75a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Tá'iin'iin tsǐnà tsìi ndò'ò mí =rí"
    glossedTokens := [("Tá'iin'iin", "each"), ("tsǐnà", "dog"), ("tsìi", "bite:COMP"), ("ndò'ò", "tail"), ("mí", "the"), ("=rí", "=its")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "exemptAnaphor"), ("antecedent", "quantified")] }

def ex_75b : Datum :=
  { id := "ostrove2026_75b"
    source := ⟨"ostrove-2026", "(75b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ni'iin =ná bálí nǐ- xini táta mí =ná"
    glossedTokens := [("Ni'iin", "no"), ("=ná", "=they.FEM"), ("bálí", "little.PL"), ("nǐ-", "COMP.NEG"), ("xini", "see"), ("táta", "father"), ("mí", "the"), ("=ná", "=their.FEM")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "exemptAnaphor"), ("antecedent", "quantified")] }

def ex_86a : Datum :=
  { id := "ostrove2026_86a"
    source := ⟨"ostrove-2026", "(86a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Tá'iin'iin tsǐnà kìxǎ tsii =rí ndò'ò mí =rí"
    glossedTokens := [("Tá'iin'iin", "each"), ("tsǐnà", "dog"), ("kìxǎ", "start:COMP"), ("tsii", "bite:IRR"), ("=rí", "=it.AML"), ("ndò'ò", "tail"), ("mí", "the"), ("=rí", "=its.AML")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "kixǎ"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "exemptAnaphor"), ("antecedent", "quantified")] }

def ex_86b : Datum :=
  { id := "ostrove2026_86b"
    source := ⟨"ostrove-2026", "(86b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Ni'iin =rà bálí kò xíniñu'u kònì =rà táta mí =rà"
    glossedTokens := [("Ni'iin", "no"), ("=rà", "=he"), ("bálí", "little.PL"), ("kò", "NEG"), ("xíniñu'u", "need:CONT"), ("kònì", "see:IRR"), ("=rà", "=he"), ("táta", "father"), ("mí", "the"), ("=rà", "=his")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "xiniñu'u"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "exemptAnaphor"), ("antecedent", "quantified")] }

def ex_87a : Datum :=
  { id := "ostrove2026_87a"
    source := ⟨"ostrove-2026", "(87a)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kìxǎ iin tsǐnà tsii =rí ndò'ò mí =rí"
    glossedTokens := [("Kìxǎ", "start:COMP"), ("iin", "one"), ("tsǐnà", "dog"), ("tsii", "bite:IRR"), ("=rí", "=it.AML"), ("ndò'ò", "tail"), ("mí", "the"), ("=rí", "=its.AML")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "kixǎ"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "exemptAnaphor"), ("antecedent", "quantified")] }

def ex_87b : Datum :=
  { id := "ostrove2026_87b"
    source := ⟨"ostrove-2026", "(87b)"⟩
    reportedIn := none
    language := "sanm1291"
    primaryText := "Kò xíniñu'u ni'iin =rà bálí kònì =rà táta mí =rà"
    glossedTokens := [("Kò", "NEG"), ("xíniñu'u", "need:CONT"), ("ni'iin", "no"), ("=rà", "=he"), ("bálí", "little.PL"), ("kònì", "see:IRR"), ("=rà", "=he"), ("táta", "father"), ("mí", "the"), ("=rà", "=his")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "xiniñu'u"), ("clauseType", "untensedSubjunctive"), ("diagnostic", "exemptAnaphor"), ("antecedent", "quantified")] }

def all : List Datum := [ex_9a_completive, ex_9a_continuous, ex_9a_irrealis, ex_9b_completive, ex_9b_continuous, ex_9b_irrealis, ex_9c_completive, ex_9c_continuous, ex_9c_irrealis, ex_13a_completive, ex_13a_continuous, ex_13a_irrealis, ex_13b_completive, ex_13b_continuous, ex_13b_irrealis, ex_13c_completive, ex_13c_continuous, ex_13c_irrealis, ex_13d_completive, ex_13d_continuous, ex_13d_irrealis, ex_10a, ex_10b, ex_16a, ex_16b, ex_17a, ex_17b, ex_12a, ex_12b, ex_18a, ex_18b, ex_18c, ex_18d, ex_19a, ex_19b, ex_40a, ex_40b, ex_41a, ex_41b, ex_20a, ex_20b, ex_21a, ex_21b, ex_22a, ex_22b, ex_23a, ex_23b, ex_24a, ex_24b, ex_25a, ex_25b, ex_109, ex_30a, ex_30b, ex_32a, ex_32b, ex_33a, ex_33b, ex_37a, ex_37b, ex_43a, ex_43b, ex_44a, ex_44b, ex_45a, ex_45b, ex_46a, ex_46b, ex_67a, ex_67b, ex_67c, ex_68a, ex_68b, ex_75a, ex_75b, ex_86a, ex_86b, ex_87a, ex_87b]

end Ostrove2026.Examples
