module

public import Linglib.Data.Examples.Schema

/-!
# `Wood2023` — typed example data

Auto-generated from `Linglib/Data/Examples/Wood2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Wood2023.Examples`.
-/

@[expose] public section

namespace Wood2023.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "wood2023_1"
    source := ⟨"wood-2023", "(6.37)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Guðrún þvoði fötin."
    glossedTokens := [("Guðrún", "Guðrún.NOM"), ("þvoði", "washed"), ("fötin", "clothes.the.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "þvo")] }

def ex_2 : LinguisticExample :=
  { id := "wood2023_2"
    source := ⟨"wood-2023", "(6.37a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "þvo-ttur Guðrúnar á fötunum"
    glossedTokens := [("þvo-ttur", "wash-NMLZ"), ("Guðrúnar", "Guðrún.GEN"), ("á", "on"), ("fötunum", "clothes.the.DAT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("complex event", .acceptable)]
    paperFeatures := [("reading", "CEN")] }

def ex_3 : LinguisticExample :=
  { id := "wood2023_3"
    source := ⟨"wood-2023", "(6.37c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þvo-ttur-inn tók langan tíma."
    glossedTokens := [("Þvo-ttur-inn", "wash-NMLZ-the"), ("tók", "took"), ("langan", "long"), ("tíma", "time")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simple event", .acceptable)]
    paperFeatures := [("reading", "SEN")] }

def ex_4 : LinguisticExample :=
  { id := "wood2023_4"
    source := ⟨"wood-2023", "(6.37d)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þvo-ttur-inn á að fara í vélina."
    glossedTokens := [("Þvo-ttur-inn", "wash-NMLZ-the"), ("á", "ought"), ("að", "to"), ("fara", "go"), ("í", "in"), ("vélina", "machine.the.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simple entity", .acceptable)]
    paperFeatures := [("reading", "RN")] }

def ex_5 : LinguisticExample :=
  { id := "wood2023_5"
    source := ⟨"wood-2023", "(6.38)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Guðrún marg-þvoði fötin."
    glossedTokens := [("Guðrún", "Guðrún.NOM"), ("marg-þvoði", "many-washed"), ("fötin", "clothes.the.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("prefix", "marg-")] }

def ex_6 : LinguisticExample :=
  { id := "wood2023_6"
    source := ⟨"wood-2023", "(6.38a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "marg-þvo-ttur Guðrúnar á fötunum"
    glossedTokens := [("marg-þvo-ttur", "many-wash-NMLZ"), ("Guðrúnar", "Guðrún.GEN"), ("á", "on"), ("fötunum", "clothes.the.DAT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("complex event", .acceptable)]
    paperFeatures := [("prefix", "marg-"), ("reading", "CEN")] }

def ex_7 : LinguisticExample :=
  { id := "wood2023_7"
    source := ⟨"wood-2023", "(6.38c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "marg-þvo-ttur fatanna"
    glossedTokens := [("marg-þvo-ttur", "many-wash-NMLZ"), ("fatanna", "clothes.the.GEN")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("complex event", .acceptable)]
    paperFeatures := [("prefix", "marg-"), ("reading", "CEN")] }

def ex_8 : LinguisticExample :=
  { id := "wood2023_8"
    source := ⟨"wood-2023", "(6.38d)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Marg-þvo-ttur-inn tók langan tíma."
    glossedTokens := [("Marg-þvo-ttur-inn", "many-wash-NMLZ-the"), ("tók", "took"), ("langan", "long"), ("tíma", "time")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := [("simple event", .ungrammatical)]
    paperFeatures := [("prefix", "marg-"), ("reading", "SEN")] }

def ex_9 : LinguisticExample :=
  { id := "wood2023_9"
    source := ⟨"wood-2023", "(6.38e)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Marg-þvo-ttur-inn á að fara í vélina."
    glossedTokens := [("Marg-þvo-ttur-inn", "many-wash-NMLZ-the"), ("á", "ought"), ("að", "to"), ("fara", "go"), ("í", "in"), ("vélina", "machine.the.ACC")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := [("simple entity", .ungrammatical)]
    paperFeatures := [("prefix", "marg-"), ("reading", "RN")] }

def ex_10 : LinguisticExample :=
  { id := "wood2023_10"
    source := ⟨"wood-2023", "(6.46)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ég endur-þvoði fötin."
    glossedTokens := [("Ég", "I.NOM"), ("endur-þvoði", "re-washed"), ("fötin", "clothes.the.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("prefix", "endur-")] }

def ex_11 : LinguisticExample :=
  { id := "wood2023_11"
    source := ⟨"wood-2023", "(6.46a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "endur-þvo-ttur Guðrúnar á fötunum"
    glossedTokens := [("endur-þvo-ttur", "re-wash-NMLZ"), ("Guðrúnar", "Guðrún.GEN"), ("á", "on"), ("fötunum", "clothes.the.DAT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("complex event", .acceptable)]
    paperFeatures := [("prefix", "endur-"), ("reading", "CEN")] }

def ex_12 : LinguisticExample :=
  { id := "wood2023_12"
    source := ⟨"wood-2023", "(6.46c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Endur-þvo-ttur-inn tók langan tíma."
    glossedTokens := [("Endur-þvo-ttur-inn", "re-wash-NMLZ-the"), ("tók", "took"), ("langan", "long"), ("tíma", "time")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simple event", .acceptable)]
    paperFeatures := [("prefix", "endur-"), ("reading", "SEN")] }

def ex_13 : LinguisticExample :=
  { id := "wood2023_13"
    source := ⟨"wood-2023", "(6.46d)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Endur-þvo-ttur-inn á að fara í vélina."
    glossedTokens := [("Endur-þvo-ttur-inn", "re-wash-NMLZ-the"), ("á", "ought"), ("að", "to"), ("fara", "go"), ("í", "in"), ("vélina", "machine.the.ACC")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := [("simple entity", .ungrammatical)]
    paperFeatures := [("prefix", "endur-"), ("reading", "RN")] }

def ex_14 : LinguisticExample :=
  { id := "wood2023_14"
    source := ⟨"wood-2023", "(6.52)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ég vona að hún týni ekki endur-prent-un-inni."
    glossedTokens := [("Ég", "I"), ("vona", "hope"), ("að", "that"), ("hún", "she"), ("týni", "loses"), ("ekki", "not"), ("endur-prent-un-inni", "re-print-NMLZ-the")]
    context := "I printed the rules for her yesterday, but now she can't find the print out. I need to reprint the rules today."
    judgment := .acceptable
    alternatives := []
    readings := [("result", .acceptable)]
    paperFeatures := [("prefix", "endur-"), ("reading", "result RN")] }

def ex_15 : LinguisticExample :=
  { id := "wood2023_15"
    source := ⟨"wood-2023", "(4.28a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "að ræða um þetta"
    glossedTokens := [("að", "to"), ("ræða", "discuss"), ("um", "about"), ("þetta", "this")]
    context := ""
    judgment := .acceptable
    alternatives := [("að um-ræða þetta", .ungrammatical)]
    readings := []
    paperFeatures := [("preposition", "um"), ("pattern", "1")] }

def ex_16 : LinguisticExample :=
  { id := "wood2023_16"
    source := ⟨"wood-2023", "(4.28b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "um-ræð-a um þetta"
    glossedTokens := [("um-ræð-a", "about-discuss-NMLZ"), ("um", "about"), ("þetta", "this")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("preposition", "um"), ("pattern", "1")] }

def ex_17 : LinguisticExample :=
  { id := "wood2023_17"
    source := ⟨"wood-2023", "(4.50a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Guðrún hug-sa-ði um þetta."
    glossedTokens := [("Guðrún", "Guðrún"), ("hug-sa-ði", "think-VBLZ-PST"), ("um", "about"), ("þetta", "this")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("preposition", "um"), ("pattern", "3")] }

def ex_18 : LinguisticExample :=
  { id := "wood2023_18"
    source := ⟨"wood-2023", "(4.50c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "hug-s-un-in um þetta"
    glossedTokens := [("hug-s-un-in", "think-VBLZ-NMLZ-the"), ("um", "about"), ("þetta", "this")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("preposition", "um"), ("pattern", "3")] }

def ex_19 : LinguisticExample :=
  { id := "wood2023_19"
    source := ⟨"wood-2023", "(4.12b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "við-ger-ð Guðrúnar á bílnum mínum með sleggju"
    glossedTokens := [("við-ger-ð", "with-do-NMLZ"), ("Guðrúnar", "Guðrún.GEN"), ("á", "on"), ("bílnum", "car.the.DAT"), ("mínum", "my"), ("með", "with"), ("sleggju", "sledge.hammer")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("complex event", .acceptable)]
    paperFeatures := [("preposition", "við"), ("pattern", "2"), ("reading", "CEN")] }

def ex_20 : LinguisticExample :=
  { id := "wood2023_20"
    source := ⟨"wood-2023", "(6.62a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "að versl-un-ar-væða heilbrigðisþjónustuna"
    glossedTokens := [("að", "to"), ("versl-un-ar-væða", "shop-NMLZ-GEN-væða"), ("heilbrigðisþjónustuna", "health.care.service.the.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "-væða")] }

def ex_21 : LinguisticExample :=
  { id := "wood2023_21"
    source := ⟨"wood-2023", "(6.63a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "stofn-an-a-væð-ing"
    glossedTokens := [("stofn-an-a-væð-ing", "office-NMLZ-GEN-væða-NMLZ")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "-væðing")] }

def ex_22 : LinguisticExample :=
  { id := "wood2023_22"
    source := ⟨"wood-2023", "(6.13c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Guðrún snerti að-dá-un-ina."
    glossedTokens := [("Guðrún", "Guðrún"), ("snerti", "touched"), ("að-dá-un-ina", "to-admire-NMLZ-the.ACC")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := [("simple entity", .ungrammatical)]
    paperFeatures := [("nominal", "að-dá-un"), ("reading", "RN")] }

def ex_23 : LinguisticExample :=
  { id := "wood2023_23"
    source := ⟨"wood-2023", "(6.14d)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ég snerti við-vör-un-ina."
    glossedTokens := [("Ég", "I"), ("snerti", "touched"), ("við-vör-un-ina", "with-warn-NMLZ-the")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simple entity", .acceptable)]
    paperFeatures := [("nominal", "við-vör-un"), ("reading", "RN")] }

def all : List LinguisticExample := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14, ex_15, ex_16, ex_17, ex_18, ex_19, ex_20, ex_21, ex_22, ex_23]

end Wood2023.Examples
