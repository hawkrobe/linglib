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
    discourseSegments := []
    glossedTokens := [("Guðrún", "Guðrún.NOM"), ("þvoði", "washed"), ("fötin", "clothes.the.ACC")]
    translation := "Guðrún washed the clothes."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "þvo")]
    comment := "The verb underlying þvottur."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2 : LinguisticExample :=
  { id := "wood2023_2"
    source := ⟨"wood-2023", "(6.37a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "þvo-ttur Guðrúnar á fötunum"
    discourseSegments := []
    glossedTokens := [("þvo-ttur", "wash-NMLZ"), ("Guðrúnar", "Guðrún.GEN"), ("á", "on"), ("fötunum", "clothes.the.DAT")]
    translation := "Guðrún's washing of the clothes"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("complex event", .acceptable)]
    paperFeatures := [("reading", "CEN")]
    comment := "A complex event reading with the internal argument in a PP."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3 : LinguisticExample :=
  { id := "wood2023_3"
    source := ⟨"wood-2023", "(6.37c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þvo-ttur-inn tók langan tíma."
    discourseSegments := []
    glossedTokens := [("Þvo-ttur-inn", "wash-NMLZ-the"), ("tók", "took"), ("langan", "long"), ("tíma", "time")]
    translation := "The washing took a long time."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simple event", .acceptable)]
    paperFeatures := [("reading", "SEN")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4 : LinguisticExample :=
  { id := "wood2023_4"
    source := ⟨"wood-2023", "(6.37d)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þvo-ttur-inn á að fara í vélina."
    discourseSegments := []
    glossedTokens := [("Þvo-ttur-inn", "wash-NMLZ-the"), ("á", "ought"), ("að", "to"), ("fara", "go"), ("í", "in"), ("vélina", "machine.the.ACC")]
    translation := "The washing should go into the washing machine."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simple entity", .acceptable)]
    paperFeatures := [("reading", "RN")]
    comment := "The laundry reading, an entity with no event."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5 : LinguisticExample :=
  { id := "wood2023_5"
    source := ⟨"wood-2023", "(6.38)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Guðrún marg-þvoði fötin."
    discourseSegments := []
    glossedTokens := [("Guðrún", "Guðrún.NOM"), ("marg-þvoði", "many-washed"), ("fötin", "clothes.the.ACC")]
    translation := "Guðrún repeatedly washed the clothes."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("prefix", "marg-")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6 : LinguisticExample :=
  { id := "wood2023_6"
    source := ⟨"wood-2023", "(6.38a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "marg-þvo-ttur Guðrúnar á fötunum"
    discourseSegments := []
    glossedTokens := [("marg-þvo-ttur", "many-wash-NMLZ"), ("Guðrúnar", "Guðrún.GEN"), ("á", "on"), ("fötunum", "clothes.the.DAT")]
    translation := "Guðrún's repeated washing of the clothes."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("complex event", .acceptable)]
    paperFeatures := [("prefix", "marg-"), ("reading", "CEN")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7 : LinguisticExample :=
  { id := "wood2023_7"
    source := ⟨"wood-2023", "(6.38c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "marg-þvo-ttur fatanna"
    discourseSegments := []
    glossedTokens := [("marg-þvo-ttur", "many-wash-NMLZ"), ("fatanna", "clothes.the.GEN")]
    translation := "the repeated washing of the clothes"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("complex event", .acceptable)]
    paperFeatures := [("prefix", "marg-"), ("reading", "CEN")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8 : LinguisticExample :=
  { id := "wood2023_8"
    source := ⟨"wood-2023", "(6.38d)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Marg-þvo-ttur-inn tók langan tíma."
    discourseSegments := []
    glossedTokens := [("Marg-þvo-ttur-inn", "many-wash-NMLZ-the"), ("tók", "took"), ("langan", "long"), ("tíma", "time")]
    translation := "The repeated washing took a long time."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := [("simple event", .ungrammatical)]
    paperFeatures := [("prefix", "marg-"), ("reading", "SEN")]
    comment := "Iterative marg- is out on the simple event reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_9 : LinguisticExample :=
  { id := "wood2023_9"
    source := ⟨"wood-2023", "(6.38e)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Marg-þvo-ttur-inn á að fara í vélina."
    discourseSegments := []
    glossedTokens := [("Marg-þvo-ttur-inn", "many-wash-NMLZ-the"), ("á", "ought"), ("að", "to"), ("fara", "go"), ("í", "in"), ("vélina", "machine.the.ACC")]
    translation := "The repeated washing should go into the washing machine."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := [("simple entity", .ungrammatical)]
    paperFeatures := [("prefix", "marg-"), ("reading", "RN")]
    comment := "Iterative marg- is out on the entity reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10 : LinguisticExample :=
  { id := "wood2023_10"
    source := ⟨"wood-2023", "(6.46)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ég endur-þvoði fötin."
    discourseSegments := []
    glossedTokens := [("Ég", "I.NOM"), ("endur-þvoði", "re-washed"), ("fötin", "clothes.the.ACC")]
    translation := "I rewashed the clothes."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("prefix", "endur-")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_11 : LinguisticExample :=
  { id := "wood2023_11"
    source := ⟨"wood-2023", "(6.46a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "endur-þvo-ttur Guðrúnar á fötunum"
    discourseSegments := []
    glossedTokens := [("endur-þvo-ttur", "re-wash-NMLZ"), ("Guðrúnar", "Guðrún.GEN"), ("á", "on"), ("fötunum", "clothes.the.DAT")]
    translation := "Guðrún's rewashing of the clothes."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("complex event", .acceptable)]
    paperFeatures := [("prefix", "endur-"), ("reading", "CEN")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12 : LinguisticExample :=
  { id := "wood2023_12"
    source := ⟨"wood-2023", "(6.46c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Endur-þvo-ttur-inn tók langan tíma."
    discourseSegments := []
    glossedTokens := [("Endur-þvo-ttur-inn", "re-wash-NMLZ-the"), ("tók", "took"), ("langan", "long"), ("tíma", "time")]
    translation := "The rewashing took a long time."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simple event", .acceptable)]
    paperFeatures := [("prefix", "endur-"), ("reading", "SEN")]
    comment := "endur- adjoins to n, where the simple event alloseme supplies the event."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_13 : LinguisticExample :=
  { id := "wood2023_13"
    source := ⟨"wood-2023", "(6.46d)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Endur-þvo-ttur-inn á að fara í vélina."
    discourseSegments := []
    glossedTokens := [("Endur-þvo-ttur-inn", "re-wash-NMLZ-the"), ("á", "ought"), ("að", "to"), ("fara", "go"), ("í", "in"), ("vélina", "machine.the.ACC")]
    translation := "The rewashing should go into the washing machine."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := [("simple entity", .ungrammatical)]
    paperFeatures := [("prefix", "endur-"), ("reading", "RN")]
    comment := "No event variable at v or n on the entity reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_14 : LinguisticExample :=
  { id := "wood2023_14"
    source := ⟨"wood-2023", "(6.52)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ég vona að hún týni ekki endur-prent-un-inni."
    discourseSegments := []
    glossedTokens := [("Ég", "I"), ("vona", "hope"), ("að", "that"), ("hún", "she"), ("týni", "loses"), ("ekki", "not"), ("endur-prent-un-inni", "re-print-NMLZ-the")]
    translation := "I hope she doesn't lose the reprinting."
    context := "I printed the rules for her yesterday, but now she can't find the print out. I need to reprint the rules today."
    judgment := .acceptable
    alternatives := []
    readings := [("result", .acceptable)]
    paperFeatures := [("prefix", "endur-"), ("reading", "result RN")]
    comment := "A result nominal built on eventive v, to which endur- adjoins."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_15 : LinguisticExample :=
  { id := "wood2023_15"
    source := ⟨"wood-2023", "(4.28a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "að ræða um þetta"
    discourseSegments := []
    glossedTokens := [("að", "to"), ("ræða", "discuss"), ("um", "about"), ("þetta", "this")]
    translation := "to discuss this"
    context := ""
    judgment := .acceptable
    alternatives := [("að um-ræða þetta", .ungrammatical)]
    readings := []
    paperFeatures := [("preposition", "um"), ("pattern", "1")]
    comment := "The verb takes an um PP; the prefixed verb um-ræða is out."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_16 : LinguisticExample :=
  { id := "wood2023_16"
    source := ⟨"wood-2023", "(4.28b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "um-ræð-a um þetta"
    discourseSegments := []
    glossedTokens := [("um-ræð-a", "about-discuss-NMLZ"), ("um", "about"), ("þetta", "this")]
    translation := "discussion about this"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("preposition", "um"), ("pattern", "1")]
    comment := "Doubling: the preposition is prefixed to the noun and heads a PP."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_17 : LinguisticExample :=
  { id := "wood2023_17"
    source := ⟨"wood-2023", "(4.50a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Guðrún hug-sa-ði um þetta."
    discourseSegments := []
    glossedTokens := [("Guðrún", "Guðrún"), ("hug-sa-ði", "think-VBLZ-PST"), ("um", "about"), ("þetta", "this")]
    translation := "Guðrún thought about this."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("preposition", "um"), ("pattern", "3")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_18 : LinguisticExample :=
  { id := "wood2023_18"
    source := ⟨"wood-2023", "(4.50c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "hug-s-un-in um þetta"
    discourseSegments := []
    glossedTokens := [("hug-s-un-in", "think-VBLZ-NMLZ-the"), ("um", "about"), ("þetta", "this")]
    translation := "the thinking about this"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("preposition", "um"), ("pattern", "3")]
    comment := "The preposition conditions no special meaning, so it is not prefixed."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_19 : LinguisticExample :=
  { id := "wood2023_19"
    source := ⟨"wood-2023", "(4.12b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "við-ger-ð Guðrúnar á bílnum mínum með sleggju"
    discourseSegments := []
    glossedTokens := [("við-ger-ð", "with-do-NMLZ"), ("Guðrúnar", "Guðrún.GEN"), ("á", "on"), ("bílnum", "car.the.DAT"), ("mínum", "my"), ("með", "with"), ("sleggju", "sledge.hammer")]
    translation := "Guðrún's repairing of my car with a sledge hammer"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("complex event", .acceptable)]
    paperFeatures := [("preposition", "við"), ("pattern", "2"), ("reading", "CEN")]
    comment := "The preposition conditions the special meaning 'repair' of gera and is prefixed."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_20 : LinguisticExample :=
  { id := "wood2023_20"
    source := ⟨"wood-2023", "(6.62a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "að versl-un-ar-væða heilbrigðisþjónustuna"
    discourseSegments := []
    glossedTokens := [("að", "to"), ("versl-un-ar-væða", "shop-NMLZ-GEN-væða"), ("heilbrigðisþjónustuna", "health.care.service.the.ACC")]
    translation := "to shopify the health care service"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "-væða")]
    comment := "The stem carries overt nominalizing and genitive morphology: -væða attaches to a categorized word."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_21 : LinguisticExample :=
  { id := "wood2023_21"
    source := ⟨"wood-2023", "(6.63a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "stofn-an-a-væð-ing"
    discourseSegments := []
    glossedTokens := [("stofn-an-a-væð-ing", "office-NMLZ-GEN-væða-NMLZ")]
    translation := "institutionization"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("suffix", "-væðing")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_22 : LinguisticExample :=
  { id := "wood2023_22"
    source := ⟨"wood-2023", "(6.13c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Guðrún snerti að-dá-un-ina."
    discourseSegments := []
    glossedTokens := [("Guðrún", "Guðrún"), ("snerti", "touched"), ("að-dá-un-ina", "to-admire-NMLZ-the.ACC")]
    translation := "Guðrún touched the admiration."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := [("simple entity", .ungrammatical)]
    paperFeatures := [("nominal", "að-dá-un"), ("reading", "RN")]
    comment := "The book also gives the verb rétti mér 'handed me'. Aðdáun has no concrete entity reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23 : LinguisticExample :=
  { id := "wood2023_23"
    source := ⟨"wood-2023", "(6.14d)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ég snerti við-vör-un-ina."
    discourseSegments := []
    glossedTokens := [("Ég", "I"), ("snerti", "touched"), ("við-vör-un-ina", "with-warn-NMLZ-the")]
    translation := "I touched the warning."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simple entity", .acceptable)]
    paperFeatures := [("nominal", "við-vör-un"), ("reading", "RN")]
    comment := "Viðvörun, with the same nominalizer as aðdáun, has a concrete entity reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14, ex_15, ex_16, ex_17, ex_18, ex_19, ex_20, ex_21, ex_22, ex_23]

end Wood2023.Examples
