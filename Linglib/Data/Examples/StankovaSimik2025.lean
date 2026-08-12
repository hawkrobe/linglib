import Linglib.Data.Examples.Schema

/-!
# `StankovaSimik2025` — typed example data

Auto-generated from `Linglib/Data/Examples/StankovaSimik2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace StankovaSimik2025.Examples`.
-/

namespace StankovaSimik2025.Examples

open Data.Examples

def ex13_v1_nci : LinguisticExample :=
  { id := "stankovasimik2025_ex13_v1_nci"
    source := ⟨"stankova-2025", "(13) B"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Nezasadila tam Dana žádné květiny?"
    discourseSegments := []
    glossedTokens := [("Nezasadila", "NEG.planted"), ("tam", "there"), ("Dana", "Dana"), ("žádné", "DET.NCI"), ("květiny", "flowers")]
    translation := "Didn't Dana plant there any flowers?"
    context := "Dana má na zahradě záhon, který vybudovala před rokem. ('Dana has a garden bed, which she built a year ago.' — neutral, implying neither p nor ¬p)"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("verbPosition", "v1"), ("indefinite", "nci"), ("context", "neutral")]
    comment := "Mean rating ≈ 3 (Figure 2a). V1 forces the outer reading (FALSUM), which cannot license the NCI žádné: main effect of INDEFINITE in V1, z = −15.674, p < .001."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex13_v1_ppi : LinguisticExample :=
  { id := "stankovasimik2025_ex13_v1_ppi"
    source := ⟨"stankova-2025", "(13) B"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Nezasadila tam Dana nějaké květiny?"
    discourseSegments := []
    glossedTokens := [("Nezasadila", "NEG.planted"), ("tam", "there"), ("Dana", "Dana"), ("nějaké", "DET.PPI"), ("květiny", "flowers")]
    translation := "Didn't Dana plant there some flowers?"
    context := "Dana má na zahradě záhon, který vybudovala před rokem. ('Dana has a garden bed, which she built a year ago.' — neutral, implying neither p nor ¬p)"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verbPosition", "v1"), ("indefinite", "ppi"), ("context", "neutral")]
    comment := "Mean rating ≈ 5, highest in neutral context (Figure 2a; CONTEXT within PPI z = −3.522, p < .001). FALSUM allows the PPI nějaké in its scope."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex13_nonv1_nci : LinguisticExample :=
  { id := "stankovasimik2025_ex13_nonv1_nci"
    source := ⟨"stankova-2025", "(13) B′"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Dana tam nezasadila žádné květiny?"
    discourseSegments := []
    glossedTokens := [("Dana", "Dana"), ("tam", "there"), ("nezasadila", "NEG.planted"), ("žádné", "DET.NCI"), ("květiny", "flowers")]
    translation := "Dana didn't plant there any flowers?"
    context := "Dana má na zahradě záhon, kam zasadila zeleninu. ('Dana has a garden bed, where she planted vegetables.' — negative, implying ¬p)"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verbPosition", "nonv1"), ("indefinite", "nci"), ("context", "negative")]
    comment := "Mean rating ≈ 5 in negative context (Figure 2b). The inner default reading licenses the NCI; nonV1 PQs need negative evidential bias (main effect of CONTEXT, z = 8.674, p < 0.01)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex13_nonv1_ppi : LinguisticExample :=
  { id := "stankovasimik2025_ex13_nonv1_ppi"
    source := ⟨"stankova-2025", "(13) B′"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Dana tam nezasadila nějaké květiny?"
    discourseSegments := []
    glossedTokens := [("Dana", "Dana"), ("tam", "there"), ("nezasadila", "NEG.planted"), ("nějaké", "DET.PPI"), ("květiny", "flowers")]
    translation := "Dana didn't plant there some flowers?"
    context := "Dana má na zahradě záhon, kam zasadila zeleninu. ('Dana has a garden bed, where she planted vegetables.' — negative, implying ¬p)"
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("verbPosition", "nonv1"), ("indefinite", "ppi"), ("context", "negative")]
    comment := "Mean rating ≈ 4 in negative context (Figure 2b). The PPI needs the outer reading, available in nonV1 but dispreferred: main effect of INDEFINITE, z = 6.208, p < 0.01, NCI over PPI."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex14 : LinguisticExample :=
  { id := "stankovasimik2025_ex14"
    source := ⟨"stankova-2025", "(14) B"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Nevyhrála Eva nějakou cenu?"
    discourseSegments := []
    glossedTokens := [("Nevyhrála", "NEG.won"), ("Eva", "Eva"), ("nějakou", "DET.PPI"), ("cenu", "prize")]
    translation := "Didn't Eva win a prize?"
    context := "Eva se zúčastnila lingvistické olympiády, kde skončila jako první. ('Eva participated in a linguistic olympiad, where she won the first place.' — positive evidence for p)"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verbPosition", "v1"), ("indefinite", "ppi"), ("context", "positive")]
    comment := "Median 6, vs 5 for the analogous neutral-context condition (§5.3): Czech FALSUM is compatible even with positive evidential bias, unlike English high negation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex17_ppi : LinguisticExample :=
  { id := "stankovasimik2025_ex17_ppi"
    source := ⟨"stankova-2025", "(17) B"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Nezarezervoval si Mikuláš náhodou nějaké sedadlo?"
    discourseSegments := []
    glossedTokens := [("Nezarezervoval", "NEG.booked"), ("si", "REFL"), ("Mikuláš", "Mikuláš"), ("náhodou", "NÁHODOU"), ("nějaké", "DET.PPI"), ("sedadlo", "seat")]
    translation := "Didn't Mikuláš book a seat?"
    context := "Mikuláš cestoval vlakem, který jel do Košic. ('Mikuláš was on the train which went to Košice.' — neutral)"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "nahodou"), ("verbPosition", "v1"), ("indefinite", "ppi"), ("context", "neutral")]
    comment := "Mean rating ≈ 4.8 in both contexts (Figure 3): náhodou, like its licensor FALSUM, is insensitive to contextual evidence."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex17_nci : LinguisticExample :=
  { id := "stankovasimik2025_ex17_nci"
    source := ⟨"stankova-2025", "(17) B"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Nezarezervoval si Mikuláš náhodou žádné sedadlo?"
    discourseSegments := []
    glossedTokens := [("Nezarezervoval", "NEG.booked"), ("si", "REFL"), ("Mikuláš", "Mikuláš"), ("náhodou", "NÁHODOU"), ("žádné", "DET.NCI"), ("sedadlo", "seat")]
    translation := "Didn't Mikuláš book a seat?"
    context := "Mikuláš cestoval vlakem, který jel do Košic. ('Mikuláš was on the train which went to Košice.' — neutral)"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "nahodou"), ("verbPosition", "v1"), ("indefinite", "nci"), ("context", "neutral")]
    comment := "Mean rating ≈ 2.3 neutral / ≈ 3.0 negative (Figure 3). náhodou requires FALSUM, which cannot license the NCI: main effect of INDEFINITE, z = −12.845, p < .001."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex18 : LinguisticExample :=
  { id := "stankovasimik2025_ex18"
    source := ⟨"stankova-2025", "(18) B"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "A Petr si náhodou nekoupil nějakou knihu?"
    discourseSegments := []
    glossedTokens := [("A", "and"), ("Petr", "Petr"), ("si", "REFL"), ("náhodou", "NÁHODOU"), ("nekoupil", "NEG.bought"), ("nějakou", "DET.PPI"), ("knihu", "book")]
    translation := "And as for Petr, did he buy a book, too, by any chance?"
    context := "Hanka si koupila knihu. ('Hanka bought a book.')"
    judgment := .acceptable
    alternatives := [("A Petr si náhodou nekoupil žádnou knihu?", .unacceptable)]
    readings := []
    paperFeatures := [("particle", "nahodou"), ("verbPosition", "nonv1"), ("indefinite", "ppi")]
    comment := "náhodou in a nonV1 PQ: needs a contrastive topic (Petr) and contrastive focus on the negated verb, and the negation must still be FALSUM — witness the infelicitous NCI alternative žádnou."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex13_v1_nci, ex13_v1_ppi, ex13_nonv1_nci, ex13_nonv1_ppi, ex14, ex17_ppi, ex17_nci, ex18]

end StankovaSimik2025.Examples
