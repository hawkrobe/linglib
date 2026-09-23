module

public import Linglib.Data.Examples.Schema

/-!
# `Wang2023` — typed example data

Auto-generated from `Linglib/Data/Examples/Wang2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Wang2023.Examples`.
-/

@[expose] public section

namespace Wang2023.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "wang2023_1"
    source := ⟨"wang-r-2023", "(1)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "As tu le livre?"
    discourseSegments := []
    glossedTokens := [("As", "have.PRES.2SG"), ("tu", "2SG"), ("le", "the"), ("livre", "book")]
    translation := "Do you have the book?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("address", "familiar"), ("number", "singular")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2 : LinguisticExample :=
  { id := "wang2023_2"
    source := ⟨"wang-r-2023", "(2)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Avez vous le livre?"
    discourseSegments := []
    glossedTokens := [("Avez", "have.PRES.2PL"), ("vous", "2PL"), ("le", "the"), ("livre", "book")]
    translation := "Do you (HON) have the book?"
    context := ""
    judgment := .acceptable
    alternatives := [("As vous le livre?", .ungrammatical)]
    readings := []
    paperFeatures := [("address", "polite"), ("number", "plural"), ("mismatch", "referentially singular")]
    comment := "Honorific vous triggers plural agreement for a singular addressee."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3a : LinguisticExample :=
  { id := "wang2023_3a"
    source := ⟨"wang-r-2023", "(3a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Alessandro, sei contento?"
    discourseSegments := []
    glossedTokens := [("Alessandro", "A"), ("sei", "2SG.COP"), ("contento", "happy.MASC")]
    translation := "Alessandro, are you happy?"
    context := ""
    judgment := .acceptable
    alternatives := [("Alessandro, è contento?", .ungrammatical)]
    readings := []
    paperFeatures := [("address", "familiar"), ("person", "second")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3b : LinguisticExample :=
  { id := "wang2023_3b"
    source := ⟨"wang-r-2023", "(3b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Signor Alessandro, è contento?"
    discourseSegments := []
    glossedTokens := [("Signor", "sir"), ("Alessandro", "A"), ("è", "3SG.COP"), ("contento", "happy.MASC")]
    translation := "Sir Alessandro, are you (HON) happy?"
    context := ""
    judgment := .acceptable
    alternatives := [("Signor Alessandro, sei contento?", .ungrammatical)]
    readings := []
    paperFeatures := [("address", "polite"), ("person", "third"), ("mismatch", "second-person addressee")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4a : LinguisticExample :=
  { id := "wang2023_4a"
    source := ⟨"wang-r-2023", "(4a)"⟩
    reportedIn := none
    language := "ainu1240"
    primaryText := "Ecioka rupne nispa-eci ne ruwe"
    discourseSegments := []
    glossedTokens := [("Ecioka", "2PL"), ("rupne", "be.grown.up"), ("nispa-eci", "man-2PL"), ("ne", "COP"), ("ruwe", "ASSERT")]
    translation := "You (all) are grown men"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("address", "familiar"), ("definiteness", "definite pronoun")]
    comment := "Refsing 1986: 94, 222, adapted."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4b : LinguisticExample :=
  { id := "wang2023_4b"
    source := ⟨"wang-r-2023", "(4b)"⟩
    reportedIn := none
    language := "ainu1240"
    primaryText := "An nu no.oka"
    discourseSegments := []
    glossedTokens := [("An", "INDEF"), ("nu", "ask"), ("no.oka", "IMPF")]
    translation := "As you (HON) are asking"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("address", "polite"), ("definiteness", "indefinite pronoun"), ("mismatch", "definite addressee")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_29 : LinguisticExample :=
  { id := "wang2023_29"
    source := ⟨"wang-r-2023", "(29)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "As tu le livre?"
    discourseSegments := []
    glossedTokens := []
    translation := "Intended: Do you all (HON) have the book?"
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("unattested", "honorific singular")]
    comment := "A hypothetical French recruiting the singular for honorification is unattested, (28a)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_30a : LinguisticExample :=
  { id := "wang2023_30a"
    source := ⟨"wang-r-2023", "(30a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Signor Alessandro, sono contento?"
    discourseSegments := []
    glossedTokens := []
    translation := "Intended: Sir Alessandro, are you (HON) happy?"
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("unattested", "honorific first person")]
    comment := "(28b)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_30b : LinguisticExample :=
  { id := "wang2023_30b"
    source := ⟨"wang-r-2023", "(30b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Sei Signor Alessandro contento?"
    discourseSegments := []
    glossedTokens := []
    translation := "Intended: Is Sir Alessandro (HON) happy?"
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("unattested", "honorific second person")]
    comment := "(28b)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_31 : LinguisticExample :=
  { id := "wang2023_31"
    source := ⟨"wang-r-2023", "(31)"⟩
    reportedIn := none
    language := "ainu1240"
    primaryText := "Eani nu no.oka"
    discourseSegments := []
    glossedTokens := []
    translation := "Intended: As someone (HON) are asking"
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("unattested", "honorific definite")]
    comment := "(28c)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_48a : LinguisticExample :=
  { id := "wang2023_48a"
    source := ⟨"wang-r-2023", "(48a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How many hamsters do I own? Just one hamster, I think."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "semantic markedness"), ("number", "plural inclusive")]
    comment := "A singular answer to a plural question: the plural is number-neutral."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_49 : LinguisticExample :=
  { id := "wang2023_49"
    source := ⟨"wang-r-2023", "(49)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every girl owns hamsters."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("each girl owns exactly one hamster", .acceptable), ("mixed: some girls own one, others several", .acceptable)]
    paperFeatures := [("diagnostic", "quantification"), ("number", "plural inclusive")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_50 : LinguisticExample :=
  { id := "wang2023_50"
    source := ⟨"wang-r-2023", "(50)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every one of us has to call his/her mother."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := [("Every one of us has to call my mother.", .ungrammatical), ("Every one of us has to call your mother.", .ungrammatical)]
    readings := []
    paperFeatures := [("diagnostic", "quantification"), ("person", "third unmarked")]
    comment := "Sauerland 2008b: 72, adapted; a mixed-person group binds only a third-person pronoun."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_53a : LinguisticExample :=
  { id := "wang2023_53a"
    source := ⟨"wang-r-2023", "(53a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I've picked up the new hamster from the store."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definiteness", "definite"), ("presupposition", "familiarity")]
    comment := "Felicitous only with a salient or previously mentioned hamster."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_53b : LinguisticExample :=
  { id := "wang2023_53b"
    source := ⟨"wang-r-2023", "(53b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I've picked up a new hamster from the store."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definiteness", "indefinite")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_60 : LinguisticExample :=
  { id := "wang2023_60"
    source := ⟨"wang-r-2023", "(60)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Avez vous le livre?"
    discourseSegments := []
    glossedTokens := []
    translation := "Do you all (HON) have the book?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("address", "polite"), ("number", "plural"), ("case", "ceiling")]
    comment := "No mismatch with a plural addressee, yet the honorific inference remains."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_72 : LinguisticExample :=
  { id := "wang2023_72"
    source := ⟨"wang-r-2023", "(72)"⟩
    reportedIn := none
    language := "motl1237"
    primaryText := "Ēt! Yohē! Amyo van tō me!"
    discourseSegments := []
    glossedTokens := [("Ēt", "EXCLAM"), ("Yohē", "DU.VOC"), ("Amyo", "2DU.IMP"), ("van", "AORIST.go"), ("tō", "POL.IMP"), ("me", "hither")]
    translation := "Hey, you (HON)! Come here for a second."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("address", "polite"), ("number", "dual"), ("system", "honorific dual only")]
    comment := "François 2005: 121."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_74b : LinguisticExample :=
  { id := "wang2023_74b"
    source := ⟨"wang-r-2023", "(74b)"⟩
    reportedIn := none
    language := "khar1287"
    primaryText := "iñ-aʔ tay konon tin bhaya-ñ-kiyar ayiʔj-kiyar."
    discourseSegments := []
    glossedTokens := [("iñ-aʔ", "1SG-GEN"), ("tay", "ABL"), ("konon", "small"), ("tin", "three"), ("bhaya-ñ-kiyar", "brother-1.POSS-3DU"), ("ayiʔj-kiyar", "COP.PRES-3DU")]
    translation := "I have three younger brothers (HON)."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("reference", "polite"), ("number", "dual for three referents"), ("system", "honorific dual only")]
    comment := "Peterson 2011: 169–170, adapted; the weak taboo outranking MP! lets the dual honorify three."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_75a : LinguisticExample :=
  { id := "wang2023_75a"
    source := ⟨"wang-r-2023", "(75a)"⟩
    reportedIn := none
    language := "slov1268"
    primaryText := "Ali se boste Vi usedli?"
    discourseSegments := []
    glossedTokens := [("Ali", "Q"), ("se", "REFLX"), ("boste", "AUX.FUT.2PL"), ("Vi", "2PL"), ("usedli", "sit-PART-PL.MASC")]
    translation := "Would you (HON) like to sit down?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("address", "polite"), ("number", "plural"), ("system", "honorific plural only")]
    comment := "Corbett 2000: 226."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_75b : LinguisticExample :=
  { id := "wang2023_75b"
    source := ⟨"wang-r-2023", "(75b)"⟩
    reportedIn := none
    language := "slov1268"
    primaryText := "Ali se bosta Vidva usedla?"
    discourseSegments := []
    glossedTokens := [("Ali", "Q"), ("se", "REFLX"), ("bosta", "AUX.FUT.2DU"), ("Vidva", "2DU"), ("usedla", "sit-PART-DU.MASC")]
    translation := "Would you like to sit down?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("address", "plain dual"), ("number", "dual")]
    comment := "The dual has no honorific effect."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_78a : LinguisticExample :=
  { id := "wang2023_78a"
    source := ⟨"wang-r-2023", "(78a)"⟩
    reportedIn := none
    language := "mele1250"
    primaryText := "korua/koteu ku-roro."
    discourseSegments := []
    glossedTokens := [("korua/koteu", "2DU/2PL"), ("ku-roro", "PF-go.NSG")]
    translation := "You (HON) have gone."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("address", "polite"), ("number", "dual or plural"), ("system", "non-escalating")]
    comment := "Own fieldwork; dual and plural indicate equal respect."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_81 : LinguisticExample :=
  { id := "wang2023_81"
    source := ⟨"wang-r-2023", "(81)"⟩
    reportedIn := none
    language := "slov1268"
    primaryText := "Vsak študent je prinesel s seboj svoji knjigi."
    discourseSegments := []
    glossedTokens := [("Vsak", "every"), ("študent", "student"), ("je", "be.SG"), ("prinesel", "brought.MASC"), ("s", "with"), ("seboj", "self"), ("svoji", "his-DU"), ("knjigi", "book-DU")]
    translation := "Every student brought his books."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "quantification"), ("number", "dual intermediate")]
    comment := "Sauerland 2008b: compatible with some students having one book and others exactly two."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1, ex_2, ex_3a, ex_3b, ex_4a, ex_4b, ex_29, ex_30a, ex_30b, ex_31, ex_48a, ex_49, ex_50, ex_53a, ex_53b, ex_60, ex_72, ex_74b, ex_75a, ex_75b, ex_78a, ex_81]

end Wang2023.Examples
