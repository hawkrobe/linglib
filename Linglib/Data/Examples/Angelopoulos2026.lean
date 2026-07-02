import Linglib.Data.Examples.Schema

/-!
# `Angelopoulos2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Angelopoulos2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Angelopoulos2026.Examples`.
-/

namespace Angelopoulos2026.Examples

open Data.Examples

def ex_1a : LinguisticExample :=
  { id := "angelopoulos2026_1a"
    source := ⟨"angelopoulos-2026", "ex. (1a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I Elena ipe oti eçi episkefti tin Vrazilia."
    discourseSegments := []
    glossedTokens := [("I", "the.F.SG.NOM"), ("Elena", "Elena.F.SG.NOM"), ("ipe", "said.3SG"), ("oti", "OTI"), ("eçi", "have.3SG"), ("episkefti", "visited"), ("tin", "the.F.SG.ACC"), ("Vrazilia", "Brazil.F.SG.ACC")]
    translation := "Elena said that she has visited Brazil."
    context := ""
    judgment := .acceptable
    alternatives := [("I Elena ipe pu eçi episkefti tin Vrazilia.", .ungrammatical)]
    readings := []
    paperFeatures := [("complementizer", "oti"), ("verbClass", "saying")]
    comment := "Paper prints 'oti/*pu' in one example; the pu variant is expanded into alternatives. OTI/PU are the paper's placeholder glosses for the complementizers (fn. 1). Verbs of saying and belief take oti, not pu."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_1b : LinguisticExample :=
  { id := "angelopoulos2026_1b"
    source := ⟨"angelopoulos-2026", "ex. (1b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I Elena metanjose pu paretiθike."
    discourseSegments := []
    glossedTokens := [("I", "the.F.SG.NOM"), ("Elena", "Elena.F.SG.NOM"), ("metanjose", "regretted.3SG"), ("pu", "PU"), ("paretiθike", "quit.3SG")]
    translation := "Elena regretted that she quit."
    context := ""
    judgment := .acceptable
    alternatives := [("I Elena metanjose oti paretiθike.", .ungrammatical)]
    readings := []
    paperFeatures := [("complementizer", "pu"), ("verbClass", "emotive-factive")]
    comment := "Paper prints 'pu/*oti' in one example; the oti variant is expanded into alternatives. Emotive factive verbs take pu, not oti."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_31a : LinguisticExample :=
  { id := "angelopoulos2026_31a"
    source := ⟨"angelopoulos-2026", "ex. (31a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "δjafono me kati."
    discourseSegments := []
    glossedTokens := [("δjafono", "disagree.1SG"), ("me", "with"), ("kati", "something.N.SG.ACC")]
    translation := "I disagree with something."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "P-ban"), ("verb", "δjafono 'disagree'")]
    comment := "δjafono 'disagree' takes a PP complement headed by me 'with'."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_31b : LinguisticExample :=
  { id := "angelopoulos2026_31b"
    source := ⟨"angelopoulos-2026", "ex. (31b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "δjafono oti prepi na kanume epenδisis."
    discourseSegments := []
    glossedTokens := [("δjafono", "disagree.1SG"), ("oti", "OTI"), ("prepi", "must.3SG"), ("na", "na"), ("kanume", "do.1PL"), ("epenδisis", "investments.F.PL.ACC")]
    translation := "I disagree that we should invest."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "P-ban"), ("verb", "δjafono 'disagree'")]
    comment := "δjafono 'disagree' also takes a bare oti-clause complement."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_31c : LinguisticExample :=
  { id := "angelopoulos2026_31c"
    source := ⟨"angelopoulos-2026", "ex. (31c)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "δjafono me oti prepi na kanume epenδisis."
    discourseSegments := []
    glossedTokens := [("δjafono", "disagree.1SG"), ("me", "with"), ("oti", "OTI"), ("prepi", "must.3SG"), ("na", "na"), ("kanume", "do.1PL"), ("epenδisis", "investments.F.PL.ACC")]
    translation := "I disagree with the idea that we should invest."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "P-ban"), ("verb", "δjafono 'disagree'")]
    comment := "Translation marked 'intended:' in the paper. The oti-clause cannot combine with the P me: like T, P cannot host light-noun incorporation."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_32a : LinguisticExample :=
  { id := "angelopoulos2026_32a"
    source := ⟨"angelopoulos-2026", "ex. (32a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Metanjono ja kati."
    discourseSegments := []
    glossedTokens := [("Metanjono", "regret.1SG"), ("ja", "for"), ("kati", "something.N.SG.ACC")]
    translation := "I regret for something."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "P-ban"), ("verb", "metanjono 'regret'")]
    comment := "metanjono 'regret' takes a PP complement headed by ja 'for'."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_32b : LinguisticExample :=
  { id := "angelopoulos2026_32b"
    source := ⟨"angelopoulos-2026", "ex. (32b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Metanjono pu paremina."
    discourseSegments := []
    glossedTokens := [("Metanjono", "regret.1SG"), ("pu", "PU"), ("paremina", "stayed.1SG")]
    translation := "I regret that I stayed."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "P-ban"), ("verb", "metanjono 'regret'")]
    comment := "metanjono 'regret' also takes a bare pu-clause complement."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_32c : LinguisticExample :=
  { id := "angelopoulos2026_32c"
    source := ⟨"angelopoulos-2026", "ex. (32c)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Metanjono ja pu paremina."
    discourseSegments := []
    glossedTokens := [("Metanjono", "regret.1SG"), ("ja", "for"), ("pu", "PU"), ("paremina", "stayed.1SG")]
    translation := "I regret for staying."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "P-ban"), ("verb", "metanjono 'regret'")]
    comment := "Translation marked 'intended:' in the paper. The pu-clause cannot combine with the P ja."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_33a : LinguisticExample :=
  { id := "angelopoulos2026_33a"
    source := ⟨"angelopoulos-2026", "ex. (33a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Afti i fimi ine aliθis."
    discourseSegments := []
    glossedTokens := [("Afti", "this.F.SG.NOM"), ("i", "the.F.SG.NOM"), ("fimi", "rumor.F.SG.NOM"), ("ine", "be.3SG"), ("aliθis", "true.F.SG.NOM")]
    translation := "This rumor is true/mistaken."
    context := ""
    judgment := .acceptable
    alternatives := [("Afti i fimi ine lanθasmeni.", .acceptable)]
    readings := []
    paperFeatures := [("diagnostic", "truth-predicates"), ("nounSort", "content")]
    comment := "Paper prints 'aliθis/lanθasmeni' in one example; expanded here. Content nouns combine with 'true'/'mistaken'."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_33b : LinguisticExample :=
  { id := "angelopoulos2026_33b"
    source := ⟨"angelopoulos-2026", "ex. (33b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Afti i katastasi ine aliθis."
    discourseSegments := []
    glossedTokens := [("Afti", "this.F.SG.NOM"), ("i", "the.F.SG.NOM"), ("katastasi", "situation.F.SG.NOM"), ("ine", "be.3SG"), ("aliθis", "true.F.SG.NOM")]
    translation := "This situation is true/mistaken."
    context := ""
    judgment := .unacceptable
    alternatives := [("Afti i katastasi ine lanθasmeni.", .unacceptable)]
    readings := []
    paperFeatures := [("diagnostic", "truth-predicates"), ("nounSort", "situation")]
    comment := "Marked # in the paper (scoping over both predicate variants): situation nouns do not combine with 'true'/'mistaken'."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_34a : LinguisticExample :=
  { id := "angelopoulos2026_34a"
    source := ⟨"angelopoulos-2026", "ex. (34a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Tetjes fimes δen simvenun sixna."
    discourseSegments := []
    glossedTokens := [("Tetjes", "such.F.PL.NOM"), ("fimes", "rumors.F.PL.NOM"), ("δen", "not"), ("simvenun", "occur.3PL"), ("sixna", "often")]
    translation := "Such rumors/ideas/warnings/beliefs/hypotheses/theories do not happen often."
    context := ""
    judgment := .unacceptable
    alternatives := [("Tetjes iδees δen simvenun sixna.", .unacceptable), ("Tetjes proiδopiisis δen simvenun sixna.", .unacceptable), ("Tetjes pepiθisis δen simvenun sixna.", .unacceptable), ("Tetjes ipoθesis δen simvenun sixna.", .unacceptable), ("Tetjes θeories δen simvenun sixna.", .unacceptable)]
    readings := []
    paperFeatures := [("diagnostic", "occurrence-predicates"), ("nounSort", "content")]
    comment := "Marked # in the paper. Paper prints the six content nouns 'fimes/ iδees/ proiδopiisis/ pepiθisis/ ipoθesis/ θeories' (rumors/ideas/warnings/beliefs/hypotheses/theories) as one slash-list; expanded here. Content nouns do not combine with simveni 'happen'."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_34b : LinguisticExample :=
  { id := "angelopoulos2026_34b"
    source := ⟨"angelopoulos-2026", "ex. (34b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Tetjes periptosis δen simvenun sixna."
    discourseSegments := []
    glossedTokens := [("Tetjes", "such.F.PL.NOM"), ("periptosis", "situations.F.PL.NOM"), ("δen", "not"), ("simvenun", "occur.3PL"), ("sixna", "often")]
    translation := "Such situations/cases do not happen often."
    context := ""
    judgment := .acceptable
    alternatives := [("Tetjes katastasis δen simvenun sixna.", .acceptable)]
    readings := []
    paperFeatures := [("diagnostic", "occurrence-predicates"), ("nounSort", "situation")]
    comment := "Paper prints 'periptosis/ katastasis' glossed 'situations.F.PL.NOM/ cases.F.PL.NOM' — transcribed verbatim, though the gloss order looks swapped relative to (35b), where periptosi = 'case' and katastasi = 'situation'. Situation nouns combine with simveni 'happen'."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex_1a, ex_1b, ex_31a, ex_31b, ex_31c, ex_32a, ex_32b, ex_32c, ex_33a, ex_33b, ex_34a, ex_34b]

end Angelopoulos2026.Examples
