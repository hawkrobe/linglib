module

public import Linglib.Data.Examples.Schema

/-!
# `HendersonCoon2018` — typed example data

Auto-generated from `Linglib/Data/Examples/HendersonCoon2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HendersonCoon2018.Examples`.
-/

@[expose] public section

namespace HendersonCoon2018.Examples

def ex_1 : Datum :=
  { id := "hendersoncoon2018_1"
    source := ⟨"henderson-coon-2018", "(1), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike x-Ø-u-löq' ri äk'?"
    glossedTokens := [("Achike", "who"), ("x-Ø-u-löq'", "CPL-ABS3S-ERG3S-buy"), ("ri", "the"), ("äk'", "chicken")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "dp"), ("subject", "3"), ("object", "3")] }

def ex_2 : Datum :=
  { id := "hendersoncoon2018_2"
    source := ⟨"henderson-coon-2018", "(2), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike x-Ø-loq'-o ri äk'?"
    glossedTokens := [("Achike", "who"), ("x-Ø-loq'-o", "CPL-ABS3S-buy-AF"), ("ri", "the"), ("äk'", "chicken")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "AF"), ("objectKind", "dp"), ("subject", "3"), ("object", "3")] }

def ex_12a : Datum :=
  { id := "hendersoncoon2018_12a"
    source := ⟨"henderson-coon-2018", "(12a), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike x-Ø-u-löq' ri tijonel?"
    glossedTokens := [("Achike", "what"), ("x-Ø-u-löq'", "CPL-ABS3S-ERG3S-buy"), ("ri", "the"), ("tijonel", "teacher")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "object"), ("verb", "TV"), ("objectKind", "dp"), ("subject", "3"), ("object", "3")] }

def ex_18a : Datum :=
  { id := "hendersoncoon2018_18a"
    source := ⟨"henderson-coon-2018", "(18a), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Ja ri ixoq x-Ø-u-ch'ëy r-i'."
    glossedTokens := [("Ja", "FOC"), ("ri", "the"), ("ixoq", "woman"), ("x-Ø-u-ch'ëy", "CPL-ABS3S-ERG3S-hit"), ("r-i'", "ERG3S-self")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "reflexive"), ("subject", "3"), ("object", "3")] }

def ex_18b : Datum :=
  { id := "hendersoncoon2018_18b"
    source := ⟨"henderson-coon-2018", "(18b), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike x-Ø-u-k'äm pe r-ixayil pa nimaq'ij"
    glossedTokens := [("Achike", "who"), ("x-Ø-u-k'äm", "CPL-ABS3S-ERG3S-bring"), ("pe", "DIR"), ("r-ixayil", "ERG3S-wife"), ("pa", "PREP"), ("nimaq'ij", "party")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "extendedReflexive"), ("subject", "3"), ("object", "3")] }

def ex_19 : Datum :=
  { id := "hendersoncoon2018_19"
    source := ⟨"henderson-coon-2018", "(19), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "... ri nik'aj chïk winäq ri ni-Ø-ki-b'ij chi ni-Ø-ki-b'än jun kosa y..."
    glossedTokens := [("ri", "the"), ("nik'aj", "half"), ("chïk", "again"), ("winäq", "people"), ("ri", "REL"), ("ni-Ø-ki-b'ij", "ICPL-ABS3S-ERG3P-say"), ("chi", "that"), ("ni-Ø-ki-b'än", "ICPL-ABS3S-ERG3P-do"), ("jun", "one"), ("kosa", "thing"), ("y", "and")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "clause"), ("subject", "3"), ("object", "3")] }

def ex_20 : Datum :=
  { id := "hendersoncoon2018_20"
    source := ⟨"henderson-coon-2018", "(20), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike x-Ø-u-b'än manifestar pa b'ey?"
    glossedTokens := [("Achike", "who"), ("x-Ø-u-b'än", "CPL-ABS3S-ERG3S-do"), ("manifestar", "protest"), ("pa", "in"), ("b'ey", "street")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "lightVerb"), ("subject", "3"), ("object", "3")] }

def ex_4 : Datum :=
  { id := "hendersoncoon2018_4"
    source := ⟨"henderson-coon-2018", "(4), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike kan qitzij x-Ø-u-tij ri wäy?"
    glossedTokens := [("Achike", "who"), ("kan", "truly"), ("qitzij", "truth"), ("x-Ø-u-tij", "CPL-ABS3S-ERG3S-eat"), ("ri", "the"), ("wäy", "tortilla")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "kan qitzij")] }

def ex_5 : Datum :=
  { id := "hendersoncoon2018_5"
    source := ⟨"henderson-coon-2018", "(5), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Ri kan qitzij y-e-ya'-on ru-q'ij k'o chi e ütz chuqa'."
    glossedTokens := [("Ri", "REL"), ("kan", "truly"), ("qitzij", "truth"), ("y-e-ya'-on", "ICPL-ABS3P-give-AF"), ("ru-q'ij", "ERG3S-day"), ("k'o chi", "must"), ("e", "ABS3P"), ("ütz", "good"), ("chuqa'", "also")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "AF"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "kan qitzij")] }

def ex_6 : Datum :=
  { id := "hendersoncoon2018_6"
    source := ⟨"henderson-coon-2018", "(6), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "... roma ri winäq ri kan qitzij n-Ø-u-ya' ru-q'ij ri Dios..."
    glossedTokens := [("roma", "because"), ("ri", "the"), ("winäq", "person"), ("ri", "REL"), ("kan", "truly"), ("qitzij", "truth"), ("n-Ø-u-ya'", "ICPL-ABS3S-ERG3S-give"), ("ru-q'ij", "ERG3S-day"), ("ri", "the"), ("Dios", "God")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "kan qitzij")] }

def ex_24 : Datum :=
  { id := "hendersoncoon2018_24"
    source := ⟨"henderson-coon-2018", "(24), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "... ri pastores ri kan x-Ø-ki-tzijoj ri ru-ch'ab'äl ri Dios ch-iw-e."
    glossedTokens := [("ri", "the"), ("pastores", "pastors"), ("ri", "REL"), ("kan", "truly"), ("x-Ø-ki-tzijoj", "CPL-ABS3S-ERG3P-preach"), ("ri", "the"), ("ru-ch'ab'äl", "ERG3S-word"), ("ri", "the"), ("Dios", "God"), ("ch-iw-e", "PREP-ERG2P-RN.to")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "kan")] }

def ex_25 : Datum :=
  { id := "hendersoncoon2018_25"
    source := ⟨"henderson-coon-2018", "(25), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Rija' kan jun achi ri kan x-Ø-u-q'alaj-saj ri nu-ch'ab'äl."
    glossedTokens := [("Rija'", "He"), ("kan", "truly"), ("jun", "a"), ("achi", "man"), ("ri", "REL"), ("kan", "truly"), ("x-Ø-u-q'alaj-saj", "CPL-ABS3S-ERG3S-visible-CAUS"), ("ri", "the"), ("nu-ch'ab'äl", "ERG1S-word")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "kan")] }

def ex_27 : Datum :=
  { id := "hendersoncoon2018_27"
    source := ⟨"henderson-coon-2018", "(27), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Ri kan xti-Ø-b'an-o k'a ri nu-samäj, xti-Ø-ya'-ox k'a ru-q'ij r-oma ri Nata'."
    glossedTokens := [("Ri", "REL"), ("kan", "truly"), ("xti-Ø-b'an-o", "POT-ABS3S-do-AF"), ("k'a ri", "then"), ("nu-samäj", "ERG1S-work"), ("xti-Ø-ya'-ox", "POT-ABS3S-give-PASS"), ("k'a", "then"), ("ru-q'ij", "ERG3S-day"), ("r-oma", "ERG3S-by"), ("ri", "the"), ("Nata'", "Father")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "AF"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "kan")] }

def ex_28 : Datum :=
  { id := "hendersoncoon2018_28"
    source := ⟨"henderson-coon-2018", "(28), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike k'a ri n-Ø-u-k'üt re tzij re' ch-qa-wäch?"
    glossedTokens := [("Achike", "who"), ("k'a ri", "then"), ("n-Ø-u-k'üt", "ICPL-ABS3S-ERG3S-show"), ("re", "this"), ("tzij", "word"), ("re'", "DEIC"), ("ch-qa-wäch", "PREP-ERG1P-RN.front")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "k'a ri")] }

def ex_29 : Datum :=
  { id := "hendersoncoon2018_29"
    source := ⟨"henderson-coon-2018", "(29), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Ri achike k'a ri n-Ø-r-ak'axaj ri ru-ch'ab'äl ri Nata' Dios y n-Ø-r-etamaj..."
    glossedTokens := [("Ri", "REL"), ("achike", "who"), ("k'a ri", "then"), ("n-Ø-r-ak'axaj", "ICPL-ABS3S-ERG3S-hear"), ("ri", "the"), ("ru-ch'ab'äl", "ERG3S-word"), ("ri", "the"), ("Nata'", "father"), ("Dios", "god"), ("y", "and"), ("n-Ø-r-etamaj", "ICPL-ABS3S-ERG3S-learn")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "k'a ri")] }

def ex_30 : Datum :=
  { id := "hendersoncoon2018_30"
    source := ⟨"henderson-coon-2018", "(30), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike k'a ri x-a-ch'ey-o?"
    glossedTokens := [("Achike", "who"), ("k'a ri", "then"), ("x-a-ch'ey-o", "CPL-ABS2S-fight-AF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "AF"), ("objectKind", "dp"), ("subject", "3"), ("object", "2"), ("intervener", "k'a ri")] }

def ex_31 : Datum :=
  { id := "hendersoncoon2018_31"
    source := ⟨"henderson-coon-2018", "(31), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Xab'achike k'a ri xti-Ø-nima-n ri Jesús kan xt-Ø-r-il wi k'a jun k'aslen ri..."
    glossedTokens := [("Xab'achike", "whoever"), ("k'a ri", "then"), ("xti-Ø-nima-n", "POT-ABS3S-believe-AF"), ("ri", "the"), ("Jesús", "Jesus"), ("kan", "truly"), ("xt-Ø-r-il", "POT-ABS3S-ERG3S-find"), ("wi", "FOC"), ("k'a", "then"), ("jun", "a"), ("k'aslen", "life"), ("ri", "REL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "AF"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "k'a ri")] }

def ex_32 : Datum :=
  { id := "hendersoncoon2018_32"
    source := ⟨"henderson-coon-2018", "(32), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike chi-k-e man x-Ø-tij-o ta ri takamal"
    glossedTokens := [("Achike", "who"), ("chi-k-e", "PREP-ERG3P-RN"), ("man", "NEG"), ("x-Ø-tij-o", "CPL-ABS3S-eat-AF"), ("ta", "IRR"), ("ri", "the"), ("takamal", "tamale")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "AF"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "man")] }

def ex_33 : Datum :=
  { id := "hendersoncoon2018_33"
    source := ⟨"henderson-coon-2018", "(33), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike chi-k-e man x-Ø-u-tij ta ri takamal"
    glossedTokens := [("Achike", "who"), ("chi-k-e", "PREP-ERG3P-RN"), ("man", "NEG"), ("x-Ø-u-tij", "CPL-ABS3S-ERG3S-eat"), ("ta", "IRR"), ("ri", "the"), ("takamal", "tamale")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "man")] }

def ex_45 : Datum :=
  { id := "hendersoncoon2018_45"
    source := ⟨"henderson-coon-2018", "(45), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "K'o q-ach'alal ri kan qitzij chi rije' y-e-ya'-o ru-q'ij."
    glossedTokens := [("K'o", "EXST"), ("q-ach'alal", "ERG1P-family"), ("ri", "REL"), ("kan", "truly"), ("qitzij", "truth"), ("chi", "COMP"), ("rije'", "PRON3P"), ("y-e-ya'-o", "ICPL-ABS3P-give-AF"), ("ru-q'ij", "ERG3S-day")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "AF"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "kan qitzij"), ("complementizer", "chi"), ("resumptive", "overt")] }

def ex_46 : Datum :=
  { id := "hendersoncoon2018_46"
    source := ⟨"henderson-coon-2018", "(46), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "K'o q-ach'alal ri kan qitzij chi rije' y-e-loq'-o ru-wäy."
    glossedTokens := [("K'o", "EXST"), ("q-ach'alal", "ERG1P-family"), ("ri", "REL"), ("kan", "truly"), ("qitzij", "truth"), ("chi", "COMP"), ("rije'", "PRON3P"), ("y-e-loq'-o", "ICPL-ABS3P-buy-AF"), ("ru-wäy", "ERG3S-food")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "AF"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "kan qitzij"), ("complementizer", "chi"), ("resumptive", "overt")] }

def ex_49 : Datum :=
  { id := "hendersoncoon2018_49"
    source := ⟨"henderson-coon-2018", "(49), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "K'o q-ach'alal ri kan qitzij chi rije' n-Ø-ki-ya' ru-q'ij."
    glossedTokens := [("K'o", "EXST"), ("q-ach'alal", "ERG1P-family"), ("ri", "REL"), ("kan", "truly"), ("qitzij", "truth"), ("chi", "COMP"), ("rije'", "PRON3P"), ("n-Ø-ki-ya'", "ICPL-ABS3S-ERG3P-give"), ("ru-q'ij", "ERG3S-day")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "kan qitzij"), ("complementizer", "chi"), ("resumptive", "overt")] }

def ex_50 : Datum :=
  { id := "hendersoncoon2018_50"
    source := ⟨"henderson-coon-2018", "(50), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "K'o q-ach'alal ri kan qitzij chi rije' n-Ø-ki-loq' ru-wäy."
    glossedTokens := [("K'o", "EXST"), ("q-ach'alal", "ERG1P-family"), ("ri", "REL"), ("kan", "truly"), ("qitzij", "truth"), ("chi", "COMP"), ("rije'", "PRON3P"), ("n-Ø-ki-loq'", "ICPL-ABS3S-ERG3P-buy"), ("ru-wäy", "ERG3S-food")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "kan qitzij"), ("complementizer", "chi"), ("resumptive", "overt")] }

def ex_51 : Datum :=
  { id := "hendersoncoon2018_51"
    source := ⟨"henderson-coon-2018", "(51), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "K'o q-ach'alal ri kan qitzij chi ja rije' y-e-ya-o ru-q'ij."
    glossedTokens := [("K'o", "EXST"), ("q-ach'alal", "ERG1P-family"), ("ri", "REL"), ("kan", "truly"), ("qitzij", "truth"), ("chi", "COMP"), ("ja", "FOC"), ("rije'", "PRON3P"), ("y-e-ya-o", "CPL-ABS3P-give-AF"), ("ru-q'ij", "ERG3S-day")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "AF"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "kan qitzij"), ("complementizer", "chi"), ("resumptive", "focused")] }

def ex_56 : Datum :=
  { id := "hendersoncoon2018_56"
    source := ⟨"henderson-coon-2018", "(56), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike kan qitzij x-Ø-tij-o ri wäy?"
    glossedTokens := [("Achike", "who"), ("kan", "truly"), ("qitzij", "truth"), ("x-Ø-tij-o", "CPL-ABS3S-eat-AF"), ("ri", "the"), ("wäy", "tortilla")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "AF"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "kan qitzij")] }

def ex_60a : Datum :=
  { id := "hendersoncoon2018_60a"
    source := ⟨"henderson-coon-2018", "(60a), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike jantäq n-Ø-tij-o ri äk'."
    glossedTokens := [("Achike", "who/what"), ("jantäq", "sometimes"), ("n-Ø-tij-o", "ICPL-ABS3S-eat-AF"), ("ri", "the"), ("äk'", "chicken")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "AF"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "jantäq")] }

def ex_60b : Datum :=
  { id := "hendersoncoon2018_60b"
    source := ⟨"henderson-coon-2018", "(60b), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike jantäq n-Ø-u-tij ri äk'."
    glossedTokens := [("Achike", "who/what"), ("jantäq", "sometimes"), ("n-Ø-u-tij", "ICPL-ABS3S-ERG3S-eat"), ("ri", "the"), ("äk'", "chicken")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := [("subject extraction", .ungrammatical), ("object extraction", .acceptable)]
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "jantäq")] }

def ex_61a : Datum :=
  { id := "hendersoncoon2018_61a"
    source := ⟨"henderson-coon-2018", "(61a), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike jumul n-Ø-tij-o ri äk'."
    glossedTokens := [("Achike", "who/what"), ("jumul", "always"), ("n-Ø-tij-o", "ICPL-ABS3S-eat-AF"), ("ri", "the"), ("äk'", "chicken")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "AF"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "jumul")] }

def ex_61b : Datum :=
  { id := "hendersoncoon2018_61b"
    source := ⟨"henderson-coon-2018", "(61b), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike jumul n-Ø-u-tij ri äk'."
    glossedTokens := [("Achike", "who/what"), ("jumul", "always"), ("n-Ø-u-tij", "ICPL-ABS3S-ERG3S-eat"), ("ri", "the"), ("äk'", "chicken")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := [("subject extraction", .ungrammatical), ("object extraction", .acceptable)]
    paperFeatures := [("construction", "extraction"), ("extracted", "subject"), ("verb", "TV"), ("objectKind", "dp"), ("subject", "3"), ("object", "3"), ("intervener", "jumul")] }

def ex_38 : Datum :=
  { id := "hendersoncoon2018_38"
    source := ⟨"henderson-coon-2018", "(38), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "K'a ri chi xi-Ø-k'achoj r-uma."
    glossedTokens := [("K'a ri", "then"), ("chi", "COMP"), ("xi-Ø-k'achoj", "CPL-ABS3S-cure"), ("r-uma", "ERG3S-RN.by")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "embedding"), ("adverb", "k'a ri"), ("complement", "chi")] }

def ex_40 : Datum :=
  { id := "hendersoncoon2018_40"
    source := ⟨"henderson-coon-2018", "(40), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "... ma x-Ø-in-kusaj ta chuqa' ch'ab'el ri kan janipe' na ru-b'an-ik..."
    glossedTokens := [("ma", "NEG"), ("x-Ø-in-kusaj", "CPL-ABS3S-ERG1S-use"), ("ta", "IRR"), ("chuqa'", "also"), ("ch'ab'el", "speech"), ("ri", "REL"), ("kan", "truly"), ("janipe'", "how.much"), ("na", "PART"), ("ru-b'an-ik", "ERG3S-do-NML")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "embedding"), ("adverb", "kan"), ("complement", "wh")] }

def ex_57 : Datum :=
  { id := "hendersoncoon2018_57"
    source := ⟨"henderson-coon-2018", "(57), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Kan qitzij chi x-a-samäj."
    glossedTokens := [("Kan", "truly"), ("qitzij", "truth"), ("chi", "COMP"), ("x-a-samäj", "CPL-ABS2S-work")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "embedding"), ("adverb", "kan qitzij"), ("complement", "chi")] }

def ex_58 : Datum :=
  { id := "hendersoncoon2018_58"
    source := ⟨"henderson-coon-2018", "(58), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Jantäq chi x-a-samäj."
    glossedTokens := [("Jantäq", "sometimes"), ("chi", "COMP"), ("x-a-samäj", "CPL-ABS2S-work")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "embedding"), ("adverb", "jantäq"), ("complement", "chi")] }

def ex_59 : Datum :=
  { id := "hendersoncoon2018_59"
    source := ⟨"henderson-coon-2018", "(59), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Jumul chi x-a-samäj."
    glossedTokens := [("Jumul", "always"), ("chi", "COMP"), ("x-a-samäj", "CPL-ABS2S-work")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "embedding"), ("adverb", "jumul"), ("complement", "chi")] }

def all : List Datum := [ex_1, ex_2, ex_12a, ex_18a, ex_18b, ex_19, ex_20, ex_4, ex_5, ex_6, ex_24, ex_25, ex_27, ex_28, ex_29, ex_30, ex_31, ex_32, ex_33, ex_45, ex_46, ex_49, ex_50, ex_51, ex_56, ex_60a, ex_60b, ex_61a, ex_61b, ex_38, ex_40, ex_57, ex_58, ex_59]

end HendersonCoon2018.Examples
