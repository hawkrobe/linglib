module

public import Linglib.Data.Examples.Schema

/-!
# `Erlewine2016` — typed example data

Auto-generated from `Linglib/Data/Examples/Erlewine2016.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Erlewine2016.Examples`.
-/

@[expose] public section

namespace Erlewine2016.Examples

open Data.Examples

def ex_8 : LinguisticExample :=
  { id := "erlewine2016_8"
    source := ⟨"erlewine-2016", "(8), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "X-at-ki-tz'ët."
    glossedTokens := [("X-at-ki-tz'ët", "COM-B2SG-A3PL-see")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "none"), ("layers", "CP"), ("subject", "3"), ("object", "2"), ("verb", "full")] }

def ex_9 : LinguisticExample :=
  { id := "erlewine2016_9"
    source := ⟨"erlewine-2016", "(9), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "X-a-wär."
    glossedTokens := [("X-a-wär", "COM-B2SG-sleep")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "intransitive"), ("extracted", "none"), ("layers", "CP"), ("subject", "2"), ("verb", "full")] }

def ex_14a : LinguisticExample :=
  { id := "erlewine2016_14a"
    source := ⟨"erlewine-2016", "(14a), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike x-∅-tj-ö ri wäy?"
    glossedTokens := [("Achike", "who"), ("x-∅-tj-ö", "COM-B3SG-eat-AF"), ("ri", "the"), ("wäy", "tortilla")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "3"), ("object", "3"), ("verb", "AF")] }

def ex_14b : LinguisticExample :=
  { id := "erlewine2016_14b"
    source := ⟨"erlewine-2016", "(14b), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike x-∅-u-tëj ri a Juan?"
    glossedTokens := [("Achike", "what"), ("x-∅-u-tëj", "COM-B3SG-A3SG-eat"), ("ri a Juan", "Juan")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "object"), ("layers", "CP"), ("landing", "1"), ("subject", "3"), ("object", "3"), ("verb", "full")] }

def ex_18a_emb : LinguisticExample :=
  { id := "erlewine2016_18a_emb"
    source := ⟨"erlewine-2016", "(18a), embedded clause, preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike n-∅-a-b'ij rat chin x-oj-tz'et-ö roj?"
    glossedTokens := [("Achike", "who"), ("n-∅-a-b'ij", "INC-B3SG-A2SG-say"), ("rat", "2sg"), ("chin", "that"), ("x-oj-tz'et-ö", "COM-B1PL-see-AF"), ("roj", "1pl")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "3"), ("object", "1"), ("verb", "AF")] }

def ex_18a_mat : LinguisticExample :=
  { id := "erlewine2016_18a_mat"
    source := ⟨"erlewine-2016", "(18a), matrix clause, preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike n-∅-a-b'ij rat chin x-oj-tz'et-ö roj?"
    glossedTokens := [("Achike", "who"), ("n-∅-a-b'ij", "INC-B3SG-A2SG-say"), ("rat", "2sg"), ("chin", "that"), ("x-oj-tz'et-ö", "COM-B1PL-see-AF"), ("roj", "1pl")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "none"), ("layers", "CP"), ("subject", "2"), ("object", "3"), ("verb", "full")] }

def ex_18b : LinguisticExample :=
  { id := "erlewine2016_18b"
    source := ⟨"erlewine-2016", "(18b), matrix clause, preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike n-a-b'i-n rat chin x-oj-tz'et-ö roj?"
    glossedTokens := [("Achike", "who"), ("n-a-b'i-n", "INC-B2SG-say-AF"), ("rat", "2sg"), ("chin", "that"), ("x-oj-tz'et-ö", "COM-B1PL-see-AF"), ("roj", "1pl")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "none"), ("layers", "CP"), ("subject", "2"), ("object", "3"), ("verb", "AF")] }

def ex_18c : LinguisticExample :=
  { id := "erlewine2016_18c"
    source := ⟨"erlewine-2016", "(18c), embedded clause, preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike n-∅-a-b'ij rat chin x-oj-r-tz'ët roj?"
    glossedTokens := [("Achike", "who"), ("n-∅-a-b'ij", "INC-B3SG-A2SG-say"), ("rat", "2sg"), ("chin", "that"), ("x-oj-r-tz'ët", "COM-B1PL-A3SG-see"), ("roj", "1pl")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "3"), ("object", "1"), ("verb", "full")] }

def ex_27b : LinguisticExample :=
  { id := "erlewine2016_27b"
    source := ⟨"erlewine-2016", "(27b), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike kanqtzij x-∅-u-tëj ri wäy?"
    glossedTokens := [("Achike", "who"), ("kanqtzij", "actually"), ("x-∅-u-tëj", "COM-B3SG-A3SG-eat"), ("ri", "the"), ("wäy", "tortilla")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "AdvP,CP"), ("landing", "2"), ("subject", "3"), ("object", "3"), ("verb", "full")] }

def ex_27c : LinguisticExample :=
  { id := "erlewine2016_27c"
    source := ⟨"erlewine-2016", "(27c), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike kanqtzij x-∅-tj-ö ri wäy?"
    glossedTokens := [("Achike", "who"), ("kanqtzij", "actually"), ("x-∅-tj-ö", "COM-B3SG-eat-AF"), ("ri", "the"), ("wäy", "tortilla")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "AdvP,CP"), ("landing", "2"), ("subject", "3"), ("object", "3"), ("verb", "AF")] }

def ex_28a : LinguisticExample :=
  { id := "erlewine2016_28a"
    source := ⟨"erlewine-2016", "(28a), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri achin ri n-∅-tj-ö wäy"
    glossedTokens := [("ri", "the"), ("achin", "man"), ("ri", "RC"), ("n-∅-tj-ö", "NONPAST-B3SG-eat-AF"), ("wäy", "tortilla")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "3"), ("object", "3"), ("verb", "AF")] }

def ex_28a_full : LinguisticExample :=
  { id := "erlewine2016_28a_full"
    source := ⟨"erlewine-2016", "(28a), full agreement, preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri achin ri n-∅-u-tëj wäy"
    glossedTokens := [("ri", "the"), ("achin", "man"), ("ri", "RC"), ("n-∅-u-tëj", "NONPAST-B3SG-A3SG-eat"), ("wäy", "tortilla")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "3"), ("object", "3"), ("verb", "full")] }

def ex_28b : LinguisticExample :=
  { id := "erlewine2016_28b"
    source := ⟨"erlewine-2016", "(28b), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri achin ri nojel mul n-∅-u-tëj wäy"
    glossedTokens := [("ri", "the"), ("achin", "man"), ("ri", "RC"), ("nojel", "all"), ("mul", "time"), ("n-∅-u-tëj", "NONPAST-B3SG-A3SG-eat"), ("wäy", "tortilla")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "AdvP,CP"), ("landing", "2"), ("subject", "3"), ("object", "3"), ("verb", "full")] }

def ex_28b_af : LinguisticExample :=
  { id := "erlewine2016_28b_af"
    source := ⟨"erlewine-2016", "(28b), AF, preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri achin ri nojel mul n-∅-tj-ö wäy"
    glossedTokens := [("ri", "the"), ("achin", "man"), ("ri", "RC"), ("nojel", "all"), ("mul", "time"), ("n-∅-tj-ö", "NONPAST-B3SG-eat-AF"), ("wäy", "tortilla")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "AdvP,CP"), ("landing", "2"), ("subject", "3"), ("object", "3"), ("verb", "AF")] }

def ex_29a : LinguisticExample :=
  { id := "erlewine2016_29a"
    source := ⟨"erlewine-2016", "(29a), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike k'o x-∅-tz'et-ö?"
    glossedTokens := [("Achike", "who"), ("k'o", "∃"), ("x-∅-tz'et-ö", "COM-B3SG-see-AF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP,CP"), ("landing", "1"), ("subject", "3"), ("object", "3"), ("verb", "AF")] }

def ex_29a_other : LinguisticExample :=
  { id := "erlewine2016_29a_other"
    source := ⟨"erlewine-2016", "(29a), other reading, preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike k'o x-∅-tz'et-ö?"
    glossedTokens := [("Achike", "who"), ("k'o", "∃"), ("x-∅-tz'et-ö", "COM-B3SG-see-AF")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP,CP"), ("landing", "2"), ("subject", "3"), ("object", "3"), ("verb", "AF")] }

def ex_29b : LinguisticExample :=
  { id := "erlewine2016_29b"
    source := ⟨"erlewine-2016", "(29b), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike k'o x-∅-u-tz'ët?"
    glossedTokens := [("Achike", "who"), ("k'o", "∃"), ("x-∅-u-tz'ët", "COM-B3SG-A3SG-see")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP,CP"), ("landing", "2"), ("subject", "3"), ("object", "3"), ("verb", "full")] }

def ex_29b_other : LinguisticExample :=
  { id := "erlewine2016_29b_other"
    source := ⟨"erlewine-2016", "(29b), other reading, preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike k'o x-∅-u-tz'ët?"
    glossedTokens := [("Achike", "who"), ("k'o", "∃"), ("x-∅-u-tz'ët", "COM-B3SG-A3SG-see")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP,CP"), ("landing", "1"), ("subject", "3"), ("object", "3"), ("verb", "full")] }

def ex_53 : LinguisticExample :=
  { id := "erlewine2016_53"
    source := ⟨"erlewine-2016", "(53), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Achike x-∅-a-tz'ët rat?"
    glossedTokens := [("Achike", "who"), ("x-∅-a-tz'ët", "COM-B3SG-A2SG-see"), ("rat", "you")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "3"), ("object", "2"), ("verb", "full")] }

def ex_64a : LinguisticExample :=
  { id := "erlewine2016_64a"
    source := ⟨"erlewine-2016", "(64a), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Ri a Pedro x-∅-u-ch'äk ri premio."
    glossedTokens := [("Ri a Pedro", "Pedro"), ("x-∅-u-ch'äk", "COM-B3SG-A3SG-win"), ("ri", "the"), ("premio", "prize")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP,TopP"), ("landing", "2"), ("subject", "3"), ("object", "3"), ("verb", "full")] }

def ex_64b : LinguisticExample :=
  { id := "erlewine2016_64b"
    source := ⟨"erlewine-2016", "(64b), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "(Ja) ri a Pedro x-∅-ch'ak-ö ri premio."
    glossedTokens := [("(Ja)", "FOC"), ("ri a Pedro", "Pedro"), ("x-∅-ch'ak-ö", "COM-B3SG-win-AF"), ("ri", "the"), ("premio", "prize")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "3"), ("object", "3"), ("verb", "AF")] }

def ex_72a : LinguisticExample :=
  { id := "erlewine2016_72a"
    source := ⟨"erlewine-2016", "(72a), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Ja rat x-at-axa-n ri achin."
    glossedTokens := [("Ja", "FOC"), ("rat", "you"), ("x-at-axa-n", "COM-B2SG-hear-AF"), ("ri", "the"), ("achin", "man")]
    context := ""
    judgment := .acceptable
    alternatives := [("Ja rat x-∅-axa-n ri achin.", .ungrammatical)]
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "2"), ("object", "3"), ("verb", "AF")] }

def ex_72b : LinguisticExample :=
  { id := "erlewine2016_72b"
    source := ⟨"erlewine-2016", "(72b), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Ja ri achin x-at-axa-n rat."
    glossedTokens := [("Ja", "FOC"), ("ri achin", "the man"), ("x-at-axa-n", "COM-B2SG-hear-AF"), ("rat", "you")]
    context := ""
    judgment := .acceptable
    alternatives := [("Ja ri achin x-∅-axa-n rat.", .ungrammatical)]
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "3"), ("object", "2"), ("verb", "AF")] }

def ex_77a : LinguisticExample :=
  { id := "erlewine2016_77a"
    source := ⟨"erlewine-2016", "(77a), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Ja yïn x-at-in-tz'ët rat."
    glossedTokens := [("Ja", "FOC"), ("yïn", "me"), ("x-at-in-tz'ët", "COM-B2SG-A1SG-see"), ("rat", "you")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "1"), ("object", "2"), ("verb", "full")] }

def ex_77b : LinguisticExample :=
  { id := "erlewine2016_77b"
    source := ⟨"erlewine-2016", "(77b), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Ja yïn x-i-tz'et-ö rat."
    glossedTokens := [("Ja", "FOC"), ("yïn", "me"), ("x-i-tz'et-ö", "COM-B1SG-see-AF"), ("rat", "you")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "1"), ("object", "2"), ("verb", "AF")] }

def ex_78a : LinguisticExample :=
  { id := "erlewine2016_78a"
    source := ⟨"erlewine-2016", "(78a), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Ja ri a Juan x-a-tz'et-ö rat."
    glossedTokens := [("Ja", "FOC"), ("ri a Juan", "Juan"), ("x-a-tz'et-ö", "COM-B2SG-see-AF"), ("rat", "you")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "3"), ("object", "2"), ("verb", "AF")] }

def ex_78b : LinguisticExample :=
  { id := "erlewine2016_78b"
    source := ⟨"erlewine-2016", "(78b), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Ja ri a Juan x-a-r-tz'ët rat."
    glossedTokens := [("Ja", "FOC"), ("ri a Juan", "Juan"), ("x-a-r-tz'ët", "COM-B2SG-A3SG-see"), ("rat", "you")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "3"), ("object", "2"), ("verb", "full")] }

def ex_79a : LinguisticExample :=
  { id := "erlewine2016_79a"
    source := ⟨"erlewine-2016", "(79a), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Ja yïn x-i-tz'et-ö ri a Juan."
    glossedTokens := [("Ja", "FOC"), ("yïn", "me"), ("x-i-tz'et-ö", "COM-B1SG-see-AF"), ("ri a Juan", "Juan")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "1"), ("object", "3"), ("verb", "AF")] }

def ex_79b : LinguisticExample :=
  { id := "erlewine2016_79b"
    source := ⟨"erlewine-2016", "(79b), preprint numbering"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Ja yïn x-∅-in-tz'ët ri a Juan."
    glossedTokens := [("Ja", "FOC"), ("yïn", "me"), ("x-∅-in-tz'ët", "COM-B3SG-A1SG-see"), ("ri a Juan", "Juan")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "1"), ("object", "3"), ("verb", "full")] }

def ex_87b : LinguisticExample :=
  { id := "erlewine2016_87b"
    source := ⟨"erlewine-2016", "(87b), preprint numbering"⟩
    reportedIn := none
    language := "popt1235"
    primaryText := "Mac xc-ach 7il-ni?"
    glossedTokens := [("Mac", "who"), ("xc-ach", "COM-B2SG"), ("7il-ni", "see-AF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "3"), ("object", "2"), ("verb", "AF")] }

def ex_88b : LinguisticExample :=
  { id := "erlewine2016_88b"
    source := ⟨"erlewine-2016", "(88b), preprint numbering"⟩
    reportedIn := none
    language := "popt1235"
    primaryText := "Ha-ch x-∅-7il-ni naj."
    glossedTokens := [("Ha-ch", "FOC-2sg"), ("x-∅-7il-ni", "COM-B3SG-see-AF"), ("naj", "3sg")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "2"), ("object", "3"), ("verb", "AF")] }

def ex_88c : LinguisticExample :=
  { id := "erlewine2016_88c"
    source := ⟨"erlewine-2016", "(88c), preprint numbering"⟩
    reportedIn := none
    language := "popt1235"
    primaryText := "Ha-ch x-∅-aw-(7)il naj."
    glossedTokens := [("Ha-ch", "FOC-2sg"), ("x-∅-aw-(7)il", "COM-B3SG-A2SG-see"), ("naj", "3sg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "2"), ("object", "3"), ("verb", "full")] }

def ex_91a : LinguisticExample :=
  { id := "erlewine2016_91a"
    source := ⟨"erlewine-2016", "(91a), preprint numbering"⟩
    reportedIn := none
    language := "west2635"
    primaryText := "Ja'-in ∅-ij-on-toj naj unin."
    glossedTokens := [("Ja'-in", "FOC-1sg"), ("∅-ij-on-toj", "B3SG-back.carry-AF-DIR"), ("naj unin", "boy")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "1"), ("object", "3"), ("verb", "AF")] }

def ex_91b : LinguisticExample :=
  { id := "erlewine2016_91b"
    source := ⟨"erlewine-2016", "(91b), preprint numbering"⟩
    reportedIn := none
    language := "west2635"
    primaryText := "Ja'-in ∅-w-ij-toj naj unin."
    glossedTokens := [("Ja'-in", "FOC-1sg"), ("∅-w-ij-toj", "B3SG-A1SG-back.carry-DIR"), ("naj unin", "boy")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "1"), ("object", "3"), ("verb", "full")] }

def ex_93 : LinguisticExample :=
  { id := "erlewine2016_93"
    source := ⟨"erlewine-2016", "(93), preprint numbering"⟩
    reportedIn := none
    language := "chol1282"
    primaryText := "Maxki tyi y-il-ä-yety?"
    glossedTokens := [("Maxki", "who"), ("tyi", "ASP"), ("y-il-ä-yety", "A3-see-TV-B2")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("extracted", "subject"), ("layers", "CP"), ("landing", "1"), ("subject", "3"), ("object", "2"), ("verb", "full")] }

def all : List LinguisticExample := [ex_8, ex_9, ex_14a, ex_14b, ex_18a_emb, ex_18a_mat, ex_18b, ex_18c, ex_27b, ex_27c, ex_28a, ex_28a_full, ex_28b, ex_28b_af, ex_29a, ex_29a_other, ex_29b, ex_29b_other, ex_53, ex_64a, ex_64b, ex_72a, ex_72b, ex_77a, ex_77b, ex_78a, ex_78b, ex_79a, ex_79b, ex_87b, ex_88b, ex_88c, ex_91a, ex_91b, ex_93]

end Erlewine2016.Examples
