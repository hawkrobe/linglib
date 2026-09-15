import Linglib.Data.Examples.Schema

/-!
# `Zimmermann2008` — typed example data

Auto-generated from `Linglib/Data/Examples/Zimmermann2008.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Zimmermann2008.Examples`.
-/

namespace Zimmermann2008.Examples

open Data.Examples

def ex_11a : LinguisticExample :=
  { id := "zimmermann2008_11a"
    source := ⟨"zimmermann-2008", "(11a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Audù bà-i sàyi hùulaa à kàasuwaa ba"
    discourseSegments := []
    glossedTokens := [("Audù", "Audu"), ("bà-i", "NEG-3SG"), ("sàyi", "buy"), ("hùulaa", "cap"), ("à", "at"), ("kàasuwaa", "market"), ("ba", "NEG")]
    translation := "Audu didn't buy a cap in the market."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "bare"), ("scope", "NEG > ∃")]
    comment := "No reading on which a certain cap escapes the negation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12a : LinguisticExample :=
  { id := "zimmermann2008_12a"
    source := ⟨"zimmermann-2008", "(12a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "manòomii bà-i zoo ba"
    discourseSegments := []
    glossedTokens := [("manòomii", "farmer"), ("bà-i", "NEG-3SG"), ("zoo", "come"), ("ba", "NEG")]
    translation := "Farmers didn't come."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "bare"), ("scope", "NEG > ∃")]
    comment := "Equivalent to no farmer came, although the subject precedes the negation marker."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_13a : LinguisticExample :=
  { id := "zimmermann2008_13a"
    source := ⟨"zimmermann-2008", "(13a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "mutàanee bà sù tàfi kàasuwaa ba"
    discourseSegments := []
    glossedTokens := [("mutàanee", "people"), ("bà", "NEG"), ("sù", "3PL"), ("tàfi", "go"), ("kàasuwaa", "market"), ("ba", "NEG")]
    translation := "People didn't go to the market."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "bare"), ("scope", "NEG > ∃")]
    comment := "Cannot describe a situation where some people went and others did not."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_63a : LinguisticExample :=
  { id := "zimmermann2008_63a"
    source := ⟨"zimmermann-2008", "(63a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "sai wani yaaròo yaa cêe"
    discourseSegments := []
    glossedTokens := [("sai", "then"), ("wani", "some"), ("yaaròo", "boy"), ("yaa", "3SG.PERF"), ("cêe", "say")]
    translation := "then a/some boy said …"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "wani"), ("function", "discourse-introducing")]
    comment := "From the Sauna Jac narrative."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_64 : LinguisticExample :=
  { id := "zimmermann2008_64"
    source := ⟨"zimmermann-2008", "(64)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "wasu sun zoo, wasu bà sù zoo ba"
    discourseSegments := []
    glossedTokens := [("wasu", "some"), ("sun", "3PL.PERF"), ("zoo", "come"), ("wasu", "some"), ("bà", "NEG"), ("sù", "3PL.SUBJ"), ("zoo", "come"), ("ba", "NEG")]
    translation := "Some came, others didn't."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "wasu"), ("reading", "partitive")]
    comment := "Cited from Cowan and Schuh (1976)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_65a : LinguisticExample :=
  { id := "zimmermann2008_65a"
    source := ⟨"zimmermann-2008", "(65a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Wani yaa zoo?"
    discourseSegments := []
    glossedTokens := [("Wani", "some/any"), ("yaa", "3SG.PERF"), ("zoo", "come")]
    translation := "Did someone come? / Did anyone come?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "wani"), ("clause", "polar question")]
    comment := "Ambiguous between an existential and a free-choice reading; cited from Cowan and Schuh (1976)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_69a : LinguisticExample :=
  { id := "zimmermann2008_69a"
    source := ⟨"zimmermann-2008", "(69a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "bà-n ga wani ba"
    discourseSegments := []
    glossedTokens := [("bà-n", "NEG-1SG.SUBJ"), ("ga", "see"), ("wani", "someone"), ("ba", "NEG")]
    translation := "I didn't see anyone. / There is someone I didn't see."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "wani"), ("position", "object"), ("scope", "ambiguous")]
    comment := "The negative existential reading is preferred; cited from Bargery."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_69b : LinguisticExample :=
  { id := "zimmermann2008_69b"
    source := ⟨"zimmermann-2008", "(69b)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Muusaa bà-i kiraa wani àbookii lìyaafaa ba"
    discourseSegments := []
    glossedTokens := [("Muusaa", "Musa"), ("bà-i", "NEG-3SG.SUBJ"), ("kiraa", "invite"), ("wani", "some"), ("àbookii", "friend"), ("lìyaafaa", "ceremony"), ("ba", "NEG")]
    translation := "Musa did not invite any friends. / There is some friend Musa didn't invite."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "wani"), ("position", "object"), ("scope", "ambiguous")]
    comment := "Here the some-not reading is preferred."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_70 : LinguisticExample :=
  { id := "zimmermann2008_70"
    source := ⟨"zimmermann-2008", "(70)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "wasu bà sù zoo ba"
    discourseSegments := []
    glossedTokens := [("wasu", "some.PL"), ("bà", "NEG"), ("sù", "3PL"), ("zoo", "come"), ("ba", "NEG")]
    translation := "Some did not come."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "wasu"), ("position", "subject"), ("scope", "∃ > NEG only")]
    comment := "No negative existential reading: the opposite of bare subject indefinites."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_71 : LinguisticExample :=
  { id := "zimmermann2008_71"
    source := ⟨"zimmermann-2008", "(71)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "baabù wan dà ya zoo"
    discourseSegments := []
    glossedTokens := [("baabù", "not.exist"), ("wan", "someone"), ("dà", "REL"), ("ya", "3SG.PERF.REL"), ("zoo", "come")]
    translation := "Nobody came."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "negative existential relative")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_73 : LinguisticExample :=
  { id := "zimmermann2008_73"
    source := ⟨"zimmermann-2008", "(73)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "bà-n ga koo-waa ba"
    discourseSegments := []
    glossedTokens := [("bà-n", "NEG-1SG.SUBJ"), ("ga", "see"), ("koo-waa", "DISJ-who"), ("ba", "NEG")]
    translation := "I didn't see anyone."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "koo+wh"), ("negation", "VP"), ("scope", "negative existential only")]
    comment := "The not-everyone reading is unavailable."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_74a : LinguisticExample :=
  { id := "zimmermann2008_74a"
    source := ⟨"zimmermann-2008", "(74a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "bàa koo-waa kèe sô-n wannàn jàriidàa ba"
    discourseSegments := []
    glossedTokens := [("bàa", "NEG"), ("koo-waa", "DISJ-who"), ("kèe", "PROG.REL"), ("sô-n", "like-LINK"), ("wannàn", "this"), ("jàriidàa", "newspaper"), ("ba", "NEG")]
    translation := "Not everyone likes this newspaper."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "koo+wh"), ("negation", "sentential"), ("scope", "negative universal only")]
    comment := "Cited from Newman (2000)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_75 : LinguisticExample :=
  { id := "zimmermann2008_75"
    source := ⟨"zimmermann-2008", "(75)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "koo-waa bà-i ci jarràbâawaa ba"
    discourseSegments := []
    glossedTokens := [("koo-waa", "DISJ-who"), ("bà-i", "NEG-3SG.SUBJ"), ("ci", "eat"), ("jarràbâawaa", "exam"), ("ba", "NEG")]
    translation := "Everybody did not pass the test."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "koo+wh"), ("position", "subject")]
    comment := "A subject koo+wh cannot take syntactic scope over VP-negation; cited from Newman (2000)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_78 : LinguisticExample :=
  { id := "zimmermann2008_78"
    source := ⟨"zimmermann-2008", "(78)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "koo-wànè ɗàalìbii nèe bà-i ci jarràbâawaa ba"
    discourseSegments := []
    glossedTokens := [("koo-wànè", "DISJ-which"), ("ɗàalìbii", "student"), ("nèe", "PRT"), ("bà-i", "NEG-3SG"), ("ci", "eat"), ("jarràbâawaa", "exam"), ("ba", "NEG")]
    translation := "EACH student didn't pass the exam."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "koo+wh"), ("position", "subject"), ("focus", "yes")]
    comment := "Focusing rescues the subject universal over negation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_85a : LinguisticExample :=
  { id := "zimmermann2008_85a"
    source := ⟨"zimmermann-2008", "(85a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "duk faasinjoojî-n"
    discourseSegments := []
    glossedTokens := [("duk", "all"), ("faasinjoojî-n", "passengers-DEF")]
    translation := "all the passengers"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "duk"), ("order", "prenominal")]
    comment := "Alternates with postnominal faasinjojî-n dukà; cited from Newman (2000)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_86 : LinguisticExample :=
  { id := "zimmermann2008_86"
    source := ⟨"zimmermann-2008", "(86)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "naa ga duk ɗàalìbii"
    discourseSegments := []
    glossedTokens := [("naa", "1SG.PERF"), ("ga", "see"), ("duk", "all"), ("ɗàalìbii", "student")]
    translation := "I saw all the students."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "duk"), ("restrictor", "singular")]
    comment := "Duk requires a plural or mass noun phrase."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_89a : LinguisticExample :=
  { id := "zimmermann2008_89a"
    source := ⟨"zimmermann-2008", "(89a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "koo-wànè ɗàalìbii yáa tàaru à gàba-n makarantaa"
    discourseSegments := []
    glossedTokens := [("koo-wànè", "DISJ-which"), ("ɗàalìbii", "student"), ("yáa", "3SG.PERF"), ("tàaru", "gather"), ("à", "at"), ("gàba-n", "front-LINK"), ("makarantaa", "school")]
    translation := "Each student gathered in front of the school."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "koo+wh"), ("predicate", "collective")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_90a : LinguisticExample :=
  { id := "zimmermann2008_90a"
    source := ⟨"zimmermann-2008", "(90a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "duk ɗàalìbâ-n sun tàaru à gàba-n makarantaa"
    discourseSegments := []
    glossedTokens := [("duk", "all"), ("ɗàalìbâ-n", "students-DEF"), ("sun", "3PL.PERF"), ("tàaru", "gather"), ("à", "at"), ("gàba-n", "front-LINK"), ("makarantaa", "school")]
    translation := "All the students gathered in front of the school."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "duk"), ("predicate", "collective")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_91a : LinguisticExample :=
  { id := "zimmermann2008_91a"
    source := ⟨"zimmermann-2008", "(91a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "bà-n karàntà duk lìttàttàafâ-n ba"
    discourseSegments := []
    glossedTokens := [("bà-n", "NEG-1SG"), ("karàntà", "read"), ("duk", "all"), ("lìttàttàafâ-n", "books-DEF"), ("ba", "NEG")]
    translation := "I didn't read all the books."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "duk"), ("negation", "VP"), ("scope", "negative universal")]
    comment := "Cited from Jaggar (2001)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_91b : LinguisticExample :=
  { id := "zimmermann2008_91b"
    source := ⟨"zimmermann-2008", "(91b)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "bàa duk bàaƙii su-kà zoo ba"
    discourseSegments := []
    glossedTokens := [("bàa", "NEG"), ("duk", "all"), ("bàaƙii", "guests"), ("su-kà", "3PL-PERF.REL"), ("zoo", "come"), ("ba", "NEG")]
    translation := "Not all the guests have come."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "duk"), ("negation", "sentential"), ("scope", "negative universal")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_11a, ex_12a, ex_13a, ex_63a, ex_64, ex_65a, ex_69a, ex_69b, ex_70, ex_71, ex_73, ex_74a, ex_75, ex_78, ex_85a, ex_86, ex_89a, ex_90a, ex_91a, ex_91b]

end Zimmermann2008.Examples
