import Linglib.Data.Examples.Schema

/-!
# `TsiliaZhao2026` — typed example data

Auto-generated from `Linglib/Data/Examples/TsiliaZhao2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace TsiliaZhao2026.Examples`.
-/

namespace TsiliaZhao2026.Examples

open Data.Examples

def ex_6 : LinguisticExample :=
  { id := "tsiliazhao2026_6"
    source := ⟨"tsilia-zhao-2026", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is feeling sick then."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary is feeling sick then."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "present"), ("environment", "root"), ("then", "incompatible")]
    comment := "In a root clause the perspective is the utterance time, which the present overlaps and *then* must avoid; the past and future of (7) admit *then*."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8 : LinguisticExample :=
  { id := "tsiliazhao2026_8"
    source := ⟨"tsilia-zhao-2026", "(8)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "To 2000, o Yanis iksere oti i Maria ine egkios."
    discourseSegments := []
    glossedTokens := []
    translation := "In 2000, Yanis knew that Maria was (lit. is) pregnant."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("shifted present: the pregnancy overlaps the knowledge in 2000", .acceptable)]
    paperFeatures := [("matrix", "past"), ("environment", "attitude report"), ("embedded", "present"), ("shifted", "yes")]
    comment := "The 2000, det Yanis know.PAST that the Maria be.PRES pregnant: the embedded present refers to a past time overlapping the matrix attitude, tense shift."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_11 : LinguisticExample :=
  { id := "tsiliazhao2026_11"
    source := ⟨"tsilia-zhao-2026", "(11)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "To 2000, o Yanis iksere oti i Maria ine egkios tote."
    discourseSegments := []
    glossedTokens := []
    translation := "In 2000, Yanis knew that Maria was (lit. is) pregnant then."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "past"), ("environment", "attitude report"), ("embedded", "present"), ("shifted", "yes"), ("then", "incompatible")]
    comment := "The ⌈then⌉-present puzzle: the shifted present does not refer to the utterance time, yet *tote* remains incompatible with it; from Tsilia (2021)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_9 : LinguisticExample :=
  { id := "tsiliazhao2026_9"
    source := ⟨"tsilia-zhao-2026", "(9)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "Lifney alpayim šana, Yosef xašav še Miriam ohevet oto az."
    discourseSegments := []
    glossedTokens := []
    translation := "2,000 years ago, Yosef thought that Miriam loved (lit. loves) him then."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "past"), ("environment", "attitude report"), ("embedded", "present"), ("shifted", "yes"), ("then", "incompatible")]
    comment := "Before 2,000 year, Yosef think.PAST that Miriam love.PRES him then; from Ogihara and Sharvit (2012), who note that not all speakers reject it."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10 : LinguisticExample :=
  { id := "tsiliazhao2026_10"
    source := ⟨"tsilia-zhao-2026", "(10)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "V 2016 godu Tanja skazala, čto Putin togda ∅ prezident Rossii."
    discourseSegments := []
    glossedTokens := []
    translation := "In 2016 Tanja said that Putin was (lit. is) the president of Russia then."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "past"), ("environment", "attitude report"), ("embedded", "present"), ("shifted", "yes"), ("then", "incompatible")]
    comment := "in 2016 year Tanja say.PAST that Putin then be.PRES president.NOM Russia.GEN; from Vostrikova (2019)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_18 : LinguisticExample :=
  { id := "tsiliazhao2026_18"
    source := ⟨"tsilia-zhao-2026", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A month ago, John found out that Mary loves him."
    discourseSegments := []
    glossedTokens := []
    translation := "A month ago, John found out that Mary loves him."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("double access: Mary loves John at the utterance time and at the finding out", .acceptable)]
    paperFeatures := [("matrix", "past"), ("environment", "attitude report"), ("embedded", "present"), ("shifted", "no")]
    comment := "The English present under past never shifts: it indicates the utterance time, and (19) with *two thousand years ago* is infelicitous; *then* is impossible, (20)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_21 : LinguisticExample :=
  { id := "tsiliazhao2026_21"
    source := ⟨"tsilia-zhao-2026", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In his childhood, Joseph met a woman who loves traveling then."
    discourseSegments := []
    glossedTokens := []
    translation := "In his childhood, Joseph met a woman who loves traveling then."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "past"), ("environment", "relative clause"), ("embedded", "present"), ("shifted", "no"), ("then", "incompatible")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_25 : LinguisticExample :=
  { id := "tsiliazhao2026_25"
    source := ⟨"tsilia-zhao-2026", "(25)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Prin 20 chronia o Pavlos sinerghastike me enan andra pu ine proedros tote."
    discourseSegments := []
    glossedTokens := []
    translation := "20 years ago, Pavlos collaborated with a man who is president (now)."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "past"), ("environment", "relative clause"), ("embedded", "present"), ("shifted", "no"), ("then", "incompatible")]
    comment := "Greek, Hebrew, (26), and Russian, (27), do not shift the present in relative clauses under past, an extensional environment with no operator to bind the index."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_28 : LinguisticExample :=
  { id := "tsiliazhao2026_28"
    source := ⟨"tsilia-zhao-2026", "(28)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "ninenn mae, Yusuke-wa Yukiko-ga tooji ninnshinn shite-iru to shitteita."
    discourseSegments := []
    glossedTokens := []
    translation := "2 years ago, Yusuke knew that Yukiko was (lit. is) pregnant then."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "past"), ("environment", "attitude report"), ("embedded", "present"), ("shifted", "yes"), ("then", "incompatible")]
    comment := "2-years before Yusuke-TOP Yukiko-NOM then pregnant be-PRES with know.PAST: Japanese shifts the present under past in attitude reports and, uniquely, in relative clauses, (29), and the puzzle arises in both."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_29 : LinguisticExample :=
  { id := "tsiliazhao2026_29"
    source := ⟨"tsilia-zhao-2026", "(29)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "ninenn mae, Yusuke-wa tooji seifu de hatarai-te-iru hito to renkei o hakat-te-ita."
    discourseSegments := []
    glossedTokens := []
    translation := "Two years ago, Yusuke collaborated with a man who was (lit. is) president then."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "past"), ("environment", "relative clause"), ("embedded", "present"), ("shifted", "yes"), ("then", "incompatible")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_30a : LinguisticExample :=
  { id := "tsiliazhao2026_30a"
    source := ⟨"tsilia-zhao-2026", "(30a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "To 2030, i Maria tha pi oti ine sti filaki tote."
    discourseSegments := []
    glossedTokens := []
    translation := "In 2030, Maria will say that she is in jail (in 2030) then."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "future"), ("environment", "attitude report"), ("embedded", "present"), ("shifted", "yes"), ("then", "incompatible")]
    comment := "Under future every surveyed language shifts the present, in attitude reports and relative clauses alike, since WOLL binds an index; Greek, Hebrew, (30b), and Russian, (30c), show the puzzle there too."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_30d : LinguisticExample :=
  { id := "tsiliazhao2026_30d"
    source := ⟨"tsilia-zhao-2026", "(30d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In 2030, John will say that he is in jail then."
    discourseSegments := []
    glossedTokens := []
    translation := "In 2030, John will say that he is in jail then."
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "future"), ("environment", "attitude report"), ("embedded", "present"), ("shifted", "deleted"), ("then", "variation")]
    comment := "English tolerates *then* with the present under future, for some speakers here and generally in relative clauses, (31d): the present is deleted by sequence of tense under WOLL's PRES rather than shifted, (92)–(93)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_31a : LinguisticExample :=
  { id := "tsiliazhao2026_31a"
    source := ⟨"tsilia-zhao-2026", "(31a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "To 2030, i Zoi tha ine pantremeni me kapion pu ine tote sti filaki."
    discourseSegments := []
    glossedTokens := []
    translation := "In 2030, Zoe will be married to someone who is in jail then."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "future"), ("environment", "relative clause"), ("embedded", "present"), ("shifted", "yes"), ("then", "incompatible")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_32 : LinguisticExample :=
  { id := "tsiliazhao2026_32"
    source := ⟨"tsilia-zhao-2026", "(32)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Tooji ai-mashou."
    discourseSegments := []
    glossedTokens := []
    translation := "See you then."
    context := "Two friends are making plans to go to the movies on Saturday; one says this before they leave."
    judgment := .ungrammatical
    alternatives := [("Sonotoki ai-mashou.", .acceptable)]
    readings := []
    paperFeatures := [("then", "past-oriented only")]
    comment := "Japanese *tōji* is used only with past expressions, so the present-under-future cells are not applicable for Japanese."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_38 : LinguisticExample :=
  { id := "tsiliazhao2026_38"
    source := ⟨"tsilia-zhao-2026", "(38)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "lifney alpayim šana, Yosef xašav še Miriam ahava oto az."
    discourseSegments := []
    glossedTokens := []
    translation := "Two thousand years ago Yosef believed that Miriam loved him then."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous: the love overlaps the belief", .acceptable)]
    paperFeatures := [("matrix", "past"), ("environment", "attitude report"), ("embedded", "past"), ("then", "compatible")]
    comment := "An embedded past with the same simultaneous reference as the shifted present admits *az*, so the puzzle is not a restriction on the reference; Russian (39) likewise."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_48 : LinguisticExample :=
  { id := "tsiliazhao2026_48"
    source := ⟨"tsilia-zhao-2026", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A week ago, John said that in ten days he would say to his girlfriend that they were meeting then for the last time."
    discourseSegments := []
    glossedTokens := []
    translation := "A week ago, John said that in ten days he would say to his girlfriend that they were meeting then for the last time."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("the meeting is at the time of the future saying, three days from now", .acceptable)]
    paperFeatures := [("matrix", "past"), ("environment", "attitude report"), ("embedded", "deleted past"), ("then", "compatible")]
    comment := "The most deeply embedded past is past relative to no time in the sentence, so it is deleted; deleted tense carries no perspectival presupposition and *then* is compatible with it, (89a); Greek (49) likewise."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_99 : LinguisticExample :=
  { id := "tsiliazhao2026_99"
    source := ⟨"tsilia-zhao-2026", "(99)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "To 1960, o Yanis iksere oti i Maria ine omorfi tora."
    discourseSegments := []
    glossedTokens := []
    translation := "In 1960, Yanis knew that Maria was (lit. is) beautiful now."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("matrix", "past"), ("environment", "attitude report"), ("embedded", "present"), ("shifted", "yes"), ("indexical", "unshifted")]
    comment := "The present shifts but *tora* 'now' does not, and Hebrew *axšav* likewise, (100): the perspective is not the context's time."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_6, ex_8, ex_11, ex_9, ex_10, ex_18, ex_21, ex_25, ex_28, ex_29, ex_30a, ex_30d, ex_31a, ex_32, ex_38, ex_48, ex_99]

end TsiliaZhao2026.Examples
