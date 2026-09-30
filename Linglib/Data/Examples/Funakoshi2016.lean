module

public import Linglib.Data.Examples.Schema

/-!
# `Funakoshi2016` — typed example data

Auto-generated from `Linglib/Data/Examples/Funakoshi2016.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Funakoshi2016.Examples`.
-/

@[expose] public section

namespace Funakoshi2016.Examples

open Data.Examples

def ex15b : Datum :=
  { id := "funakoshi2016_ex15b"
    source := ⟨"funakoshi-2016", "(15b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "John-mo Δ araw-anak-atta"
    glossedTokens := [("John-mo", "John-also"), ("araw-anak-atta", "wash-NEG-PAST")]
    context := "Antecedent: Bill-wa teineini kuruma-o araw-anak-atta 'Bill didn't wash the car carefully'."
    judgment := .acceptable
    alternatives := []
    readings := [("null adjunct", .acceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "null"), ("subjectNull", "no"), ("available", "yes")] }

def ex16 : Datum :=
  { id := "funakoshi2016_ex16"
    source := ⟨"funakoshi-2016", "(16)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Bill-wa teineini kuruma-o arat-ta kedo, John-wa Δ araw-anak-atta"
    glossedTokens := [("Bill-wa", "Bill-TOP"), ("teineini", "carefully"), ("kuruma-o", "car-ACC"), ("arat-ta", "wash-PAST"), ("kedo,", "but"), ("John-wa", "John-TOP"), ("araw-anak-atta", "wash-NEG-PAST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("null adjunct", .acceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "null"), ("subjectNull", "no"), ("available", "yes")] }

def ex17b : Datum :=
  { id := "funakoshi2016_ex17b"
    source := ⟨"funakoshi-2016", "(17b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Hanako-wa Δ araw-anak-atta"
    glossedTokens := [("Hanako-wa", "Hanako-TOP"), ("araw-anak-atta", "wash-NEG-PAST")]
    context := "Taroo and Hanako washed their parents' cars to get allowance. Taroo was thorough in his work while Hanako was not. Antecedent: Taroo-wa teineini kuruma-o arat-ta 'Taroo washed the car carefully'."
    judgment := .acceptable
    alternatives := []
    readings := [("null adjunct", .acceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "null"), ("subjectNull", "no"), ("available", "yes")] }

def ex18b : Datum :=
  { id := "funakoshi2016_ex18b"
    source := ⟨"funakoshi-2016", "(18b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Hanako-wa Δ kak-ana-i."
    glossedTokens := [("Hanako-wa", "Hanako-TOP"), ("kak-ana-i.", "write-NEG-PRES")]
    context := "Taroo and Hanako are graduate students who often write papers. Taroo likes Microsoft Office while Hanako does not. Antecedent: Taroo-wa Word-de ronbun-o kak-u 'Taroo writes papers with Word'."
    judgment := .acceptable
    alternatives := []
    readings := [("null adjunct", .acceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "null"), ("subjectNull", "no"), ("available", "yes")] }

def ex19b : Datum :=
  { id := "funakoshi2016_ex19b"
    source := ⟨"funakoshi-2016", "(19b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Motiron Hanako-wa Δ kaw-ana-i."
    glossedTokens := [("Motiron", "of.course"), ("Hanako-wa", "Hanako-TOP"), ("kaw-ana-i.", "buy-NEG-PRES")]
    context := "Taroo and Hanako are faculty of a linguistics department and like comic books. Antecedent: Odoroitakotoni Taroo-wa kenkyuuhi-de manga-o ka-u 'Surprisingly, Taroo buys comic books with his research fund'."
    judgment := .acceptable
    alternatives := []
    readings := [("null adjunct", .acceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "null"), ("subjectNull", "no"), ("available", "yes")] }

def ex20b : Datum :=
  { id := "funakoshi2016_ex20b"
    source := ⟨"funakoshi-2016", "(20b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Hanako-wa Δ kuruma-o araw-anak-atta"
    glossedTokens := [("Hanako-wa", "Hanako-TOP"), ("kuruma-o", "car-ACC"), ("araw-anak-atta", "wash-NEG-PAST")]
    context := "Taroo and Hanako washed their parents' cars to get allowance. Taroo was thorough in his work while Hanako was not. Antecedent: Taroo-wa teineini kuruma-o arat-ta 'Taroo washed the car carefully'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex21b : Datum :=
  { id := "funakoshi2016_ex21b"
    source := ⟨"funakoshi-2016", "(21b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Hanako-wa Δ ronbun-o kak-ana-i."
    glossedTokens := [("Hanako-wa", "Hanako-TOP"), ("ronbun-o", "paper-ACC"), ("kak-ana-i.", "write-NEG-PRES")]
    context := "Taroo and Hanako are graduate students who often write papers. Taroo likes Microsoft Office while Hanako does not. Antecedent: Taroo-wa Word-de ronbun-o kak-u 'Taroo writes papers with Word'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex22b : Datum :=
  { id := "funakoshi2016_ex22b"
    source := ⟨"funakoshi-2016", "(22b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Motiron Hanako-wa Δ manga-o kaw-ana-i."
    glossedTokens := [("Motiron", "of.course"), ("Hanako-wa", "Hanako-TOP"), ("manga-o", "comic.book-ACC"), ("kaw-ana-i.", "buy-NEG-PRES")]
    context := "Taroo and Hanako are faculty of a linguistics department and like comic books. Antecedent: Odoroitakotoni Taroo-wa kenkyuuhi-de manga-o ka-u 'Surprisingly, Taroo buys comic books with his research fund'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex23b : Datum :=
  { id := "funakoshi2016_ex23b"
    source := ⟨"funakoshi-2016", "(23b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Hanako-mo Δ kuruma-o araw-anak-atta"
    glossedTokens := [("Hanako-mo", "Hanako-also"), ("kuruma-o", "car-ACC"), ("araw-anak-atta", "wash-NEG-PAST")]
    context := "Taroo and Hanako both did careless work. Antecedent: Taroo-wa teineini kuruma-o araw-anak-atta 'Taroo did not wash the car carefully'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex24b : Datum :=
  { id := "funakoshi2016_ex24b"
    source := ⟨"funakoshi-2016", "(24b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Hanako-mo Δ ronbun-o kak-ana-i."
    glossedTokens := [("Hanako-mo", "Hanako-also"), ("ronbun-o", "paper-ACC"), ("kak-ana-i.", "write-NEG-PRES")]
    context := "Taroo and Hanako do not like Microsoft Office. Antecedent: Taroo-wa Word-de ronbun-o kak-ana-i 'Taroo does not write papers with Word'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex25b : Datum :=
  { id := "funakoshi2016_ex25b"
    source := ⟨"funakoshi-2016", "(25b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Motiron Hanako-mo Δ manga-o kaw-ana-i."
    glossedTokens := [("Motiron", "of.course"), ("Hanako-mo", "Hanako-also"), ("manga-o", "comic.book-ACC"), ("kaw-ana-i.", "buy-NEG-PRES")]
    context := "Antecedent: Taroo-wa kenkyuuhi-de manga-o kaw-ana-i 'Taroo does not buy comic books with his research fund'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex26b : Datum :=
  { id := "funakoshi2016_ex26b"
    source := ⟨"funakoshi-2016", "(26b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Demo Hanako-wa Δ madogarasu-o huk-anak-atta."
    glossedTokens := [("Demo", "but"), ("Hanako-wa", "Hanako-TOP"), ("madogarasu-o", "window-ACC"), ("huk-anak-atta.", "wipe-NEG-PAST")]
    context := "Taroo and Hanako washed a car together: Taroo the body, then Hanako the windows. Taroo was thorough, Hanako not. Antecedent: Taroo-wa teineini syatai-o arat-ta 'Taroo washed the body of the car carefully'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex27b : Datum :=
  { id := "funakoshi2016_ex27b"
    source := ⟨"funakoshi-2016", "(27b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Demo sensei-wa Δ komento-o irete-kure-nanak-atta."
    glossedTokens := [("Demo", "but"), ("sensei-wa", "teacher-TOP"), ("komento-o", "comment-ACC"), ("irete-kure-nanak-atta.", "put-BEN-NEG-PAST")]
    context := "Taroo gave his paper to his advisor expecting comments with the Comments feature of Word, but the advisor does not like Microsoft Office. Antecedent: Taroo-wa Word-de ronbun-o kai-ta 'Taroo wrote the paper with Word'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex32b : Datum :=
  { id := "funakoshi2016_ex32b"
    source := ⟨"funakoshi-2016", "(32b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Ippou pro [Hanako-wa Δ yame-ta to] omottei-na-i."
    glossedTokens := [("Ippou", "on.the.other.hand"), ("pro", "pro"), ("[Hanako-wa", "Hanako-TOP"), ("yame-ta", "quit-PAST"), ("to]", "C"), ("omottei-na-i.", "think-NEG-PRES")]
    context := "Antecedent: Boku-wa [Taroo-wa [pro baka-da kara] kaisya-o yame-ta to] omottei-ru 'I think that Taroo quit the company because he was a fool'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "reason"), ("object", "null"), ("subjectNull", "no"), ("available", "no")] }

def ex39b : Datum :=
  { id := "funakoshi2016_ex39b"
    source := ⟨"funakoshi-2016", "(39b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Basu-wa Δ ko-nak-atta."
    glossedTokens := [("Basu-wa", "bus-TOP"), ("ko-nak-atta.", "come-NEG-PAST")]
    context := "Antecedent: Densya-wa zikandoorini ki-ta 'The train came on time'."
    judgment := .acceptable
    alternatives := []
    readings := [("null adjunct", .acceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "absent"), ("subjectNull", "no"), ("available", "yes")] }

def ex41b : Datum :=
  { id := "funakoshi2016_ex41b"
    source := ⟨"funakoshi-2016", "(41b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Hanako-wa Δ shukudai-o das-anak-atta."
    glossedTokens := [("Hanako-wa", "Hanako-TOP"), ("shukudai-o", "homework-ACC"), ("das-anak-atta.", "submit-NEG-PAST")]
    context := "Antecedent: Taroo-wa {zikandoorini / okurete} shukudai-o dasi-ta 'Taroo submitted the homework on time / late'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex43b : Datum :=
  { id := "funakoshi2016_ex43b"
    source := ⟨"funakoshi-2016", "(43b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Demo Δ madogarasu-o huk-anak-atta."
    glossedTokens := [("Demo", "but"), ("madogarasu-o", "window-ACC"), ("huk-anak-atta.", "wipe-NEG-PAST")]
    context := "Taroo washed his car, meaning to wipe the windows after the body, but felt tired. Antecedent: Taroo-wa teineini shatai-o arat-ta 'Taroo washed the body of the car carefully'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "yes"), ("available", "no")] }

def ex44b : Datum :=
  { id := "funakoshi2016_ex44b"
    source := ⟨"funakoshi-2016", "(44b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Demo Δ gakusei-no ronbun-o naos-ana-i."
    glossedTokens := [("Demo", "but"), ("gakusei-no", "student-GEN"), ("ronbun-o", "paper-ACC"), ("naos-ana-i.", "revise-NEG-PRES")]
    context := "Taroo writes his own papers and looks at his students' papers every day. Antecedent: Taroo-wa Word-de zibun-no ronbun-o kak-u 'Taroo writes his own papers with Word'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "yes"), ("available", "no")] }

def ex51b : Datum :=
  { id := "funakoshi2016_ex51b"
    source := ⟨"funakoshi-2016", "(51b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Kuruma-o Hanako-wa Δ araw-anak-atta"
    glossedTokens := [("Kuruma-o", "car-ACC"), ("Hanako-wa", "Hanako-TOP"), ("araw-anak-atta", "wash-NEG-PAST")]
    context := "Antecedent: Kuruma-o Taroo-wa teineini arat-ta 'The car, Taroo washed carefully'. Taroo and Hanako washed their parents' cars to get allowance. Taroo was thorough in his work while Hanako was not. Antecedent: Taroo-wa teineini kuruma-o arat-ta 'Taroo washed the car carefully'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex52b : Datum :=
  { id := "funakoshi2016_ex52b"
    source := ⟨"funakoshi-2016", "(52b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Kuruma-o Hanako-mo Δ araw-anak-atta"
    glossedTokens := [("Kuruma-o", "car-ACC"), ("Hanako-mo", "Hanako-also"), ("araw-anak-atta", "wash-NEG-PAST")]
    context := "Both did careless work. Antecedent: Kuruma-o Taroo-wa teineini araw-anak-atta."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex53b : Datum :=
  { id := "funakoshi2016_ex53b"
    source := ⟨"funakoshi-2016", "(53b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Demo madogarasu-o Hanako-wa Δ huk-anak-atta."
    glossedTokens := [("Demo", "but"), ("madogarasu-o", "window-ACC"), ("Hanako-wa", "Hanako-TOP"), ("huk-anak-atta.", "wipe-NEG-PAST")]
    context := "Antecedent: Syatai-o Taroo-wa teineini arat-ta 'The body of the car, Taroo washed carefully'."
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex55b : Datum :=
  { id := "funakoshi2016_ex55b"
    source := ⟨"funakoshi-2016", "(55b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Iya, boku-wa Δ ATTI-no kuruma-o araw-anak-attanda."
    glossedTokens := [("Iya,", "no"), ("boku-wa", "I-TOP"), ("ATTI-no", "that-GEN"), ("kuruma-o", "car-ACC"), ("araw-anak-attanda.", "wash-NEG-PAST")]
    context := "Taroo ordered Ziroo to wash his two cars clean; Ziroo washed one sloppily and the other carefully. Taroo: Kimi-wa teineini kotti-no kuruma-o araw-anak-atta daro? 'You didn't wash this car carefully, did you?'"
    judgment := .acceptable
    alternatives := []
    readings := [("null adjunct", .acceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "focused"), ("subjectNull", "no"), ("available", "yes")] }

def ex55b2 : Datum :=
  { id := "funakoshi2016_ex55b2"
    source := ⟨"funakoshi-2016", "(55b')"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Iya, ATTI-no kuruma-o boku-wa Δ araw-anak-attanda."
    glossedTokens := [("Iya,", "no"), ("ATTI-no", "that-GEN"), ("kuruma-o", "car-ACC"), ("boku-wa", "I-TOP"), ("araw-anak-attanda.", "wash-NEG-PAST")]
    context := "Taroo ordered Ziroo to wash his two cars clean; Ziroo washed one sloppily and the other carefully. Taroo: Kimi-wa teineini kotti-no kuruma-o araw-anak-atta daro? 'You didn't wash this car carefully, did you?'"
    judgment := .acceptable
    alternatives := []
    readings := [("null adjunct", .acceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "focused"), ("subjectNull", "no"), ("available", "yes")] }

def ex56b : Datum :=
  { id := "funakoshi2016_ex56b"
    source := ⟨"funakoshi-2016", "(56b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Iya, boku-wa kono kuruma-WA araw-anak-attayo."
    glossedTokens := [("Iya,", "no"), ("boku-wa", "I-TOP"), ("kono", "this"), ("kuruma-WA", "car-CONT"), ("araw-anak-attayo.", "wash-NEG-PAST")]
    context := "Same scenario. Taroo: Kimi-wa teineini kono kuruma-o arat-ta no? 'Did you wash this car carefully?'"
    judgment := .acceptable
    alternatives := []
    readings := [("null adjunct", .acceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "focused"), ("subjectNull", "no"), ("available", "yes")] }

def ex56b2 : Datum :=
  { id := "funakoshi2016_ex56b2"
    source := ⟨"funakoshi-2016", "(56b')"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Iya, kono kuruma-WA boku-wa araw-anak-attayo."
    glossedTokens := [("Iya,", "no"), ("kono", "this"), ("kuruma-WA", "car-CONT"), ("boku-wa", "I-TOP"), ("araw-anak-attayo.", "wash-NEG-PAST")]
    context := "Same scenario. Taroo: Kimi-wa teineini kono kuruma-o arat-ta no?"
    judgment := .acceptable
    alternatives := []
    readings := [("null adjunct", .acceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "focused"), ("subjectNull", "no"), ("available", "yes")] }

def ex57b : Datum :=
  { id := "funakoshi2016_ex57b"
    source := ⟨"funakoshi-2016", "(57b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Un, boku-wa Δ kotti-no kuruma-o araw-anak-attayo."
    glossedTokens := [("Un,", "yes"), ("boku-wa", "I-TOP"), ("kotti-no", "this-GEN"), ("kuruma-o", "car-ACC"), ("araw-anak-attayo.", "wash-NEG-PAST")]
    context := "Taroo ordered Ziroo to wash his two cars clean; Ziroo washed one sloppily and the other carefully. Taroo: Kimi-wa teineini kotti-no kuruma-o araw-anak-atta daro? 'You didn't wash this car carefully, did you?'"
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex57b2 : Datum :=
  { id := "funakoshi2016_ex57b2"
    source := ⟨"funakoshi-2016", "(57b')"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Un, kotti-no kuruma-o boku-wa Δ araw-anak-attayo."
    glossedTokens := [("Un,", "yes"), ("kotti-no", "this-GEN"), ("kuruma-o", "car-ACC"), ("boku-wa", "I-TOP"), ("araw-anak-attayo.", "wash-NEG-PAST")]
    context := "Taroo ordered Ziroo to wash his two cars clean; Ziroo washed one sloppily and the other carefully. Taroo: Kimi-wa teineini kotti-no kuruma-o araw-anak-atta daro? 'You didn't wash this car carefully, did you?'"
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex58b : Datum :=
  { id := "funakoshi2016_ex58b"
    source := ⟨"funakoshi-2016", "(58b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Iya, boku-wa kono kuruma-o araw-anak-attayo."
    glossedTokens := [("Iya,", "no"), ("boku-wa", "I-TOP"), ("kono", "this"), ("kuruma-o", "car-ACC"), ("araw-anak-attayo.", "wash-NEG-PAST")]
    context := "Same scenario. Taroo: Kimi-wa teineini kono kuruma-o arat-ta no?"
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def ex58b2 : Datum :=
  { id := "funakoshi2016_ex58b2"
    source := ⟨"funakoshi-2016", "(58b')"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Iya, kono kuruma-o boku-wa araw-anak-attayo."
    glossedTokens := [("Iya,", "no"), ("kono", "this"), ("kuruma-o", "car-ACC"), ("boku-wa", "I-TOP"), ("araw-anak-attayo.", "wash-NEG-PAST")]
    context := "Same scenario. Taroo: Kimi-wa teineini kono kuruma-o arat-ta no?"
    judgment := .unacceptable
    alternatives := []
    readings := [("null adjunct", .unacceptable)]
    paperFeatures := [("adjunct", "vp"), ("object", "overt"), ("subjectNull", "no"), ("available", "no")] }

def all : List Datum := [ex15b, ex16, ex17b, ex18b, ex19b, ex20b, ex21b, ex22b, ex23b, ex24b, ex25b, ex26b, ex27b, ex32b, ex39b, ex41b, ex43b, ex44b, ex51b, ex52b, ex53b, ex55b, ex55b2, ex56b, ex56b2, ex57b, ex57b2, ex58b, ex58b2]

end Funakoshi2016.Examples
