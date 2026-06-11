import Linglib.Data.Examples.Schema

/-!
# `Steedman2000` — typed example data

Auto-generated from `Linglib/Data/Examples/Steedman2000.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Steedman2000.Examples`.
-/

namespace Steedman2000.Examples

open Data.Examples

def ex_96 : LinguisticExample :=
  { id := "steedman2000_96"
    source := ⟨"steedman-2000", "(96)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "(Weil) irgendjemand auf jeden gespannt ist."
    discourseSegments := []
    glossedTokens := [("(Weil)", "(since)"), ("irgendjemand", "someone"), ("auf", "on"), ("jeden", "everybody"), ("gespannt", "curious"), ("ist", "is")]
    translation := "Since someone is curious about everybody."
    context := "German verb-final subordinate clause; the quantified PP precedes the predicate-tense cluster."
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .acceptable)]
    paperFeatures := [("wordOrder", "verbRaising")]
    comment := "Marked (Ambiguous) in the book. Steedman credits the German contrast to Kayne (1998), following Bayer (1990, 1996). The verb-raising classification follows Steedman's compositional story: 'gespannt ist' can form by composition and 'auf jeden' then combines with the whole thing to take scope over the tensed verb."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_97 : LinguisticExample :=
  { id := "steedman2000_97"
    source := ⟨"steedman-2000", "(97)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "(Weil) jemand versucht hat jeden reinzulegen."
    discourseSegments := []
    glossedTokens := [("(Weil)", "(since)"), ("jemand", "someone"), ("versucht", "tried"), ("hat", "has"), ("jeden", "everyone"), ("reinzulegen", "cheat")]
    translation := "Since someone has tried to cheat everyone."
    context := "German verb-final subordinate clause; the quantified object follows the matrix verb cluster."
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .unacceptable)]
    paperFeatures := [("wordOrder", "verbProjectionRaising")]
    comment := "Marked (Unambiguous) in the book. Although 'versucht hat' can compose, it cannot combine with 'reinzulegen' until 'jeden' has combined with it, so 'jeden' cannot take scope over tense or inverse scope over 'jemand'."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_98a : LinguisticExample :=
  { id := "steedman2000_98a"
    source := ⟨"steedman-2000", "(98a)"⟩
    reportedIn := none
    language := "vlaa1240"
    primaryText := "(da) Jan vee boeken hee willen lezen"
    discourseSegments := []
    glossedTokens := [("(da)", "(that)"), ("Jan", "Jan"), ("vee", "many"), ("boeken", "books"), ("hee", "has"), ("willen", "wanted"), ("lezen", "read")]
    translation := "that Jan wanted to read many books"
    context := "West Flemish subordinate clause in the verb-raising word order."
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .acceptable)]
    paperFeatures := [("wordOrder", "verbRaising")]
    comment := "Marked (Ambiguous) in the book: 'many books' can take wider scope than 'wanted'. Steedman cites Haegeman and van Riemsdijk (1986, 444-445) and Haegeman (1992, 202) for verb-projection-raising effects on scope in West Flemish and Zurich German."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_98b : LinguisticExample :=
  { id := "steedman2000_98b"
    source := ⟨"steedman-2000", "(98b)"⟩
    reportedIn := none
    language := "vlaa1240"
    primaryText := "(da) Jan hee willen vee boeken lezen"
    discourseSegments := []
    glossedTokens := [("(da)", "(that)"), ("Jan", "Jan"), ("hee", "has"), ("willen", "wanted"), ("vee", "many"), ("boeken", "books"), ("lezen", "read")]
    translation := "that Jan wanted to read many books"
    context := "West Flemish subordinate clause in the verb-projection-raising word order."
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .unacceptable)]
    paperFeatures := [("wordOrder", "verbProjectionRaising")]
    comment := "Marked (Unambiguous) in the book; minimal pair with (98a)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_99a : LinguisticExample :=
  { id := "steedman2000_99a"
    source := ⟨"steedman-2000", "(99a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "(omdat) Jan veel liederen probeert te zingen"
    discourseSegments := []
    glossedTokens := [("(omdat)", "(because)"), ("Jan", "Jan"), ("veel", "many"), ("liederen", "songs"), ("probeert", "tries"), ("te", "to"), ("zingen", "sing")]
    translation := "because Jan tries to sing many songs"
    context := "Dutch subordinate clause with an equi verb, verb-raising word order."
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .acceptable)]
    paperFeatures := [("wordOrder", "verbRaising")]
    comment := "Marked (Ambiguous) in the book; Steedman's own extension of the pattern to Dutch equi verbs."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_99b : LinguisticExample :=
  { id := "steedman2000_99b"
    source := ⟨"steedman-2000", "(99b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "(omdat) Jan probeert veel liederen te zingen"
    discourseSegments := []
    glossedTokens := [("(omdat)", "(because)"), ("Jan", "Jan"), ("probeert", "tries"), ("veel", "many"), ("liederen", "songs"), ("te", "to"), ("zingen", "sing")]
    translation := "because Jan tries to sing many songs"
    context := "Dutch subordinate clause with an equi verb, verb-projection-raising word order."
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .unacceptable)]
    paperFeatures := [("wordOrder", "verbProjectionRaising")]
    comment := "Marked (Unambiguous) in the book; minimal pair with (99a)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_100a : LinguisticExample :=
  { id := "steedman2000_100a"
    source := ⟨"steedman-2000", "(100a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "(omdat) iemand alle liederen probeert te zingen"
    discourseSegments := []
    glossedTokens := [("(omdat)", "(because)"), ("iemand", "someone"), ("alle", "every"), ("liederen", "song"), ("probeert", "tries"), ("te", "to"), ("zingen", "sing")]
    translation := "because someone tries to sing every song"
    context := "Dutch subordinate clause, verb-raising word order, two quantified arguments."
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .acceptable)]
    paperFeatures := [("wordOrder", "verbRaising")]
    comment := "Marked (Ambiguous) in the book."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_100b : LinguisticExample :=
  { id := "steedman2000_100b"
    source := ⟨"steedman-2000", "(100b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "(omdat) iemand probeert alle liederen te zingen"
    discourseSegments := []
    glossedTokens := [("(omdat)", "(because)"), ("iemand", "someone"), ("probeert", "tries"), ("alle", "every"), ("liederen", "song"), ("te", "to"), ("zingen", "sing")]
    translation := "because someone tries to sing every song"
    context := "Dutch subordinate clause, verb-projection-raising word order, two quantified arguments."
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .unacceptable)]
    paperFeatures := [("wordOrder", "verbProjectionRaising")]
    comment := "Marked (Unambiguous) in the book: these verbs under this word order 'limit scope inversion similarly to Bayer's (97)'."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex_96, ex_97, ex_98a, ex_98b, ex_99a, ex_99b, ex_100a, ex_100b]

end Steedman2000.Examples
