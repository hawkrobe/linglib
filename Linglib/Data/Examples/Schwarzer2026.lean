module

public import Linglib.Data.Examples.Schema

/-!
# `Schwarzer2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Schwarzer2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Schwarzer2026.Examples`.
-/

@[expose] public section

namespace Schwarzer2026.Examples

open Data.Examples

def ex11a : LinguisticExample :=
  { id := "schwarzer2026_ex11a"
    source := ⟨"schwarzer-2026", "(11a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Stadt beendet zum Jahreswechsel dass für Neugeborene ein Baum gepflanzt wird."
    discourseSegments := []
    glossedTokens := [("Die", "the"), ("Stadt", "city"), ("beendet", "ends"), ("zum", "at.the"), ("Jahreswechsel", "year.turn"), ("dass", "that"), ("für", "for"), ("Neugeborene", "newborns"), ("ein", "a"), ("Baum", "tree"), ("gepflanzt", "planted"), ("wird", "AUX.PASS")]
    translation := "The city stops its scheme of planting trees for newborn children at the turn of the year."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("verb", "beenden"), ("selectsCP", "no"), ("complement", "dass"), ("position", "postverbal")]
    comment := "Bare dass-clause with a non-CP-selecting verb."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex11b : LinguisticExample :=
  { id := "schwarzer2026_ex11b"
    source := ⟨"schwarzer-2026", "(11b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Stadt beendet zum Jahreswechsel die Überarbeitung des Nahverkehrskonzepts und dass für Neugeborene ein Baum gepflanzt wird."
    discourseSegments := []
    glossedTokens := [("Die", "the"), ("Stadt", "city"), ("beendet", "ends"), ("zum", "at.the"), ("Jahreswechsel", "year.turn"), ("die", "the"), ("Überarbeitung", "revision"), ("des", "of.the"), ("Nahverkehrskonzepts", "public.transport.plan"), ("und", "and"), ("dass", "that"), ("für", "for"), ("Neugeborene", "newborns"), ("ein", "a"), ("Baum", "tree"), ("gepflanzt", "planted"), ("wird", "AUX.PASS")]
    translation := "At the turn of the year, the city completes its revision of the local transport plan and stops the scheme of planting a tree for every newborn child."
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("verb", "beenden"), ("selectsCP", "no"), ("complement", "coord"), ("position", "postverbal"), ("order", "dpFirst")]
    comment := "DP-CP coordination with a non-CP-selecting verb, rated like the marked-but-grammatical filler group C; the coordination improves over the bare clause by more than the selected contexts predict."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex12a : LinguisticExample :=
  { id := "schwarzer2026_ex12a"
    source := ⟨"schwarzer-2026", "(12a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Stadt veranlasst zum Jahreswechsel dass für Neugeborene ein Baum gepflanzt wird."
    discourseSegments := []
    glossedTokens := [("Die", "the"), ("Stadt", "city"), ("veranlasst", "starts"), ("zum", "at.the"), ("Jahreswechsel", "year.turn"), ("dass", "that"), ("für", "for"), ("Neugeborene", "newborns"), ("ein", "a"), ("Baum", "tree"), ("gepflanzt", "planted"), ("wird", "AUX.PASS")]
    translation := "The city starts its scheme of planting trees for newborn children at the turn of the year."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("verb", "veranlassen"), ("selectsCP", "yes"), ("complement", "dass"), ("position", "postverbal")]
    comment := "Bare dass-clause with a CP-selecting verb."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex12b : LinguisticExample :=
  { id := "schwarzer2026_ex12b"
    source := ⟨"schwarzer-2026", "(12b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Stadt veranlasst zum Jahreswechsel die Überarbeitung des Nahverkehrskonzepts und dass für Neugeborene ein Baum gepflanzt wird."
    discourseSegments := []
    glossedTokens := [("Die", "the"), ("Stadt", "city"), ("veranlasst", "starts"), ("zum", "at.the"), ("Jahreswechsel", "year.turn"), ("die", "the"), ("Überarbeitung", "revision"), ("des", "of.the"), ("Nahverkehrskonzepts", "public.transport.plan"), ("und", "and"), ("dass", "that"), ("für", "for"), ("Neugeborene", "newborns"), ("ein", "a"), ("Baum", "tree"), ("gepflanzt", "planted"), ("wird", "AUX.PASS")]
    translation := "At the turn of the year, the city starts its revision of the local transport plan and the scheme of planting a tree for every newborn child."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("verb", "veranlassen"), ("selectsCP", "yes"), ("complement", "coord"), ("position", "postverbal"), ("order", "dpFirst")]
    comment := "DP-CP coordination with a CP-selecting verb."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex16a : LinguisticExample :=
  { id := "schwarzer2026_ex16a"
    source := ⟨"schwarzer-2026", "(16a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Stadt hat zum Jahreswechsel die Überarbeitung des Nahverkehrskonzepts und dass für Neugeborene ein Baum gepflanzt wird beendet."
    discourseSegments := []
    glossedTokens := [("Die", "the"), ("Stadt", "city"), ("hat", "has"), ("zum", "at.the"), ("Jahreswechsel", "year.turn"), ("die", "the"), ("Überarbeitung", "revision"), ("des", "of.the"), ("Nahverkehrskonzepts", "public.transport.plan"), ("und", "and"), ("dass", "that"), ("für", "for"), ("Neugeborene", "newborns"), ("ein", "a"), ("Baum", "tree"), ("gepflanzt", "planted"), ("wird", "AUX.PASS"), ("beendet", "ended")]
    translation := "At the turn of the year, the city completed its revision of the local transport plan and stopped the scheme of planting a tree for every newborn child."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("verb", "beenden"), ("selectsCP", "no"), ("complement", "coord"), ("position", "preverbal"), ("order", "dpFirst")]
    comment := "Preverbal coordination, DP first: chosen over (16b) more often in the forced choice."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex16b : LinguisticExample :=
  { id := "schwarzer2026_ex16b"
    source := ⟨"schwarzer-2026", "(16b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Stadt hat zum Jahreswechsel dass für Neugeborene ein Baum gepflanzt wird und die Überarbeitung des Nahverkehrskonzepts beendet."
    discourseSegments := []
    glossedTokens := [("Die", "the"), ("Stadt", "city"), ("hat", "has"), ("zum", "at.the"), ("Jahreswechsel", "year.turn"), ("dass", "that"), ("für", "for"), ("Neugeborene", "newborns"), ("ein", "a"), ("Baum", "tree"), ("gepflanzt", "planted"), ("wird", "AUX.PASS"), ("und", "and"), ("die", "the"), ("Überarbeitung", "revision"), ("des", "of.the"), ("Nahverkehrskonzepts", "public.transport.plan"), ("beendet", "ended")]
    translation := "At the turn of the year, the city stopped the scheme of planting a tree for every newborn child and completed its revision of the local transport plan."
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("verb", "beenden"), ("selectsCP", "no"), ("complement", "coord"), ("position", "preverbal"), ("order", "cpFirst")]
    comment := "Preverbal coordination, CP first: the order the linear and temporal closeness accounts predict to be preferred."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex17a : LinguisticExample :=
  { id := "schwarzer2026_ex17a"
    source := ⟨"schwarzer-2026", "(17a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Stadt beendet zum Jahreswechsel die Überarbeitung des Nahverkehrskonzepts und dass für Neugeborene ein Baum gepflanzt wird."
    discourseSegments := []
    glossedTokens := [("Die", "the"), ("Stadt", "city"), ("beendet", "ends"), ("zum", "at.the"), ("Jahreswechsel", "year.turn"), ("die", "the"), ("Überarbeitung", "revision"), ("des", "of.the"), ("Nahverkehrskonzepts", "public.transport.plan"), ("und", "and"), ("dass", "that"), ("für", "for"), ("Neugeborene", "newborns"), ("ein", "a"), ("Baum", "tree"), ("gepflanzt", "planted"), ("wird", "AUX.PASS")]
    translation := "At the turn of the year, the city completes its revision of the local transport plan and stops the scheme of planting a tree for every newborn child."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("verb", "beenden"), ("selectsCP", "no"), ("complement", "coord"), ("position", "postverbal"), ("order", "dpFirst")]
    comment := "Postverbal coordination, DP first: chosen as often as in preverbal position."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex17b : LinguisticExample :=
  { id := "schwarzer2026_ex17b"
    source := ⟨"schwarzer-2026", "(17b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Stadt beendet zum Jahreswechsel dass für Neugeborene ein Baum gepflanzt wird und die Überarbeitung des Nahverkehrskonzepts."
    discourseSegments := []
    glossedTokens := [("Die", "the"), ("Stadt", "city"), ("beendet", "ends"), ("zum", "at.the"), ("Jahreswechsel", "year.turn"), ("dass", "that"), ("für", "for"), ("Neugeborene", "newborns"), ("ein", "a"), ("Baum", "tree"), ("gepflanzt", "planted"), ("wird", "AUX.PASS"), ("und", "and"), ("die", "the"), ("Überarbeitung", "revision"), ("des", "of.the"), ("Nahverkehrskonzepts", "public.transport.plan")]
    translation := "At the turn of the year, the city stops the scheme of planting a tree for every newborn child and completes its revision of the local transport plan."
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("verb", "beenden"), ("selectsCP", "no"), ("complement", "coord"), ("position", "postverbal"), ("order", "cpFirst")]
    comment := "Postverbal coordination, CP first."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex11a, ex11b, ex12a, ex12b, ex16a, ex16b, ex17a, ex17b]

end Schwarzer2026.Examples
