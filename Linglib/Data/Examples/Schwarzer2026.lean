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

def ex11a : Datum :=
  { id := "schwarzer2026_ex11a"
    source := ⟨"schwarzer-2026", "(11a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Stadt beendet zum Jahreswechsel dass für Neugeborene ein Baum gepflanzt wird."
    glossedTokens := [("Die", "the"), ("Stadt", "city"), ("beendet", "ends"), ("zum", "at.the"), ("Jahreswechsel", "year.turn"), ("dass", "that"), ("für", "for"), ("Neugeborene", "newborns"), ("ein", "a"), ("Baum", "tree"), ("gepflanzt", "planted"), ("wird", "AUX.PASS")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("verb", "beenden"), ("selectsCP", "no"), ("complement", "dass"), ("position", "postverbal")] }

def ex11b : Datum :=
  { id := "schwarzer2026_ex11b"
    source := ⟨"schwarzer-2026", "(11b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Stadt beendet zum Jahreswechsel die Überarbeitung des Nahverkehrskonzepts und dass für Neugeborene ein Baum gepflanzt wird."
    glossedTokens := [("Die", "the"), ("Stadt", "city"), ("beendet", "ends"), ("zum", "at.the"), ("Jahreswechsel", "year.turn"), ("die", "the"), ("Überarbeitung", "revision"), ("des", "of.the"), ("Nahverkehrskonzepts", "public.transport.plan"), ("und", "and"), ("dass", "that"), ("für", "for"), ("Neugeborene", "newborns"), ("ein", "a"), ("Baum", "tree"), ("gepflanzt", "planted"), ("wird", "AUX.PASS")]
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("verb", "beenden"), ("selectsCP", "no"), ("complement", "coord"), ("position", "postverbal"), ("order", "dpFirst")] }

def ex12a : Datum :=
  { id := "schwarzer2026_ex12a"
    source := ⟨"schwarzer-2026", "(12a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Stadt veranlasst zum Jahreswechsel dass für Neugeborene ein Baum gepflanzt wird."
    glossedTokens := [("Die", "the"), ("Stadt", "city"), ("veranlasst", "starts"), ("zum", "at.the"), ("Jahreswechsel", "year.turn"), ("dass", "that"), ("für", "for"), ("Neugeborene", "newborns"), ("ein", "a"), ("Baum", "tree"), ("gepflanzt", "planted"), ("wird", "AUX.PASS")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("verb", "veranlassen"), ("selectsCP", "yes"), ("complement", "dass"), ("position", "postverbal")] }

def ex12b : Datum :=
  { id := "schwarzer2026_ex12b"
    source := ⟨"schwarzer-2026", "(12b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Stadt veranlasst zum Jahreswechsel die Überarbeitung des Nahverkehrskonzepts und dass für Neugeborene ein Baum gepflanzt wird."
    glossedTokens := [("Die", "the"), ("Stadt", "city"), ("veranlasst", "starts"), ("zum", "at.the"), ("Jahreswechsel", "year.turn"), ("die", "the"), ("Überarbeitung", "revision"), ("des", "of.the"), ("Nahverkehrskonzepts", "public.transport.plan"), ("und", "and"), ("dass", "that"), ("für", "for"), ("Neugeborene", "newborns"), ("ein", "a"), ("Baum", "tree"), ("gepflanzt", "planted"), ("wird", "AUX.PASS")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("verb", "veranlassen"), ("selectsCP", "yes"), ("complement", "coord"), ("position", "postverbal"), ("order", "dpFirst")] }

def ex16a : Datum :=
  { id := "schwarzer2026_ex16a"
    source := ⟨"schwarzer-2026", "(16a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Stadt hat zum Jahreswechsel die Überarbeitung des Nahverkehrskonzepts und dass für Neugeborene ein Baum gepflanzt wird beendet."
    glossedTokens := [("Die", "the"), ("Stadt", "city"), ("hat", "has"), ("zum", "at.the"), ("Jahreswechsel", "year.turn"), ("die", "the"), ("Überarbeitung", "revision"), ("des", "of.the"), ("Nahverkehrskonzepts", "public.transport.plan"), ("und", "and"), ("dass", "that"), ("für", "for"), ("Neugeborene", "newborns"), ("ein", "a"), ("Baum", "tree"), ("gepflanzt", "planted"), ("wird", "AUX.PASS"), ("beendet", "ended")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("verb", "beenden"), ("selectsCP", "no"), ("complement", "coord"), ("position", "preverbal"), ("order", "dpFirst")] }

def ex16b : Datum :=
  { id := "schwarzer2026_ex16b"
    source := ⟨"schwarzer-2026", "(16b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Stadt hat zum Jahreswechsel dass für Neugeborene ein Baum gepflanzt wird und die Überarbeitung des Nahverkehrskonzepts beendet."
    glossedTokens := [("Die", "the"), ("Stadt", "city"), ("hat", "has"), ("zum", "at.the"), ("Jahreswechsel", "year.turn"), ("dass", "that"), ("für", "for"), ("Neugeborene", "newborns"), ("ein", "a"), ("Baum", "tree"), ("gepflanzt", "planted"), ("wird", "AUX.PASS"), ("und", "and"), ("die", "the"), ("Überarbeitung", "revision"), ("des", "of.the"), ("Nahverkehrskonzepts", "public.transport.plan"), ("beendet", "ended")]
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("verb", "beenden"), ("selectsCP", "no"), ("complement", "coord"), ("position", "preverbal"), ("order", "cpFirst")] }

def ex17a : Datum :=
  { id := "schwarzer2026_ex17a"
    source := ⟨"schwarzer-2026", "(17a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Stadt beendet zum Jahreswechsel die Überarbeitung des Nahverkehrskonzepts und dass für Neugeborene ein Baum gepflanzt wird."
    glossedTokens := [("Die", "the"), ("Stadt", "city"), ("beendet", "ends"), ("zum", "at.the"), ("Jahreswechsel", "year.turn"), ("die", "the"), ("Überarbeitung", "revision"), ("des", "of.the"), ("Nahverkehrskonzepts", "public.transport.plan"), ("und", "and"), ("dass", "that"), ("für", "for"), ("Neugeborene", "newborns"), ("ein", "a"), ("Baum", "tree"), ("gepflanzt", "planted"), ("wird", "AUX.PASS")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("verb", "beenden"), ("selectsCP", "no"), ("complement", "coord"), ("position", "postverbal"), ("order", "dpFirst")] }

def ex17b : Datum :=
  { id := "schwarzer2026_ex17b"
    source := ⟨"schwarzer-2026", "(17b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Stadt beendet zum Jahreswechsel dass für Neugeborene ein Baum gepflanzt wird und die Überarbeitung des Nahverkehrskonzepts."
    glossedTokens := [("Die", "the"), ("Stadt", "city"), ("beendet", "ends"), ("zum", "at.the"), ("Jahreswechsel", "year.turn"), ("dass", "that"), ("für", "for"), ("Neugeborene", "newborns"), ("ein", "a"), ("Baum", "tree"), ("gepflanzt", "planted"), ("wird", "AUX.PASS"), ("und", "and"), ("die", "the"), ("Überarbeitung", "revision"), ("des", "of.the"), ("Nahverkehrskonzepts", "public.transport.plan")]
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("verb", "beenden"), ("selectsCP", "no"), ("complement", "coord"), ("position", "postverbal"), ("order", "cpFirst")] }

def all : List Datum := [ex11a, ex11b, ex12a, ex12b, ex16a, ex16b, ex17a, ex17b]

end Schwarzer2026.Examples
