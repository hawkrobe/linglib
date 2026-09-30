module

public import Linglib.Data.Examples.Schema

/-!
# `DelPrete2013` — typed example data

Auto-generated from `Linglib/Data/Examples/DelPrete2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace DelPrete2013.Examples`.
-/

@[expose] public section

namespace DelPrete2013.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "delprete2013_1"
    source := ⟨"del-prete-2013", "(1)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "(In quel periodo / In quel momento) Gianni leggeva il giornale."
    glossedTokens := [("Gianni", "Gianni"), ("leggeva", "read.IPFV.PST.3SG"), ("il", "DEF.M.SG"), ("giornale", "newspaper")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable), ("PROG", .acceptable)]
    paperFeatures := [("object", "definite"), ("qAdverb", "none"), ("soe", "none")] }

def ex_2a : LinguisticExample :=
  { id := "delprete2013_2a"
    source := ⟨"del-prete-2013", "(2a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "(In quel periodo / In quel momento) Gianni guidava un'auto sportiva."
    glossedTokens := [("Gianni", "Gianni"), ("guidava", "drive.IPFV.PST.3SG"), ("un'", "INDEF.F.SG"), ("auto", "car"), ("sportiva", "sports.F.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable), ("PROG", .acceptable)]
    paperFeatures := [("object", "singularIndefinite"), ("qAdverb", "none"), ("soe", "individual")] }

def ex_2b : LinguisticExample :=
  { id := "delprete2013_2b"
    source := ⟨"del-prete-2013", "(2b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "(In quel periodo / In quel momento) Gianni leggeva un libro di filosofia."
    glossedTokens := [("Gianni", "Gianni"), ("leggeva", "read.IPFV.PST.3SG"), ("un", "INDEF.M.SG"), ("libro", "book"), ("di", "of"), ("filosofia", "philosophy")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .unacceptable), ("PROG", .acceptable)]
    paperFeatures := [("object", "singularIndefinite"), ("qAdverb", "none"), ("soe", "individual")] }

def ex_3 : LinguisticExample :=
  { id := "delprete2013_3"
    source := ⟨"del-prete-2013", "(3)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "(In quel periodo) Gianni fumava un sigaro toscano (il Toscanello)."
    glossedTokens := [("Gianni", "Gianni"), ("fumava", "smoke.IPFV.PST.3SG"), ("un", "INDEF.M.SG"), ("sigaro", "cigar"), ("toscano", "tuscan.M.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable)]
    paperFeatures := [("object", "kindIndefinite"), ("qAdverb", "none"), ("soe", "kind")] }

def ex_4a : LinguisticExample :=
  { id := "delprete2013_4a"
    source := ⟨"del-prete-2013", "(4a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni viaggia in treno."
    glossedTokens := [("Gianni", "Gianni"), ("viaggia", "travel.PRS.3SG"), ("in", "in"), ("treno", "train")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable)]
    paperFeatures := [("object", "none"), ("qAdverb", "none"), ("soe", "none")] }

def ex_4b : LinguisticExample :=
  { id := "delprete2013_4b"
    source := ⟨"del-prete-2013", "(4b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni viaggia sempre in treno."
    glossedTokens := [("Gianni", "Gianni"), ("viaggia", "travel.PRS.3SG"), ("sempre", "always"), ("in", "in"), ("treno", "train")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable)]
    paperFeatures := [("object", "none"), ("qAdverb", "sempre"), ("soe", "none")] }

def ex_6 : LinguisticExample :=
  { id := "delprete2013_6"
    source := ⟨"del-prete-2013", "(6)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Quando va a trovare i suoi parenti, Gianni viaggia sempre in treno."
    glossedTokens := [("Quando", "when"), ("va", "go.PRS.3SG"), ("a", "to"), ("trovare", "find.INF"), ("i", "DEF.M.PL"), ("suoi", "his.M.PL"), ("parenti", "relatives"), ("Gianni", "Gianni"), ("viaggia", "travel.PRS.3SG"), ("sempre", "always"), ("in", "in"), ("treno", "train")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable)]
    paperFeatures := [("object", "none"), ("qAdverb", "sempre"), ("soe", "none")] }

def ex_8 : LinguisticExample :=
  { id := "delprete2013_8"
    source := ⟨"del-prete-2013", "(8)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "(In quel periodo) Gianni leggeva sempre / spesso un libro di filosofia."
    glossedTokens := [("Gianni", "Gianni"), ("leggeva", "read.IPFV.PST.3SG"), ("sempre", "always"), ("spesso", "often"), ("un", "INDEF.M.SG"), ("libro", "book"), ("di", "of"), ("filosofia", "philosophy")]
    context := "A discourse supplying a restriction for the Q-adverb, such as the occasions on which Gianni wanted to meditate (footnote 9)."
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable)]
    paperFeatures := [("object", "singularIndefinite"), ("qAdverb", "sempre"), ("soe", "none")] }

def ex_9b : LinguisticExample :=
  { id := "delprete2013_9b"
    source := ⟨"del-prete-2013", "(9b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni non fumava nessun sigaro toscano (ma ora ha una passione per il Toscanello)."
    glossedTokens := [("Gianni", "Gianni"), ("non", "NEG"), ("fumava", "smoke.IPFV.PST.3SG"), ("nessun", "NEG.INDEF.M.SG"), ("sigaro", "cigar"), ("toscano", "tuscan.M.SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable)]
    paperFeatures := [("object", "negativeKindIndefinite"), ("qAdverb", "none"), ("soe", "none")] }

def ex_11 : LinguisticExample :=
  { id := "delprete2013_11"
    source := ⟨"del-prete-2013", "(11)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "(In quel periodo / In quel momento) Gianni leggeva libri di filosofia."
    glossedTokens := [("Gianni", "Gianni"), ("leggeva", "read.IPFV.PST.3SG"), ("libri", "book.PL"), ("di", "of"), ("filosofia", "philosophy")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable), ("PROG", .unacceptable)]
    paperFeatures := [("object", "barePlural"), ("qAdverb", "none"), ("soe", "kind")] }

def ex_12 : LinguisticExample :=
  { id := "delprete2013_12"
    source := ⟨"del-prete-2013", "(12)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni leggeva un genere di libri di filosofia (libri di filosofia morale)."
    glossedTokens := [("Gianni", "Gianni"), ("leggeva", "read.IPFV.PST.3SG"), ("un", "INDEF.M.SG"), ("genere", "kind"), ("di", "of"), ("libri", "book.PL"), ("di", "of"), ("filosofia", "philosophy")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable), ("PROG", .unacceptable)]
    paperFeatures := [("object", "kindIndefinite"), ("qAdverb", "none"), ("soe", "kind")] }

def ex_13 : LinguisticExample :=
  { id := "delprete2013_13"
    source := ⟨"del-prete-2013", "(13)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni fumava sigari toscani."
    glossedTokens := [("Gianni", "Gianni"), ("fumava", "smoke.IPFV.PST.3SG"), ("sigari", "cigar.PL"), ("toscani", "tuscan.M.PL")]
    context := "Gianni had the habit of smoking tuscan cigars without an inclination for any particular sub-kind (footnote 12)."
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable)]
    paperFeatures := [("object", "barePlural"), ("qAdverb", "none"), ("soe", "kind")] }

def ex_14 : LinguisticExample :=
  { id := "delprete2013_14"
    source := ⟨"del-prete-2013", "(14)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni leggeva un certo genere di libri (i.e. libri di filosofia)."
    glossedTokens := [("Gianni", "Gianni"), ("leggeva", "read.IPFV.PST.3SG"), ("un", "INDEF.M.SG"), ("certo", "certain.M.SG"), ("genere", "kind"), ("di", "of"), ("libri", "book.PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable)]
    paperFeatures := [("object", "kindIndefinite"), ("qAdverb", "none"), ("soe", "kind")] }

def fn11 : LinguisticExample :=
  { id := "delprete2013_fn11"
    source := ⟨"del-prete-2013", "footnote 11 (i)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni mangiava ciliegie."
    glossedTokens := [("Gianni", "Gianni"), ("mangiava", "eat.IPFV.PST.3SG"), ("ciliegie", "cherry.PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable), ("PROG", .acceptable)]
    paperFeatures := [("object", "barePlural"), ("qAdverb", "none"), ("soe", "kind")] }

def ex_17 : LinguisticExample :=
  { id := "delprete2013_17"
    source := ⟨"del-prete-2013", "(17)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Alle 15 Gianni era a casa, leggeva un libro."
    glossedTokens := [("Alle", "at.DEF.F.PL"), ("15", "15"), ("Gianni", "Gianni"), ("era", "be.IPFV.PST.3SG"), ("a", "at"), ("casa", "home"), ("leggeva", "read.IPFV.PST.3SG"), ("un", "INDEF.M.SG"), ("libro", "book")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("PROG", .acceptable)]
    paperFeatures := [("object", "singularIndefinite"), ("qAdverb", "none"), ("soe", "none")] }

def ex_19 : LinguisticExample :=
  { id := "delprete2013_19"
    source := ⟨"del-prete-2013", "(19)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ogni giorno alle 15 Gianni prendeva il caffé."
    glossedTokens := [("Ogni", "every"), ("giorno", "day"), ("alle", "at.DEF.F.PL"), ("15", "15"), ("Gianni", "Gianni"), ("prendeva", "take.IPFV.PST.3SG"), ("il", "DEF.M.SG"), ("caffé", "coffee")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable)]
    paperFeatures := [("object", "definite"), ("qAdverb", "ogni"), ("soe", "none")] }

def ex_20 : LinguisticExample :=
  { id := "delprete2013_20"
    source := ⟨"del-prete-2013", "(20)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "In quel periodo, ogni giorno alle 15 Gianni prendeva il caffé."
    glossedTokens := [("In", "in"), ("quel", "that.M.SG"), ("periodo", "period"), ("ogni", "every"), ("giorno", "day"), ("alle", "at.DEF.F.PL"), ("15", "15"), ("Gianni", "Gianni"), ("prendeva", "take.IPFV.PST.3SG"), ("il", "DEF.M.SG"), ("caffé", "coffee")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable)]
    paperFeatures := [("object", "definite"), ("qAdverb", "ogni"), ("soe", "none")] }

def fn29 : LinguisticExample :=
  { id := "delprete2013_fn29"
    source := ⟨"del-prete-2013", "footnote 29 (i)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "? Alle 15 Gianni guidava auto sportive."
    glossedTokens := [("Alle", "at.DEF.F.PL"), ("15", "15"), ("Gianni", "Gianni"), ("guidava", "drive.IPFV.PST.3SG"), ("auto", "car.PL"), ("sportive", "sports.F.PL")]
    context := ""
    judgment := .questionable
    alternatives := []
    readings := [("PROG", .questionable)]
    paperFeatures := [("object", "barePlural"), ("qAdverb", "none"), ("soe", "kind")] }

def fn31 : LinguisticExample :=
  { id := "delprete2013_fn31"
    source := ⟨"del-prete-2013", "footnote 31 (i)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Quando voleva meditare, Gianni leggeva sempre un libro di filosofia."
    glossedTokens := [("Quando", "when"), ("voleva", "want.IPFV.PST.3SG"), ("meditare", "meditate.INF"), ("Gianni", "Gianni"), ("leggeva", "read.IPFV.PST.3SG"), ("sempre", "always"), ("un", "INDEF.M.SG"), ("libro", "book"), ("di", "of"), ("filosofia", "philosophy")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable)]
    paperFeatures := [("object", "singularIndefinite"), ("qAdverb", "sempre"), ("soe", "none")] }

def tennis : LinguisticExample :=
  { id := "delprete2013_tennis"
    source := ⟨"del-prete-2013", "§4"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "(In quel periodo) Gianni giocava a tennis."
    glossedTokens := [("Gianni", "Gianni"), ("giocava", "play.IPFV.PST.3SG"), ("a", "at"), ("tennis", "tennis")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("HAB", .acceptable)]
    paperFeatures := [("object", "none"), ("qAdverb", "none"), ("soe", "none")] }

def frequentative : LinguisticExample :=
  { id := "delprete2013_frequentative"
    source := ⟨"del-prete-2013", "§4.3"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni ha fumato Toscanelli per vent'anni."
    glossedTokens := [("Gianni", "Gianni"), ("ha", "have.PRS.3SG"), ("fumato", "smoke.PTCP"), ("Toscanelli", "Toscanello.PL"), ("per", "for"), ("vent'anni", "twenty.years")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("object", "barePlural"), ("qAdverb", "none"), ("soe", "kind")] }

def all : List LinguisticExample := [ex_1, ex_2a, ex_2b, ex_3, ex_4a, ex_4b, ex_6, ex_8, ex_9b, ex_11, ex_12, ex_13, ex_14, fn11, ex_17, ex_19, ex_20, fn29, fn31, tennis, frequentative]

end DelPrete2013.Examples
