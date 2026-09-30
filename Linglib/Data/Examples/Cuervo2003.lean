module

public import Linglib.Data.Examples.Schema

/-!
# `Cuervo2003` — typed example data

Auto-generated from `Linglib/Data/Examples/Cuervo2003.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Cuervo2003.Examples`.
-/

@[expose] public section

namespace Cuervo2003.Examples

open Data.Examples

def ex_29a : LinguisticExample :=
  { id := "cuervo2003_29a"
    source := ⟨"cuervo-2003", "(29a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Pablo le mandó un diccionario a Gabi."
    glossedTokens := [("Pablo", "Pablo"), ("le", "CL.DAT"), ("mandó", "sent"), ("un", "a"), ("diccionario", "dictionary"), ("a", "DAT"), ("Gabi", "Gabi")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "mandar"), ("animate", "yes"), ("dative", "dp"), ("meaning", "recipient")] }

def ex_30 : LinguisticExample :=
  { id := "cuervo2003_30"
    source := ⟨"cuervo-2003", "(30)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Pablo nos preparó sandwichitos de miga a todos."
    glossedTokens := [("Pablo", "Pablo"), ("nos", "CL.1PL.DAT"), ("preparó", "fixed"), ("sandwichitos", "sandwiches"), ("de", "of"), ("miga", "crumb"), ("a", "DAT"), ("todos", "all")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "preparar"), ("animate", "yes"), ("dative", "dp"), ("meaning", "recipient")] }

def ex_31 : LinguisticExample :=
  { id := "cuervo2003_31"
    source := ⟨"cuervo-2003", "(31)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Pablo le sacó la bicicleta a Andreína."
    glossedTokens := [("Pablo", "Pablo"), ("le", "CL.DAT"), ("sacó", "took.away"), ("la", "the"), ("bicicleta", "bicycle"), ("a", "DAT"), ("Andreína", "Andreína")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "sacar"), ("animate", "yes"), ("dative", "dp"), ("meaning", "source")] }

def ex_32 : LinguisticExample :=
  { id := "cuervo2003_32"
    source := ⟨"cuervo-2003", "(32)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Pablo le lavó el auto a Valeria."
    glossedTokens := [("Pablo", "Pablo"), ("le", "CL.DAT"), ("lavó", "washed"), ("el", "the"), ("auto", "car"), ("a", "DAT"), ("Valeria", "Valeria")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "lavar"), ("animate", "yes"), ("dative", "dp"), ("meaning", "possessor")] }

def ex_33 : LinguisticExample :=
  { id := "cuervo2003_33"
    source := ⟨"cuervo-2003", "(33)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Pablo le admira la paciencia a Valeria."
    glossedTokens := [("Pablo", "Pablo"), ("le", "CL.DAT"), ("admira", "admires"), ("la", "the"), ("paciencia", "patience"), ("a", "DAT"), ("Valeria", "Valeria")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "admirar"), ("animate", "yes"), ("dative", "dp"), ("meaning", "possessor")] }

def ex_34 : LinguisticExample :=
  { id := "cuervo2003_34"
    source := ⟨"cuervo-2003", "(34)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A Gabi le llegaron dos cartas de Londres."
    glossedTokens := [("A", "DAT"), ("Gabi", "Gabi"), ("le", "CL.DAT"), ("llegaron", "arrived.PL"), ("dos", "two"), ("cartas", "letters"), ("de", "from"), ("Londres", "London")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "llegar"), ("animate", "yes"), ("dative", "dp"), ("meaning", "recipient")] }

def ex_35 : LinguisticExample :=
  { id := "cuervo2003_35"
    source := ⟨"cuervo-2003", "(35)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Emilio le rompió la radio a Carolina."
    glossedTokens := [("Emilio", "Emilio"), ("le", "CL.DAT"), ("rompió", "broke"), ("la", "the"), ("radio", "radio"), ("a", "DAT"), ("Carolina", "Carolina")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "romperCausative"), ("animate", "yes"), ("dative", "dp"), ("meaning", "affected")] }

def ex_36 : LinguisticExample :=
  { id := "cuervo2003_36"
    source := ⟨"cuervo-2003", "(36)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A Carolina se le rompió la radio."
    glossedTokens := [("A", "DAT"), ("Carolina", "Carolina"), ("se", "SE"), ("le", "CL.DAT"), ("rompió", "broke"), ("la", "the"), ("radio", "radio")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "romperInchoative"), ("animate", "yes"), ("dative", "dp"), ("meaning", "affected")] }

def ex_37 : LinguisticExample :=
  { id := "cuervo2003_37"
    source := ⟨"cuervo-2003", "(37)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A Daniela no le gustan los gatos."
    glossedTokens := [("A", "DAT"), ("Daniela", "Daniela"), ("no", "not"), ("le", "CL.DAT"), ("gustan", "like.PL"), ("los", "the"), ("gatos", "cats")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "gustar"), ("animate", "yes"), ("dative", "dp"), ("meaning", "experiencer")] }

def ex_38 : LinguisticExample :=
  { id := "cuervo2003_38"
    source := ⟨"cuervo-2003", "(38)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A Laura le sobraron veinte pesos."
    glossedTokens := [("A", "DAT"), ("Laura", "Laura"), ("le", "CL.DAT"), ("sobraron", "were.extra.PL"), ("veinte", "twenty"), ("pesos", "pesos")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "sobrar"), ("animate", "yes"), ("dative", "dp"), ("meaning", "possessor")] }

def ex_39a : LinguisticExample :=
  { id := "cuervo2003_39a"
    source := ⟨"cuervo-2003", "(39a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Juanita ya le camina."
    glossedTokens := [("Juanita", "Juanita"), ("ya", "already"), ("le", "CL.DAT"), ("camina", "walks")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "caminar"), ("animate", "yes"), ("dative", "clitic"), ("meaning", "ethical")] }

def ex_49 : LinguisticExample :=
  { id := "cuervo2003_49"
    source := ⟨"cuervo-2003", "(49)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A Daniela le sucedió algo buenísimo."
    glossedTokens := [("A", "DAT"), ("Daniela", "Daniela"), ("le", "CL.DAT"), ("sucedió", "happened"), ("algo", "something"), ("buenísimo", "very.good")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "suceder"), ("animate", "yes"), ("dative", "dp"), ("meaning", "experiencer")] }

def ex_54a : LinguisticExample :=
  { id := "cuervo2003_54a"
    source := ⟨"cuervo-2003", "(54a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A la plantas les salieron flores."
    glossedTokens := [("A", "DAT"), ("la", "the"), ("plantas", "plants"), ("les", "CL.DAT.PL"), ("salieron", "came.out"), ("flores", "flowers")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "salir"), ("animate", "no"), ("dative", "dp"), ("meaning", "possessor")] }

def ex_55 : LinguisticExample :=
  { id := "cuervo2003_55"
    source := ⟨"cuervo-2003", "(55)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Al tintorero se le quemaron los pantalones de Carolina."
    glossedTokens := [("Al", "DAT.the"), ("tintorero", "dry.cleaner"), ("se", "SE"), ("le", "CL.DAT"), ("quemaron", "burnt.PL"), ("los", "the"), ("pantalones", "trousers"), ("de", "of"), ("Carolina", "Carolina")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("affected", .acceptable), ("unintentional responsibility", .acceptable)]
    paperFeatures := [("predicate", "quemarInchoative"), ("animate", "yes"), ("dative", "dp"), ("meaning", "affected")] }

def ex_60 : LinguisticExample :=
  { id := "cuervo2003_60"
    source := ⟨"cuervo-2003", "(60)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A la mesa se le rompieron dos patas."
    glossedTokens := [("A", "DAT"), ("la", "the"), ("mesa", "table"), ("se", "SE"), ("le", "CL.DAT"), ("rompieron", "broke"), ("dos", "two"), ("patas", "legs")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("affected", .acceptable), ("unintentional responsibility", .unacceptable)]
    paperFeatures := [("predicate", "romperInchoative"), ("animate", "no"), ("dative", "dp"), ("meaning", "affected")] }

def ex_66 : LinguisticExample :=
  { id := "cuervo2003_66"
    source := ⟨"cuervo-2003", "(66)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Hugo le corrió a Vicki."
    glossedTokens := [("Hugo", "Hugo"), ("le", "CL.DAT"), ("corrió", "ran"), ("a", "DAT"), ("Vicki", "Vicki")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "correr"), ("animate", "yes"), ("dative", "dp")] }

def ex_67a : LinguisticExample :=
  { id := "cuervo2003_67a"
    source := ⟨"cuervo-2003", "(67a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Hugo le corrió una carrera a Vicki."
    glossedTokens := [("Hugo", "Hugo"), ("le", "CL.DAT"), ("corrió", "ran"), ("una", "a"), ("carrera", "race"), ("a", "DAT"), ("Vicki", "Vicki")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "correrTransitive"), ("animate", "yes"), ("dative", "dp")] }

def ex_78 : LinguisticExample :=
  { id := "cuervo2003_78"
    source := ⟨"cuervo-2003", "(78)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Juanita ya le camina a él."
    glossedTokens := [("Juanita", "Juanita"), ("ya", "already"), ("le", "CL.DAT"), ("camina", "walks"), ("a", "DAT"), ("él", "him")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "caminar"), ("animate", "yes"), ("dative", "dp")] }

def ex_90a : LinguisticExample :=
  { id := "cuervo2003_90a"
    source := ⟨"cuervo-2003", "(90a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Emilio le abrió las puertas a Carolina."
    glossedTokens := [("Emilio", "Emilio"), ("le", "CL.DAT"), ("abrió", "opened"), ("las", "the"), ("puertas", "doors"), ("a", "DAT"), ("Carolina", "Carolina")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "abrirCausative"), ("animate", "yes"), ("dative", "dp"), ("meaning", "affected")] }

def ex_90b : LinguisticExample :=
  { id := "cuervo2003_90b"
    source := ⟨"cuervo-2003", "(90b)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A Carolina se le abrió la puerta."
    glossedTokens := [("A", "DAT"), ("Carolina", "Carolina"), ("se", "CL.REF"), ("le", "CL.DAT"), ("abrió", "opened"), ("la", "the"), ("puerta", "door")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "abrirInchoative"), ("animate", "yes"), ("dative", "dp"), ("meaning", "affected")] }

def ex_85ap : LinguisticExample :=
  { id := "cuervo2003_85ap"
    source := ⟨"cuervo-2003", "(85a')"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John passed Mary the ring."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "pass"), ("animate", "yes"), ("dative", "dp"), ("meaning", "recipient")] }

def ex_88 : LinguisticExample :=
  { id := "cuervo2003_88"
    source := ⟨"cuervo-2003", "(88)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Daniel opened Stephanie the door."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "openCausative"), ("animate", "yes"), ("dative", "dp")] }

def ex_89a : LinguisticExample :=
  { id := "cuervo2003_89a"
    source := ⟨"cuervo-2003", "(89a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The door opened Stephanie."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "openInchoative"), ("animate", "yes"), ("dative", "dp")] }

def ex_92b : LinguisticExample :=
  { id := "cuervo2003_92b"
    source := ⟨"cuervo-2003", "(92b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Two letters arrived Daniel."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate", "arrive"), ("animate", "yes"), ("dative", "dp")] }

def all : List LinguisticExample := [ex_29a, ex_30, ex_31, ex_32, ex_33, ex_34, ex_35, ex_36, ex_37, ex_38, ex_39a, ex_49, ex_54a, ex_55, ex_60, ex_66, ex_67a, ex_78, ex_90a, ex_90b, ex_85ap, ex_88, ex_89a, ex_92b]

end Cuervo2003.Examples
