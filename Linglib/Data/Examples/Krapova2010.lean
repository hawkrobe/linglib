module

public import Linglib.Data.Examples.Schema

/-!
# `Krapova2010` — typed example data

Auto-generated from `Linglib/Data/Examples/Krapova2010.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Krapova2010.Examples`.
-/

@[expose] public section

namespace Krapova2010.Examples

open Data.Examples

def ex_56a : Datum :=
  { id := "krapova2010_56a"
    source := ⟨"krapova-2010", "(56a)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Naistina săžaljavam, deto ne otdelix poveče vnimanie na postrojkata."
    glossedTokens := [("Naistina", "really"), ("săžaljavam,", "regret-1sg"), ("deto", "that"), ("ne", "not"), ("otdelix", "devoted-1sg"), ("poveče", "more"), ("vnimanie", "attention"), ("na", "to"), ("postrojkata", "construction-the")]
    context := ""
    judgment := .acceptable
    alternatives := [("Naistina săžaljavam, če ne otdelix poveče vnimanie na postrojkata.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "săžaljavam"), ("complementizer", "deto"), ("diagnostic", "detoSelection")] }

def ex_56b : Datum :=
  { id := "krapova2010_56b"
    source := ⟨"krapova-2010", "(56b)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Samo me e jad, deto grivnata izčezna sled zatămnenieto."
    glossedTokens := [("Samo", "only"), ("me", "me-ClAcc"), ("e", "is"), ("jad,", "anger"), ("deto", "that"), ("grivnata", "bracelet-the"), ("izčezna", "disappeared-3sg"), ("sled", "after"), ("zatămnenieto", "eclipse-the")]
    context := ""
    judgment := .acceptable
    alternatives := [("Samo me e jad, če grivnata izčezna sled zatămnenieto.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "jad me e"), ("complementizer", "deto"), ("diagnostic", "detoSelection")] }

def ex_57a : Datum :=
  { id := "krapova2010_57a"
    source := ⟨"krapova-2010", "(57a)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Nikak ne săžaljavam, deto sreštata im se e provalila."
    glossedTokens := [("Nikak", "not-at-all"), ("ne", "not"), ("săžaljavam,", "regret-1sg"), ("deto", "that"), ("sreštata", "meeting-the"), ("im", "their"), ("se", "refl"), ("e", "is"), ("provalila", "failed-prt")]
    context := ""
    judgment := .acceptable
    alternatives := [("Nikak ne săžaljavam, če sreštata im se e provalila.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "săžaljavam"), ("complementizer", "deto"), ("diagnostic", "projection"), ("environment", "negation"), ("projective", "yes"), ("person", "1")] }

def ex_57b : Datum :=
  { id := "krapova2010_57b"
    source := ⟨"krapova-2010", "(57b)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Vinoven li săm deto gostite pristignaxa kăsno?"
    glossedTokens := [("Vinoven", "guilty"), ("li", "Q"), ("săm", "am"), ("deto", "that"), ("gostite", "guests-the"), ("pristignaxa", "arrived-3pl"), ("kăsno", "late")]
    context := ""
    judgment := .acceptable
    alternatives := [("Vinoven li săm če gostite pristignaxa kăsno?", .acceptable)]
    readings := []
    paperFeatures := [("verb", "vinoven săm"), ("complementizer", "deto"), ("diagnostic", "projection"), ("environment", "question"), ("projective", "yes"), ("person", "1")] }

def ex_57c : Datum :=
  { id := "krapova2010_57c"
    source := ⟨"krapova-2010", "(57c)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Săžaljavam, deto ne moža da ostaneš poveče."
    glossedTokens := [("Săžaljavam,", "regret-1sg"), ("deto", "that"), ("ne", "not"), ("moža", "could-2sg"), ("da", "Mod"), ("ostaneš", "stay-2sg"), ("poveče", "more")]
    context := ""
    judgment := .acceptable
    alternatives := [("Săžaljavam, če ne moža da ostaneš poveče.", .acceptable), ("Săžaljavam, deto ne moža da ostaneš poveče, no vsăšnost ti ostana poveče.", .unacceptable)]
    readings := []
    paperFeatures := [("verb", "săžaljavam"), ("complementizer", "deto"), ("diagnostic", "contradiction"), ("person", "1")] }

def ex_58a : Datum :=
  { id := "krapova2010_58a"
    source := ⟨"krapova-2010", "(58a)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Văzmutix se deto ne sa mogli da provedat sreštata."
    glossedTokens := [("Văzmutix", "resent-1sg"), ("se", "refl"), ("deto", "that"), ("ne", "not"), ("sa", "are-3pl"), ("mogli", "able-pl"), ("da", "Mod"), ("provedat", "organize-3pl"), ("sreštata", "meeting-the")]
    context := ""
    judgment := .ungrammatical
    alternatives := [("Văzmutix se če ne sa mogli da provedat sreštata.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "văzmuštavam se"), ("complementizer", "deto"), ("diagnostic", "detoSelection")] }

def ex_58b : Datum :=
  { id := "krapova2010_58b"
    source := ⟨"krapova-2010", "(58b)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Otkrix deto sreštata im se e provalila."
    glossedTokens := [("Otkrix", "found-out-1sg"), ("deto", "that"), ("sreštata", "meeting-the"), ("im", "their"), ("se", "refl"), ("e", "is"), ("provalila", "failed-prt")]
    context := ""
    judgment := .ungrammatical
    alternatives := [("Otkrix če sreštata im se e provalila.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "otkrivam"), ("complementizer", "deto"), ("diagnostic", "detoSelection")] }

def ex_59a : Datum :=
  { id := "krapova2010_59a"
    source := ⟨"krapova-2010", "(59a)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Săžaljavam za provala na sreštata."
    glossedTokens := [("Săžaljavam", "regret-1sg"), ("za", "for"), ("provala", "failure-the"), ("na", "of"), ("sreštata", "meeting-the")]
    context := ""
    judgment := .acceptable
    alternatives := [("Săžaljavam na provala na sreštata.", .ungrammatical), ("Săžaljavam provala na sreštata.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "săžaljavam"), ("diagnostic", "zaPhrase")] }

def ex_59b : Datum :=
  { id := "krapova2010_59b"
    source := ⟨"krapova-2010", "(59b)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Vinoven li săm za zakăsnenieto na gostite?"
    glossedTokens := [("Vinoven", "guilty"), ("li", "Q"), ("săm", "am"), ("za", "for"), ("zakăsnenieto", "delay-the"), ("na", "of"), ("gostite", "visitors-the")]
    context := ""
    judgment := .acceptable
    alternatives := [("Vinoven li săm na zakăsnenieto na gostite?", .ungrammatical), ("Vinoven li săm zakăsnenieto na gostite?", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "vinoven săm"), ("diagnostic", "zaPhrase")] }

def fn46i : Datum :=
  { id := "krapova2010_fn46i"
    source := ⟨"krapova-2010", "fn. 46 (i)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Văzmutix se če ne sa mogli da provedat sreštata."
    glossedTokens := [("Văzmutix", "resent-1sg"), ("se", "refl"), ("če", "that"), ("ne", "not"), ("sa", "are-3pl"), ("mogli", "able-pl"), ("da", "Mod"), ("provedat", "organize-3pl"), ("sreštata", "meeting-the")]
    context := ""
    judgment := .acceptable
    alternatives := [("Văzmutix se če ne sa mogli da provedat sreštata, no vsăšnost te provedoxa sreštata.", .unacceptable)]
    readings := []
    paperFeatures := [("verb", "văzmuštavam se"), ("complementizer", "če"), ("diagnostic", "contradiction"), ("person", "1")] }

def all : List Datum := [ex_56a, ex_56b, ex_57a, ex_57b, ex_57c, ex_58a, ex_58b, ex_59a, ex_59b, fn46i]

end Krapova2010.Examples
