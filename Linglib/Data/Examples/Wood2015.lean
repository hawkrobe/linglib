module

public import Linglib.Data.Examples.Schema

/-!
# `Wood2015` — typed example data

Auto-generated from `Linglib/Data/Examples/Wood2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Wood2015.Examples`.
-/

@[expose] public section

namespace Wood2015.Examples

open Data.Examples

def ex_1 : Datum :=
  { id := "wood2015_1"
    source := ⟨"wood-2015", "Ch. 2 (1a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jóna og Siggi kysstust eftir ballið."
    glossedTokens := [("Jóna", "Jóna.NOM"), ("og", "and"), ("Siggi", "Siggi.NOM"), ("kysstust", "kissed-ST"), ("eftir", "after"), ("ballið", "dance.the")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "reciprocal")] }

def ex_2 : Datum :=
  { id := "wood2015_2"
    source := ⟨"wood-2015", "Ch. 2 (1b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jón dulbjóst sem prestur."
    glossedTokens := [("Jón", "John.NOM"), ("dulbjóst", "disguised-ST"), ("sem", "as"), ("prestur", "priest")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "reflexive")] }

def ex_3 : Datum :=
  { id := "wood2015_3"
    source := ⟨"wood-2015", "Ch. 2 (1c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Glugginn opnaðist af sjálfu sér."
    glossedTokens := [("Glugginn", "window.the.NOM"), ("opnaðist", "opened-ST"), ("af", "by"), ("sjálfu", "self.DAT"), ("sér", "REFL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "anticausative")] }

def ex_4 : Datum :=
  { id := "wood2015_4"
    source := ⟨"wood-2015", "Ch. 2 (1d)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Rafmagnsbílar seljast vel hér."
    glossedTokens := [("Rafmagnsbílar", "electric.cars.NOM"), ("seljast", "sell-ST"), ("vel", "well"), ("hér", "here")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "generic middle")] }

def ex_5 : Datum :=
  { id := "wood2015_5"
    source := ⟨"wood-2015", "Ch. 3 (16a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Fólk dýp-ka-ði skurðinn."
    glossedTokens := [("Fólk", "people.NOM"), ("dýp-ka-ði", "deep-KA-PST"), ("skurðinn", "ditch.the.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("exponent", "-ka"), ("voice", "Voice{D}")] }

def ex_6 : Datum :=
  { id := "wood2015_6"
    source := ⟨"wood-2015", "Ch. 3 (16b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Skurðurinn dýp-ka-ði."
    glossedTokens := [("Skurðurinn", "ditch.the.NOM"), ("dýp-ka-ði", "deep-KA-PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("exponent", "-ka"), ("voice", "Voice{}")] }

def ex_7 : Datum :=
  { id := "wood2015_7"
    source := ⟨"wood-2015", "Ch. 3 (20a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jón hita-ði vatnið."
    glossedTokens := [("Jón", "John.NOM"), ("hita-ði", "heat-3SG.PST"), ("vatnið", "water.the.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("voice", "Voice{D}")] }

def ex_8 : Datum :=
  { id := "wood2015_8"
    source := ⟨"wood-2015", "Ch. 3 (20b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Vatnið hit-na-ði."
    glossedTokens := [("Vatnið", "water.the.NOM"), ("hit-na-ði", "heat-NA-3SG.PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("exponent", "-na"), ("voice", "Voice{}")] }

def ex_9 : Datum :=
  { id := "wood2015_9"
    source := ⟨"wood-2015", "Ch. 3 (52)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Dyrnar opnuðust."
    glossedTokens := [("Dyrnar", "door.the.NOM"), ("opnuðust", "opened-ST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "anticausative"), ("site", "SpecVoiceP")] }

def ex_10 : Datum :=
  { id := "wood2015_10"
    source := ⟨"wood-2015", "Ch. 3 (70)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Rúðan splundraðist."
    glossedTokens := [("Rúðan", "window.the.NOM"), ("splundraðist", "shattered-ST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "anticausative"), ("site", "SpecVoiceP")] }

def ex_11 : Datum :=
  { id := "wood2015_11"
    source := ⟨"wood-2015", "Ch. 3 (72a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Konan myrti manninn."
    glossedTokens := [("Konan", "woman.the.NOM"), ("myrti", "murdered"), ("manninn", "man.the.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("voice", "agentive")] }

def ex_12 : Datum :=
  { id := "wood2015_12"
    source := ⟨"wood-2015", "Ch. 3 (72b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Hraunstraumurinn myrti manninn."
    glossedTokens := [("Hraunstraumurinn", "lava.stream.the.NOM"), ("myrti", "murdered"), ("manninn", "man.the.ACC")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("voice", "agentive")] }

def ex_13 : Datum :=
  { id := "wood2015_13"
    source := ⟨"wood-2015", "Ch. 3 (72c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Maðurinn myrtist."
    glossedTokens := [("Maðurinn", "man.the.NOM"), ("myrtist", "murdered-ST")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("use", "anticausative")] }

def ex_14 : Datum :=
  { id := "wood2015_14"
    source := ⟨"wood-2015", "Ch. 5 (47a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Bjartur gaf sjálfum sér bókina í jólagjöf."
    glossedTokens := [("Bjartur", "Bjartur.NOM"), ("gaf", "gave"), ("sjálfum", "self"), ("sér", "REFL.DAT"), ("bókina", "book.the.ACC"), ("í", "in"), ("jólagjöf", "christmas.gift")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "SpecApplP")] }

def ex_15 : Datum :=
  { id := "wood2015_15"
    source := ⟨"wood-2015", "Ch. 5 (47b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Bjartur gafst bókina í jólagjöf."
    glossedTokens := [("Bjartur", "Bjartur.NOM"), ("gafst", "gave-ST"), ("bókina", "book.the.ACC"), ("í", "in"), ("jólagjöf", "christmas.gift")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("position", "SpecApplP")] }

def ex_16 : Datum :=
  { id := "wood2015_16"
    source := ⟨"wood-2015", "Ch. 5 (52a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Fólk leyfði þeim alla hluti."
    glossedTokens := [("Fólk", "people.NOM"), ("leyfði", "allowed"), ("þeim", "them.DAT"), ("alla", "all"), ("hluti", "things.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dative", "Appl")] }

def ex_17 : Datum :=
  { id := "wood2015_17"
    source := ⟨"wood-2015", "Ch. 5 (52b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þeim leyfðust allir hlutir."
    glossedTokens := [("Þeim", "them.DAT"), ("leyfðust", "allowed-ST"), ("allir", "all"), ("hlutir", "things.NOM")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dative", "Appl")] }

def ex_18 : Datum :=
  { id := "wood2015_18"
    source := ⟨"wood-2015", "Ch. 5 (53a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ásta splundraði rúðunni."
    glossedTokens := [("Ásta", "Ásta.NOM"), ("splundraði", "shattered"), ("rúðunni", "window.the.DAT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dative", "direct object")] }

def ex_19 : Datum :=
  { id := "wood2015_19"
    source := ⟨"wood-2015", "Ch. 5 (53b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Rúðan splundraðist."
    glossedTokens := [("Rúðan", "window.the.NOM"), ("splundraðist", "shattered-ST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dative", "direct object")] }

def ex_20 : Datum :=
  { id := "wood2015_20"
    source := ⟨"wood-2015", "Ch. 5 (92a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Henni leiddist Ólafur."
    glossedTokens := [("Henni", "her.DAT"), ("leiddist", "bored-ST"), ("Ólafur", "Ólafur.NOM")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "subject experiencer"), ("site", "SpecVoiceP")] }

def ex_21 : Datum :=
  { id := "wood2015_21"
    source := ⟨"wood-2015", "Ch. 6 (55a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jóna og Siggi kysstust."
    glossedTokens := [("Jóna", "Jóna"), ("og", "and"), ("Siggi", "Siggi"), ("kysstust", "kissed-ST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "reciprocal"), ("type", "2")] }

def ex_22 : Datum :=
  { id := "wood2015_22"
    source := ⟨"wood-2015", "Ch. 6 (55b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jóna kysstist við Sigga."
    glossedTokens := [("Jóna", "Jóna"), ("kysstist", "kissed-ST"), ("við", "with"), ("Sigga", "Siggi")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("use", "reciprocal"), ("type", "2")] }

def ex_23 : Datum :=
  { id := "wood2015_23"
    source := ⟨"wood-2015", "Ch. 6 (76b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Keisarinn klæddist nýjum fötum."
    glossedTokens := [("Keisarinn", "emperor.the.NOM"), ("klæddist", "dressed-ST"), ("nýjum", "new"), ("fötum", "clothes.DAT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "reflexive")] }

def all : List Datum := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14, ex_15, ex_16, ex_17, ex_18, ex_19, ex_20, ex_21, ex_22, ex_23]

end Wood2015.Examples
