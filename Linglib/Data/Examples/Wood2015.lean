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

def ex_1 : LinguisticExample :=
  { id := "wood2015_1"
    source := ⟨"wood-2015", "Ch. 2 (1a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jóna og Siggi kysstust eftir ballið."
    discourseSegments := []
    glossedTokens := [("Jóna", "Jóna.NOM"), ("og", "and"), ("Siggi", "Siggi.NOM"), ("kysstust", "kissed-ST"), ("eftir", "after"), ("ballið", "dance.the")]
    translation := "Jóna and Siggi kissed after the dance."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "reciprocal")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2 : LinguisticExample :=
  { id := "wood2015_2"
    source := ⟨"wood-2015", "Ch. 2 (1b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jón dulbjóst sem prestur."
    discourseSegments := []
    glossedTokens := [("Jón", "John.NOM"), ("dulbjóst", "disguised-ST"), ("sem", "as"), ("prestur", "priest")]
    translation := "John disguised himself as a priest."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "reflexive")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3 : LinguisticExample :=
  { id := "wood2015_3"
    source := ⟨"wood-2015", "Ch. 2 (1c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Glugginn opnaðist af sjálfu sér."
    discourseSegments := []
    glossedTokens := [("Glugginn", "window.the.NOM"), ("opnaðist", "opened-ST"), ("af", "by"), ("sjálfu", "self.DAT"), ("sér", "REFL")]
    translation := "The window opened by itself."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "anticausative")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4 : LinguisticExample :=
  { id := "wood2015_4"
    source := ⟨"wood-2015", "Ch. 2 (1d)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Rafmagnsbílar seljast vel hér."
    discourseSegments := []
    glossedTokens := [("Rafmagnsbílar", "electric.cars.NOM"), ("seljast", "sell-ST"), ("vel", "well"), ("hér", "here")]
    translation := "Electric cars sell well here."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "generic middle")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5 : LinguisticExample :=
  { id := "wood2015_5"
    source := ⟨"wood-2015", "Ch. 3 (16a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Fólk dýp-ka-ði skurðinn."
    discourseSegments := []
    glossedTokens := [("Fólk", "people.NOM"), ("dýp-ka-ði", "deep-KA-PST"), ("skurðinn", "ditch.the.ACC")]
    translation := "People deepened the ditch."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("exponent", "-ka"), ("voice", "Voice{D}")]
    comment := "-ka spells out v in the context of listed roots and is indifferent to Voice."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6 : LinguisticExample :=
  { id := "wood2015_6"
    source := ⟨"wood-2015", "Ch. 3 (16b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Skurðurinn dýp-ka-ði."
    discourseSegments := []
    glossedTokens := [("Skurðurinn", "ditch.the.NOM"), ("dýp-ka-ði", "deep-KA-PST")]
    translation := "The ditch deepened."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("exponent", "-ka"), ("voice", "Voice{}")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7 : LinguisticExample :=
  { id := "wood2015_7"
    source := ⟨"wood-2015", "Ch. 3 (20a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jón hita-ði vatnið."
    discourseSegments := []
    glossedTokens := [("Jón", "John.NOM"), ("hita-ði", "heat-3SG.PST"), ("vatnið", "water.the.ACC")]
    translation := "John heated the water."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("voice", "Voice{D}")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8 : LinguisticExample :=
  { id := "wood2015_8"
    source := ⟨"wood-2015", "Ch. 3 (20b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Vatnið hit-na-ði."
    discourseSegments := []
    glossedTokens := [("Vatnið", "water.the.NOM"), ("hit-na-ði", "heat-NA-3SG.PST")]
    translation := "The water heated."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("exponent", "-na"), ("voice", "Voice{}")]
    comment := "-na spells out specifierless Voice in the context of listed roots, adjacent to the root because v is zero."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_9 : LinguisticExample :=
  { id := "wood2015_9"
    source := ⟨"wood-2015", "Ch. 3 (52)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Dyrnar opnuðust."
    discourseSegments := []
    glossedTokens := [("Dyrnar", "door.the.NOM"), ("opnuðust", "opened-ST")]
    translation := "The door opened."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "anticausative"), ("site", "SpecVoiceP")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10 : LinguisticExample :=
  { id := "wood2015_10"
    source := ⟨"wood-2015", "Ch. 3 (70)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Rúðan splundraðist."
    discourseSegments := []
    glossedTokens := [("Rúðan", "window.the.NOM"), ("splundraðist", "shattered-ST")]
    translation := "The window shattered."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "anticausative"), ("site", "SpecVoiceP")]
    comment := "The root is incompatible with specifierless Voice, so the anticausative needs Voice{D} with -st in its specifier."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_11 : LinguisticExample :=
  { id := "wood2015_11"
    source := ⟨"wood-2015", "Ch. 3 (72a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Konan myrti manninn."
    discourseSegments := []
    glossedTokens := [("Konan", "woman.the.NOM"), ("myrti", "murdered"), ("manninn", "man.the.ACC")]
    translation := "The woman murdered the man."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("voice", "agentive")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12 : LinguisticExample :=
  { id := "wood2015_12"
    source := ⟨"wood-2015", "Ch. 3 (72b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Hraunstraumurinn myrti manninn."
    discourseSegments := []
    glossedTokens := [("Hraunstraumurinn", "lava.stream.the.NOM"), ("myrti", "murdered"), ("manninn", "man.the.ACC")]
    translation := "The lava stream murdered the man."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("voice", "agentive")]
    comment := "Generable only with a sentient lava stream: murdering events force the agentive alloseme of Voice."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_13 : LinguisticExample :=
  { id := "wood2015_13"
    source := ⟨"wood-2015", "Ch. 3 (72c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Maðurinn myrtist."
    discourseSegments := []
    glossedTokens := [("Maðurinn", "man.the.NOM"), ("myrtist", "murdered-ST")]
    translation := "The man got murdered."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("use", "anticausative")]
    comment := "Not generable: Voice must be agentive, and -st cannot saturate the agent role."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_14 : LinguisticExample :=
  { id := "wood2015_14"
    source := ⟨"wood-2015", "Ch. 5 (47a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Bjartur gaf sjálfum sér bókina í jólagjöf."
    discourseSegments := []
    glossedTokens := [("Bjartur", "Bjartur.NOM"), ("gaf", "gave"), ("sjálfum", "self"), ("sér", "REFL.DAT"), ("bókina", "book.the.ACC"), ("í", "in"), ("jólagjöf", "christmas.gift")]
    translation := "Bjartur gave himself the book as a Christmas present."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "SpecApplP")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_15 : LinguisticExample :=
  { id := "wood2015_15"
    source := ⟨"wood-2015", "Ch. 5 (47b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Bjartur gafst bókina í jólagjöf."
    discourseSegments := []
    glossedTokens := [("Bjartur", "Bjartur.NOM"), ("gafst", "gave-ST"), ("bókina", "book.the.ACC"), ("í", "in"), ("jólagjöf", "christmas.gift")]
    translation := "Bjartur gave himself the book as a Christmas present."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("position", "SpecApplP")]
    comment := "-st cannot merge in SpecApplP, which demands dative."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_16 : LinguisticExample :=
  { id := "wood2015_16"
    source := ⟨"wood-2015", "Ch. 5 (52a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Fólk leyfði þeim alla hluti."
    discourseSegments := []
    glossedTokens := [("Fólk", "people.NOM"), ("leyfði", "allowed"), ("þeim", "them.DAT"), ("alla", "all"), ("hluti", "things.ACC")]
    translation := "People allowed them all things."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dative", "Appl")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_17 : LinguisticExample :=
  { id := "wood2015_17"
    source := ⟨"wood-2015", "Ch. 5 (52b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Þeim leyfðust allir hlutir."
    discourseSegments := []
    glossedTokens := [("Þeim", "them.DAT"), ("leyfðust", "allowed-ST"), ("allir", "all"), ("hlutir", "things.NOM")]
    translation := "They were allowed all things."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dative", "Appl")]
    comment := "The Appl dative is retained under -st."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_18 : LinguisticExample :=
  { id := "wood2015_18"
    source := ⟨"wood-2015", "Ch. 5 (53a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ásta splundraði rúðunni."
    discourseSegments := []
    glossedTokens := [("Ásta", "Ásta.NOM"), ("splundraði", "shattered"), ("rúðunni", "window.the.DAT")]
    translation := "Ásta shattered the window."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dative", "direct object")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_19 : LinguisticExample :=
  { id := "wood2015_19"
    source := ⟨"wood-2015", "Ch. 5 (53b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Rúðan splundraðist."
    discourseSegments := []
    glossedTokens := [("Rúðan", "window.the.NOM"), ("splundraðist", "shattered-ST")]
    translation := "The window shattered."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dative", "direct object")]
    comment := "The direct object dative, dependent on Voice, is lost under -st."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_20 : LinguisticExample :=
  { id := "wood2015_20"
    source := ⟨"wood-2015", "Ch. 5 (92a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Henni leiddist Ólafur."
    discourseSegments := []
    glossedTokens := [("Henni", "her.DAT"), ("leiddist", "bored-ST"), ("Ólafur", "Ólafur.NOM")]
    translation := "She was bored by Ólafur."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "subject experiencer"), ("site", "SpecVoiceP")]
    comment := "-st in SpecVoiceP with the dative introduced in SpecApplP."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_21 : LinguisticExample :=
  { id := "wood2015_21"
    source := ⟨"wood-2015", "Ch. 6 (55a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jóna og Siggi kysstust."
    discourseSegments := []
    glossedTokens := [("Jóna", "Jóna"), ("og", "and"), ("Siggi", "Siggi"), ("kysstust", "kissed-ST")]
    translation := "Jóna and Siggi kissed."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "reciprocal"), ("type", "2")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_22 : LinguisticExample :=
  { id := "wood2015_22"
    source := ⟨"wood-2015", "Ch. 6 (55b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jóna kysstist við Sigga."
    discourseSegments := []
    glossedTokens := [("Jóna", "Jóna"), ("kysstist", "kissed-ST"), ("við", "with"), ("Sigga", "Siggi")]
    translation := "Jóna kissed with Siggi."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("use", "reciprocal"), ("type", "2")]
    comment := "A Type 2 reciprocal takes no við phrase and no singular subject."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23 : LinguisticExample :=
  { id := "wood2015_23"
    source := ⟨"wood-2015", "Ch. 6 (76b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Keisarinn klæddist nýjum fötum."
    discourseSegments := []
    glossedTokens := [("Keisarinn", "emperor.the.NOM"), ("klæddist", "dressed-ST"), ("nýjum", "new"), ("fötum", "clothes.DAT")]
    translation := "The emperor dressed himself in new clothes."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("use", "reflexive")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14, ex_15, ex_16, ex_17, ex_18, ex_19, ex_20, ex_21, ex_22, ex_23]

end Wood2015.Examples
