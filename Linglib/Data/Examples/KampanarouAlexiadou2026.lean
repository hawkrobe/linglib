module

public import Linglib.Data.Examples.Schema

/-!
# `KampanarouAlexiadou2026` — typed example data

Auto-generated from `Linglib/Data/Examples/KampanarouAlexiadou2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace KampanarouAlexiadou2026.Examples`.
-/

@[expose] public section

namespace KampanarouAlexiadou2026.Examples

open Data.Examples

def ka2026_5a : Datum :=
  { id := "ka2026_5a"
    source := ⟨"kampanarou-alexiadou-2026", "(5a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "episkevasame to pomolo apo tin porta"
    glossedTokens := [("episkevasame", "fix.PST.1PL"), ("to", "DEF.SG.ACC"), ("pomolo", "handle.SG.ACC"), ("apo", "of"), ("tin", "DEF.SG.ACC"), ("porta", "door.SG.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := [("episkevasame to pomolo tis portas", .acceptable)]
    readings := []
    paperFeatures := [("section", "2"), ("group", "possessive"), ("relation", "partWhole"), ("possessor", "common"), ("animate", "no"), ("number", "sg"), ("modified", "no"), ("gap", "no")] }

def ka2026_5b : Datum :=
  { id := "ka2026_5b"
    source := ⟨"kampanarou-alexiadou-2026", "(5b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "vrasame to nero apo tin piji"
    glossedTokens := [("vrasame", "boil.PST.1PL"), ("to", "DEF.SG.ACC"), ("nero", "water.SG.ACC"), ("apo", "of"), ("tin", "DEF.SG.ACC"), ("piji", "spring.SG.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := [("vrasame to nero tis pijis", .acceptable)]
    readings := []
    paperFeatures := [("section", "2"), ("group", "possessive"), ("relation", "source"), ("possessor", "common"), ("animate", "no"), ("number", "sg"), ("modified", "no"), ("gap", "no")] }

def ka2026_5c : Datum :=
  { id := "ka2026_5c"
    source := ⟨"kampanarou-alexiadou-2026", "(5c)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "blextike i ura apo to aloɣo"
    glossedTokens := [("blextike", "tangle.PST.3SG"), ("i", "DEF.SG.NOM"), ("ura", "tail.SG.NOM"), ("apo", "of"), ("to", "DEF.SG.ACC"), ("aloɣo", "horse.SG.ACC")]
    context := ""
    judgment := .marginal
    alternatives := [("blextike i ura tu aloɣu", .acceptable)]
    readings := []
    paperFeatures := [("section", "2"), ("group", "possessive"), ("relation", "partWhole"), ("possessor", "common"), ("animate", "yes"), ("number", "sg"), ("modified", "no"), ("gap", "no")] }

def ka2026_6a : Datum :=
  { id := "ka2026_6a"
    source := ⟨"kampanarou-alexiadou-2026", "(6a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "kalesame ton aðerfo apo ta koritsja"
    glossedTokens := [("kalesame", "invite.PST.1PL"), ("ton", "DEF.SG.ACC"), ("aðerfo", "brother.SG.ACC"), ("apo", "of"), ("ta", "DEF.PL.ACC"), ("koritsja", "girl.PL.ACC")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("group", "possessive"), ("relation", "kinship"), ("possessor", "common"), ("animate", "yes"), ("number", "pl"), ("modified", "no"), ("gap", "no")] }

def ka2026_6b : Datum :=
  { id := "ka2026_6b"
    source := ⟨"kampanarou-alexiadou-2026", "(6b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "eksisa to molivi apo ti ðaskala"
    glossedTokens := [("eksisa", "sharpen.PST.1SG"), ("to", "DEF.SG.ACC"), ("molivi", "pencil.SG.ACC"), ("apo", "of"), ("ti", "DEF.SG.ACC"), ("ðaskala", "teacher.SG.ACC")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("group", "possessive"), ("relation", "ownership"), ("possessor", "common"), ("animate", "yes"), ("number", "sg"), ("modified", "no"), ("gap", "no")] }

def ka2026_9a_book : Datum :=
  { id := "ka2026_9a_book"
    source := ⟨"kampanarou-alexiadou-2026", "(9a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "evapsa to vivlio apo sena"
    glossedTokens := [("evapsa", "paint.PST.1SG"), ("to", "DEF.SG.ACC"), ("vivlio", "book.SG.ACC"), ("apo", "of"), ("sena", "2SG.ACC")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("group", "possessive"), ("relation", "ownership"), ("possessor", "pronoun"), ("animate", "yes"), ("number", "sg"), ("modified", "no"), ("gap", "no")] }

def ka2026_9a_eyes : Datum :=
  { id := "ka2026_9a_eyes"
    source := ⟨"kampanarou-alexiadou-2026", "(9a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "evapsa ta matja apo sena"
    glossedTokens := [("evapsa", "paint.PST.1SG"), ("ta", "DEF.PL.ACC"), ("matja", "eye.PL.ACC"), ("apo", "of"), ("sena", "2SG.ACC")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("group", "possessive"), ("relation", "partWhole"), ("possessor", "pronoun"), ("animate", "yes"), ("number", "sg"), ("modified", "no"), ("gap", "no")] }

def ka2026_10a_shoulder : Datum :=
  { id := "ka2026_10a_shoulder"
    source := ⟨"kampanarou-alexiadou-2026", "(10a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "travmatistike o omos apo ti Fani"
    glossedTokens := [("travmatistike", "get.hurt.PST.3SG"), ("o", "DEF.SG.NOM"), ("omos", "shoulder.SG.NOM"), ("apo", "of"), ("ti", "DEF.ACC"), ("Fani", "Fani.ACC")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("group", "possessive"), ("relation", "partWhole"), ("possessor", "properName"), ("animate", "yes"), ("number", "sg"), ("modified", "no"), ("gap", "no")] }

def ka2026_10a_mom : Datum :=
  { id := "ka2026_10a_mom"
    source := ⟨"kampanarou-alexiadou-2026", "(10a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "travmatistike i mama apo ti Fani"
    glossedTokens := [("travmatistike", "get.hurt.PST.3SG"), ("i", "DEF.SG.NOM"), ("mama", "mom.SG.NOM"), ("apo", "of"), ("ti", "DEF.ACC"), ("Fani", "Fani.ACC")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("group", "possessive"), ("relation", "kinship"), ("possessor", "properName"), ("animate", "yes"), ("number", "sg"), ("modified", "no"), ("gap", "no")] }

def ka2026_11a : Datum :=
  { id := "ka2026_11a"
    source := ⟨"kampanarou-alexiadou-2026", "(11a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "alaksa to xalaki apo tin porta"
    glossedTokens := [("alaksa", "change.PST.1SG"), ("to", "DEF.SG.ACC"), ("xalaki", "mat-DIM.SG.ACC"), ("apo", "of"), ("tin", "DEF.SG.ACC"), ("porta", "door.SG.ACC")]
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("group", "possessive"), ("relation", "association"), ("possessor", "common"), ("animate", "no"), ("number", "sg"), ("modified", "no"), ("gap", "no")] }

def ka2026_11b : Datum :=
  { id := "ka2026_11b"
    source := ⟨"kampanarou-alexiadou-2026", "(11b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "alaksa to xalaki apo tis portes"
    glossedTokens := [("alaksa", "change.PST.1SG"), ("to", "DEF.SG.ACC"), ("xalaki", "mat.DIM.SG.ACC"), ("apo", "of"), ("tis", "DEF.PL.ACC"), ("portes", "door.PL.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("group", "possessive"), ("relation", "association"), ("possessor", "common"), ("animate", "no"), ("number", "pl"), ("modified", "no"), ("gap", "no")] }

def ka2026_fn5 : Datum :=
  { id := "ka2026_fn5"
    source := ⟨"kampanarou-alexiadou-2026", "fn. 5 (i)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "alaksa to xalaki apo tin brostini porta"
    glossedTokens := [("alaksa", "change.PST.1SG"), ("to", "DEF.SG.ACC"), ("xalaki", "mat.DIM.SG.ACC"), ("apo", "of"), ("tin", "DEF.SG.ACC"), ("brostini", "front"), ("porta", "door.SG.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("group", "possessive"), ("relation", "association"), ("possessor", "common"), ("animate", "no"), ("number", "sg"), ("modified", "yes"), ("gap", "no")] }

def ka2026_14a : Datum :=
  { id := "ka2026_14a"
    source := ⟨"kampanarou-alexiadou-2026", "(14a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "i epikalipsi apo ta sokolat-akia"
    glossedTokens := [("i", "DEF.SG.NOM"), ("epikalipsi", "coating.SG.NOM"), ("apo", "of"), ("ta", "DEF.PL.ACC"), ("sokolat-akia", "chocolate-DIM.PL.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := [("i epikalipsi ton sokolat-akion", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "3"), ("group", "possessive"), ("relation", "partWhole"), ("possessor", "common"), ("animate", "no"), ("number", "pl"), ("modified", "no"), ("gap", "yes")] }

def ka2026_14b : Datum :=
  { id := "ka2026_14b"
    source := ⟨"kampanarou-alexiadou-2026", "(14b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "to trixoma apo to katsik-aki"
    glossedTokens := [("to", "DEF.SG.NOM"), ("trixoma", "fur.SG.NOM"), ("apo", "of"), ("to", "DEF.SG.ACC"), ("katsik-aki", "goat-DIM.SG.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := [("to trixoma tu katsik-akiu", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "3"), ("group", "possessive"), ("relation", "partWhole"), ("possessor", "common"), ("animate", "yes"), ("number", "sg"), ("modified", "no"), ("gap", "yes")] }

def ka2026_15a : Datum :=
  { id := "ka2026_15a"
    source := ⟨"kampanarou-alexiadou-2026", "(15a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "petai psila to baloni apo to aɣor-aki"
    glossedTokens := [("petai", "fly.3SG"), ("psila", "high"), ("to", "DEF.NOM"), ("baloni", "balloon.NOM"), ("apo", "of"), ("to", "DEF.SG.ACC"), ("aɣor-aki", "boy-DIM.SG.ACC")]
    context := ""
    judgment := .unacceptable
    alternatives := [("petai psila to baloni tu aɣor-akiu", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "3"), ("group", "possessive"), ("relation", "ownership"), ("possessor", "common"), ("animate", "yes"), ("number", "sg"), ("modified", "no"), ("gap", "yes")] }

def ka2026_15b : Datum :=
  { id := "ka2026_15b"
    source := ⟨"kampanarou-alexiadou-2026", "(15b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "efije o babas apo to peð-aki"
    glossedTokens := [("efije", "leave.PST.3SG"), ("o", "DEF.NOM"), ("babas", "dad.SG.NOM"), ("apo", "of"), ("to", "DEF.SG.ACC"), ("peð-aki", "kid-DIM.SG.ACC")]
    context := ""
    judgment := .unacceptable
    alternatives := [("efije o babas tu peð-akiu", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "3"), ("group", "possessive"), ("relation", "kinship"), ("possessor", "common"), ("animate", "yes"), ("number", "sg"), ("modified", "no"), ("gap", "yes")] }

def ka2026_28 : Datum :=
  { id := "ka2026_28"
    source := ⟨"kampanarou-alexiadou-2026", "(28)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "o babas apo to isixo peð-aki ðen ipe pola. o babas apo to zoiro peð-aki olo miluse."
    glossedTokens := [("o", "DEF.SG.NOM"), ("babas", "dad.SG.NOM"), ("apo", "of"), ("to", "DEF.SG.ACC"), ("isixo", "quiet"), ("peð-aki", "kid-DIM.SG.ACC"), ("ðen", "NEG"), ("ipe", "say.PST.3SG"), ("pola", "much"), ("o", "DEF.SG.NOM"), ("babas", "dad.SG.NOM"), ("apo", "of"), ("to", "DEF.SG.ACC"), ("zoiro", "naughty"), ("peð-aki", "kid-DIM.SG.ACC"), ("olo", "continuously"), ("miluse", "talk.PST.3SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("group", "possessive"), ("relation", "kinship"), ("possessor", "common"), ("animate", "yes"), ("number", "sg"), ("modified", "yes"), ("gap", "no")] }

def ka2026_25a : Datum :=
  { id := "ka2026_25a"
    source := ⟨"kampanarou-alexiadou-2026", "(25a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "episkevasa to stiriɣma tu poðju tu trapezju"
    glossedTokens := [("episkevasa", "fix.PST.1SG"), ("to", "DEF.SG.ACC"), ("stiriɣma", "support.SG.ACC"), ("tu", "DEF.SG.GEN"), ("poðju", "leg.SG.GEN"), ("tu", "DEF.SG.GEN"), ("trapezju", "table.SG.GEN")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("group", "stacking"), ("inner", "genitive"), ("outer", "genitive")] }

def ka2026_25b : Datum :=
  { id := "ka2026_25b"
    source := ⟨"kampanarou-alexiadou-2026", "(25b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "episkevasa to stiriɣma apo to poði apo to trapezi"
    glossedTokens := [("episkevasa", "fix.PST.1SG"), ("to", "DEF.SG.ACC"), ("stiriɣma", "support.SG.ACC"), ("apo", "of"), ("to", "DEF.SG.ACC"), ("poði", "leg.SG.ACC"), ("apo", "of"), ("to", "DEF.SG.ACC"), ("trapezi", "table.SG.ACC")]
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("group", "stacking"), ("inner", "apo"), ("outer", "apo")] }

def ka2026_27a : Datum :=
  { id := "ka2026_27a"
    source := ⟨"kampanarou-alexiadou-2026", "(27a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "episkevasa to stiriɣma apo to poði tu trapezju"
    glossedTokens := [("episkevasa", "fix.PST.1SG"), ("to", "DEF.SG.ACC"), ("stiriɣma", "support.SG.ACC"), ("apo", "of"), ("to", "DEF.SG.ACC"), ("poði", "leg.SG.ACC"), ("tu", "DEF.SG.GEN"), ("trapezju", "table.SG.GEN")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("group", "stacking"), ("inner", "apo"), ("outer", "genitive")] }

def ka2026_27b : Datum :=
  { id := "ka2026_27b"
    source := ⟨"kampanarou-alexiadou-2026", "(27b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "episkevasa to stiriɣma tu poðju apo to trapezi"
    glossedTokens := [("episkevasa", "fix.PST.1SG"), ("to", "DEF.SG.ACC"), ("stiriɣma", "support.SG.ACC"), ("tu", "DEF.SG.GEN"), ("poðju", "leg.SG.GEN"), ("apo", "of"), ("to", "DEF.SG.ACC"), ("trapezi", "table.SG.ACC")]
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("group", "stacking"), ("inner", "genitive"), ("outer", "apo")] }

def ka2026_7a : Datum :=
  { id := "ka2026_7a"
    source := ⟨"kampanarou-alexiadou-2026", "(7a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "xriazode tria lepta ja to vrasimo apo ta zimarika"
    glossedTokens := [("xriazode", "need.3PL"), ("tria", "three"), ("lepta", "minutes"), ("ja", "for"), ("to", "DEF.ACC"), ("vrasimo", "boiling.ACC"), ("apo", "of"), ("ta", "DEF.PL.ACC"), ("zimarika", "pasta.PL.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := [("xriazode tria lepta ja to vrasimo ton zimarikon", .acceptable)]
    readings := []
    paperFeatures := [("section", "2"), ("group", "derived"), ("variety", "smg"), ("theme", "apo"), ("agent", "none"), ("aspectual", "no")] }

def ka2026_8a : Datum :=
  { id := "ka2026_8a"
    source := ⟨"kampanarou-alexiadou-2026", "(8a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "kratise ena xrono i metafrasi tu miθistorimatos apo to Jani"
    glossedTokens := [("kratise", "last.PST.3SG"), ("ena", "one"), ("xrono", "year.SG.ACC"), ("i", "DEF.SG.NOM"), ("metafrasi", "translation.SG.NOM"), ("tu", "DEF.SG.GEN"), ("miθistorimatos", "novel.SG.GEN"), ("apo", "of"), ("to", "DEF.SG.ACC"), ("Jani", "John.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("group", "derived"), ("variety", "smg"), ("theme", "genitive"), ("agent", "apo"), ("aspectual", "no")] }

def ka2026_8b : Datum :=
  { id := "ka2026_8b"
    source := ⟨"kampanarou-alexiadou-2026", "(8b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "kratise ena xrono i metafrasi apo to miθistorima"
    glossedTokens := [("kratise", "last.PST.3SG"), ("ena", "one"), ("xrono", "year.SG.ACC"), ("i", "DEF.SG.NOM"), ("metafrasi", "translation.SG.NOM"), ("apo", "of"), ("to", "DEF.SG.ACC"), ("miθistorima", "novel.SG.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("group", "derived"), ("variety", "smg"), ("theme", "apo"), ("agent", "none"), ("aspectual", "no")] }

def ka2026_8c : Datum :=
  { id := "ka2026_8c"
    source := ⟨"kampanarou-alexiadou-2026", "(8c)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "kratise ena xrono i metafrasi apo to miθistorima tu Jani"
    glossedTokens := [("kratise", "last.PST.3SG"), ("ena", "one"), ("xrono", "year.SG.ACC"), ("i", "DEF.SG.NOM"), ("metafrasi", "translation.SG.NOM"), ("apo", "of"), ("to", "DEF.SG.ACC"), ("miθistorima", "novel.SG.ACC."), ("tu", "DEF.SG.GEN"), ("Jani", "John.GEN")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("group", "derived"), ("variety", "smg"), ("theme", "apo"), ("agent", "genitive"), ("aspectual", "no")] }

def ka2026_8d : Datum :=
  { id := "ka2026_8d"
    source := ⟨"kampanarou-alexiadou-2026", "(8d)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "kratise ena xrono i metafrasi apo to miθistorima apo to Jani"
    glossedTokens := [("kratise", "last.PST.3SG"), ("ena", "one"), ("xrono", "year.SG.ACC"), ("i", "DEF.SG.NOM"), ("metafrasi", "translation.SG.NOM"), ("apo", "of"), ("to", "DEF.SG.ACC"), ("miθistorima", "novel.SG.ACC"), ("apo", "of"), ("to", "DEF.SG.ACC"), ("Jani", "John.ACC")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("group", "derived"), ("variety", "smg"), ("theme", "apo"), ("agent", "apo"), ("aspectual", "no")] }

def ka2026_12 : Datum :=
  { id := "ka2026_12"
    source := ⟨"kampanarou-alexiadou-2026", "(12)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "i piriɣrafi ap tun ðimarxu ap ta piðja"
    glossedTokens := [("i", "DEF.SG.NOM"), ("piriɣrafi", "description.SG.NOM"), ("ap", "of"), ("tun", "DEF.SG.ACC"), ("ðimarxu", "mayor.SG.ACC"), ("ap", "of"), ("ta", "DEF.PL.ACC"), ("piðja", "kid.PL.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("group", "derived"), ("variety", "grevena"), ("theme", "apo"), ("agent", "apo"), ("aspectual", "no")] }

def ka2026_30a : Datum :=
  { id := "ka2026_30a"
    source := ⟨"kampanarou-alexiadou-2026", "(30a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "i katastrofi tis polis apo tus varvarus"
    glossedTokens := [("i", "DEF.SG.NOM"), ("katastrofi", "destruction.SG.NOM"), ("tis", "DEF.SG.GEN"), ("polis", "city.SG.GEN"), ("apo", "by"), ("tus", "DEF.PL.ACC"), ("varvarus", "barbarian.PL.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6"), ("group", "derived"), ("variety", "smg"), ("theme", "genitive"), ("agent", "apo"), ("aspectual", "no")] }

def ka2026_33b : Datum :=
  { id := "ka2026_33b"
    source := ⟨"kampanarou-alexiadou-2026", "(33b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "to kolibi apo tus aθlites"
    glossedTokens := [("to", "DEF.SG.NOM"), ("kolibi", "swimming.SG.NOM"), ("apo", "of"), ("tus", "DEF.PL.ACC"), ("aθlites", "athlete.PL.ACC")]
    context := ""
    judgment := .marginal
    alternatives := [("to kolibi ton aθliton", .acceptable)]
    readings := []
    paperFeatures := [("section", "6"), ("group", "derived"), ("variety", "smg"), ("theme", "apo"), ("agent", "none"), ("aspectual", "no")] }

def ka2026_34a : Datum :=
  { id := "ka2026_34a"
    source := ⟨"kampanarou-alexiadou-2026", "(34a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "i kinisi apo tus planites ja ekatomiria xronja"
    glossedTokens := [("i", "DEF.SG.NOM"), ("kinisi", "movement.SG.NOM"), ("apo", "of"), ("tus", "DEF.PL.ACC"), ("planites", "planet.PL.ACC"), ("ja", "for"), ("ekatomiria", "million.PL.ACC"), ("xronja", "year.PL.ACC")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "6"), ("group", "derived"), ("variety", "smg"), ("theme", "apo"), ("agent", "none"), ("aspectual", "yes")] }

def ka2026_35a : Datum :=
  { id := "ka2026_35a"
    source := ⟨"kampanarou-alexiadou-2026", "(35a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "i kinisi ton planiton ja ekatomiria xronja"
    glossedTokens := [("i", "DEF.SG.NOM"), ("kinisi", "movement.SG.NOM"), ("ton", "DEF.PL.GEN"), ("planiton", "planet.PL.GEN"), ("ja", "for"), ("ekatomiria", "million.PL.ACC"), ("xronja", "year.PL.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6"), ("group", "derived"), ("variety", "smg"), ("theme", "genitive"), ("agent", "none"), ("aspectual", "yes")] }

def ka2026_36a : Datum :=
  { id := "ka2026_36a"
    source := ⟨"kampanarou-alexiadou-2026", "(36a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "meletun tis kinisis apo tus planites"
    glossedTokens := [("meletun", "study.3PL"), ("tis", "DEF.PL.ACC"), ("kinisis", "movement.PL.ACC"), ("apo", "of"), ("tus", "DEF.PL.ACC"), ("planites", "planet.PL.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "6"), ("group", "derived"), ("variety", "smg"), ("theme", "apo"), ("agent", "none"), ("aspectual", "no")] }

def ka2026_38a : Datum :=
  { id := "ka2026_38a"
    source := ⟨"kampanarou-alexiadou-2026", "(38a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "espase ena poði kaθe trapezju"
    glossedTokens := [("espase", "break.PST.3SG"), ("ena", "a"), ("poði", "leg.SG.ACC"), ("kaθe", "each"), ("trapezju", "table.SG.GEN")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .acceptable)]
    paperFeatures := [("section", "7"), ("group", "scope"), ("marking", "genitive"), ("relation", "partWhole")] }

def ka2026_38b : Datum :=
  { id := "ka2026_38b"
    source := ⟨"kampanarou-alexiadou-2026", "(38b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "espase ena pexniði kaθe peðju"
    glossedTokens := [("espase", "break.PST.3SG"), ("ena", "a"), ("pexniði", "toy.SG.ACC"), ("kaθe", "each"), ("peðju", "kid.SG.GEN")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .unacceptable), ("inverse", .acceptable)]
    paperFeatures := [("section", "7"), ("group", "scope"), ("marking", "genitive"), ("relation", "ownership")] }

def ka2026_39a : Datum :=
  { id := "ka2026_39a"
    source := ⟨"kampanarou-alexiadou-2026", "(39a)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "espase ena poði apo kaθe trapezi"
    glossedTokens := [("espase", "break.PST.3SG"), ("ena", "a"), ("poði", "leg.SG.ACC"), ("apo", "of"), ("kaθe", "each"), ("trapezi", "table.SG.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .acceptable)]
    paperFeatures := [("section", "7"), ("group", "scope"), ("marking", "apo"), ("relation", "partWhole")] }

def ka2026_39b : Datum :=
  { id := "ka2026_39b"
    source := ⟨"kampanarou-alexiadou-2026", "(39b)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "espase ena pexniði apo kaθe peði"
    glossedTokens := [("espase", "break.PST.3SG"), ("ena", "a"), ("pexniði", "toy.SG.ACC"), ("apo", "of"), ("kaθe", "each"), ("peði", "kid.SG.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .acceptable)]
    paperFeatures := [("section", "7"), ("group", "scope"), ("marking", "apo"), ("relation", "ownership")] }

def all : List Datum := [ka2026_5a, ka2026_5b, ka2026_5c, ka2026_6a, ka2026_6b, ka2026_9a_book, ka2026_9a_eyes, ka2026_10a_shoulder, ka2026_10a_mom, ka2026_11a, ka2026_11b, ka2026_fn5, ka2026_14a, ka2026_14b, ka2026_15a, ka2026_15b, ka2026_28, ka2026_25a, ka2026_25b, ka2026_27a, ka2026_27b, ka2026_7a, ka2026_8a, ka2026_8b, ka2026_8c, ka2026_8d, ka2026_12, ka2026_30a, ka2026_33b, ka2026_34a, ka2026_35a, ka2026_36a, ka2026_38a, ka2026_38b, ka2026_39a, ka2026_39b]

end KampanarouAlexiadou2026.Examples
