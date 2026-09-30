module

public import Linglib.Data.Examples.Schema

/-!
# `Partee2010` — typed example data

Auto-generated from `Linglib/Data/Examples/Partee2010.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Partee2010.Examples`.
-/

@[expose] public section

namespace Partee2010.Examples

open Data.Examples

def ex_10a : Datum :=
  { id := "partee2010_10a"
    source := ⟨"partee-2010", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A fake gun is not a gun."
    glossedTokens := [("A", "INDEF"), ("fake", "fake"), ("gun", "gun"), ("is", "be.PRS.3SG"), ("not", "NEG"), ("a", "INDEF"), ("gun", "gun")]
    context := "Cited as an apparently-true privative entailment (the prima facie evidence for the privative class)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_10b : Datum :=
  { id := "partee2010_10b"
    source := ⟨"partee-2010", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is that gun real or fake?"
    glossedTokens := [("Is", "be.PRS.3SG"), ("that", "DEM"), ("gun", "gun"), ("real", "real"), ("or", "or"), ("fake", "fake")]
    context := "The 'gun puzzle': for this question to be well-formed, 'gun' must include both real and fake guns. Direct evidence that the noun's denotation coerces to include the adjective's extension."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_11a : Datum :=
  { id := "partee2010_11a"
    source := ⟨"nowak-2000", "(11a)"⟩
    reportedIn := some ⟨"partee-2010", "(11a)"⟩
    language := "poli1260"
    primaryText := "Kelnerki rozmawiały o przystojnym chłopcu."
    glossedTokens := [("Kelnerki", "waitress.NOM.PL"), ("rozmawiały", "talk.PST.3PL.F"), ("o", "about"), ("przystojnym", "handsome.LOC.SG.M"), ("chłopcu", "boy.LOC.SG")]
    context := "Unmarked NP-internal word order; Adj+N adjacent within the PP."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_11b : Datum :=
  { id := "partee2010_11b"
    source := ⟨"nowak-2000", "(11b)"⟩
    reportedIn := some ⟨"partee-2010", "(11b)"⟩
    language := "poli1260"
    primaryText := "O przystojnym kelnerki rozmawiały chłopcu."
    glossedTokens := [("O", "about"), ("przystojnym", "handsome.LOC.SG.M"), ("kelnerki", "waitress.NOM.PL"), ("rozmawiały", "talk.PST.3PL.F"), ("chłopcu", "boy.LOC.SG")]
    context := "NP-split: preposition + adjective in sentence-initial position, head noun sentence-final. Topic-focus structure highlights the noun."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_13b : Datum :=
  { id := "partee2010_13b"
    source := ⟨"nowak-2000", "(13b)"⟩
    reportedIn := some ⟨"partee-2010", "(13b)"⟩
    language := "poli1260"
    primaryText := "Do doliny weszliśmy rozległej."
    glossedTokens := [("Do", "to"), ("doliny", "valley.GEN.SG"), ("weszliśmy", "enter.PST.1PL"), ("rozległej", "large.GEN.SG.F")]
    context := "NP-split with intersective adjective 'rozległy' (large). The split succeeds, as expected for intersective Adj+N."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_14b : Datum :=
  { id := "partee2010_14b"
    source := ⟨"nowak-2000", "(14b)"⟩
    reportedIn := some ⟨"partee-2010", "(14b)"⟩
    language := "poli1260"
    primaryText := "Z prezydentem rozmawiała byłym."
    glossedTokens := [("Z", "with"), ("prezydentem", "president.INS.SG"), ("rozmawiała", "talk.PST.3SG.F"), ("byłym", "former.INS.SG.M")]
    context := "Attempted NP-split with non-subsective modal adjective 'były' (former). The split is ungrammatical."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def biedny_ambiguity : Datum :=
  { id := "partee2010_biedny_ambiguity"
    source := ⟨"nowak-2000", "(15b),(16a)"⟩
    reportedIn := some ⟨"partee-2010", "(15b),(16a)"⟩
    language := "poli1260"
    primaryText := "biedny"
    glossedTokens := [("biedny", "poor.NOM.SG.M")]
    context := "Polish 'biedny' is lexically ambiguous between an intersective reading 'not rich' (15b: can split in NP-split construction) and a non-subsective reading 'pitiful' (16a: cannot split). The splitting diagnostic tracks the READING, not the lexical form."
    judgment := .acceptable
    alternatives := []
    readings := [("intersective 'not rich'", .acceptable), ("non-subsective 'pitiful'", .unacceptable)]
    paperFeatures := [] }

def ex_17b : Datum :=
  { id := "partee2010_17b"
    source := ⟨"partee-2010", "(17b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't care whether that fur is fake or real."
    glossedTokens := [("I", "1SG"), ("don't", "do.PRS.NEG"), ("care", "care"), ("whether", "whether"), ("that", "DEM"), ("fur", "fur"), ("is", "be.PRS.3SG"), ("fake", "fake"), ("or", "or"), ("real", "real")]
    context := "Generalization of the (10b) gun-puzzle to 'fur'. The polar disjunction 'fake or real' presupposes that 'fur' covers both fake and real fur; otherwise 'real' would be redundant. Direct evidence of NVP-licensed coercion of the noun extension."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_19b : Datum :=
  { id := "partee2010_19b"
    source := ⟨"kamp-partee-1995", "(19b) in Partee 2010"⟩
    reportedIn := some ⟨"partee-2010", "(19b)"⟩
    language := "stan1293"
    primaryText := "a midget giant (a giant, but an exceptionally small one)"
    glossedTokens := [("a", "INDEF"), ("midget", "midget"), ("giant", "giant")]
    context := "Test case for HPP (Head Primacy Principle): the head 'giant' fixes the local domain; the modifier 'midget' is interpreted relative to that domain, yielding 'small for a giant'. Compare (19a) 'giant midget' = a midget who is exceptionally large."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_21b : Datum :=
  { id := "partee2010_21b"
    source := ⟨"kamp-partee-1995", "(21b) in Partee 2010"⟩
    reportedIn := some ⟨"partee-2010", "(21b)"⟩
    language := "stan1293"
    primaryText := "Knives are sharp."
    glossedTokens := [("Knives", "knife.PL"), ("are", "be.PRS.3PL"), ("sharp", "sharp")]
    context := "Test case for NVP (Non-Vacuity Principle). Generic predication: 'sharp' would be redundant if 'knife' presupposed sharpness; NVP forces a reading where some knives are not sharp, so the generic claim is non-vacuous."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_22b : Datum :=
  { id := "partee2010_22b"
    source := ⟨"partee-2010", "(22b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How many poets are buried in Amherst?"
    glossedTokens := [("How", "how"), ("many", "many"), ("poets", "poet.PL"), ("are", "be.PRS.3PL"), ("buried", "bury.PASS.PTCP"), ("in", "in"), ("Amherst", "Amherst")]
    context := "Demonstrates context-shift of the noun 'poet' independent of any adjective. With predicate 'buried', 'poets' presupposes dead poets; with 'live in' or similar present-tense, 'poets' presupposes living poets. Shows N's extension is itself adjustable, supporting the coercion mechanism Partee invokes for privatives."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_12a : Datum :=
  { id := "partee2010_12a"
    source := ⟨"nowak-2000", "(12a)"⟩
    reportedIn := some ⟨"partee-2010", "(12a)"⟩
    language := "poli1260"
    primaryText := "Włamano się do nowego sklepu."
    glossedTokens := [("Włamano", "break.in-NEUT.SG"), ("się", "REFL"), ("do", "to"), ("nowego", "new.GEN.SG.M"), ("sklepu", "store.GEN.SG")]
    context := "Unmarked NP-internal order; baseline for the split in (12b)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_12b : Datum :=
  { id := "partee2010_12b"
    source := ⟨"nowak-2000", "(12b)"⟩
    reportedIn := some ⟨"partee-2010", "(12b)"⟩
    language := "poli1260"
    primaryText := "Do sklepu włamano się nowego."
    glossedTokens := [("Do", "to"), ("sklepu", "store.GEN.SG"), ("włamano", "break.in-NEUT.SG"), ("się", "REFL"), ("nowego", "new.GEN.SG.M")]
    context := "NP-split: noun-in-PP sentence-initial, adjective sentence-final. Intersective 'nowy' (new) splits cleanly."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_13a : Datum :=
  { id := "partee2010_13a"
    source := ⟨"nowak-2000", "(13a)"⟩
    reportedIn := some ⟨"partee-2010", "(13a)"⟩
    language := "poli1260"
    primaryText := "Do rozległej weszliśmy doliny."
    glossedTokens := [("Do", "to"), ("rozległej", "large.GEN.SG.F"), ("weszliśmy", "enter.PST.1PL"), ("doliny", "valley.GEN.SG")]
    context := "Alternate split order: preposition + adjective initial, noun final. Pair-mate of (13b)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_14a : Datum :=
  { id := "partee2010_14a"
    source := ⟨"nowak-2000", "(14a)"⟩
    reportedIn := some ⟨"partee-2010", "(14a)"⟩
    language := "poli1260"
    primaryText := "Z byłym rozmawiała prezydentem."
    glossedTokens := [("Z", "with"), ("byłym", "former.INS.SG.M"), ("rozmawiała", "talk.PST.3SG.F"), ("prezydentem", "president.INS.SG")]
    context := "Attempted NP-split with non-subsective 'były' (former). Ungrammatical regardless of split order; pair-mate of (14b)."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_17a : Datum :=
  { id := "partee2010_17a"
    source := ⟨"partee-2010", "(17a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I don't care whether that fur is fake fur or real fur."
    glossedTokens := [("I", "1SG"), ("don't", "do.PRS.NEG"), ("care", "care"), ("whether", "whether"), ("that", "DEM"), ("fur", "fur"), ("is", "be.PRS.3SG"), ("fake", "fake"), ("fur", "fur"), ("or", "or"), ("real", "real"), ("fur", "fur")]
    context := "Explicit form of the fur disjunction, with both 'fake fur' and 'real fur' as full NPs. The acceptability shows the noun 'fur' uncontroversially covers both extensions."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_19a : Datum :=
  { id := "partee2010_19a"
    source := ⟨"kamp-partee-1995", "(19a) in Partee 2010"⟩
    reportedIn := some ⟨"partee-2010", "(19a)"⟩
    language := "stan1293"
    primaryText := "a giant midget (a midget, but an exceptionally large one)"
    glossedTokens := [("a", "INDEF"), ("giant", "giant"), ("midget", "midget")]
    context := "HPP pair-mate of (19b): with 'midget' as head, the local domain is midgets; 'giant' shifts to 'large for a midget'. Same words, opposite interpretations."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_21a : Datum :=
  { id := "partee2010_21a"
    source := ⟨"kamp-partee-1995", "(21a) in Partee 2010"⟩
    reportedIn := some ⟨"partee-2010", "(21a)"⟩
    language := "stan1293"
    primaryText := "This is a sharp knife."
    glossedTokens := [("This", "DEM"), ("is", "be.PRS.3SG"), ("a", "INDEF"), ("sharp", "sharp"), ("knife", "knife")]
    context := "Episodic predication mate of the generic (21b). Both can be true together; 'sharp' is not redundant in (21a) because NVP requires the local domain of knives to contain both sharp and non-sharp instances."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_22a : Datum :=
  { id := "partee2010_22a"
    source := ⟨"partee-2010", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "How many poets are there in Amherst?"
    glossedTokens := [("How", "how"), ("many", "many"), ("poets", "poet.PL"), ("are", "be.PRS.3PL"), ("there", "EXIST"), ("in", "in"), ("Amherst", "Amherst")]
    context := "Existential predicate companion of (22b). With 'are there', 'poets' presupposes living poets, contrasting with (22b) where 'are buried' presupposes dead poets. Same noun, context-shifted extension."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_10a, ex_10b, ex_11a, ex_11b, ex_13b, ex_14b, biedny_ambiguity, ex_17b, ex_19b, ex_21b, ex_22b, ex_12a, ex_12b, ex_13a, ex_14a, ex_17a, ex_19a, ex_21a, ex_22a]

end Partee2010.Examples
