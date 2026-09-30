module

public import Linglib.Data.Examples.Schema

/-!
# `HarizanovGribanova2019` — typed example data

Auto-generated from `Linglib/Data/Examples/HarizanovGribanova2019.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HarizanovGribanova2019.Examples`.
-/

@[expose] public section

namespace HarizanovGribanova2019.Examples

open Data.Examples

def ex2a : Datum :=
  { id := "harizanovgribanova2019_ex2a"
    source := ⟨"harley-2013-diagnosing", "p. 113, (2)"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(2a)"⟩
    language := "stan1290"
    primaryText := "Astérix mangeait souvent du sanglier."
    glossedTokens := [("Astérix", "Asterix"), ("mangeait", "eat.3.IMPF"), ("souvent", "often"), ("du", "of"), ("sanglier.", "boar")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "finiteVerbPlacement"), ("diagnostic", "adverb")] }

def ex2b : Datum :=
  { id := "harizanovgribanova2019_ex2b"
    source := ⟨"harley-2013-diagnosing", "p. 113, (2)"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(2b)"⟩
    language := "stan1290"
    primaryText := "Astérix souvent mangeait du sanglier."
    glossedTokens := [("Astérix", "Asterix"), ("souvent", "often"), ("mangeait", "eat.3.IMPF"), ("du", "of"), ("sanglier.", "boar")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "finiteVerbPlacement"), ("diagnostic", "adverb")] }

def ex3a : Datum :=
  { id := "harizanovgribanova2019_ex3a"
    source := ⟨"harley-2013-morphemes", "p. 46, (1)"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(3a)"⟩
    language := "stan1290"
    primaryText := "Jean ne parlait pas français."
    glossedTokens := [("Jean", "Jean"), ("ne", "NE"), ("parlait", "speak.3.IMPF"), ("pas", "not"), ("français.", "French")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "finiteVerbPlacement"), ("diagnostic", "negation")] }

def ex3b : Datum :=
  { id := "harizanovgribanova2019_ex3b"
    source := ⟨"harley-2013-morphemes", "p. 46, (1)"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(3b)"⟩
    language := "stan1290"
    primaryText := "Jean ne pas parlait français."
    glossedTokens := [("Jean", "Jean"), ("ne", "NE"), ("pas", "not"), ("parlait", "speak.3.IMPF"), ("français.", "French")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "finiteVerbPlacement"), ("diagnostic", "negation")] }

def ex4a : Datum :=
  { id := "harizanovgribanova2019_ex4a"
    source := ⟨"pollock-1989", "p. 367, (5b)"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(4a)"⟩
    language := "stan1290"
    primaryText := "Mes amis aiment tous Marie."
    glossedTokens := [("Mes", "my"), ("amis", "friends"), ("aiment", "love.3PL.PRES"), ("tous", "all"), ("Marie.", "Marie")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "finiteVerbPlacement"), ("diagnostic", "quantifier")] }

def ex4b : Datum :=
  { id := "harizanovgribanova2019_ex4b"
    source := ⟨"pollock-1989", "p. 367, (5d)"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(4b)"⟩
    language := "stan1290"
    primaryText := "Mes amis tous aiment Marie."
    glossedTokens := [("Mes", "my"), ("amis", "friends"), ("tous", "all"), ("aiment", "love.3PL.PRES"), ("Marie.", "Marie")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "finiteVerbPlacement"), ("diagnostic", "quantifier")] }

def ex5a : Datum :=
  { id := "harizanovgribanova2019_ex5a"
    source := ⟨"pollock-1989", "p. 377, (24a), adapted"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(5a)"⟩
    language := "stan1290"
    primaryText := "à peine parler l'italien ..."
    glossedTokens := [("à", "hardly"), ("parler", "speak"), ("l'italien", "Italian")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "nonfiniteVerbPlacement"), ("diagnostic", "adverb")] }

def ex5b : Datum :=
  { id := "harizanovgribanova2019_ex5b"
    source := ⟨"pollock-1989", "p. 374, (16e), adapted"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(5b)"⟩
    language := "stan1290"
    primaryText := "ne pas regarder la télévision ..."
    glossedTokens := [("ne", "NE"), ("pas", "not"), ("regarder", "to.watch"), ("la", "the"), ("télévision", "television")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "nonfiniteVerbPlacement"), ("diagnostic", "negation")] }

def ex5c : Datum :=
  { id := "harizanovgribanova2019_ex5c"
    source := ⟨"pollock-1989", "p. 377, (25c), adapted"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(5c)"⟩
    language := "stan1290"
    primaryText := "... tous sortir en même temps de la salle"
    glossedTokens := [("tous", "all"), ("sortir", "leave"), ("en", "at"), ("même", "same"), ("temps", "time"), ("de", "from"), ("la", "the"), ("salle", "room")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "nonfiniteVerbPlacement"), ("diagnostic", "quantifier")] }

def ex6a : Datum :=
  { id := "harizanovgribanova2019_ex6a"
    source := ⟨"harizanov-gribanova-2019", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Paul has arrived on campus."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "tToC")] }

def ex6b : Datum :=
  { id := "harizanovgribanova2019_ex6b"
    source := ⟨"harizanov-gribanova-2019", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Has Paul arrived on campus?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "tToC")] }

def ex7a : Datum :=
  { id := "harizanovgribanova2019_ex7a"
    source := ⟨"harizanov-gribanova-2019", "(7a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Ich glaube, dass Fritz dieses Auto in München geklaut hat."
    glossedTokens := [("Ich", "I"), ("glaube,", "believe"), ("dass", "that"), ("Fritz", "Fritz"), ("dieses", "this"), ("Auto", "car"), ("in", "in"), ("München", "Munich"), ("geklaut", "stolen"), ("hat.", "has")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "tToC")] }

def ex7b : Datum :=
  { id := "harizanovgribanova2019_ex7b"
    source := ⟨"harizanov-gribanova-2019", "(7b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Dieses Auto hat Fritz in München geklaut."
    glossedTokens := [("Dieses", "this"), ("Auto", "car"), ("hat", "has"), ("Fritz", "Fritz"), ("in", "in"), ("München", "Munich"), ("geklaut.", "stolen")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "tToC")] }

def ex8a : Datum :=
  { id := "harizanovgribanova2019_ex8a"
    source := ⟨"vikner-1995", "p. 47, (33c)"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(8a)"⟩
    language := "dani1285"
    primaryText := "Peter drikker often kaffe om morgonen."
    glossedTokens := [("Peter", "Peter"), ("drikker", "drinks"), ("often", "often"), ("kaffe", "coffee"), ("om", "in"), ("morgonen.", "morning.DEF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "finiteVerbPlacement"), ("clause", "root"), ("diagnostic", "adverb")] }

def ex8b : Datum :=
  { id := "harizanovgribanova2019_ex8b"
    source := ⟨"vikner-1995", "p. 47, (33f)"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(8b)"⟩
    language := "dani1285"
    primaryText := "Vi ved at Peter ofte drikker kaffe om morgenen."
    glossedTokens := [("Vi", "we"), ("ved", "know"), ("at", "that"), ("Peter", "Peter"), ("ofte", "often"), ("drikker", "drinks"), ("kaffe", "coffee"), ("om", "in"), ("morgenen.", "morning.DEF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "finiteVerbPlacement"), ("clause", "embedded"), ("diagnostic", "adverb")] }

def ex9a : Datum :=
  { id := "harizanovgribanova2019_ex9a"
    source := ⟨"vikner-1995", "p. 145, (32b)"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(9a)"⟩
    language := "dani1285"
    primaryText := "Jeg spurgte hvorfor Peter ofte havde læst den."
    glossedTokens := [("Jeg", "I"), ("spurgte", "asked"), ("hvorfor", "why"), ("Peter", "Peter"), ("ofte", "often"), ("havde", "had"), ("læst", "read"), ("den.", "it")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "finiteVerbPlacement"), ("clause", "embedded"), ("diagnostic", "adverb")] }

def ex9b : Datum :=
  { id := "harizanovgribanova2019_ex9b"
    source := ⟨"vikner-1995", "p. 145, (32a)"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(9b)"⟩
    language := "dani1285"
    primaryText := "Jeg spurgte hvorfor Peter havde ofte læst den."
    glossedTokens := [("Jeg", "I"), ("spurgte", "asked"), ("hvorfor", "why"), ("Peter", "Peter"), ("havde", "had"), ("ofte", "often"), ("læst", "read"), ("den.", "it")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "finiteVerbPlacement"), ("clause", "embedded"), ("diagnostic", "adverb")] }

def ex10a : Datum :=
  { id := "harizanovgribanova2019_ex10a"
    source := ⟨"vikner-1995", "p. 145, (31b)"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(10a)"⟩
    language := "dani1285"
    primaryText := "Jeg spurgte hvorfor Peter ikke havde læst den."
    glossedTokens := [("Jeg", "I"), ("spurgte", "asked"), ("hvorfor", "why"), ("Peter", "Peter"), ("ikke", "not"), ("havde", "had"), ("læst", "read"), ("den.", "it")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "finiteVerbPlacement"), ("clause", "embedded"), ("diagnostic", "negation")] }

def ex10b : Datum :=
  { id := "harizanovgribanova2019_ex10b"
    source := ⟨"vikner-1995", "p. 145, (31a)"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(10b)"⟩
    language := "dani1285"
    primaryText := "Jeg spurgte hvorfor Peter havde ikke læst den."
    glossedTokens := [("Jeg", "I"), ("spurgte", "asked"), ("hvorfor", "why"), ("Peter", "Peter"), ("havde", "had"), ("ikke", "not"), ("læst", "read"), ("den.", "it")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "finiteVerbPlacement"), ("clause", "embedded"), ("diagnostic", "negation")] }

def ex11 : Datum :=
  { id := "harizanovgribanova2019_ex11"
    source := ⟨"harizanov-gribanova-2019", "(11)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "ne za-bol'-e-va-la"
    glossedTokens := [("ne", "NEG"), ("za-bol'-e-va-la", "PFX-hurt-THEME-2IMPF-PST.SG.F")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "verbalComplex")] }

def ex12 : Datum :=
  { id := "harizanovgribanova2019_ex12"
    source := ⟨"gribanova-2017", "p. 1095, (32)"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(12)"⟩
    language := "russ1263"
    primaryText := "Ivan často ubiraet (*často) komnatu."
    glossedTokens := [("Ivan", "Ivan.NOM"), ("často", "often"), ("ubiraet", "cleans.3SG"), ("(*často)", "often"), ("komnatu.", "room.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "finiteVerbPlacement"), ("diagnostic", "adverb")] }

def ex13 : Datum :=
  { id := "harizanovgribanova2019_ex13"
    source := ⟨"gribanova-2017", "p. 1095, (33)"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(13)"⟩
    language := "russ1263"
    primaryText := "My vse čitaem (*vse) gazetu."
    glossedTokens := [("My", "we.NOM"), ("vse", "all"), ("čitaem", "read.1PL"), ("(*vse)", "all"), ("gazetu.", "newspaper.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "finiteVerbPlacement"), ("diagnostic", "quantifier")] }

def ex14 : Datum :=
  { id := "harizanovgribanova2019_ex14"
    source := ⟨"gribanova-2013", "p. 96, (8)"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(14)"⟩
    language := "russ1263"
    primaryText := "Petja budet priglašat' Mašu v muzej segodnja, a Dinu v kino zavtra."
    glossedTokens := [("Petja", "Petja.NOM"), ("budet", "will.3SG"), ("priglašat'", "invite.INF"), ("Mašu", "Maša.ACC"), ("v", "in"), ("muzej", "museum"), ("segodnja,", "today"), ("a", "CONJ"), ("Dinu", "Dina.ACC"), ("v", "in"), ("kino", "movie"), ("zavtra.", "tomorrow")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("phenomenon", "finiteVerbPlacement"), ("diagnostic", "coordination")] }

def ex29a : Datum :=
  { id := "harizanovgribanova2019_ex29a"
    source := ⟨"harizanov-2016", "p. 1, (3)"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(29a)"⟩
    language := "bulg1262"
    primaryText := "Bjah pročel knigata."
    glossedTokens := [("Bjah", "had"), ("pročel", "read"), ("knigata.", "the.book")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.2"), ("phenomenon", "longHeadMovement"), ("order", "auxiliaryParticiple")] }

def ex29b : Datum :=
  { id := "harizanovgribanova2019_ex29b"
    source := ⟨"harizanov-2016", "p. 1, (3)"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(29b)"⟩
    language := "bulg1262"
    primaryText := "Pročel bjah knigata."
    glossedTokens := [("Pročel", "read"), ("bjah", "had"), ("knigata.", "the.book")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.2"), ("phenomenon", "longHeadMovement"), ("order", "participleAuxiliary")] }

def ex30a : Datum :=
  { id := "harizanovgribanova2019_ex30a"
    source := ⟨"harizanov-2016", "p. 1, (4)"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(30a)"⟩
    language := "bulg1262"
    primaryText := "Razbrah če e pročel knigata."
    glossedTokens := [("Razbrah", "understood.1.SG"), ("če", "that"), ("e", "is"), ("pročel", "read"), ("knigata.", "the.book")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.2"), ("phenomenon", "longHeadMovement"), ("order", "auxiliaryParticiple")] }

def ex30b : Datum :=
  { id := "harizanovgribanova2019_ex30b"
    source := ⟨"harizanov-2016", "p. 1, (4)"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(30b)"⟩
    language := "bulg1262"
    primaryText := "Razbrah če pročel e knigata."
    glossedTokens := [("Razbrah", "understood.1.SG"), ("če", "that"), ("pročel", "read"), ("e", "is"), ("knigata.", "the.book")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.2"), ("phenomenon", "longHeadMovement"), ("order", "participleAuxiliary")] }

def ex31a : Datum :=
  { id := "harizanovgribanova2019_ex31a"
    source := ⟨"embick-izvorski-1997", "(30)"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(31a)"⟩
    language := "bulg1262"
    primaryText := "Šte săm pročel knigata."
    glossedTokens := [("Šte", "will"), ("săm", "have"), ("pročel", "read"), ("knigata.", "the.book")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.2"), ("phenomenon", "longHeadMovement"), ("order", "auxiliaryParticiple")] }

def ex31b : Datum :=
  { id := "harizanovgribanova2019_ex31b"
    source := ⟨"embick-izvorski-1997", "(30)"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(31b)"⟩
    language := "bulg1262"
    primaryText := "Pročel šte săm knigata."
    glossedTokens := [("Pročel", "read"), ("šte", "will"), ("săm", "have"), ("knigata.", "the.book")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.2"), ("phenomenon", "longHeadMovement"), ("order", "participleAuxiliary"), ("locality", "crossesTwoHeads")] }

def ex32a : Datum :=
  { id := "harizanovgribanova2019_ex32a"
    source := ⟨"harizanov-2016", "p. 7, (23)"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(32a)"⟩
    language := "bulg1262"
    primaryText := "zagazil može [ da e ]"
    glossedTokens := [("zagazil", "gotten.in.trouble"), ("može", "might"), ("da", "to"), ("e", "be")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.2"), ("phenomenon", "longHeadMovement"), ("locality", "crossesNontensedClause")] }

def ex32b : Datum :=
  { id := "harizanovgribanova2019_ex32b"
    source := ⟨"harizanov-2016", "p. 7, (23)"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(32b)"⟩
    language := "bulg1262"
    primaryText := "zaspali si pomislih [ če bjaha decata veče. ]"
    glossedTokens := [("zaspali", "fallen.asleep"), ("si", "REFL"), ("pomislih", "I.thought"), ("če", "that"), ("bjaha", "were"), ("decata", "the.children"), ("veče.", "already")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.2"), ("phenomenon", "longHeadMovement"), ("locality", "crossesTensedClause")] }

def ex33a : Datum :=
  { id := "harizanovgribanova2019_ex33a"
    source := ⟨"harizanov-2016", "p. 7, (24)"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(33a)"⟩
    language := "bulg1262"
    primaryText := "polučila si trăgna [ predi da e podarăka si ]"
    glossedTokens := [("polučila", "received"), ("si", "REFL"), ("trăgna", "left.3.SG"), ("predi", "before"), ("da", "to"), ("e", "is"), ("podarăka", "the.gift"), ("si", "REFL")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.2"), ("phenomenon", "longHeadMovement"), ("locality", "island")] }

def ex33b : Datum :=
  { id := "harizanovgribanova2019_ex33b"
    source := ⟨"harizanov-2016", "p. 7, (24)"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(33b)"⟩
    language := "bulg1262"
    primaryText := "pročel [ ne beše novata kniga ]"
    glossedTokens := [("pročel", "read"), ("ne", "not"), ("beše", "was"), ("novata", "the.new"), ("kniga", "book")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.3.2"), ("phenomenon", "longHeadMovement"), ("locality", "island")] }

def ex42 : Datum :=
  { id := "harizanovgribanova2019_ex42"
    source := ⟨"harizanov-gribanova-2019", "(42)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "ne po-plav-a-la"
    glossedTokens := [("ne", "NEG"), ("po-plav-a-la", "PFX-swim-THEME-PST.SG.F")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("phenomenon", "verbalComplex")] }

def ex58 : Datum :=
  { id := "harizanovgribanova2019_ex58"
    source := ⟨"harizanov-gribanova-2019", "(58)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Dieses Auto hat Fritz in München geklaut."
    glossedTokens := [("Dieses", "this"), ("Auto", "car"), ("hat", "has"), ("Fritz", "Fritz"), ("in", "in"), ("München", "Munich"), ("geklaut.", "stolen")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1.1"), ("phenomenon", "verbSecond")] }

def ex60 : Datum :=
  { id := "harizanovgribanova2019_ex60"
    source := ⟨"vikner-1995", "p. 47, (33c)"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(60)"⟩
    language := "dani1285"
    primaryText := "Peter drikker often kaffe om morgonen."
    glossedTokens := [("Peter", "Peter"), ("drikker", "drinks"), ("often", "often"), ("kaffe", "coffee"), ("om", "in"), ("morgonen.", "morning.DEF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1.2"), ("phenomenon", "verbSecond")] }

def ex64a : Datum :=
  { id := "harizanovgribanova2019_ex64a"
    source := ⟨"gribanova-2017", "p. 1091, (23)"⟩
    reportedIn := some ⟨"harizanov-gribanova-2019", "(64a)"⟩
    language := "russ1263"
    primaryText := "Ja v vojnu pil tože kakoj-to. V Germanii. Klopami paxnet."
    glossedTokens := [("Ja", "I"), ("v", "in"), ("vojnu", "war"), ("pil", "drank"), ("tože", "also"), ("kakoj-to.", "some-kind"), ("V", "in"), ("Germanii.", "Germany"), ("Klopami", "bedbugs.INSTR.PL"), ("paxnet.", "smells.3SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1.3"), ("phenomenon", "polarityFocus")] }

def ex64b : Datum :=
  { id := "harizanovgribanova2019_ex64b"
    source := ⟨"harizanov-gribanova-2019", "(64b)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Da ne paxnet on klopami!"
    glossedTokens := [("Da", "PRT"), ("ne", "NEG"), ("paxnet", "smell.3SG"), ("on", "it.NOM"), ("klopami!", "bedbugs.INSTR")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1.3"), ("phenomenon", "polarityFocus")] }

def all : List Datum := [ex2a, ex2b, ex3a, ex3b, ex4a, ex4b, ex5a, ex5b, ex5c, ex6a, ex6b, ex7a, ex7b, ex8a, ex8b, ex9a, ex9b, ex10a, ex10b, ex11, ex12, ex13, ex14, ex29a, ex29b, ex30a, ex30b, ex31a, ex31b, ex32a, ex32b, ex33a, ex33b, ex42, ex58, ex60, ex64a, ex64b]

end HarizanovGribanova2019.Examples
