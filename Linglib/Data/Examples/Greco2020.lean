module

public import Linglib.Data.Examples.Schema

/-!
# `Greco2020` — typed example data

Auto-generated from `Linglib/Data/Examples/Greco2020.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Greco2020.Examples`.
-/

@[expose] public section

namespace Greco2020.Examples

open Data.Examples

def ex_2 : Datum :=
  { id := "greco2020_2"
    source := ⟨"greco-2020", "(2)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E non mi è scesa dal treno Maria?!"
    glossedTokens := [("E", "and"), ("non", "NEG"), ("mi", "CL.to me"), ("è", "is"), ("scesa", "got"), ("dal", "off-the"), ("treno", "train"), ("Maria", "Mary")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "baseline"), ("requirement", "any")] }

def ex_9a : Datum :=
  { id := "greco2020_9a"
    source := ⟨"greco-2020", "(9a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E Maria non mi ha alzato un dito per aiutare Luca?!"
    glossedTokens := [("E", "and"), ("Maria", "Mary"), ("non", "EN"), ("mi", "CL.to me"), ("ha", "has"), ("alzato", "lifted"), ("un", "a"), ("dito", "finger"), ("per", "to"), ("aiutare", "help"), ("Luca", "Luke")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "weak NPI"), ("requirement", "negScope"), ("polarity", "weak NPI")] }

def ex_9b : Datum :=
  { id := "greco2020_9b"
    source := ⟨"greco-2020", "(9b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E non mi è sceso dal treno nessuno?!"
    glossedTokens := [("E", "and"), ("non", "EN"), ("mi", "CL.to me"), ("è", "is"), ("sceso", "got"), ("dal", "off-the"), ("treno", "train"), ("nessuno", "nobody")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "n-word"), ("requirement", "negScope"), ("polarity", "n-word")] }

def ex_9c : Datum :=
  { id := "greco2020_9c"
    source := ⟨"greco-2020", "(9c)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E non mi è affatto scesa dal treno Maria?!"
    glossedTokens := [("E", "and"), ("non", "EN"), ("mi", "ED.to me"), ("è", "is"), ("affatto", "at all"), ("scesa", "got"), ("dal", "off-the"), ("treno", "train"), ("Maria", "Mary")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "strong NPI"), ("requirement", "negScope"), ("polarity", "strong NPI")] }

def ex_9d : Datum :=
  { id := "greco2020_9d"
    source := ⟨"greco-2020", "(9d)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E non mi è scesa dal treno Maria e neanche Gianni?!"
    glossedTokens := [("E", "and"), ("non", "EN"), ("mi", "ED.to me"), ("è", "is"), ("scesa", "got"), ("dal", "off-the"), ("treno", "train"), ("Maria", "Mary"), ("e", "and"), ("neanche", "not-also"), ("Gianni", "John")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "not-also conjunction"), ("requirement", "negScope"), ("polarity", "not-also conjunction")] }

def ex_23a : Datum :=
  { id := "greco2020_23a"
    source := ⟨"greco-2020", "(23a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E Gianni non ti ha trovato alcunché di importante nel cassetto?!"
    glossedTokens := [("E", "EE"), ("Gianni", "John"), ("non", "NEG"), ("ti", "CL.to me"), ("ha", "has"), ("trovato", "found"), ("alcunché", "anything"), ("di", "of"), ("importante", "important"), ("nel", "in the"), ("cassetto", "drawer")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "al-word"), ("requirement", "negScope")] }

def ex_24b : Datum :=
  { id := "greco2020_24b"
    source := ⟨"greco-2020", "(24b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E Gianni non mi ha già finito i compiti?!"
    glossedTokens := [("E", "and"), ("Gianni", "John"), ("non", "EN"), ("mi", "ED.to me"), ("ha", "has"), ("già", "already"), ("finito", "finished"), ("i", "the"), ("compiti", "homework")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "PPI"), ("requirement", "noNegScope")] }

def ex_17a : Datum :=
  { id := "greco2020_17a"
    source := ⟨"greco-2020", "(17a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E il libro non me lo ha dato a Luca?!"
    glossedTokens := [("E", "and"), ("il", "the"), ("libro", "book"), ("non", "EN"), ("me", "ED.to me"), ("lo", "CL.it"), ("ha", "has"), ("dato", "given"), ("a", "to"), ("Luca", "Luke")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "fronted topic"), ("requirement", "any")] }

def ex_17b : Datum :=
  { id := "greco2020_17b"
    source := ⟨"greco-2020", "(17b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E LA PENNA non mi ha dato a Luca (non il libro)?!"
    glossedTokens := [("E", "and"), ("LA", "the"), ("PENNA", "pen"), ("non", "EN"), ("mi", "ED.to me"), ("ha", "has"), ("dato", "given"), ("a", "to"), ("Luca", "Luke"), ("non", "not"), ("il", "the"), ("libro", "book")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "fronted contrastive focus"), ("requirement", "freeFocP")] }

def ex_18a : Datum :=
  { id := "greco2020_18a"
    source := ⟨"greco-2020", "(18a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E Gianni non me lo ha dato a Luca il libro?!"
    glossedTokens := [("E", "and"), ("Gianni", "John"), ("non", "EN"), ("me", "ED.to me"), ("lo", "CL.it"), ("ha", "has"), ("dato", "given"), ("a", "to"), ("Luca", "Luke"), ("il", "the"), ("libro", "book")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "in-situ topic"), ("requirement", "any")] }

def ex_18b : Datum :=
  { id := "greco2020_18b"
    source := ⟨"greco-2020", "(18b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E Gianni non mi ha dato LA PENNA a Luca (non il libro)?!"
    glossedTokens := [("E", "and"), ("Gianni", "John"), ("non", "EN"), ("mi", "ED.to me"), ("ha", "has"), ("dato", "given"), ("LA", "the"), ("PENNA", "pen"), ("a", "to"), ("Luca", "Luke"), ("non", "not"), ("il", "the"), ("libro", "book")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "in-situ focus"), ("requirement", "freeFocP")] }

def ex_53a : Datum :=
  { id := "greco2020_53a"
    source := ⟨"greco-2020", "(53a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E Gianni, gli amici, non gli hanno fatto un brutto scherzo?!"
    glossedTokens := [("E", "EE"), ("Gianni", "John"), ("gli", "the"), ("amici", "friends"), ("non", "EN"), ("gli", "to-him"), ("hanno", "have.3PL"), ("fatto", "done"), ("un", "a"), ("brutto", "bad"), ("scherzo", "joke")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "hanging topic"), ("requirement", "any")] }

def ex_53c : Datum :=
  { id := "greco2020_53c"
    source := ⟨"greco-2020", "(53c)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E domani Gianni non mi viene a trovare?!"
    glossedTokens := [("E", "EE"), ("domani", "tomorrow"), ("Gianni", "John"), ("non", "EN"), ("mi", "CL.me"), ("viene", "comes"), ("a", "to"), ("trovare", "see")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "scene-setting topic"), ("requirement", "any")] }

def ex_54 : Datum :=
  { id := "greco2020_54"
    source := ⟨"greco-2020", "(54)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ora ricordo. E una sciarpa rossa non mi ha regalato Gianni per Natale?!"
    glossedTokens := [("Ora", "now"), ("ricordo", "remember.1SG.PRS"), ("E", "EE"), ("una", "a"), ("sciarpa", "scarf"), ("rossa", "red"), ("non", "EN"), ("mi", "CL.to-me"), ("ha", "has"), ("regalato", "given"), ("Gianni", "John"), ("per", "for"), ("Natale", "Christmas")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "mirative fronting"), ("requirement", "freeFocP")] }

def ex_55 : Datum :=
  { id := "greco2020_55"
    source := ⟨"greco-2020", "(55)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E qualcosa non mi ha concluso Luca stando qui?!"
    glossedTokens := [("E", "EE"), ("qualcosa", "something"), ("non", "EN"), ("mi", "ED"), ("ha", "has"), ("concluso", "accomplished"), ("Luca", "Luke"), ("stando", "being"), ("qui", "here")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "quantifier fronting"), ("requirement", "freeFocP")] }

def ex_56 : Datum :=
  { id := "greco2020_56"
    source := ⟨"greco-2020", "(56B)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E questo non mi ha fatto Gianni?!"
    glossedTokens := [("E", "EE"), ("questo", "this"), ("non", "EN"), ("mi", "ED"), ("ha", "has"), ("fatto", "done"), ("Gianni", "John")]
    context := "A: Gianni è andato al bar invece di andare a scuola."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "anaphoric anteposition"), ("requirement", "freeFocP")] }

def ex_57c : Datum :=
  { id := "greco2020_57c"
    source := ⟨"greco-2020", "(57c)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E non mi ha mangiato solo la pizza Gianni?!"
    glossedTokens := [("E", "EE"), ("non", "EN"), ("mi", "ED"), ("ha", "has"), ("mangiato", "eaten"), ("solo", "only"), ("la", "the"), ("pizza", "pizza"), ("Gianni", "John")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "solo in situ"), ("requirement", "any")] }

def ex_57d : Datum :=
  { id := "greco2020_57d"
    source := ⟨"greco-2020", "(57d)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E SOLO LA PIZZA non mi ha mangiato Gianni?! (non anche la pasta)"
    glossedTokens := [("E", "EE"), ("SOLO", "only"), ("LA", "the"), ("PIZZA", "pizza"), ("non", "EN"), ("mi", "ED"), ("ha", "has"), ("mangiato", "eaten"), ("Gianni", "John"), ("non", "not"), ("anche", "also"), ("la", "the"), ("pasta", "pasta")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "solo fronted"), ("requirement", "freeFocP")] }

def ex_26 : Datum :=
  { id := "greco2020_26"
    source := ⟨"greco-2020", "(26B)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "(E) non mi è scesa dal treno Maria?!"
    glossedTokens := [("E", "EE"), ("non", "EN"), ("mi", "ED.to me"), ("è", "is"), ("scesa", "got"), ("dal", "off-the"), ("treno", "train"), ("Maria", "Mary")]
    context := "A: Che cosa è successo?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "answer to a propositional question"), ("requirement", "activeFocP")] }

def ex_27 : Datum :=
  { id := "greco2020_27"
    source := ⟨"greco-2020", "(27B)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "(E) non mi è scesa dal treno Maria?!"
    glossedTokens := [("E", "EE"), ("non", "EN"), ("mi", "ED.to me"), ("è", "is"), ("scesa", "got"), ("dal", "off-the"), ("treno", "train"), ("Maria", "Mary")]
    context := "A: Chi è sceso dal treno?"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "answer to an entity question"), ("requirement", "freeFocP")] }

def ex_21 : Datum :=
  { id := "greco2020_21"
    source := ⟨"greco-2020", "(21)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E non mi è scesa dal treno Maria?!"
    glossedTokens := [("E", "EE"), ("non", "EN"), ("mi", "ED.to me"), ("è", "is"), ("scesa", "got"), ("dal", "off-the"), ("treno", "train"), ("Maria", "Mary")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "expletive e"), ("requirement", "activeFocP")] }

def ex_74b : Datum :=
  { id := "greco2020_74b"
    source := ⟨"greco-2020", "(74b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E non mi è mica scesa dal treno Maria?!"
    glossedTokens := [("E", "EE"), ("non", "EN"), ("mi", "ED"), ("è", "is"), ("mica", "NEG"), ("scesa", "got"), ("dal", "off-the"), ("treno", "train"), ("Maria", "Mary")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "presuppositional mica"), ("requirement", "any")] }

def ex_76a : Datum :=
  { id := "greco2020_76a"
    source := ⟨"greco-2020", "(76a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E da quale treno non mi è scesa Maria?!"
    glossedTokens := [("E", "EE"), ("da", "from"), ("quale", "which"), ("treno", "train"), ("non", "EN"), ("mi", "ED"), ("è", "is"), ("scesa", "got"), ("Maria", "Mary")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "wh-element"), ("requirement", "freeFocP")] }

def ex_77 : Datum :=
  { id := "greco2020_77"
    source := ⟨"greco-2020", "(77)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E nessuno mi è sceso dal treno?!"
    glossedTokens := [("E", "and"), ("nessuno", "nobody"), ("mi", "ED.to me"), ("è", "is"), ("sceso", "got"), ("dal", "off to-the"), ("treno", "train")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "quantifier raising"), ("requirement", "freeFocP")] }

def ex_60 : Datum :=
  { id := "greco2020_60"
    source := ⟨"greco-2020", "(60)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E no mi è scesa dal treno Maria?!"
    glossedTokens := [("E", "EE"), ("no", "not2"), ("mi", "ED"), ("è", "is"), ("scesa", "got"), ("dal", "off-the"), ("treno", "train"), ("Maria", "Mary")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "phrasal negator no"), ("requirement", "phrasalNegator")] }

def ex_61a : Datum :=
  { id := "greco2020_61a"
    source := ⟨"greco-2020", "(61a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E non raggiunta Maria, siamo andati al bar?!"
    glossedTokens := [("E", "EE"), ("non", "EN"), ("raggiunta", "reached"), ("Maria", "Mary"), ("siamo", "are.1PL"), ("andati", "went"), ("al", "to-the"), ("bar", "bar")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "past participle clause"), ("requirement", "noTP")] }

def ex_64 : Datum :=
  { id := "greco2020_64"
    source := ⟨"greco-2020", "(64)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E non essendo arrivata Maria, siamo venuti da soli?!"
    glossedTokens := [("E", "EE"), ("non", "EN"), ("essendo", "be.gerund"), ("arrivata", "arrived"), ("Maria", "Mary"), ("siamo", "be.1PL"), ("venuti", "come"), ("da", "by"), ("soli", "alone")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "Aux-to-Comp"), ("requirement", "negScope")] }

def ex_72b : Datum :=
  { id := "greco2020_72b"
    source := ⟨"greco-2020", "(72b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E Luca non mi pensa che sia scesa dal treno Maria?!"
    glossedTokens := [("E", "EE"), ("Luca", "Luke"), ("non", "EN"), ("mi", "ED"), ("pensa", "thinks"), ("che", "that"), ("sia", "be.3SG.SBJ"), ("scesa", "got"), ("dal", "off-the"), ("treno", "train"), ("Maria", "Mary")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("Luke thinks that Mary did not get off the train!", .unacceptable), ("Luke thinks that Mary got off the train!", .acceptable)]
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "NEG-raising reading"), ("requirement", "negScope"), ("reading", "Luke thinks that Mary did not get off the train!")] }

def ex_81a : Datum :=
  { id := "greco2020_81a"
    source := ⟨"greco-2020", "(81a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Mi chiedo se non mi sia scesa dal treno Maria?!"
    glossedTokens := [("Mi", "CL.to me"), ("chiedo", "wonder.1SG.PRS"), ("se", "if"), ("non", "EN"), ("mi", "ED"), ("sia", "be.3SG.SBJ"), ("scesa", "got"), ("dal", "off to-the"), ("treno", "train"), ("Maria", "Mary")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "indirect question"), ("requirement", "embedded")] }

def ex_81b : Datum :=
  { id := "greco2020_81b"
    source := ⟨"greco-2020", "(81b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Mi spiace che non mi sia scesa dal treno Maria?!"
    glossedTokens := [("Mi", "CL.to me"), ("spiace", "sorry"), ("che", "that"), ("non", "EN"), ("mi", "ED"), ("sia", "be.3SG.SBJ"), ("scesa", "got"), ("dal", "off-the"), ("treno", "train"), ("Maria", "Mary")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "factive predicate"), ("requirement", "embedded")] }

def ex_81c : Datum :=
  { id := "greco2020_81c"
    source := ⟨"greco-2020", "(81c)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Luca dice che non mi è scesa dal treno Maria?!"
    glossedTokens := [("Luca", "Luke"), ("dice", "says"), ("che", "that"), ("non", "EN"), ("mi", "ED"), ("è", "is"), ("scesa", "got"), ("dal", "off-the"), ("treno", "train"), ("Maria", "Mary")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "bridge verb"), ("requirement", "embedded")] }

def ex_83B : Datum :=
  { id := "greco2020_83B"
    source := ⟨"greco-2020", "(83B)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Mi chiedo se ROMA i turisti pensino che sia bella (non Firenze)."
    glossedTokens := [("Mi", "CL.to me"), ("chiedo", "wonder.1SG.PRS"), ("se", "whether"), ("ROMA", "ROMA"), ("i", "the"), ("turisti", "tourists"), ("pensino", "think.3PL.SBJ"), ("che", "that"), ("sia", "be.3SG.SBJ"), ("bella", "beautiful"), ("non", "not"), ("Firenze", "Firenze")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "embedded focus"), ("phenomenon", "embedded DP focus"), ("focus", "DP")] }

def ex_83B2 : Datum :=
  { id := "greco2020_83B2"
    source := ⟨"greco-2020", "(83B′)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Mi chiedo se ROMA SIA PULITA i turisti pensino (non Firenze sia bella)."
    glossedTokens := [("Mi", "CL.to me"), ("chiedo", "wonder.1SG.PRS"), ("se", "whether"), ("ROMA", "Roma"), ("SIA", "be.3SG.SBJ"), ("PULITA", "clean"), ("i", "the"), ("turisti", "tourists"), ("pensino", "think.3PL.SBJ"), ("non", "not"), ("Firenze", "Firenze"), ("sia", "be.3SG.SBJ"), ("bella", "beautiful")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "embedded focus"), ("phenomenon", "embedded whole-TP focus"), ("focus", "TP")] }

def ex_84B : Datum :=
  { id := "greco2020_84B"
    source := ⟨"greco-2020", "(84B)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Mi spiace che ROMA i turisti pensino che sia brutta (non Firenze)"
    glossedTokens := [("Mi", "CL.to me"), ("spiace", "sorry"), ("che", "that"), ("ROMA", "Rome"), ("i", "the"), ("turisti", "tourists"), ("pensino", "think.3PL.SBJ"), ("che", "that"), ("sia", "be.3SG.SBJ"), ("brutta", "ugly"), ("non", "not"), ("Firenze", "Firenze")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "embedded focus"), ("phenomenon", "embedded DP focus"), ("focus", "DP")] }

def ex_84B2 : Datum :=
  { id := "greco2020_84B2"
    source := ⟨"greco-2020", "(84B′)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Mi spiace che ROMA SIA SPORCA i turisti pensino (non Firenze sia brutta)"
    glossedTokens := [("Mi", "CL.to me"), ("spiace", "sorry"), ("che", "that"), ("ROMA", "Rome"), ("SIA", "be.3SG.SBJ"), ("SPORCA", "dirty"), ("i", "the"), ("turisti", "tourists"), ("pensino", "think.3PL.SBJ"), ("non", "not"), ("Firenze", "Firenze"), ("sia", "be.3SG.SBJ"), ("brutta", "ugly")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "embedded focus"), ("phenomenon", "embedded whole-TP focus"), ("focus", "TP")] }

def ex_85B : Datum :=
  { id := "greco2020_85B"
    source := ⟨"greco-2020", "(85B)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Luca dice che ROMA i turisti pensano che sia bella (non Firenze)"
    glossedTokens := [("Luca", "Luca"), ("dice", "says"), ("che", "that"), ("ROMA", "Rome"), ("i", "the"), ("turisti", "tourists"), ("pensano", "think.3PL.SG"), ("che", "that"), ("sia", "be.3SG.SBJ"), ("bella", "beautiful"), ("non", "not"), ("Firenze", "Firenze")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "embedded focus"), ("phenomenon", "embedded DP focus"), ("focus", "DP")] }

def ex_85B2 : Datum :=
  { id := "greco2020_85B2"
    source := ⟨"greco-2020", "(85B′)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Luca dice che ROMA SIA PULITA i turisti pensano (non Firenze sia bella)."
    glossedTokens := [("Luca", "Luca"), ("dice", "says"), ("che", "that"), ("ROMA", "Rome"), ("SIA", "be.3SG.SBJ"), ("PULITA", "clean"), ("i", "the"), ("turisti", "tourists"), ("pensano", "think.3PL.SG"), ("non", "not"), ("Firenze", "Firenze"), ("sia", "be.3SG.SBJ"), ("bella", "beautiful")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "embedded focus"), ("phenomenon", "embedded whole-TP focus"), ("focus", "TP")] }

def ex_86a : Datum :=
  { id := "greco2020_86a"
    source := ⟨"greco-2020", "(86a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E Maria non mi è scesa dal treno?!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "preverbal subject"), ("requirement", "any")] }

def ex_86b : Datum :=
  { id := "greco2020_86b"
    source := ⟨"greco-2020", "(86b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E non mi è scesa dal treno Maria?!"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "postverbal subject"), ("requirement", "any")] }

def ex_31B : Datum :=
  { id := "greco2020_31B"
    source := ⟨"greco-2020", "(31B)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Non mi è scesa dal treno Maria?!"
    glossedTokens := []
    context := "A: Sembri sconvolto. Cos'è successo?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "answer to a question"), ("diagnostic", "answerhood")] }

def ex_31B2 : Datum :=
  { id := "greco2020_31B2"
    source := ⟨"greco-2020", "(31B′)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Dopo tutto, non è scesa dal treno Maria?"
    glossedTokens := [("Dopo", "after"), ("tutto", "all"), ("non", "EN"), ("è", "is"), ("scesa", "got"), ("dal", "off the"), ("treno", "train"), ("Maria", "Mary")]
    context := "A: Sembri sconvolto. Cos'è successo?"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "NRQ"), ("phenomenon", "answer to a question"), ("diagnostic", "answerhood")] }

def ex_34a : Datum :=
  { id := "greco2020_34a"
    source := ⟨"greco-2020", "(34a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Dopo tutto, Gianni non è arrivato primo?"
    glossedTokens := [("Dopo", "after"), ("tutto", "all"), ("Gianni", "John"), ("non", "EN"), ("è", "is"), ("arrivato", "come"), ("primo", "first")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "NRQ"), ("phenomenon", "dopo tutto"), ("diagnostic", "dopo tutto")] }

def ex_34b : Datum :=
  { id := "greco2020_34b"
    source := ⟨"greco-2020", "(34b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E dopo tutto, Gianni non mi è arrivato primo?!"
    glossedTokens := [("E", "EE"), ("dopo", "after"), ("tutto", "all"), ("Gianni", "John"), ("non", "EN"), ("mi", "ED.to me"), ("è", "is"), ("arrivato", "come"), ("primo", "first")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "dopo tutto"), ("diagnostic", "dopo tutto")] }

def ex_35a : Datum :=
  { id := "greco2020_35a"
    source := ⟨"greco-2020", "(35a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Dopo tutto, che cosa non ha fatto Maria per Gianni?"
    glossedTokens := [("Dopo", "after"), ("tutto", "all"), ("che cosa", "what"), ("non", "EN"), ("ha", "has"), ("fatto", "done"), ("Maria", "Mary"), ("per", "for"), ("Gianni", "John")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "NRQ"), ("phenomenon", "wh-element"), ("diagnostic", "wh")] }

def ex_35b : Datum :=
  { id := "greco2020_35b"
    source := ⟨"greco-2020", "(35b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "E che cosa non mi ha fatto Maria per Gianni?!"
    glossedTokens := [("E", "and"), ("che cosa", "what"), ("non", "EN"), ("mi", "ED.to me"), ("ha", "has"), ("fatto", "done"), ("Maria", "Mary"), ("per", "for"), ("Gianni", "John")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "wh-element"), ("diagnostic", "wh")] }

def ex_40a : Datum :=
  { id := "greco2020_40a"
    source := ⟨"greco-2020", "(40a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "È incredibile che cosa non abbia mangiato Gianni!"
    glossedTokens := [("È", "is"), ("incredibile", "incredible"), ("che cosa", "what"), ("non", "EN"), ("abbia", "had.3SG.SBJ"), ("mangiato", "eaten"), ("Gianni", "John")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ENE"), ("phenomenon", "factive embedding"), ("diagnostic", "factive embedding")] }

def ex_40b : Datum :=
  { id := "greco2020_40b"
    source := ⟨"greco-2020", "(40b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "È incredibile che Maria non mi sia scesa dal treno!?"
    glossedTokens := [("È", "is"), ("incredibile", "incredible"), ("che", "that"), ("Maria", "Mary"), ("non", "EN"), ("mi", "ED.to me"), ("sia", "was.3PRS.SBJ"), ("scesa", "got"), ("dal", "off-the"), ("treno", "train")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "Sneg"), ("phenomenon", "factive embedding"), ("diagnostic", "factive embedding")] }

def ex_41B : Datum :=
  { id := "greco2020_41B"
    source := ⟨"greco-2020", "(41B)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Che cosa non ha mangiato Gianni!"
    glossedTokens := [("Che cosa", "what"), ("non", "NEG"), ("ha", "has"), ("mangiato", "eaten"), ("Gianni", "John")]
    context := "A: Sembri sconvolto. Cos'è successo?"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ENE"), ("phenomenon", "answer to a question"), ("diagnostic", "answerhood")] }

def ex_42a : Datum :=
  { id := "greco2020_42a"
    source := ⟨"greco-2020", "(42a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Che cosa non ha fatto Maria per Gianni!"
    glossedTokens := [("Che cosa", "what"), ("non", "EN"), ("ha", "has"), ("fatto", "done"), ("Maria", "Mary"), ("per", "for"), ("Gianni", "John")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "ENE"), ("phenomenon", "wh-element"), ("diagnostic", "wh")] }

def all : List Datum := [ex_2, ex_9a, ex_9b, ex_9c, ex_9d, ex_23a, ex_24b, ex_17a, ex_17b, ex_18a, ex_18b, ex_53a, ex_53c, ex_54, ex_55, ex_56, ex_57c, ex_57d, ex_26, ex_27, ex_21, ex_74b, ex_76a, ex_77, ex_60, ex_61a, ex_64, ex_72b, ex_81a, ex_81b, ex_81c, ex_83B, ex_83B2, ex_84B, ex_84B2, ex_85B, ex_85B2, ex_86a, ex_86b, ex_31B, ex_31B2, ex_34a, ex_34b, ex_35a, ex_35b, ex_40a, ex_40b, ex_41B, ex_42a]

end Greco2020.Examples
