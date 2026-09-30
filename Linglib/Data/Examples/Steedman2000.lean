module

public import Linglib.Data.Examples.Schema

/-!
# `Steedman2000` — typed example data

Auto-generated from `Linglib/Data/Examples/Steedman2000.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Steedman2000.Examples`.
-/

@[expose] public section

namespace Steedman2000.Examples

open Data.Examples

def ex_96 : Datum :=
  { id := "steedman2000_96"
    source := ⟨"steedman-2000", "(96)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "(Weil) irgendjemand auf jeden gespannt ist."
    glossedTokens := [("(Weil)", "(since)"), ("irgendjemand", "someone"), ("auf", "on"), ("jeden", "everybody"), ("gespannt", "curious"), ("ist", "is")]
    context := "German verb-final subordinate clause; the quantified PP precedes the predicate-tense cluster."
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .acceptable)]
    paperFeatures := [("wordOrder", "verbRaising")] }

def ex_97 : Datum :=
  { id := "steedman2000_97"
    source := ⟨"steedman-2000", "(97)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "(Weil) jemand versucht hat jeden reinzulegen."
    glossedTokens := [("(Weil)", "(since)"), ("jemand", "someone"), ("versucht", "tried"), ("hat", "has"), ("jeden", "everyone"), ("reinzulegen", "cheat")]
    context := "German verb-final subordinate clause; the quantified object follows the matrix verb cluster."
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .unacceptable)]
    paperFeatures := [("wordOrder", "verbProjectionRaising")] }

def ex_98a : Datum :=
  { id := "steedman2000_98a"
    source := ⟨"steedman-2000", "(98a)"⟩
    reportedIn := none
    language := "vlaa1240"
    primaryText := "(da) Jan vee boeken hee willen lezen"
    glossedTokens := [("(da)", "(that)"), ("Jan", "Jan"), ("vee", "many"), ("boeken", "books"), ("hee", "has"), ("willen", "wanted"), ("lezen", "read")]
    context := "West Flemish subordinate clause in the verb-raising word order."
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .acceptable)]
    paperFeatures := [("wordOrder", "verbRaising")] }

def ex_98b : Datum :=
  { id := "steedman2000_98b"
    source := ⟨"steedman-2000", "(98b)"⟩
    reportedIn := none
    language := "vlaa1240"
    primaryText := "(da) Jan hee willen vee boeken lezen"
    glossedTokens := [("(da)", "(that)"), ("Jan", "Jan"), ("hee", "has"), ("willen", "wanted"), ("vee", "many"), ("boeken", "books"), ("lezen", "read")]
    context := "West Flemish subordinate clause in the verb-projection-raising word order."
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .unacceptable)]
    paperFeatures := [("wordOrder", "verbProjectionRaising")] }

def ex_99a : Datum :=
  { id := "steedman2000_99a"
    source := ⟨"steedman-2000", "(99a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "(omdat) Jan veel liederen probeert te zingen"
    glossedTokens := [("(omdat)", "(because)"), ("Jan", "Jan"), ("veel", "many"), ("liederen", "songs"), ("probeert", "tries"), ("te", "to"), ("zingen", "sing")]
    context := "Dutch subordinate clause with an equi verb, verb-raising word order."
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .acceptable)]
    paperFeatures := [("wordOrder", "verbRaising")] }

def ex_99b : Datum :=
  { id := "steedman2000_99b"
    source := ⟨"steedman-2000", "(99b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "(omdat) Jan probeert veel liederen te zingen"
    glossedTokens := [("(omdat)", "(because)"), ("Jan", "Jan"), ("probeert", "tries"), ("veel", "many"), ("liederen", "songs"), ("te", "to"), ("zingen", "sing")]
    context := "Dutch subordinate clause with an equi verb, verb-projection-raising word order."
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .unacceptable)]
    paperFeatures := [("wordOrder", "verbProjectionRaising")] }

def ex_100a : Datum :=
  { id := "steedman2000_100a"
    source := ⟨"steedman-2000", "(100a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "(omdat) iemand alle liederen probeert te zingen"
    glossedTokens := [("(omdat)", "(because)"), ("iemand", "someone"), ("alle", "every"), ("liederen", "song"), ("probeert", "tries"), ("te", "to"), ("zingen", "sing")]
    context := "Dutch subordinate clause, verb-raising word order, two quantified arguments."
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .acceptable)]
    paperFeatures := [("wordOrder", "verbRaising")] }

def ex_100b : Datum :=
  { id := "steedman2000_100b"
    source := ⟨"steedman-2000", "(100b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "(omdat) iemand probeert alle liederen te zingen"
    glossedTokens := [("(omdat)", "(because)"), ("iemand", "someone"), ("probeert", "tries"), ("alle", "every"), ("liederen", "song"), ("te", "to"), ("zingen", "sing")]
    context := "Dutch subordinate clause, verb-projection-raising word order, two quantified arguments."
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .unacceptable)]
    paperFeatures := [("wordOrder", "verbProjectionRaising")] }

def ch7_4 : Datum :=
  { id := "steedman2000_ch7_4"
    source := ⟨"steedman-2000", "ch. 7 (4)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "[Ken-ga Naomi-o], [Erika-ga Sara-o] tazuneta"
    glossedTokens := [("Ken-ga", "Ken-NOM"), ("Naomi-o", "Naomi-ACC"), ("Erika-ga", "Erika-NOM"), ("Sara-o", "Sara-ACC"), ("tazuneta", "visit-PST.CONCL")]
    context := "Japanese (pure SOV): backward gapping — the nonstandard subject-object argument clusters conjoin and the verb surfaces only in the final conjunct."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "gapping"), ("wordOrder", "SOV"), ("gappingDirection", "backward")] }

def ch7_5 : Datum :=
  { id := "steedman2000_ch7_5"
    source := ⟨"steedman-2000", "ch. 7 (5)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Ken-ga Naomi-o tazunete, Erika-ga Sara-o"
    glossedTokens := [("Ken-ga", "Ken-NOM"), ("Naomi-o", "Naomi-ACC"), ("tazunete", "visit-PST.ADV"), ("Erika-ga", "Erika-NOM"), ("Sara-o", "Sara-ACC")]
    context := "Japanese (pure SOV): forward gapping — the verb in the first conjunct with a verbless second conjunct — is excluded."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "gapping"), ("wordOrder", "SOV"), ("gappingDirection", "forward")] }

def ch7_11 : Datum :=
  { id := "steedman2000_ch7_11"
    source := ⟨"steedman-2000", "ch. 7 (11)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "...dat [Jan Syntactic Structures en Piet Aspects] gelezen heeft"
    glossedTokens := [("dat", "that"), ("Jan", "Jan"), ("Syntactic Structures", "Syntactic Structures"), ("en", "and"), ("Piet", "Piet"), ("Aspects", "Aspects"), ("gelezen", "read.PTCP"), ("heeft", "has")]
    context := "Dutch subordinate clause (SOV): backward gapping — conjoined subject-object clusters precede the shared verb cluster."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "gapping"), ("wordOrder", "SOV"), ("gappingDirection", "backward")] }

def ch7_19 : Datum :=
  { id := "steedman2000_ch7_19"
    source := ⟨"steedman-2000", "ch. 7 (19)"⟩
    reportedIn := none
    language := "iris1253"
    primaryText := "Chonaic [Eoghan Siobhán] agus [Eoghnai Ciaran]"
    glossedTokens := [("Chonaic", "saw"), ("Eoghan", "Eoghan"), ("Siobhán", "Siobhán"), ("agus", "and"), ("Eoghnai", "Eoghnai"), ("Ciaran", "Ciaran")]
    context := "Irish (pure VSO): forward gapping — the initial verb is shared by conjoined subject-object argument clusters."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "gapping"), ("wordOrder", "VSO"), ("gappingDirection", "forward")] }

def ch7_20 : Datum :=
  { id := "steedman2000_ch7_20"
    source := ⟨"steedman-2000", "ch. 7 (20)"⟩
    reportedIn := none
    language := "iris1253"
    primaryText := "[Eoghan Siobhán] agus chonaic [Eoghnai Ciaran]"
    glossedTokens := [("Eoghan", "Eoghan"), ("Siobhán", "Siobhán"), ("agus", "and"), ("chonaic", "saw"), ("Eoghnai", "Eoghnai"), ("Ciaran", "Ciaran")]
    context := "Irish (pure VSO): backward gapping — verbless first conjunct with the verb in the second conjunct — is excluded."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "gapping"), ("wordOrder", "VSO"), ("gappingDirection", "backward")] }

def ch7_21 : Datum :=
  { id := "steedman2000_ch7_21"
    source := ⟨"steedman-2000", "ch. 7 (21)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Wil jij een ijsje en Marietje limonade?"
    glossedTokens := [("Wil", "want"), ("jij", "you"), ("een", "an"), ("ijsje", "ice-cream"), ("en", "and"), ("Marietje", "Marietje"), ("limonade", "lemonade")]
    context := "Dutch main clause (verb-initial yes/no question, conforming to the VSO pattern per Steedman): forward gapping, the mirror image of the backward-gapping subordinate clauses."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "gapping"), ("wordOrder", "VSO"), ("gappingDirection", "forward")] }

def ch7_41 : Datum :=
  { id := "steedman2000_ch7_41"
    source := ⟨"steedman-2000", "ch. 7 (41)/(62)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dexter ate bread, and Warren, potatoes"
    glossedTokens := []
    context := "English (SVO): forward gapping — the verb in the first conjunct is shared by the verbless right conjunct."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "gapping"), ("wordOrder", "SVO"), ("gappingDirection", "forward")] }

def ch7_63 : Datum :=
  { id := "steedman2000_ch7_63"
    source := ⟨"steedman-2000", "ch. 7 (63)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Warren, potatoes and Dexter bought bread"
    glossedTokens := []
    context := "English (SVO): backward gapping — verbless left conjunct with the verb in the right conjunct — is excluded by universal principles."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "gapping"), ("wordOrder", "SVO"), ("gappingDirection", "backward")] }

def all : List Datum := [ex_96, ex_97, ex_98a, ex_98b, ex_99a, ex_99b, ex_100a, ex_100b, ch7_4, ch7_5, ch7_11, ch7_19, ch7_20, ch7_21, ch7_41, ch7_63]

end Steedman2000.Examples
