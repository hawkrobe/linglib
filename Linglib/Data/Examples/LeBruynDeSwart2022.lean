module

public import Linglib.Data.Examples.Schema

/-!
# `LeBruynDeSwart2022` — typed example data

Auto-generated from `Linglib/Data/Examples/LeBruynDeSwart2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace LeBruynDeSwart2022.Examples`.
-/

@[expose] public section

namespace LeBruynDeSwart2022.Examples

def boeken_niet_uitgelezen : Datum :=
  { id := "lebruyndeswart2022_boeken_niet_uitgelezen"
    source := ⟨"le-bruyn-de-swart-2022", "(35)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Het klopt dat ik boeken niet heb uitgelezen. Dan begon ik er aan maar kwam ik er achter dat ik het toch niet leuk vond."
    glossedTokens := [("Het", "it"), ("klopt", "knocks"), ("dat", "that"), ("ik", "I"), ("boeken", "books"), ("niet", "not"), ("heb", "have"), ("uitgelezen", "UIT.read"), ("Dan", "then"), ("begon", "began"), ("ik", "I"), ("er", "ER"), ("aan", "on"), ("maar", "but"), ("kwam", "came"), ("ik", "I"), ("er", "ER"), ("achter", "after"), ("dat", "that"), ("ik", "I"), ("het", "it"), ("toch", "after_all"), ("niet", "not"), ("leuk", "fun"), ("vond", "found")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wide_scope", .acceptable), ("narrow_scope", .unacceptable)]
    paperFeatures := [("position", "scrambled")] }

def boeken_gehaat : Datum :=
  { id := "lebruyndeswart2022_boeken_gehaat"
    source := ⟨"le-bruyn-de-swart-2022", "(36b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "dat ik boeken altijd gehaat heb"
    glossedTokens := [("dat", "that"), ("ik", "I"), ("boeken", "books"), ("altijd", "always"), ("gehaat", "hated"), ("heb", "have")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("kind_reference", .acceptable)]
    paperFeatures := [("position", "scrambled")] }

def all : List Datum := [boeken_niet_uitgelezen, boeken_gehaat]

end LeBruynDeSwart2022.Examples
