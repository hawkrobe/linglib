import Linglib.Data.Examples.Schema

/-!
# `LeBruynDeSwart2022` — typed example data

Auto-generated from `Linglib/Data/Examples/LeBruynDeSwart2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace LeBruynDeSwart2022.Examples`.
-/

namespace LeBruynDeSwart2022.Examples

open Data.Examples

def boeken_niet_uitgelezen : LinguisticExample :=
  { id := "lebruyndeswart2022_boeken_niet_uitgelezen"
    source := ⟨"le-bruyn-de-swart-2022", "(35)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Het klopt dat ik boeken niet heb uitgelezen."
    discourseSegments := []
    glossedTokens := [("Het", "it"), ("klopt", "is.true"), ("dat", "that"), ("ik", "I"), ("boeken", "books"), ("niet", "not"), ("heb", "have"), ("uitgelezen", "finished")]
    translation := "It's true that there are books I didn't finish."
    context := "Preceded in the source by a discussion of reading habits; followed by 'Then I started on them but found out that I did not like them after all.'"
    judgment := .acceptable
    alternatives := []
    readings := [("wide_scope", .acceptable), ("narrow_scope", .unacceptable)]
    paperFeatures := [("position", "scrambled")]
    comment := "Naturally occurring scrambled bare plural over negation: obligatory wide scope (there are books I didn't finish), not 'I finished no books'; the follow-up sentence confirms the wide scope reading."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def boeken_gehaat : LinguisticExample :=
  { id := "lebruyndeswart2022_boeken_gehaat"
    source := ⟨"le-bruyn-de-swart-2022", "(36b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "dat ik boeken altijd gehaat heb"
    discourseSegments := []
    glossedTokens := [("dat", "that"), ("ik", "I"), ("boeken", "books"), ("altijd", "always"), ("gehaat", "hated"), ("heb", "have")]
    translation := "that I've always hated books"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("kind_reference", .acceptable)]
    paperFeatures := [("position", "scrambled")]
    comment := "A scrambled bare plural under a kind-level predicate ('hate') keeps its kind reading: scrambling affects scope, not kind reference."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [boeken_niet_uitgelezen, boeken_gehaat]

end LeBruynDeSwart2022.Examples
