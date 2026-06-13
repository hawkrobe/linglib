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
    source := ⟨"le-bruyn-de-swart-2022", "UNVERIFIED ex. 34-35"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Het klopt dat ik boeken niet heb uitgelezen."
    discourseSegments := []
    glossedTokens := [("Het", "it"), ("klopt", "is.true"), ("dat", "that"), ("ik", "I"), ("boeken", "books"), ("niet", "not"), ("heb", "have"), ("uitgelezen", "finished")]
    translation := "It's true that there are books I didn't finish."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("wide_scope", .acceptable), ("narrow_scope", .unacceptable)]
    paperFeatures := [("position", "scrambled")]
    comment := "Migrated from Phenomena/Generics/KindReference.lean dutchScrambledBoeken. Scrambled bare plural with negation: obligatory wide scope (there are books I didn't finish), not 'I finished no books'."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def boeken_gehaat : LinguisticExample :=
  { id := "lebruyndeswart2022_boeken_gehaat"
    source := ⟨"le-bruyn-de-swart-2022", "UNVERIFIED ex. 36-37"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "dat ik boeken altijd gehaat heb"
    discourseSegments := []
    glossedTokens := [("dat", "that"), ("ik", "I"), ("boeken", "books"), ("altijd", "always"), ("gehaat", "hated"), ("heb", "have")]
    translation := "that I've always hated books"
    context := "Embedded clause."
    judgment := .acceptable
    alternatives := []
    readings := [("kind_reference", .acceptable)]
    paperFeatures := [("position", "scrambled")]
    comment := "Migrated from Phenomena/Generics/KindReference.lean dutchScrambledKindBoeken. A scrambled bare plural can still be kind-referring with a kind-level predicate ('hate'): scrambling affects scope, not kindhood."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [boeken_niet_uitgelezen, boeken_gehaat]

end LeBruynDeSwart2022.Examples
