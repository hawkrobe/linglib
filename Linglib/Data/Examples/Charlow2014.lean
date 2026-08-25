import Linglib.Data.Examples.Schema

/-!
# `Charlow2014` — typed example data

Auto-generated from `Linglib/Data/Examples/Charlow2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Charlow2014.Examples`.
-/

namespace Charlow2014.Examples

open Data.Examples

def ex4_1a : LinguisticExample :=
  { id := "charlow2014_ex4_1a"
    source := ⟨"charlow-2014", "(4.1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If a relative of mine dies, I'll inherit a house."
    discourseSegments := []
    glossedTokens := []
    translation := "If a relative of mine dies, I'll inherit a house."
    context := "A single rich relative has put the speaker in her will, though the speaker may not know who."
    judgment := .acceptable
    alternatives := []
    readings := [("∃ > if", .acceptable)]
    paperFeatures := []
    comment := "Exceptional scope of an indefinite out of a conditional antecedent, a scope island."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_1b : LinguisticExample :=
  { id := "charlow2014_ex4_1b"
    source := ⟨"charlow-2014", "(4.1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If every relative of mine dies, I'll inherit a house."
    discourseSegments := []
    glossedTokens := []
    translation := "If every relative of mine dies, I'll inherit a house."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("∀ > if", .unacceptable)]
    paperFeatures := []
    comment := "A universal cannot scope out of the antecedent; contrast with (4.1a)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_1c : LinguisticExample :=
  { id := "charlow2014_ex4_1c"
    source := ⟨"charlow-2014", "(4.1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If no relative of mine dies, I'll inherit a house."
    discourseSegments := []
    glossedTokens := []
    translation := "If no relative of mine dies, I'll inherit a house."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("¬∃ > if", .unacceptable)]
    paperFeatures := []
    comment := "A negative quantifier cannot scope out of the antecedent."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_2a : LinguisticExample :=
  { id := "charlow2014_ex4_2a"
    source := ⟨"charlow-2014", "(4.2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No student read every book that a teacher of his recommended."
    discourseSegments := []
    glossedTokens := []
    translation := "No student read every book that a teacher of his recommended."
    context := "Teachers vary with students but not with books."
    judgment := .acceptable
    alternatives := []
    readings := [("no > ∃ > every (intermediate)", .acceptable)]
    paperFeatures := []
    comment := "Intermediate exceptional scope out of a tensed relative clause, with the indefinite bound into by the subject."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_4 : LinguisticExample :=
  { id := "charlow2014_ex4_4"
    source := ⟨"schwarz-2001", "(25)"⟩
    reportedIn := some ⟨"charlow-2014", "(4.4)"⟩
    language := "stan1293"
    primaryText := "No candidate submitted a paper he had written."
    discourseSegments := []
    glossedTokens := []
    translation := "No candidate submitted a paper he had written."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("∃ > no (pronoun bound)", .unacceptable)]
    paperFeatures := []
    comment := "The Binder Roof Constraint: an indefinite cannot take existential scope over an operator that binds into its restrictor."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_6 : LinguisticExample :=
  { id := "charlow2014_ex4_6"
    source := ⟨"charlow-2014", "(4.6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I didn't read a book by a famous linguist."
    discourseSegments := []
    glossedTokens := []
    translation := "I didn't read a book by a famous linguist."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("a book > not > a famous linguist", .unacceptable)]
    paperFeatures := []
    comment := "A container indefinite cannot outscope negation while the embedded indefinite scopes below it."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_18b : LinguisticExample :=
  { id := "charlow2014_ex4_18b"
    source := ⟨"charlow-2014", "(4.18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If a persuasive lawyer visits a relative of mine, I'll inherit a house."
    discourseSegments := []
    glossedTokens := []
    translation := "If a persuasive lawyer visits a relative of mine, I'll inherit a house."
    context := "For some relative of mine, if some persuasive lawyer or other visits them, I'll inherit a house; continue with 'she lives in Highland Park'."
    judgment := .acceptable
    alternatives := []
    readings := [("a relative > if > a lawyer", .acceptable)]
    paperFeatures := []
    comment := "Selective exceptional scope: two indefinites on one island scope differently outside it."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_23a : LinguisticExample :=
  { id := "charlow2014_ex4_23a"
    source := ⟨"rooth-partee-1982", "(21c)"⟩
    reportedIn := some ⟨"charlow-2014", "(4.23a)"⟩
    language := "stan1293"
    primaryText := "Bill hopes that someone will hire a maid or a cook."
    discourseSegments := []
    glossedTokens := []
    translation := "Bill hopes that someone will hire a maid or a cook."
    context := "Bill either hopes de dicto that someone hires a maid, or hopes de dicto that someone hires a cook."
    judgment := .acceptable
    alternatives := []
    readings := [("or > hopes, indefinites de dicto", .acceptable)]
    paperFeatures := []
    comment := "Disjunction takes exceptional scope while its disjuncts stay below the attitude verb: disjunction does not respect the Binder Roof Constraint."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_23b : LinguisticExample :=
  { id := "charlow2014_ex4_23b"
    source := ⟨"rooth-partee-1982", "(21a)"⟩
    reportedIn := some ⟨"charlow-2014", "(4.23b)"⟩
    language := "stan1293"
    primaryText := "Bill hopes that someone will hire a maid and a cook."
    discourseSegments := []
    glossedTokens := []
    translation := "Bill hopes that someone will hire a maid and a cook."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("and > hopes", .unacceptable)]
    paperFeatures := []
    comment := "Unstressed conjunction does not scope out of the island."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_25b : LinguisticExample :=
  { id := "charlow2014_ex4_25b"
    source := ⟨"charlow-2014", "(4.25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If a farmer owns a donkey or a horse, he beats it."
    discourseSegments := []
    glossedTokens := []
    translation := "If a farmer owns a donkey or a horse, he beats it."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("every farmer beats every donkey or horse he owns", .acceptable)]
    paperFeatures := []
    comment := "Disjunctions license donkey anaphora like indefinites."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex5_7a : LinguisticExample :=
  { id := "charlow2014_ex5_7a"
    source := ⟨"charlow-2014", "(5.7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If everyone thinks John will come, we'll have to invite him. If everyone thinks BILL will, we WON'T have to invite him."
    discourseSegments := ["If everyone thinks John will come, we'll have to invite him.", "If everyone thinks BILL will, we WON'T have to invite him."]
    glossedTokens := []
    translation := "If everyone thinks John will come, we'll have to invite him. If everyone thinks BILL will, we WON'T have to invite him."
    context := "Sloppy reading of the elided pronoun: we won't have to invite Bill."
    judgment := .acceptable
    alternatives := []
    readings := [("sloppy (him = Bill)", .acceptable)]
    paperFeatures := []
    comment := "Surprising sloppy reading: Bill's dref must scope out of a tensed clause and over the dynamically closed 'everyone' to bind the sloppy pro-form."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex5_22 : LinguisticExample :=
  { id := "charlow2014_ex5_22"
    source := ⟨"charlow-2014", "(5.22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everyone heard the rumor that at least six senators supported Cruz's filibuster. It turned out to be erroneous: they numbered at most three."
    discourseSegments := ["Everyone heard the rumor that at least six senators supported Cruz's filibuster.", "It turned out to be erroneous: they numbered at most three."]
    glossedTokens := []
    translation := "Everyone heard the rumor that at least six senators supported Cruz's filibuster. It turned out to be erroneous: they numbered at most three."
    context := "'they' refers to the senators who supported the filibuster."
    judgment := .acceptable
    alternatives := []
    readings := [("they = maximal refset", .acceptable)]
    paperFeatures := []
    comment := "A maximal refset dref created inside a scope island, under dynamically closed operators, is available for cross-sentential anaphora."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex5_23 : LinguisticExample :=
  { id := "charlow2014_ex5_23"
    source := ⟨"charlow-2014", "(5.23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's absolutely false that no senators admire Cruz. But even so, they're all very junior."
    discourseSegments := ["It's absolutely false that no senators admire Cruz.", "But even so, they're all very junior."]
    glossedTokens := []
    translation := "It's absolutely false that no senators admire Cruz. But even so, they're all very junior."
    context := "'they' refers to the senators who admire Cruz."
    judgment := .acceptable
    alternatives := []
    readings := [("they = maximal refset", .acceptable)]
    paperFeatures := []
    comment := "The refset dref of 'no senators' survives the negation scoping over its island."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex5_27b : LinguisticExample :=
  { id := "charlow2014_ex5_27b"
    source := ⟨"charlow-2014", "(5.27b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He also only introduced BILL to SUE."
    discourseSegments := []
    glossedTokens := []
    translation := "He also only introduced BILL to SUE."
    context := "Reply to 'John only introduced BILL to Mary' at a party where Mary met only Bill and Sue also met only Bill."
    judgment := .acceptable
    alternatives := []
    readings := [("also > SUE > only > BILL", .acceptable)]
    paperFeatures := []
    comment := "Selective association with focus: only associates with BILL, also with SUE."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex4_1a, ex4_1b, ex4_1c, ex4_2a, ex4_4, ex4_6, ex4_18b, ex4_23a, ex4_23b, ex4_25b, ex5_7a, ex5_22, ex5_23, ex5_27b]

end Charlow2014.Examples
