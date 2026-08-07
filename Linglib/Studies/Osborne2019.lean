import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Determiners
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Auxiliaries
import Linglib.Fragments.English.FunctionWords
import Linglib.Syntax.WordGrammar.LexicalRules
import Linglib.Syntax.DependencyGrammar.Valency
import Linglib.Syntax.DependencyGrammar.Catena
import Linglib.Syntax.DependencyGrammar.Basic

/-!
# Osborne 2019: valency, catenae, control, and ellipsis
[osborne-2019] [tesniere-1959]

[osborne-2019]'s dependency grammar, from the English Fragment lexicon:
each verb's valency is derived from its Fragment `complementType` (not
stipulated), concrete trees are checked against those valencies, the
passive lexical rule derives the passive valency from the transitive one,
catenae separate from constituents on the book's own examples, control
and raising lose their embedded subjects in the basic tree and recover
them in the enhanced graph, and gapping elides a catena that is not a
constituent. Formerly three files (`Osborne2019Control`,
`Osborne2019Ellipsis`); consolidated per the same-paper rule.
-/

namespace Osborne2019

open DependencyGrammar WordGrammar
open Morphology (Word)

/-! ### Words from the Fragment lexicon -/

private abbrev john := English.Nouns.john.toWordSg
private abbrev mary := English.Nouns.mary.toWordSg
private abbrev ball := English.Nouns.ball.toWordSg
private abbrev book := English.Nouns.book.toWordSg
private abbrev pizza := English.Nouns.pizza.toWordSg
private abbrev the_ := English.Determiners.the.toWord
private abbrev was_ := English.Auxiliaries.was.toWord
private abbrev by_ := English.FunctionWords.by_.toWord
private abbrev to_ := English.FunctionWords.to_.toWord
private abbrev sleeps := English.Predicates.Verbal.sleep.toWord3sg
private abbrev devours := English.Predicates.Verbal.devour.toWord3sg
private abbrev gives := English.Predicates.Verbal.give.toWord3sg
private abbrev kicked := English.Predicates.Verbal.kick.toWordPast
private abbrev kickedPass := English.Predicates.Verbal.kick.toWordPassive
private abbrev manages := English.Predicates.Verbal.manage.toWord3sg
private abbrev persuaded := English.Predicates.Verbal.persuade.toWordPast
private abbrev seems := English.Predicates.Verbal.seem.toWord3sg
private abbrev sleep_ := English.Predicates.Verbal.sleep.toWordBase
private abbrev run_ := English.Predicates.Verbal.run.toWordBase

/-! ### Valencies derived from the Fragment -/

theorem sleep_valency_from_fragment :
    English.Predicates.Verbal.sleep.complementType.valency =
      some Valency.intransitive := rfl

theorem devour_valency_from_fragment :
    English.Predicates.Verbal.devour.complementType.valency =
      some Valency.transitive := rfl

theorem give_valency_from_fragment :
    English.Predicates.Verbal.give.complementType.valency =
      some Valency.ditransitive := rfl

theorem kick_valency_from_fragment :
    English.Predicates.Verbal.kick.complementType.valency =
      some Valency.transitive := rfl

/-! ### Grammatical trees satisfy their valencies -/

def intransTree : Graph 2 := .ofArcs [john, sleeps] 1 [(1, 0, .nsubj)]

def transTree : Graph 3 :=
  .ofArcs [john, devours, pizza] 1 [(1, 0, .nsubj), (1, 2, .obj)]

def ditransTree : Graph 4 :=
  .ofArcs [john, gives, mary, book] 1
    [(1, 0, .nsubj), (1, 2, .iobj), (1, 3, .obj)]

example : checkVerbSubcat intransTree (.ofList [(1, Valency.intransitive)]) = true := by
  decide
example : checkVerbSubcat transTree (.ofList [(1, Valency.transitive)]) = true := by decide
example : checkVerbSubcat ditransTree (.ofList [(1, Valency.ditransitive)]) = true := by
  decide

/-! ### Ungrammatical trees violate them -/

/-- "*John sleeps book": intransitive with a spurious object. -/
def intransWithObj : Graph 3 :=
  .ofArcs [john, sleeps, book] 1 [(1, 0, .nsubj), (1, 2, .obj)]

/-- "*John devours": transitive missing its object. -/
def transNoObj : Graph 2 := .ofArcs [john, devours] 1 [(1, 0, .nsubj)]

example : checkVerbSubcat intransWithObj (.ofList [(1, Valency.intransitive)]) = false := by
  decide
example : checkVerbSubcat transNoObj (.ofList [(1, Valency.transitive)]) = false := by
  decide

/-! ### The passive lexical rule derives the passive valency -/

private def lexKicked : LexEntry :=
  { form := kicked.form, cat := .VERB, features := kicked.features
    valency := Valency.transitive }

theorem passive_derives_valency :
    passiveRule.applies lexKicked = true ∧
    (passiveRule.transform lexKicked).valency = Valency.passiveTransitive := ⟨rfl, rfl⟩

/-- "The ball was kicked (by John)": the passive tree satisfies the
    rule-derived valency. -/
def passiveTree : Graph 4 :=
  .ofArcs [the_, ball, was_, kickedPass] 3
    [(1, 0, .det), (3, 1, .nsubj), (3, 2, .auxPass)]

def longPassiveTree : Graph 6 :=
  .ofArcs [the_, ball, was_, kickedPass, by_, john] 3
    [(1, 0, .det), (3, 1, .nsubj), (3, 2, .auxPass), (3, 5, .obl), (5, 4, .case_)]

example : checkVerbSubcat passiveTree (.ofList [(3, Valency.passiveTransitive)]) = true := by
  decide
example :
    checkVerbSubcat longPassiveTree (.ofList [(3, Valency.passiveTransitive)]) = true := by
  decide

/-- "*The ball was kicked the pizza": passive with a leftover object. -/
def passiveWithObj : Graph 6 :=
  .ofArcs [the_, ball, was_, kickedPass, the_, pizza] 3
    [(1, 0, .det), (3, 1, .nsubj), (3, 2, .auxPass), (3, 5, .obj), (5, 4, .det)]

example :
    checkVerbSubcat passiveWithObj (.ofList [(3, Valency.passiveTransitive)]) = false := by
  decide

/-! ### Catenae vs constituents (Ch. 4)

In "John devours pizza", the verb with its subject {0, 1} is a catena but
not a constituent; each dominance cone is both. -/

example : IsCatena transTree {0, 1} := by decide
example : ¬ IsConstituent transTree {0, 1} := by decide
example : IsCatena transTree {0, 1, 2} := by decide
example : IsConstituent transTree {0, 1, 2} := by decide
example : IsConstituent transTree {2} := by decide
example : ¬ IsCatena transTree {0, 2} := by decide

/-! ### Control and raising (Ch. 7): the basic tree loses the embedded
subject; the enhanced graph recovers it -/

/-- "John manages to sleep" — subject control, basic tree. -/
def subjControl : Graph 4 :=
  .ofArcs [john, manages, to_, sleep_] 1
    [(1, 0, .nsubj), (1, 3, .xcomp), (3, 2, .mark)]

/-- "John persuaded Mary to run" — object control, basic tree. -/
def objControl : Graph 5 :=
  .ofArcs [john, persuaded, mary, to_, run_] 1
    [(1, 0, .nsubj), (1, 2, .obj), (1, 4, .xcomp), (4, 3, .mark)]

/-- "John seems to sleep" — raising: same basic geometry as subject
    control; the difference is thematic, not structural. -/
def raising : Graph 4 :=
  .ofArcs [john, seems, to_, sleep_] 1
    [(1, 0, .nsubj), (1, 3, .xcomp), (3, 2, .mark)]

example : HasUnrepresentedArg subjControl (subjControl.enhance [(3, 0, .nsubj)]) 0 := by
  decide
example : HasUnrepresentedArg objControl (objControl.enhance [(4, 2, .nsubj)]) 2 := by
  decide
example : HasUnrepresentedArg raising (raising.enhance [(3, 0, .nsubj)]) 0 := by decide
example : ¬ (subjControl.enhance [(3, 0, .nsubj)]).IsTree := by decide

/-! ### Gapping elides a catena that is not a constituent (Ch. 4, Ch. 12)

In gapping ("John devours pizza and Mary ___ wine"), the elided material —
the verb with its subject slot but without its object — is a catena of the
antecedent clause that is not one of its constituents. -/

example : IsCatena transTree {1, 0} := by decide
example : ¬ IsConstituent transTree {1, 0} := by decide

end Osborne2019
