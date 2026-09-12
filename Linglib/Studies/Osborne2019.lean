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
# Osborne (2019): A Dependency Grammar of English

This file formalizes the parts of the dependency grammar of [osborne-2019] that the English
fragment lexicon supports. A verb's valency frame (sixth chapter) is a lexical property, read
here off the fragment's complement type, and the passive participle's frame is not listed but
derived by a lexical rule that removes the object slot and adds an optional *by*-phrase
(`passive_valency`); trees over fragment words satisfy their frames, and a spurious or a
missing object violates them. The catena (fourth chapter), any set of words connected by
dominance, is the unit that constituents do not always match: every constituent is a catena,
a head with one of its dependents is always a catena, and it is never a constituent when the
head has another dependent, so a verb with its subject but not its object is a catena and not
a constituent (`IsConstituent.isCatena`, `isCatena_pair`, `not_isConstituent_pair`); that is
the material gapping elides (§12.7). Control and raising (§6.8, §6.9) share one basic tree,
whose embedded verb lacks a subject; the enhanced graph adds the subject arc, which the basic
tree cannot carry without ceasing to be a tree (`hasUnrepresentedArg_enhance`,
`Graph.not_isTree_enhance`).

## Implementation notes

The trees are Universal Dependencies graphs over fragment words after [tesniere-1959], and
the enhanced graph is the basic tree with the recovered subject arc added; the general lemmas
live in the dependency-grammar substrate and are instantiated here on the fragment trees.

## References

* [osborne-2019]
* [tesniere-1959]
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

/-! ### Valency frames from the Fragment (sixth chapter) -/

/-- The frame of a tree whose verb at position `i` is the fragment entry `v`: the valency its
complement type determines. -/
private def frameOf {n : ℕ} (v : English.Predicates.Verbal.VerbEntry) (i : Fin n) : Frames n :=
  .ofList [(i, (v.complementType.valency).getD [])]

def intransTree : Graph 2 := .ofArcs [john, sleeps] 1 [(1, 0, .nsubj)]

def transTree : Graph 3 :=
  .ofArcs [john, devours, pizza] 1 [(1, 0, .nsubj), (1, 2, .obj)]

def ditransTree : Graph 4 :=
  .ofArcs [john, gives, mary, book] 1 [(1, 0, .nsubj), (1, 2, .iobj), (1, 3, .obj)]

example : intransTree.SatisfiesFrames (frameOf English.Predicates.Verbal.sleep 1) := by decide
example : transTree.SatisfiesFrames (frameOf English.Predicates.Verbal.devour 1) := by decide
example : ditransTree.SatisfiesFrames (frameOf English.Predicates.Verbal.give 1) := by decide

/-- *John sleeps book: an intransitive with a spurious object. -/
def intransWithObj : Graph 3 :=
  .ofArcs [john, sleeps, book] 1 [(1, 0, .nsubj), (1, 2, .obj)]

/-- *John devours: a transitive missing its object. -/
def transNoObj : Graph 2 := .ofArcs [john, devours] 1 [(1, 0, .nsubj)]

example : ¬ intransWithObj.SatisfiesFrames (frameOf English.Predicates.Verbal.sleep 1) := by
  decide
example : ¬ transNoObj.SatisfiesFrames (frameOf English.Predicates.Verbal.devour 1) := by
  decide

/-! ### The passive valency is rule-derived (§6.6) -/

/-- The lexical entry of *kicked*, its valency from the fragment. -/
private def lexKicked : LexEntry :=
  { form := kicked.form, cat := .VERB, features := kicked.features
    valency := (English.Predicates.Verbal.kick.complementType.valency).getD [] }

/-- The passive rule applies to *kicked* and yields the passive valency. -/
theorem passive_valency :
    passiveRule.applies lexKicked = true ∧
      (passiveRule.transform lexKicked).valency = Valency.passiveTransitive :=
  passiveRule_transitive lexKicked rfl (by decide) rfl

/-- *The ball was kicked (by John)* satisfies the rule-derived valency. -/
def passiveTree : Graph 4 :=
  .ofArcs [the_, ball, was_, kickedPass] 3 [(1, 0, .det), (3, 1, .nsubj), (3, 2, .auxPass)]

def longPassiveTree : Graph 6 :=
  .ofArcs [the_, ball, was_, kickedPass, by_, john] 3
    [(1, 0, .det), (3, 1, .nsubj), (3, 2, .auxPass), (3, 5, .obl), (5, 4, .case_)]

example :
    passiveTree.SatisfiesFrames (.ofList [(3, (passiveRule.transform lexKicked).valency)]) := by
  decide
example :
    longPassiveTree.SatisfiesFrames
      (.ofList [(3, (passiveRule.transform lexKicked).valency)]) := by
  decide

/-- *The ball was kicked the pizza: a passive with a leftover object. -/
def passiveWithObj : Graph 6 :=
  .ofArcs [the_, ball, was_, kickedPass, the_, pizza] 3
    [(1, 0, .det), (3, 1, .nsubj), (3, 2, .auxPass), (3, 5, .obj), (5, 4, .det)]

example :
    ¬ passiveWithObj.SatisfiesFrames
      (.ofList [(3, (passiveRule.transform lexKicked).valency)]) := by
  decide

/-! ### Catenae against constituents (fourth chapter, §12.7)

In *John devours pizza* the verb with its subject is a catena, being a head with a dependent,
but not a constituent, since the verb has another dependent; the whole clause and the object
are constituents and therefore catenae. The verb with its subject is what gapping elides in
*John devours pizza and Mary wine*. -/

example : IsCatena transTree {1, 0} := isCatena_pair transTree (by decide) (by decide)

example : ¬ IsConstituent transTree {1, 0} :=
  not_isConstituent_pair (u := 2) (by decide) (by decide) (by decide) (by decide)

example : IsCatena transTree {0, 1, 2} :=
  (show IsConstituent transTree {0, 1, 2} by decide).isCatena

example : IsCatena transTree {2} := (show IsConstituent transTree {2} by decide).isCatena

example : ¬ IsCatena transTree {0, 2} := by decide

/-! ### Control and raising (§6.8, §6.9)

The basic tree of *John manages to sleep*, *John persuaded Mary to run*, and *John seems to
sleep* leaves the embedded verb without a subject; control and raising differ thematically,
not structurally. The enhanced graph recovers the subject arc, an argument relation the
basic tree does not carry and cannot, since a second head breaks the tree. -/

def subjControl : Graph 4 :=
  .ofArcs [john, manages, to_, sleep_] 1 [(1, 0, .nsubj), (1, 3, .xcomp), (3, 2, .mark)]

def objControl : Graph 5 :=
  .ofArcs [john, persuaded, mary, to_, run_] 1
    [(1, 0, .nsubj), (1, 2, .obj), (1, 4, .xcomp), (4, 3, .mark)]

def raising : Graph 4 :=
  .ofArcs [john, seems, to_, sleep_] 1 [(1, 0, .nsubj), (1, 3, .xcomp), (3, 2, .mark)]

example : HasUnrepresentedArg subjControl (subjControl.enhance [(3, 0, .nsubj)]) 0 :=
  hasUnrepresentedArg_enhance _ (x := 3) .nsubj _ (by simp) (by decide)

example : HasUnrepresentedArg objControl (objControl.enhance [(4, 2, .nsubj)]) 2 :=
  hasUnrepresentedArg_enhance _ (x := 4) .nsubj _ (by simp) (by decide)

example : HasUnrepresentedArg raising (raising.enhance [(3, 0, .nsubj)]) 0 :=
  hasUnrepresentedArg_enhance _ (x := 3) .nsubj _ (by simp) (by decide)

example : ¬ (subjControl.enhance [(3, 0, .nsubj)]).IsTree :=
  Graph.not_isTree_enhance (v := 1) (w := 0) (x := 3) (by decide) (by decide) .nsubj _ (by simp)

end Osborne2019
