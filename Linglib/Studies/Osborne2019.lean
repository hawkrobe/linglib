import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Determiners
import Linglib.Fragments.English.Verbs
import Linglib.Fragments.English.Auxiliaries
import Linglib.Fragments.English.Adposition
import Linglib.Syntax.DependencyGrammar.Valency
import Linglib.Syntax.Voice.Basic
import Linglib.Syntax.DependencyGrammar.Catena
import Linglib.Syntax.DependencyGrammar.Basic

/-!
# Osborne (2019): A Dependency Grammar of English

This file formalizes the parts of the dependency grammar of [osborne-2019] that the English
fragment lexicon supports. A verb's valency frame (sixth chapter) is a lexical property, read
here off the coding roles of the fragment's citation frame, and the passive participle's frame
is not listed but related to the active one by a shuffle of indices, the slot correspondence of
the passive voice, with the demoted subject an optional *by*-phrase (`voiceValency_passive`);
an ergative verb's intransitive use suppresses the agent instead and has no *by*-phrase
(`voiceValency_anticausative`). Trees over fragment words satisfy their frames, and a spurious
or a missing object violates them. The catena (fourth chapter), any set of words connected by
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
live in the dependency-grammar substrate and are instantiated here on the fragment trees. The
UD trees make the subject of a passive participle its dependent, where [osborne-2019]'s
function-word-headed trees mark it with ↑ as a dependent of the finite auxiliary.

## References

* [osborne-2019]
* [tesniere-1959]
-/

namespace Osborne2019

open DependencyGrammar
open Morphology (Word)

/-! ### Words from the Fragment lexicon -/

private abbrev john := English.Nouns.john.toWord
private abbrev mary := English.Nouns.mary.toWord
private abbrev ball := English.Nouns.ball.toWordSg
private abbrev book := English.Nouns.book.toWordSg
private abbrev pizza := English.Nouns.pizza.toWordSg
private abbrev the_ := English.Determiners.the.toWord
private abbrev was_ := English.Auxiliaries.was.toWord
private abbrev by_ := English.Adpositions.by_.toWord
private abbrev to_ := English.Adpositions.to_.toWord
private abbrev sleeps := English.sleep.toWord .thirdSg
private abbrev devours := English.devour.toWord .thirdSg
private abbrev gives := English.give.toWord .thirdSg
private abbrev kicked := English.kick.toWord .past
private abbrev kickedPass := English.kick.passiveParticiple
private abbrev givenPass := English.give.passiveParticiple
private abbrev a_ := English.Determiners.a.toWord
private abbrev manages := English.manage.toWord .thirdSg
private abbrev persuaded := English.persuade.toWord .past
private abbrev seems := English.seem.toWord .thirdSg
private abbrev sleep_ := English.sleep.toWord .base
private abbrev run_ := English.run.toWord .base

/-! ### Valency frames from the Fragment (sixth chapter) -/

/-- The valency of the fragment entry's citation frame. -/
private def citationValency (v : English.Verb) : Valency :=
  (v.citationFrame?.map Valency.ofFrame).getD []

def intransTree : Graph 2 := .ofArcs [john, sleeps] 1 [(1, 0, .nsubj)]

def transTree : Graph 3 :=
  .ofArcs [john, devours, pizza] 1 [(1, 0, .nsubj), (1, 2, .obj)]

def ditransTree : Graph 4 :=
  .ofArcs [john, gives, mary, book] 1 [(1, 0, .nsubj), (1, 2, .iobj), (1, 3, .obj)]

example : intransTree.SatisfiesFrames (.ofList [(1, citationValency English.sleep)]) := by
  decide
example : transTree.SatisfiesFrames (.ofList [(1, citationValency English.devour)]) := by
  decide
example : ditransTree.SatisfiesFrames (.ofList [(1, citationValency English.give)]) := by
  decide

/-- *John sleeps book: an intransitive with a spurious object. -/
def intransWithObj : Graph 3 :=
  .ofArcs [john, sleeps, book] 1 [(1, 0, .nsubj), (1, 2, .obj)]

/-- *John devours: a transitive missing its object. -/
def transNoObj : Graph 2 := .ofArcs [john, devours] 1 [(1, 0, .nsubj)]

example : ¬ intransWithObj.SatisfiesFrames (.ofList [(1, citationValency English.sleep)]) := by
  decide
example : ¬ transNoObj.SatisfiesFrames (.ofList [(1, citationValency English.devour)]) := by
  decide

/-! ### The passive frame from the active frame (§6.6)

The passive participle's frame is not listed but related to the active frame by a shuffle of
indices, (8): the active object is the subject and the active subject the optional object of
*by*. The shuffle is the slot correspondence of the passive voice, and the *by*-phrase
realizes the participant it denucleativizes. The intransitive use of an ergative verb, *It
opened*, also makes the object the subject, but it suppresses the agent, and no *by*-phrase
expresses it. -/

/-- The valency of the construction a voice derives: its derived frame's valency and an
optional *by*-phrase for each initial core term the voice denucleativizes. -/
def voiceValency (v : Voice) : Valency :=
  Valency.ofFrame v.target ++
    (v.source.coreSlots.filter (v.fate · = .denucleativized)).map fun _ ↦ ⟨.obl, .right, false⟩

/-- (8a): the English passive has the subject and an optional *by*-phrase. -/
theorem voiceValency_passive : voiceValency English.passive = Valency.passiveTransitive := by
  decide

/-- (8b): the passive of the double-object frame keeps the second object. -/
theorem voiceValency_passive_np_np : voiceValency (Voice.passive .np_np) =
    [⟨.nsubj, .left, true⟩, ⟨.obj, .right, true⟩, ⟨.obl, .right, false⟩] := by
  decide

/-- *Open* alternates by the anticausative, whose valency has no *by*-phrase. -/
theorem voiceValency_anticausative : English.open_.Alternates Voice.anticausative ∧
    voiceValency Voice.anticausative = Valency.intransitive := by
  decide

/-- The valency of the fragment entry's passive participle. -/
private def passiveValency (v : English.Verb) : Valency :=
  (v.citationFrame?.map fun fr ↦ voiceValency (Voice.passive fr)).getD []

/-- *The ball was kicked (by John)* satisfies the participle's derived valency. -/
def passiveTree : Graph 4 :=
  .ofArcs [the_, ball, was_, kickedPass] 3 [(1, 0, .det), (3, 1, .nsubj), (3, 2, .auxPass)]

def longPassiveTree : Graph 6 :=
  .ofArcs [the_, ball, was_, kickedPass, by_, john] 3
    [(1, 0, .det), (3, 1, .nsubj), (3, 2, .auxPass), (3, 5, .obl), (5, 4, .case_)]

example : passiveTree.SatisfiesFrames (.ofList [(3, passiveValency English.kick)]) := by decide
example : longPassiveTree.SatisfiesFrames (.ofList [(3, passiveValency English.kick)]) := by
  decide

/-- *The ball was kicked the pizza: a passive with a leftover object. -/
def passiveWithObj : Graph 6 :=
  .ofArcs [the_, ball, was_, kickedPass, the_, pizza] 3
    [(1, 0, .det), (3, 1, .nsubj), (3, 2, .auxPass), (3, 5, .obj), (5, 4, .det)]

example : ¬ passiveWithObj.SatisfiesFrames (.ofList [(3, passiveValency English.kick)]) := by
  decide

/-- *Mary was given a book*: the passive of a double-object verb keeps its second object. -/
def ditransPassiveTree : Graph 5 :=
  .ofArcs [mary, was_, givenPass, a_, book] 2
    [(2, 0, .nsubj), (2, 1, .auxPass), (2, 4, .obj), (4, 3, .det)]

/-- *Mary was given: the second object is missing. -/
def ditransPassiveNoObj : Graph 3 :=
  .ofArcs [mary, was_, givenPass] 2 [(2, 0, .nsubj), (2, 1, .auxPass)]

example : ditransPassiveTree.SatisfiesFrames (.ofList [(2, passiveValency English.give)]) := by
  decide
example : ¬ ditransPassiveNoObj.SatisfiesFrames (.ofList [(2, passiveValency English.give)]) := by
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
