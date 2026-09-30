module

public import Mathlib.Tactic.TypeStar

/-!
# Dialogue gameboards

This file defines the dialogue gameboard of Ginzburg's theory of dialogue KoS and the records it
holds. A dialogue gameboard is one participant's view of the public state of a conversation: who
holds the turn and whom they address, the facts accepted so far, the moves made, the utterances
not yet grounded, and the questions under discussion. An utterance is recorded as a locutionary
proposition, which keeps its phonology, category, contextual parameters and sub-utterances beside
its content, so that a clarification request can target any part of its form, as Ginzburg and
Cooper argue. A question under discussion is paired with its focus-establishing constituents, the
sub-utterances a fragment resolving it must match.

## Main definitions

* `Discourse.Gameboard.IllocMove`: illocutionary moves, the content of the Ch. 4 gameboard.
* `Discourse.Gameboard.SubUtterance`: sub-utterances.
* `Discourse.Gameboard.LocProp`: locutionary propositions.
* `Discourse.Gameboard.InfoStruc`: a question with its focus-establishing constituents.
* `Discourse.Gameboard.DGB`: the dialogue gameboard.

## Implementation notes

* A locutionary proposition is written with the utterance's values as fields, Ginzburg's single
  type notation, rather than as an Austinian proposition pairing the utterance with its type.
* A contextual parameter is its label; the restriction on its value is not represented.
* The sub-utterances of a locutionary proposition are listed, not computed from its daughters,
  and focus-establishing constituents are sub-utterances, since the rules that set them pick a
  constituent of an utterance.
* FACTS and QUD are lists, the gameboard omits the utterance time and the addressing condition,
  and `non-resolve-cond` is the predicate `DGB.NonResolveCond` of `Gameboard/Basic.lean`.

## TODO

* Phonological forms, syntactic categories and parameter labels are strings, as in the papers'
  attribute-value matrices; they become types once linglib has a type of syntactic categories.

## References

* [ginzburg-2012]
* [ginzburg-cooper-2004]
* [ginzburg-sag-2000]
-/

@[expose] public section

namespace Discourse.Gameboard

/-- An illocutionary move is the illocutionary relation of an illocutionary proposition applied
to its content ([ginzburg-2012] (8c) p. 361), without the speaker and addressee that the
proposition also records. The inventory is that of the rules of Ch. 4 less parting and
counter-parting. -/
inductive IllocMove (Fact QContent : Type*) where
  /-- Asserting a fact. -/
  | assert : Fact → IllocMove Fact QContent
  /-- Asking a question. -/
  | ask : QContent → IllocMove Fact QContent
  /-- Accepting an assertion. -/
  | accept : Fact → IllocMove Fact QContent
  /-- Asking for confirmation of an assertion. -/
  | check : Fact → IllocMove Fact QContent
  /-- Confirming in response to a check. -/
  | confirm : Fact → IllocMove Fact QContent
  /-- Greeting. -/
  | greet : IllocMove Fact QContent
  /-- Counter-greeting. -/
  | counterGreet : IllocMove Fact QContent
  deriving Repr, DecidableEq

/-- A sub-utterance, with the phonology, category and content that make any constituent of an
utterance clarifiable, the fractal heterogeneity of [ginzburg-cooper-2004]. -/
structure SubUtterance where
  /-- Phonological form. -/
  phon : String
  /-- Syntactic category. -/
  cat : String
  /-- The content, which for a sub-utterance contributing a contextual parameter is its label. -/
  cont : String
  deriving Repr, DecidableEq

/-- A locutionary proposition records an utterance in MOVES or PENDING with its phonology,
category, content, contextual parameters and constituents ([ginzburg-2012] pp. 172–174), so that
a clarification request can target the form of the utterance and any of its constituents, not
only its content. The fields are the single-type notation of (42) p. 174; the Austinian
proposition `[sit = u, sit-type = Tᵤ]` of (41) p. 173 and Appendix A (8d) p. 362 is not
represented. -/
structure LocProp (Cont : Type*) where
  /-- Phonological form. -/
  phon : String
  /-- Syntactic category. -/
  cat : String
  /-- Content. -/
  cont : Cont
  /-- The labels of the contextual parameters, which grounding must witness; like SLASH they are
  pooled from the words of the utterance ([ginzburg-cooper-2004] (29)). The restrictions on
  their values, the RESTR of (28), are not represented. -/
  cparams : List String := []
  /-- The sub-utterances, the utterance itself among them as in (42) p. 174, listed rather than
  computed from the daughters by the CONSTITS Amalgamation Constraint of
  [ginzburg-cooper-2004] (30). -/
  constits : List SubUtterance := []
  deriving Repr, DecidableEq

/-- An `InfoStruc` pairs a question under discussion with its focus-establishing constituents
(FECs), the sub-utterances a fragment resolving the question must match in category
([ginzburg-2012] p. 239 and (9) p. 362). The FEC of a wh-question is its wh-phrase, and that of a
clarification request the sub-utterance it clarifies; it replaces the `sal-utt` of
[ginzburg-sag-2000]. (9) types the FECs as locutionary propositions; they are sub-utterances here
because the rules that set them pick a constituent of an utterance (p. 241, and Appendix B (26e)
p. 374). -/
structure InfoStruc (QContent : Type*) where
  /-- The question. -/
  q : QContent
  /-- The focus-establishing constituents. -/
  fec : List SubUtterance := []
  deriving Repr, DecidableEq

/-- The dialogue gameboard of a participant is their public share of the conversational state
([ginzburg-2012] (43) p. 175); each participant has their own. `Cont` is the content of the
utterances in MOVES and PENDING: `IllocMove Fact QContent` recovers the gameboard of Ch. 4
((100) p. 111), whose moves are illocutionary propositions. FACTS is a set and QUD a partial
order in (43), `utt-time` and `c-utt` are omitted, and `non-resolve-cond` is a predicate on
gameboards rather than a field. -/
structure DGB (Participant Fact QContent Cont : Type*) where
  /-- The speaker. -/
  spkr : Participant
  /-- The addressee. -/
  addr : Participant
  /-- The commonly accepted facts. -/
  facts : List Fact := []
  /-- The moves made, the latest last. -/
  moves : List (LocProp Cont) := []
  /-- The utterances not yet grounded, MaxPending first. -/
  pending : List (LocProp Cont) := []
  /-- The questions under discussion, MaxQUD first. -/
  qud : List (InfoStruc QContent) := []
  deriving DecidableEq

namespace DGB

variable {Participant Fact QContent Cont : Type*}

/-- The latest move. -/
def latestMove (dgb : DGB Participant Fact QContent Cont) : Option (LocProp Cont) :=
  dgb.moves.getLast?

/-- The gameboard of a conversation with no moves yet, `spkr` addressing `addr`. -/
def initial (spkr addr : Participant) : DGB Participant Fact QContent Cont where
  spkr := spkr
  addr := addr

end DGB

end Discourse.Gameboard
