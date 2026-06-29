import Linglib.Discourse.CommonGround
import Linglib.Semantics.TypeTheoretic.Basic

/-!
# KOS: Type Definitions
[ginzburg-2012]

Pure type definitions for the KOS framework. No operations beyond the
trivial constructors / accessors required for type families to compose.
Operations live in sibling files (`Basic`, `InquiryCycle`, `Grounding`,
`Genre`).

## TTR-residence

KOS is built on TTR ([cooper-2023]). `LocProp` is a structural
refinement of `TTRSign String Cont` (Cooper §2.5 ex 70): same
`phon : String` + `cont : Cont` fields, plus dialogue-grade additions
(`cat`, `cparams`, `qcparams`, `constits`). The `Coe` instance and
the forgetful projection `LocProp.toTTRSign` live with the type definition
itself — `LocProp ⊐ TTRSign` is part of the substrate, not a downstream
bridge file.

(Lean's `deriving` machinery doesn't compose smoothly with `extends`-based
inheritance when parent fields involve free type parameters, so we keep
`LocProp` as a flat structure and provide the forgetful map by hand.
The structural commitment is unchanged: every `LocProp` projects to a
`TTRSign`, dischargeable via the typeclass.)

## Universe pinning

`Participant`, `Fact`, `QContent` are universe-polymorphic (`Type*`).
`Cont` is **pinned to `Type` (= `Type 0`)** because it flows into the
`TTRSign String Cont` projection (`LocProp.toTTRSign`), and TTRSign is
itself `Type`-pinned in `Semantics/TypeTheoretic/Core.lean`
(Cooper's "type-is-a-type" semantics requires `Type 0` for the carrier).
Same pinning applies in `KOS/Austinian.lean` (where `BCheckableAustinian`
and `TTRQuestionB` similarly require `Type`).

Migrating `Cont` to `Type*` requires lifting the entire TTR substrate
to universe polymorphism — out of scope for this layer's cleanup.
Document, don't migrate.

## Architecture

This file collects the load-bearing KOS types in dependency order:

- §1. `IllocMove` — speech-act labels
- §2. `CParam`, `CParamSet` — contextual parameters (Ginzburg-Cooper 2004 ex. 28,
       surviving as `dgb-params` in 2012). Shared between 2004 and 2012 study sites.
- §3. `SubUtterance` — addressable sub-utterance (G-C 2004 §2). Shared.
- §4. `LocProp` — locutionary proposition (Ch. 6 ex. 8d), polymorphic in content
- §5. `InfoStruc` — QUD-cell with focus-establishing constituents (Ch. 7 App. B ex. 2)
- §6. `DGB` — the dialogue gameboard, Ch. 6 final shape (ex. 43 p. 175):
       pending = LocProp, qud = InfoStruc
- §7. `GenreType` — TTR record classifying conversations (§4.6, ex. 88).
       Currently a thin record; full TTR enrichment in `Genre.lean`.
- §8. `MaxPending`, `PrivateState`, `TIS` — total information state (ex. 93)

## Ginzburg fidelity

The DGB and TIS types take a `Cont` parameter for utterance content,
enabling the Ch. 6 final shape (ex. 43 p. 175) where `Pending` stores
`LocProp Cont` (utterances with form + cparams + content) and `QUD`
stores `InfoStruc QContent Cont` (questions paired with their
focus-establishing constituents, §6.3 (Pending added to DGB; QUD-as-InfoStruc treatment in §7.6 FEC discussion)). Moves still use
`IllocMove Fact QContent` for case-analysis convenience; in the book's
final version they are also LocProps, but the IllocMove constructor
tags carry information our consumers find useful.

-/

namespace Discourse.KOS

open Semantics.TypeTheoretic (TTRSign)

-- ════════════════════════════════════════════════════
-- § 1. Illocutionary Moves
-- ════════════════════════════════════════════════════

/-- An illocutionary move in dialogue.

[ginzburg-2012] Ch. 4: moves are illocutionary propositions — speech
events classified by their illocutionary force. We abstract over the
content: assertions carry propositional content, queries carry
question content.

The `Fact` and `QContent` parameters match the DGB's content types.

**Note**: in the Ch. 6 final version (p. 215), MOVES stores LocProps
(situated speech events). Here we keep `IllocMove` for case-analysis
convenience — every constructor tag is a proper inductive case, which
downstream pattern-matching consumers depend on. -/
inductive IllocMove (Fact QContent : Type*) where
  /-- An assertion: speaker commits to propositional content. -/
  | assert : Fact → IllocMove Fact QContent
  /-- A query: speaker raises a question. -/
  | ask : QContent → IllocMove Fact QContent
  /-- Accept: addressee grounds an assertion. -/
  | accept : Fact → IllocMove Fact QContent
  /-- Check: addressee requests confirmation of an assertion. -/
  | check : Fact → IllocMove Fact QContent
  /-- Confirm: speaker confirms in response to check. -/
  | confirm : Fact → IllocMove Fact QContent
  /-- Greeting. -/
  | greet : IllocMove Fact QContent
  /-- Counter-greeting. -/
  | counterGreet : IllocMove Fact QContent
  deriving Repr, DecidableEq

/-- Extract the question content from a move, if any. -/
def IllocMove.questionContent {Fact QContent : Type*} : IllocMove Fact QContent → Option QContent
  | .ask q => some q
  | _ => none

-- ════════════════════════════════════════════════════
-- § 2. Contextual Parameters (shared 2004/2012 primitive)
-- ════════════════════════════════════════════════════

/-- A contextual parameter with INDEX and RESTR(ICTION).

Each C-PARAM has an index variable (e.g., "b" for the referent of "Bo")
and a restriction characterizing what values are acceptable (e.g.,
"named(Bo)(b)"). [ginzburg-cooper-2004] ex. 28; surviving in
[ginzburg-2012] as the `dgb-params` primitive.

This type is shared between 2004-paper-anchored studies (resolves/coercion
operations live in the 2004 study file) and 2012-paper-anchored substrate
(LocProp.cparams uses this as the dgb-params apparatus). -/
structure CParam where
  index : String
  restriction : String
  deriving Repr, DecidableEq

/-- A set of contextual parameters, analogous to the RSRL `GAP` set (`Syntax/HPSG/Construction`).

Both are non-local features (sets of outstanding dependencies):
- SLASH tracks syntactic gaps (filler-gap dependencies)
- C-PARAMS tracks contextual dependencies (referent resolution)

Both propagate via the same amalgamation mechanism (ex. 29 ≈ Nonlocal
Feature Principle) and get discharged at specific sites. -/
abbrev CParamSet := List CParam

-- ════════════════════════════════════════════════════
-- § 3. Sub-utterances (shared substrate)
-- ════════════════════════════════════════════════════

/-- A sub-utterance: the minimal addressable unit for clarification.

Every sub-utterance encodes PHON, CAT, and CONT — this **fractal
heterogeneity** is what makes clarification of any constituent possible.
[ginzburg-cooper-2004] §2; surviving in [ginzburg-2012] Ch. 6
as the `constits` field on LocProps. -/
structure SubUtterance where
  phon : String
  cat : String
  cont : String
  deriving Repr, DecidableEq

-- ════════════════════════════════════════════════════
-- § 4. Locutionary Propositions
-- ════════════════════════════════════════════════════

/-- A locutionary proposition: a speech event with both form and content.

[ginzburg-2012] Ch. 6, Appendix A (ex. 8d): LocProp replaces IllocProp
in MOVES and Pending. A LocProp records the phonological form, syntactic
category, and contextual parameters of the utterance — not just its
illocutionary content. This is crucial for CRification: clarification
requests target the *form* of the utterance, not just its content.

Parameterized over the content type `Cont` for grammar-neutrality.
When `Cont = String`, this subsumes the 2004 `UttSkeleton` representation.

The two parameter fields reflect [ginzburg-2012]'s sign architecture:
`cparams` carries dgb-params (referential, requiring contextual anchoring);
`qcparams` carries q-params (existentially closed at proposition level).
The asymmetry: only `cparams` triggers CRification under
`integrateLocProp`; q-params travel with the sign but do not block
grounding. This is the structural prerequisite for the Reprise Content
Hypothesis ([purver-ginzburg-2004], [ginzburg-2012] §8.5.1):
fragment reprises query the q-params record, not the dgb-params one. -/
structure LocProp (Cont : Type) where
  /-- Phonological form of the utterance — same field name as `TTRSign.phon`. -/
  phon : String
  /-- Syntactic category -/
  cat : String
  /-- Semantic content — same field name as `TTRSign.cont`. -/
  cont : Cont
  /-- DGB-PARAMS: referential parameters requiring contextual resolution.
      Empty = fully grounded; non-empty = CRification may be needed. -/
  cparams : CParamSet := []
  /-- Q-PARAMS: parameters whose index is existentially closed at the
      sentential level ([ginzburg-2012] §8.5.1, ex. 101–103, p. 325–326).
      Travel with the sign but do *not* trigger CRification — they
      contribute the descriptive content of non-referential NPs. -/
  qcparams : CParamSet := []
  /-- Sub-constituents accessible for clarification.
      [ginzburg-2012] Ch. 6: any sub-utterance can be targeted by a CR. -/
  constits : List SubUtterance := []
  deriving Repr, DecidableEq

/-- Forgetful projection `LocProp Cont → TTRSign String Cont`: keep `phon`
+ `cont`, drop dialogue-grade fields. -/
def LocProp.toTTRSign {Cont : Type} (lp : LocProp Cont) : TTRSign String Cont where
  phon := lp.phon
  cont := lp.cont

/-- `LocProp Cont ⊐ TTRSign String Cont` is structural: every `LocProp`
projects to a `TTRSign` via `LocProp.toTTRSign`. -/
instance {Cont : Type} : Coe (LocProp Cont) (TTRSign String Cont) where
  coe := LocProp.toTTRSign

/-- The projection preserves `phon`. -/
@[simp] theorem LocProp.toTTRSign_phon {Cont : Type} (lp : LocProp Cont) :
    lp.toTTRSign.phon = lp.phon := rfl

/-- The projection preserves `cont`. -/
@[simp] theorem LocProp.toTTRSign_cont {Cont : Type} (lp : LocProp Cont) :
    lp.toTTRSign.cont = lp.cont := rfl

-- ════════════════════════════════════════════════════
-- § 5. InfoStruc — QUD entries with focus-establishing constituents
-- ════════════════════════════════════════════════════

/-- An information structure: a question paired with its focus-establishing
constituents (FECs).

[ginzburg-2012] Ch. 7 (p. 239): QUD entries are not bare
questions but InfoStructs. The FEC records which sub-utterance(s)
established the question — this is what enables NSU resolution.

Example: "Who left?" pushes an InfoStruc with:
- q = "who left?"
- fec = [the LocProp for "who"]
A subsequent fragment "Bo" resolves the question by filling the FEC slot. -/
structure InfoStruc (QContent : Type*) (Cont : Type) where
  /-- The question under discussion -/
  q : QContent
  /-- Focus-establishing constituents from the utterance that introduced q -/
  fec : List (LocProp Cont) := []
  deriving Repr, DecidableEq

/-- Create an InfoStruc from a bare question (no FECs). -/
def InfoStruc.fromQuestion {QContent : Type*} {Cont : Type} (q : QContent) :
    InfoStruc QContent Cont where
  q := q

-- ════════════════════════════════════════════════════
-- § 6. Dialogue Gameboard
-- ════════════════════════════════════════════════════

/-- The Dialogue Gameboard.

[ginzburg-2012] ex. 100 (p. 111) and final version ex. 43 (p. 175).

Each conversational participant maintains their own DGB — distinct but
coupled gameboards, NOT a single shared context. The DGB tracks the
public component of a participant's conversational state.

The type parameters make content types explicit:
- `Participant`: type of participant identifiers (e.g., `String`, `Fin 2`)
- `Fact`: type of accumulated facts (e.g., `Set W` for typed CommonGround access)
- `QContent`: type of QUD questions (e.g., partition-based `QUD W`)
- `Cont`: type of locutionary content (e.g., `String` for surface form
  or `BCheckableAustinian S` for TTR-typed propositions)

This shape matches Ginzburg's Ch. 6 final DGB (ex. 43 p. 175), where
`pending`/`moves` store `LocProp`s and `qud` is a poset of questions:
- `pending` stores `LocProp` (with cparams, enabling CRification on form)
- `qud` stores `InfoStruc` (questions paired with FECs) — the InfoStruc-as-QUD
  refinement is the Ch. 7 development (p. 239), not ex. 43 itself
- `moves` keeps `IllocMove` for case-analysis convenience (the book's
  final form uses LocProps; converting incurs no fidelity cost since
  IllocMove constructors carry information LocProps would have to recover) -/
structure DGB (Participant Fact QContent : Type*) (Cont : Type) where
  /-- Current speaker ([ginzburg-2012] ex. 100) -/
  spkr : Option Participant := none
  /-- Current addressee ([ginzburg-2012] ex. 100) -/
  addr : Option Participant := none
  /-- Shared commitments. [ginzburg-2012]: "Facts : Set(Prop)" -/
  facts : List Fact := []
  /-- History of illocutionary moves (Ch. 4 ex. 100; cf. Ch. 6 ex. 43 LocProp form) -/
  moves : List (IllocMove Fact QContent) := []
  /-- Ungrounded locutionary propositions: Ch. 6 ex. 43 (p. 175) final shape.
      Each LocProp carries cparams (dgb-params) that the integration protocol
      (`integrateLocProp` in `KOS/Grounding.lean`) checks for resolution. -/
  pending : List (LocProp Cont) := []
  /-- Partially ordered set of questions under discussion.
      [ginzburg-2012] §6.3 / §7.6 (location verified against Ch. 6/7 narrative; specific ex. number not directly cited) final shape: QUD entries are
      `InfoStruc`s (questions with focus-establishing constituents),
      not bare questions. We use a list (most recent = front) following
      QUD-maximality. -/
  qud : List (InfoStruc QContent Cont) := []

/-- The latest move is the last element of the moves list. -/
def DGB.latestMove {Participant Fact QContent : Type*} {Cont : Type}
    (dgb : DGB Participant Fact QContent Cont) : Option (IllocMove Fact QContent) :=
  dgb.moves.getLast?

/-- An empty DGB. -/
def DGB.initial {Participant Fact QContent : Type*} {Cont : Type} :
    DGB Participant Fact QContent Cont := {}

-- ════════════════════════════════════════════════════
-- § 7. Genre Types
-- ════════════════════════════════════════════════════

/-- A conversational genre type.

[ginzburg-2012] §4.6 (pp. 101–110, ex. 88 p. 104): genres are TTR
record types that classify conversations by their characteristic
conversational structures. Example genres from the book: CasualChat
(ex. 88a), PetrolMarket (ex. 88b), BakeryChat (ex. 88c).

This schema captures the load-bearing fields from ex. 88:
- `qnud` (anticipated questions) — the question types that conversations
  of this genre are expected to raise
- `anticipatedMoves` — illocutionary moves the genre licenses
- `qudConstraint` — an optional explicit predicate on QUD content,
  subsuming qnud when set (used for thin worked examples)

The full TTR record per ex. 88 also includes agent fields (A, B : Ind),
utt-time, facts subset, and a co-propositionality constraint (eq. 91
p. 106) between MaxQUD and what each move can add. These need additional
type parameters (Participant, Fact, Cont) and richer co-propositionality
machinery that we defer to consumer-driven enrichment.

The relevance check (ex. 90 p. 105) and outcome predicate live in
`KOS/Genre.lean`. -/
structure GenreType (Fact QContent : Type*) where
  /-- Genre name for identification -/
  name : String
  /-- Anticipated questions in this genre (Ginzburg eq. 88 `qnud` field).
      Empty list = no anticipation (unrestricted on questions). -/
  qnud : List QContent := []
  /-- Anticipated illocutionary moves the genre licenses (Ginzburg eq. 88
      `moves` field). Used for outcome-fulfillability checks. -/
  anticipatedMoves : List (IllocMove Fact QContent) := []
  /-- Optional explicit constraint on QUD content; supersedes qnud when set.
      `none` = unrestricted (like CasualChat). The `qudConstraint`-based
      `genreRelevant` predicate (Ginzburg eq. 90) lives in `KOS/Genre.lean`. -/
  qudConstraint : Option (List QContent → Bool) := none

-- ════════════════════════════════════════════════════
-- § 8. Total Information State
-- ════════════════════════════════════════════════════

/-! ### MaxPending = head of Pending (no separate field)

Per [ginzburg-2012] §6.3 (footnote 31 p. 168) and §8.2: **MaxPending
is the maximal element of the `dgb.pending` field**, not a separately-
stored struct. Pending stores `LocProp Cont`s in last-in-first-out order;
MaxPending is `pending.head?`. The previous formaliser struct
(`MaxPending` with `phonSoFar`/`cat`/`partialContent`) bore no resemblance
to Ginzburg's notion and is now deleted. The accessor lives on `TIS`
(see `KOS/SelfRepair.lean`).

For incremental construction (§8.2.3 word-by-word), substrate operates
on the head of Pending directly — the LocProp's `phon` field gets
extended, no separate "phonSoFar" field needed. -/

/-- The private component of an information state.

[ginzburg-2012] ex. 93 (p. 107): PRType has genre, beliefs, and agenda.
Agenda is a list of illocutionary propositions that the participant plans
to realize. Beliefs are private (non-public) propositional attitudes. -/
structure PrivateState (Fact QContent : Type*) where
  /-- The conversational genre the participant takes the interaction to be. -/
  genre : Option (GenreType Fact QContent) := none
  /-- The participant's agenda: planned illocutionary moves. -/
  agenda : List (IllocMove Fact QContent) := []

/-- Total Information State (TIS).

[ginzburg-2012] ex. 93 (p. 107): the TIS consists of the public DGB
and a private component (genre, beliefs, agenda). The `Cont` parameter
threads through to the DGB's pending and qud fields. -/
structure TIS (Participant Fact QContent : Type*) (Cont : Type) where
  /-- The public dialogue gameboard -/
  dgb : DGB Participant Fact QContent Cont := {}
  /-- Private state: genre, agenda -/
  priv : PrivateState Fact QContent := {}

/-- An empty TIS. -/
def TIS.initial {Participant Fact QContent : Type*} {Cont : Type} :
    TIS Participant Fact QContent Cont := {}

end Discourse.KOS
