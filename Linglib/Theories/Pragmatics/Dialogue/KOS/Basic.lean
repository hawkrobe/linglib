import Linglib.Core.Semantics.CommonGround
import Linglib.Core.Discourse.SpeechActs
/-!
# KOS: Dialogue Gameboards

This file formalizes the KOS framework for dialogue as presented in two
distinct sources:

1. **@cite{ginzburg-2012} Ch. 4** (§§4.1–4.7): The Dialogue Gameboard (DGB) and
   Total Information State (TIS), conversational rules, genres, and
   M-Coherence. This is the **primary** source.

2. **@cite{ginzburg-cooper-2004}**: Clarification Ellipsis machinery — C-PARAMS,
   coercion operations (parameter focussing, parameter identification,
   existential generalization), utterance skeletons, and the sign+assignment
   model of grounding. This is a **supplementary** source for the CE analysis.

## @cite{ginzburg-2012} DGB (ex. 100, p. 111; final version ex. 113, p. 215)

The DGB is a conversational participant's own version of the public context:

- **spkr, addr**: current speaker and addressee
- **Facts**: shared commitments (Set of propositions)
- **Moves**: history of illocutionary moves (list of LocProp)
- **Pending**: ungrounded locutionary propositions (added in Ch. 6)
- **QUD**: partially ordered set of questions under discussion
- **non-resolve-cond**: well-formedness constraint — no QUD question is
  resolved by FACTS (see `DGB.nonResolveCond` in `Rules.lean`)

### Known simplifications

Our DGB corresponds to the **Ch. 4 intermediate version** (ex. 100), not
the final Ch. 6 version (ex. 113). Specific differences:

1. **MOVES**: stores `IllocMove` (Ch. 4) not `LocProp` (Ch. 6 final)
2. **QUD**: stores bare `QContent` not `InfoStruc` (question + FECs, ex. 39)
3. **Pending**: uses `PendingLoc` not `LocProp` (Ch. 6 final)
4. **utt-time / c-utt**: temporal fields from ex. 100 are not modeled

## @cite{ginzburg-2012} TIS (ex. 93, p. 107)

The Total Information State wraps the DGB and adds a private component:

- **DGB**: the public dialogue gameboard
- **Private**: genre, beliefs, agenda — non-public processing state

## @cite{ginzburg-cooper-2004}: Clarification Ellipsis (§§3–6)

C-PARAMS, coercion operations, utterance skeletons, and the MAX-QUD/SAL-UTT
processing state for Clarification Ellipsis. These are preserved in a
clearly separated section below.
-/

namespace Pragmatics.Dialogue.KOS

-- ════════════════════════════════════════════════════════════
-- Part I: @cite{ginzburg-2012} — Core DGB/TIS Framework
-- ════════════════════════════════════════════════════════════

-- ════════════════════════════════════════════════════
-- § 1. Illocutionary Moves
-- ════════════════════════════════════════════════════

/-- An illocutionary move in dialogue.

@cite{ginzburg-2012} Ch. 4: moves are illocutionary propositions — speech
events classified by their illocutionary force. In the final version (p. 215),
MOVES stores locutionary propositions (situated speech events). We abstract
over the content: assertions carry propositional content, queries carry
question content.

The `Fact` and `QContent` parameters match the DGB's content types. -/
inductive IllocMove (Fact QContent : Type) where
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

/-- Extract the propositional content from a move, if any. -/
def IllocMove.factContent {Fact QContent : Type} : IllocMove Fact QContent → Option Fact
  | .assert p | .accept p | .check p | .confirm p => some p
  | _ => none

/-- Extract the question content from a move, if any. -/
def IllocMove.questionContent {Fact QContent : Type} : IllocMove Fact QContent → Option QContent
  | .ask q => some q
  | _ => none

-- ════════════════════════════════════════════════════
-- § 1b. IllocMove ↔ Searle Bridge
-- ════════════════════════════════════════════════════

/-- Map an illocutionary move to @cite{searle-1979}'s five-class taxonomy.

Assert/accept/confirm are assertives (mind-to-world fit). Ask is a directive
(world-to-mind: the speaker tries to get the addressee to provide information).
Check is a directive (requesting confirmation). Greet/counterGreet are
expressives (null fit). -/
def IllocMove.toSearleClass {Fact QContent : Type} :
    IllocMove Fact QContent → Core.Discourse.SearleClass
  | .assert _   => .assertive
  | .accept _   => .assertive
  | .confirm _  => .assertive
  | .ask _      => .directive
  | .check _    => .directive
  | .greet      => .expressive
  | .counterGreet => .expressive

/-- Direction of fit for an illocutionary move, derived via Searle class. -/
def IllocMove.directionOfFit {Fact QContent : Type}
    (m : IllocMove Fact QContent) : Core.Discourse.DirectionOfFit :=
  m.toSearleClass.directionOfFit

/-- Assertions have mind-to-world fit: the speaker is responsible if p is false. -/
theorem IllocMove.assert_mind_to_world {Fact QContent : Type} (p : Fact) :
    (IllocMove.assert (QContent := QContent) p).directionOfFit = .mindToWorld := rfl

/-- Queries have world-to-mind fit: the speaker wants the addressee to act. -/
theorem IllocMove.ask_world_to_mind {Fact QContent : Type} (q : QContent) :
    (IllocMove.ask (Fact := Fact) q).directionOfFit = .worldToMind := rfl

/-- Greetings have null fit: they express social acknowledgement. -/
theorem IllocMove.greet_null_fit {Fact QContent : Type} :
    (IllocMove.greet : IllocMove Fact QContent).directionOfFit = .null := rfl

-- ════════════════════════════════════════════════════
-- § 2. Dialogue Gameboard (@cite{ginzburg-2012} ex. 100/113)
-- ════════════════════════════════════════════════════

/-- A pending locutionary proposition: an ungrounded utterance.

@cite{ginzburg-2012} Ch. 6, ex. 113 (p. 215): in the final DGB version,
Pending stores full LocProps (defined in §15 below). This `PendingLoc`
is a simplified representation used in the DGB struct. For the full
LocProp-based grounding protocol, see `integrateLocProp` in `Rules.lean`.

**Known simplification**: the final DGB (ex. 113) uses `List(LocProp)` for
both MOVES and Pending. Our DGB uses `IllocMove` for MOVES and `PendingLoc`
for Pending — this corresponds to the Ch. 4 intermediate version. -/
structure PendingLoc where
  /-- The utterance event identifier -/
  utt : String
  /-- The classifying type (as string description) -/
  uttType : String
  deriving Repr, DecidableEq

/-- The Dialogue Gameboard.

@cite{ginzburg-2012} ex. 100 (p. 111) and final version ex. 113 (p. 215).

Each conversational participant maintains their own DGB — distinct but
coupled gameboards, NOT a single shared context. The DGB tracks the
public component of a participant's conversational state.

The type parameters make content types explicit:
- `Participant`: type of participant identifiers (e.g., `String`, `Fin 2`)
- `Fact`: type of accumulated facts (e.g., `BProp W` for typed CG access)
- `QContent`: type of QUD entries (e.g., partition-based `QUD W`) -/
structure DGB (Participant Fact QContent : Type) where
  /-- Current speaker (@cite{ginzburg-2012} ex. 100) -/
  spkr : Option Participant := none
  /-- Current addressee (@cite{ginzburg-2012} ex. 100) -/
  addr : Option Participant := none
  /-- Shared commitments. @cite{ginzburg-2012}: "Facts : Set(Prop)" -/
  facts : List Fact := []
  /-- History of illocutionary moves. @cite{ginzburg-2012}: "Moves : list(IllocProp)".
      The last element is the LatestMove.

      **Known simplification**: the final DGB (ex. 113, p. 215) stores LocProps
      in MOVES, not illocutionary propositions. We use `IllocMove` here,
      matching the Ch. 4 version. -/
  moves : List (IllocMove Fact QContent) := []
  /-- Ungrounded locutionary propositions.
      @cite{ginzburg-2012} Ch. 6 (p. 215): added to the DGB in the final version. -/
  pending : List PendingLoc := []
  /-- Partially ordered set of questions under discussion.
      @cite{ginzburg-2012}: "QUD : poset(Question)". We use a list
      (most recent = front) following QUD-maximality.

      **Known simplification**: the final version (ex. 39, p. 239) makes QUD
      entries `InfoStruc` (question + FECs) rather than bare questions. We use
      bare `QContent` here; the `InfoStruc` type is defined in §16 below. -/
  qud : List QContent := []

/-- The latest move is the last element of the moves list. -/
def DGB.latestMove {Participant Fact QContent : Type}
    (dgb : DGB Participant Fact QContent) : Option (IllocMove Fact QContent) :=
  dgb.moves.getLast?

/-- An empty DGB. -/
def DGB.initial {Participant Fact QContent : Type} : DGB Participant Fact QContent := {}

-- ════════════════════════════════════════════════════
-- § 3. Genre Types (@cite{ginzburg-2012} §4.6, pp. 101–110)
-- ════════════════════════════════════════════════════

/-- A conversational genre type.

@cite{ginzburg-2012} §4.6 (pp. 101–110): genres are TTR record types that
classify conversations by their characteristic conversational structures.
Example genres from the book: CasualChat (ex. 88a), PetrolMarket (ex. 88b),
BakeryChat (ex. 88c).

We model genre types as records with optional constraints on the QUD
content and move patterns. The `qudConstraint` field captures the genre-
specific restrictions on what questions may be discussed. -/
structure GenreType (QContent : Type) where
  /-- Genre name for identification -/
  name : String
  /-- Constraint on which questions may be in QUD.
      `none` means unrestricted (like CasualChat). -/
  qudConstraint : Option (List QContent → Bool) := none

/-- The generic DGBType — the supertype of all genre types.
@cite{ginzburg-2012} ex. 86 (p. 103): `DGBTypefin GenreType`. -/
def GenreType.generic {QContent : Type} : GenreType QContent where
  name := "generic"

-- ════════════════════════════════════════════════════
-- § 4. Total Information State (@cite{ginzburg-2012} ex. 93, p. 107)
-- ════════════════════════════════════════════════════

/-- A turn under construction: an incomplete utterance being built incrementally.

@cite{ginzburg-2012} Ch. 6–7: the TuC tracks the unfolding utterance as it is
produced word-by-word. Participants can intervene mid-turn (completions,
collaborative finishes, self-repairs). The TuC is part of the private state
because each participant may have a different parse of the emerging turn.

The `pending` field on the DGB tracks ungrounded *complete* utterances;
TuC tracks *incomplete* ones. When the turn is complete, its content
moves from TuC to Pending (if unresolved) or Facts (if grounded). -/
structure TurnUnderConstr where
  /-- Phonological material produced so far -/
  phonSoFar : String := ""
  /-- Syntactic category of the emerging constituent -/
  cat : Option String := none
  /-- Partial content accumulated -/
  partialContent : Option String := none
  deriving Repr, DecidableEq

/-- The private component of an information state.

@cite{ginzburg-2012} ex. 93 (p. 107): PRType has genre, beliefs, and agenda.
Agenda is a list of illocutionary propositions that the participant plans
to realize. Beliefs are private (non-public) propositional attitudes. -/
structure PrivateState (Fact QContent : Type) where
  /-- The conversational genre the participant takes the interaction to be. -/
  genre : Option (GenreType QContent) := none
  /-- The participant's agenda: planned illocutionary moves. -/
  agenda : List (IllocMove Fact QContent) := []
  /-- The turn currently under construction (if any).
      @cite{ginzburg-2012} Ch. 7: enables self-repair and collaborative completion. -/
  turnUnderConstr : Option TurnUnderConstr := none

/-- Total Information State (TIS).

@cite{ginzburg-2012} ex. 93 (p. 107): the TIS consists of the public DGB
and a private component (genre, beliefs, agenda).

This replaces the earlier `IS` type which conflated @cite{ginzburg-cooper-2004}
processing state (MAX-QUD, SAL-UTT) with the 2012 architecture. The 2004
clarification processing state is available separately via `CEState`. -/
structure TIS (Participant Fact QContent : Type) where
  /-- The public dialogue gameboard -/
  dgb : DGB Participant Fact QContent := {}
  /-- Private state: genre, agenda -/
  private_ : PrivateState Fact QContent := {}

/-- An empty TIS. -/
def TIS.initial {Participant Fact QContent : Type} : TIS Participant Fact QContent := {}

-- ════════════════════════════════════════════════════════════
-- Part II: @cite{ginzburg-cooper-2004} — Clarification Ellipsis
-- ════════════════════════════════════════════════════════════

/-! ## Clarification Ellipsis Machinery

The following definitions are from @cite{ginzburg-cooper-2004}, which
develops a theory of Clarification Ellipsis (CE) using contextual parameters
(C-PARAMS), utterance skeletons, and coercion operations. These concepts
predate the TTR reformulation in @cite{ginzburg-2012} Ch. 5–6.

In the 2012 book, the corresponding machinery uses `dgb-params` (record
types) rather than C-PARAMS (index-restriction pairs), and Clarification
Context Update Rules (CCURs) rather than the three coercion operations.
We preserve the 2004 formulation as it is more directly computational. -/

-- ════════════════════════════════════════════════════
-- § 5. Contextual Parameters (@cite{ginzburg-cooper-2004})
-- ════════════════════════════════════════════════════

/-- A contextual parameter with INDEX and RESTR(ICTION).

Each C-PARAM has an index variable (e.g., "b" for the referent of "Bo")
and a restriction characterizing what values are acceptable (e.g.,
"named(Bo)(b)"). @cite{ginzburg-cooper-2004} ex. 28. -/
structure CParam where
  index : String
  restriction : String
  deriving Repr, DecidableEq

/-- A set of contextual parameters, analogous to `HPSG.SlashValue`.

Both are non-local features (sets of outstanding dependencies):
- SLASH tracks syntactic gaps (filler-gap dependencies)
- C-PARAMS tracks contextual dependencies (referent resolution)

Both propagate via the same amalgamation mechanism (ex. 29 ≈ Nonlocal
Feature Principle) and get discharged at specific sites. -/
abbrev CParamSet := List CParam

-- ════════════════════════════════════════════════════
-- § 6. Contextual Assignment (@cite{ginzburg-cooper-2004})
-- ════════════════════════════════════════════════════

/-- A contextual assignment maps parameter indices to values.

Grounding requires a *total* assignment (all C-PARAMS resolved).
Clarification arises when the assignment is *partial*.
@cite{ginzburg-cooper-2004} §6, ex. 81–82. -/
structure CtxtAssignment where
  bindings : List (String × String) := []
  deriving Repr, DecidableEq

/-- Does the assignment resolve a given parameter? -/
def CtxtAssignment.resolves (f : CtxtAssignment) (cp : CParam) : Bool :=
  f.bindings.any (·.1 == cp.index)

/-- Does the assignment resolve all parameters in a set? -/
def CtxtAssignment.resolvesAll (f : CtxtAssignment) (ps : CParamSet) : Bool :=
  ps.all f.resolves

/-- Which parameters remain unresolved? -/
def CtxtAssignment.unresolved (f : CtxtAssignment) (ps : CParamSet) : CParamSet :=
  ps.filter (!f.resolves ·)

-- ════════════════════════════════════════════════════
-- § 7. Utterance Skeletons (@cite{ginzburg-cooper-2004})
-- ════════════════════════════════════════════════════

/-- A sub-utterance: the minimal addressable unit for clarification.

Every sub-utterance encodes PHON, CAT, and CONT — this **fractal
heterogeneity** is what makes clarification of any constituent possible.
@cite{ginzburg-cooper-2004} §2. -/
structure SubUtterance where
  phon : String
  cat : String
  cont : String
  deriving Repr, DecidableEq

/-- An utterance skeleton: a sign with C-PARAMS and CONSTITS.

The CONSTITS feature (ex. 30) provides access to all sub-utterances.
C-PARAMS (ex. 28–29) are the contextual dependencies introduced by the
sign, amalgamated from daughters via the Non-local Amalgamation Constraint.
@cite{ginzburg-cooper-2004} §3. -/
structure UttSkeleton where
  phon : String
  cat : String
  cont : String
  cparams : CParamSet := []
  constits : List SubUtterance := []
  deriving Repr, DecidableEq

/-- Find the constituent whose CONT matches a parameter index. -/
def UttSkeleton.constitForParam (u : UttSkeleton) (paramIdx : String) :
    Option SubUtterance :=
  u.constits.find? (·.cont == paramIdx)

-- ════════════════════════════════════════════════════
-- § 8. CE Processing State (@cite{ginzburg-cooper-2004})
-- ════════════════════════════════════════════════════

/-- A sign paired with a contextual assignment.

@cite{ginzburg-cooper-2004} ex. 81, p.353. The assignment f records which
C-PARAMS have been resolved. Grounding checks whether f is total. -/
structure SignAssignment where
  sign : UttSkeleton
  assignment : CtxtAssignment
  deriving Repr, DecidableEq

/-- Clarification Ellipsis processing state.

@cite{ginzburg-cooper-2004}: MAX-QUD and SAL-UTT are processing state for
the CE analysis. These are NOT part of the @cite{ginzburg-2012} DGB or TIS
(in 2012, MaxQUD is computed from the QUD poset's maximal element, not
stored separately).

This state can be used alongside the 2012 TIS when CE processing is needed. -/
structure CEState (QContent : Type) where
  /-- The currently maximal question — for CE coercion operations -/
  maxQud : Option QContent := none
  /-- The salient sub-utterance — target of clarification -/
  salUtt : Option SubUtterance := none
  /-- Pending utterances awaiting C-PARAMS resolution -/
  pendingUtts : List SignAssignment := []

-- ════════════════════════════════════════════════════
-- § 9. Coercion Operations (@cite{ginzburg-cooper-2004})
-- ════════════════════════════════════════════════════

/-- The three coercion operations on signs with unresolved C-PARAMS.
@cite{ginzburg-cooper-2004} §5. -/
inductive CoercionOp where
  /-- Clausal CE reading: polar question about content (ex. 53) -/
  | paramFocussing
  /-- Constituent CE reading: wh-question about speaker meaning (ex. 59) -/
  | paramIdentification
  /-- Ground without clarification: ∃-quantify a parameter (ex. 77) -/
  | existentialGeneralization
  deriving Repr, DecidableEq

/-- Output of a coercion operation: partial specification for the
    clarification context. -/
structure CoercionOutput where
  op : CoercionOp
  /-- SAL-UTT: the sub-utterance to be echoed -/
  salUtt : SubUtterance
  /-- MAX-QUD: the question raised (string representation) -/
  maxQud : String
  deriving Repr, DecidableEq

/-- Parameter focussing (@cite{ginzburg-cooper-2004} ex. 53):
derive clausal CE reading.

Takes the *antecedent sign* and a problematic parameter index.
Finds the constituent that introduced the parameter.
Produces MAX-QUD = polar question about the antecedent content. -/
def parameterFocussing (antecedent : UttSkeleton) (paramIdx : String) :
    Option CoercionOutput :=
  match antecedent.constitForParam paramIdx with
  | none => none
  | some constit => some {
    op := .paramFocussing
    salUtt := constit
    maxQud := s!"?{paramIdx}.{antecedent.cont}"
  }

/-- Parameter identification (@cite{ginzburg-cooper-2004} ex. 59):
derive constituent CE reading.

Produces MAX-QUD = wh-question about speaker meaning. -/
def parameterIdentification (antecedent : UttSkeleton) (paramIdx : String) :
    Option CoercionOutput :=
  match antecedent.constitForParam paramIdx with
  | none => none
  | some constit => some {
    op := .paramIdentification
    salUtt := constit
    maxQud := s!"?c.spkr-meaning-rel(addr,{constit.phon},c)"
  }

/-- Contextual existential generalization (@cite{ginzburg-cooper-2004} ex. 77):
ground without clarifying.

Removes a parameter from C-PARAMS by existentially quantifying it. -/
def existentialGeneralization (sk : UttSkeleton) (paramIdx : String) : UttSkeleton :=
  { sk with
    cparams := sk.cparams.filter (·.index != paramIdx)
    cont := s!"∃{paramIdx}.{sk.cont}" }

-- ════════════════════════════════════════════════════
-- § 10. IS: 2004-era Information State (@cite{ginzburg-cooper-2004})
-- ════════════════════════════════════════════════════

/-- Information State for the @cite{ginzburg-cooper-2004} model.

Bundles a DGB with CE processing state (pending utterances). Uses `String`
for both Fact and QContent, matching the string-based representations in
the 2004 paper. The `Participant` type parameter is set to `String`.

This is NOT the @cite{ginzburg-2012} TIS — it predates the genre/agenda
private state. It exists to support the CE running example. -/
structure IS (Fact QContent : Type) where
  dgb : DGB String Fact QContent := {}
  /-- Utterances awaiting full C-PARAMS resolution -/
  pending : List SignAssignment := []
  ce : CEState QContent := {}

/-- An empty IS. -/
def IS.initial {Fact QContent : Type} : IS Fact QContent := {}

/-- Integrate an utterance into the IS.

If the assignment fully resolves all C-PARAMS, the utterance is grounded:
its content goes to FACTS. Otherwise, it goes to PENDING.
@cite{ginzburg-cooper-2004} §6, ex. 82. -/
def IS.integrateUtterance {Fact QContent : Type} [BEq Fact]
    (is_ : IS Fact QContent) (skel : UttSkeleton) (assign : CtxtAssignment)
    (toFact : String → Fact) : IS Fact QContent :=
  if assign.resolvesAll skel.cparams then
    { is_ with dgb := { is_.dgb with facts := is_.dgb.facts ++ [toFact skel.cont] } }
  else
    { is_ with pending := is_.pending ++ [{ sign := skel, assignment := assign }] }

/-- String-specialized integration (content IS the fact). -/
def IS.integrateUtteranceStr (is_ : IS String String)
    (skel : UttSkeleton) (assign : CtxtAssignment) : IS String String :=
  is_.integrateUtterance skel assign id

/-- Apply a coercion output to the IS: set MAX-QUD and SAL-UTT. -/
def IS.applyCoercion {Fact QContent : Type}
    (is_ : IS Fact QContent) (co : CoercionOutput)
    (toQ : String → QContent) : IS Fact QContent :=
  { is_ with ce := { is_.ce with maxQud := some (toQ co.maxQud), salUtt := some co.salUtt } }

/-- String-specialized coercion application. -/
def IS.applyCoercionStr (is_ : IS String String) (co : CoercionOutput) : IS String String :=
  is_.applyCoercion co id

-- ════════════════════════════════════════════════════════════
-- Part III: Structural Theorems
-- ════════════════════════════════════════════════════════════

-- ════════════════════════════════════════════════════
-- § 11. DGB Properties
-- ════════════════════════════════════════════════════

/-- An empty DGB has no moves. -/
theorem DGB.initial_no_moves {Participant Fact QContent : Type} :
    (DGB.initial : DGB Participant Fact QContent).moves = [] := rfl

/-- An empty DGB has empty QUD. -/
theorem DGB.initial_no_qud {Participant Fact QContent : Type} :
    (DGB.initial : DGB Participant Fact QContent).qud = [] := rfl

/-- An empty DGB has no latest move. -/
theorem DGB.initial_no_latestMove {Participant Fact QContent : Type} :
    (DGB.initial : DGB Participant Fact QContent).latestMove = none := rfl

-- ════════════════════════════════════════════════════
-- § 12. CE Theorems (@cite{ginzburg-cooper-2004})
-- ════════════════════════════════════════════════════

/-- Both coercion operations target the same SAL-UTT. -/
theorem coercions_same_salUtt (ant : UttSkeleton) (idx : String) :
    (parameterFocussing ant idx).map CoercionOutput.salUtt =
    (parameterIdentification ant idx).map CoercionOutput.salUtt := by
  unfold parameterFocussing parameterIdentification
  cases ant.constitForParam idx <;> rfl

/-- The two coercion operations produce different operation types. -/
theorem coercions_different_op (ant : UttSkeleton) (idx : String)
    (r1 r2 : CoercionOutput)
    (h1 : parameterFocussing ant idx = some r1)
    (h2 : parameterIdentification ant idx = some r2) :
    r1.op ≠ r2.op := by
  unfold parameterFocussing at h1; unfold parameterIdentification at h2
  cases h : ant.constitForParam idx with
  | none => rw [h] at h1; simp at h1
  | some _ =>
    rw [h] at h1 h2; simp only [Option.some.injEq] at h1 h2
    subst h1; subst h2; exact CoercionOp.noConfusion

/-- A fully resolved assignment leaves no unresolved parameters. -/
theorem resolved_means_no_unresolved (f : CtxtAssignment) (ps : CParamSet)
    (h : f.resolvesAll ps = true) :
    f.unresolved ps = [] := by
  unfold CtxtAssignment.unresolved CtxtAssignment.resolvesAll at *
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.filter_cons, h.1]
    exact ih h.2

/-- Existential generalization never increases the parameter count. -/
theorem existential_gen_weakens (sk : UttSkeleton) (idx : String) :
    (existentialGeneralization sk idx).cparams.length ≤ sk.cparams.length := by
  simp [existentialGeneralization]
  exact List.length_filter_le _ _

-- ════════════════════════════════════════════════════
-- § 13. HasContextSet Bridge
-- ════════════════════════════════════════════════════

open Core.CommonGround in
open Core.Proposition (BProp) in
/-- DGB with `BProp W` facts projects to a context set.
    @cite{ginzburg-2012} Ch. 4: the DGB's FACTS field IS the common ground. -/
instance {W Participant QContent : Type} :
    HasContextSet (DGB Participant (BProp W) QContent) W where
  toContextSet dgb := λ w => dgb.facts.all (· w)

open Core.CommonGround in
open Core.Proposition (BProp) in
/-- TIS with `BProp W` facts inherits the DGB's context set. -/
instance {W Participant QContent : Type} :
    HasContextSet (TIS Participant (BProp W) QContent) W where
  toContextSet tis := λ w => tis.dgb.facts.all (· w)

open Core.CommonGround in
open Core.Proposition (BProp) in
/-- TIS context set is extracted from the DGB. -/
theorem tis_contextSet_eq_dgb {W Participant QContent : Type}
    (tis : TIS Participant (BProp W) QContent) :
    HasContextSet.toContextSet tis = HasContextSet.toContextSet tis.dgb := rfl

-- ════════════════════════════════════════════════════
-- § 14. DGB Content Mapping
-- ════════════════════════════════════════════════════

/-- Map over a DGB's fact type, preserving structure. -/
def DGB.mapFacts {Participant Fact Fact' QContent : Type} (f : Fact → Fact')
    (dgb : DGB Participant Fact QContent) : DGB Participant Fact' QContent where
  spkr := dgb.spkr
  addr := dgb.addr
  facts := dgb.facts.map f
  moves := []  -- moves are not mapped (content types change)
  pending := dgb.pending
  qud := dgb.qud

/-- Map over a DGB's question type, preserving structure. -/
def DGB.mapQud {Participant Fact QContent QContent' : Type} (f : QContent → QContent')
    (dgb : DGB Participant Fact QContent) : DGB Participant Fact QContent' where
  spkr := dgb.spkr
  addr := dgb.addr
  facts := dgb.facts
  moves := []  -- moves are not mapped (content types change)
  pending := dgb.pending
  qud := dgb.qud.map f

/-- Mapping facts preserves fact count. -/
theorem DGB.mapFacts_length {Participant Fact Fact' QContent : Type} (f : Fact → Fact')
    (dgb : DGB Participant Fact QContent) :
    (dgb.mapFacts f).facts.length = dgb.facts.length := by
  simp only [DGB.mapFacts, List.length_map]

-- ════════════════════════════════════════════════════
-- § 15. Locutionary Propositions (@cite{ginzburg-2012} Ch. 6)
-- ════════════════════════════════════════════════════

/-- A locutionary proposition: a speech event with both form and content.

@cite{ginzburg-2012} Ch. 6, Appendix A (ex. 8d): LocProp replaces IllocProp
in MOVES and Pending. A LocProp records the phonological form, syntactic
category, and contextual parameters of the utterance — not just its
illocutionary content. This is crucial for CRification: clarification
requests target the *form* of the utterance, not just its content.

Parameterized over the content type `Cont` for grammar-neutrality.
When `Cont = String`, this subsumes both `PendingLoc` and `UttSkeleton`. -/
structure LocProp (Cont : Type) where
  /-- Phonological form of the utterance -/
  phon : String
  /-- Syntactic category -/
  cat : String
  /-- Semantic content -/
  cont : Cont
  /-- Contextual parameters: unresolved dependencies.
      Empty = fully grounded; non-empty = CRification may be needed. -/
  cparams : CParamSet := []
  /-- Sub-constituents accessible for clarification.
      @cite{ginzburg-2012} Ch. 6: any sub-utterance can be targeted by a CR. -/
  constits : List SubUtterance := []
  deriving Repr

/-- Convert a `PendingLoc` to a string-content `LocProp`. -/
def PendingLoc.toLocProp (pl : PendingLoc) : LocProp String where
  phon := pl.utt
  cat := pl.uttType
  cont := pl.utt

/-- Convert a `LocProp String` to a `PendingLoc`. -/
def LocProp.toPendingLoc (lp : LocProp String) : PendingLoc where
  utt := lp.phon
  uttType := lp.cat

/-- Convert an `UttSkeleton` to a string-content `LocProp`.
    Subsumes the @cite{ginzburg-cooper-2004} skeleton representation. -/
def UttSkeleton.toLocProp (sk : UttSkeleton) : LocProp String where
  phon := sk.phon
  cat := sk.cat
  cont := sk.cont
  cparams := sk.cparams
  constits := sk.constits

/-- Convert a `LocProp String` back to an `UttSkeleton`. -/
def LocProp.toSkeleton (lp : LocProp String) : UttSkeleton where
  phon := lp.phon
  cat := lp.cat
  cont := lp.cont
  cparams := lp.cparams
  constits := lp.constits

/-- Round-trip: UttSkeleton → LocProp → UttSkeleton is identity. -/
theorem skeleton_locprop_roundtrip (sk : UttSkeleton) :
    sk.toLocProp.toSkeleton = sk := rfl

-- ════════════════════════════════════════════════════
-- § 16. InfoStruc (@cite{ginzburg-2012} Ch. 7, Appendix B)
-- ════════════════════════════════════════════════════

/-- An information structure: a question paired with its focus-establishing
constituents (FECs).

@cite{ginzburg-2012} Ch. 7, Appendix B (ex. 2): QUD entries are not bare
questions but InfoStructs. The FEC records which sub-utterance(s)
established the question — this is what enables NSU resolution.

Example: "Who left?" pushes an InfoStruc with:
- q = "who left?"
- fec = [the LocProp for "who"]
A subsequent fragment "Bo" resolves the question by filling the FEC slot. -/
structure InfoStruc (QContent Cont : Type) where
  /-- The question under discussion -/
  q : QContent
  /-- Focus-establishing constituents from the utterance that introduced q -/
  fec : List (LocProp Cont) := []
  deriving Repr

/-- Create an InfoStruc from a bare question (no FECs). -/
def InfoStruc.fromQuestion {QContent Cont : Type} (q : QContent) :
    InfoStruc QContent Cont where
  q := q

/-- Create an InfoStruc from a question and a wh-word sub-utterance. -/
def InfoStruc.withFEC {QContent Cont : Type}
    (q : QContent) (fec : LocProp Cont) : InfoStruc QContent Cont where
  q := q
  fec := [fec]

end Pragmatics.Dialogue.KOS
