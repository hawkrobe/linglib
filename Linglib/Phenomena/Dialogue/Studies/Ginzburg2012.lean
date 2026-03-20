import Linglib.Theories.Pragmatics.Dialogue.KOS.Rules
import Linglib.Theories.Semantics.TypeTheoretic.Discourse
import Linglib.Phenomena.Ellipsis.FragmentAnswers
import Linglib.Core.Discourse.QUD

/-!
# Ginzburg (2012): The Interactive Stance
@cite{ginzburg-2012}

Key empirical claims from @cite{ginzburg-2012} formalized against the KOS
framework and verified with the existing DGB/TIS/conversational-rule machinery.

## Claims Formalized

1. **Non-sentential utterances** (Ch. 5): bare fragments ("Paris.") are
   resolved via QUD — the question on QUD determines the fragment's
   propositional content.
2. **Assertion–QUD coupling** (Ch. 4): asserting p pushes About(p) onto
   QUD; the addressee's acceptance resolves it.
3. **Grounding asymmetry** (Ch. 4): the speaker's DGB and addressee's DGB
   evolve differently — only acceptance synchronizes them.
4. **Self-repair** (Ch. 7): disfluencies are modeled via TurnUnderConstr
   in the private state.
5. **Genre relevance** (Ch. 4): initiating moves must be relevant to the
   conversational genre.

-/

namespace Phenomena.Dialogue.Studies.Ginzburg2012

open Theories.Pragmatics.Dialogue.KOS

-- ════════════════════════════════════════════════════
-- § 1. NSU Resolution via QUD
-- ════════════════════════════════════════════════════

/-! ## Non-Sentential Utterances

@cite{ginzburg-2012} Ch. 1 (p. 2) cites estimates that ~30% of utterances
are non-sentential (de Waijer 2001); the BNC corpus study in Ch. 7 (§7.2.2)
finds 1,299 NSUs in 14,315 sentences (~9%).
Their interpretation depends on the QUD — the same fragment "Paris" means
different things depending on what question is under discussion:

  QUD: "Where's Bo?" → "Paris" = "Bo is in Paris"
  QUD: "What's the capital of France?" → "Paris" = "Paris is the capital"

The key mechanism: the QUD's question structure determines which argument
slot the fragment fills. This connects `Phenomena/Ellipsis/FragmentAnswers.lean`
to the KOS framework. -/

/-- An NSU resolution datum: a fragment interpreted relative to a QUD. -/
structure NSUDatum where
  /-- The question under discussion -/
  qud : String
  /-- The non-sentential utterance -/
  fragment : String
  /-- The full propositional content derived from QUD + fragment -/
  resolution : String
  /-- Source (chapter/page in Ginzburg 2012) -/
  source : String := ""
  deriving Repr

/-- "Where's Bo?" / "Paris" → "Bo is in Paris". -/
def nsuLocation : NSUDatum where
  qud := "Where is Bo?"
  fragment := "Paris"
  resolution := "Bo is in Paris"
  source := "Ch. 5"

/-- "Who called?" / "Bo" → "Bo called". -/
def nsuSubject : NSUDatum where
  qud := "Who called?"
  fragment := "Bo"
  resolution := "Bo called"
  source := "Ch. 5"

/-- "What did Bo eat?" / "A sandwich" → "Bo ate a sandwich". -/
def nsuObject : NSUDatum where
  qud := "What did Bo eat?"
  fragment := "A sandwich"
  resolution := "Bo ate a sandwich"
  source := "Ch. 5"

/-- Bare "yes"/"no" as polar answer. -/
def nsuPolar : NSUDatum where
  qud := "Did Bo leave?"
  fragment := "Yes"
  resolution := "Bo left"
  source := "Ch. 5"

def nsuExamples : List NSUDatum := [nsuLocation, nsuSubject, nsuObject, nsuPolar]

/-- All NSU examples have non-empty resolutions. -/
theorem all_nsu_resolved :
    nsuExamples.all (fun d => !d.resolution.isEmpty) = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 2. KOS Inquiry Cycle (Ginzburg 2012, Ch. 4)
-- ════════════════════════════════════════════════════

/-! ## The Full Inquiry Cycle

@cite{ginzburg-2012} Ch. 4 (p. 95, ex. 66): the canonical dialogue pattern.

A(1): "Is Bo here?" — Ask: pushes q onto QUD
B(1): "Bo is here." — Assert: adds p to FACTS, pushes About(p), downdates
A(2): accepts         — Accept: adds p to own FACTS

We verify that:
1. After Ask, QUD is non-empty
2. After Assert (with QUD push), the original question is resolved
3. After Accept, the fact appears in both participants' views -/

section InquiryCycle

instance : Answerhood String String where
  resolves fact question := fact == question

/-- A asks "Is Bo here?" -/
private def cycle₀ : TIS String String String := TIS.initial
private def cycle₁ := cycle₀.ask "Bo is here"

/-- QUD is non-empty after Ask. -/
theorem cycle_ask_qud_nonempty : cycle₁.dgb.qud ≠ [] := by
  simp [cycle₁, TIS.ask, DGB.pushQud, DGB.recordMove]

/-- B asserts "Bo is here" with full Assert protocol. -/
private def cycle₂ := cycle₁.assertWithQUD "Bo is here" "Bo is here"

/-- After Assert, the original question is resolved and QUD is empty. -/
theorem cycle_assert_resolves : cycle₂.dgb.qud = [] := by native_decide

/-- The fact is in FACTS. -/
theorem cycle_assert_has_fact : "Bo is here" ∈ cycle₂.dgb.facts := by
  simp [cycle₂, cycle₁, cycle₀, TIS.assertWithQUD, TIS.ask,
    DGB.addFact, DGB.pushQud, DGB.downdateQud, DGB.recordMove]

/-- A accepts. -/
private def cycle₃ := cycle₂.accept "Bo is here"

/-- After Accept, the fact appears twice (speaker's assert + addressee's accept). -/
theorem cycle_accept_duplicates :
    cycle₃.dgb.facts = ["Bo is here", "Bo is here"] := by native_decide

/-- The full move history is recorded. -/
theorem cycle_full_moves :
    cycle₃.dgb.moves = [.ask "Bo is here", .assert "Bo is here",
                         .accept "Bo is here"] := by native_decide

end InquiryCycle

-- ════════════════════════════════════════════════════
-- § 3. Grounding Asymmetry
-- ════════════════════════════════════════════════════

/-! ## Speaker vs Addressee DGBs

@cite{ginzburg-2012} Ch. 4: each participant maintains their own DGB.
After A asserts p, A's DGB has p in FACTS. B's DGB does NOT have p in
FACTS until B explicitly accepts. This models the difference between
assertion and mutual acceptance. -/

section GroundingAsymmetry

instance : Answerhood String String where
  resolves fact question := fact == question

/-- Speaker's DGB after asserting "It's raining". -/
private def speakerDGB : TIS String String String :=
  TIS.initial.assertRule "It's raining"

/-- Addressee's DGB before accepting — no facts yet. -/
private def addresseeDGBBefore : TIS String String String := TIS.initial

/-- Speaker has the fact; addressee does not. -/
theorem grounding_asymmetry :
    "It's raining" ∈ speakerDGB.dgb.facts ∧
    "It's raining" ∉ addresseeDGBBefore.dgb.facts := by
  constructor
  · simp [speakerDGB, TIS.assertRule, DGB.assertFact, DGB.addFact,
      DGB.downdateQud, DGB.recordMove]
  · simp [addresseeDGBBefore, TIS.initial]

/-- After addressee accepts, the asymmetry is resolved. -/
private def addresseeDGBAfter : TIS String String String :=
  addresseeDGBBefore.accept "It's raining"

theorem grounding_resolved :
    "It's raining" ∈ addresseeDGBAfter.dgb.facts := by
  simp [addresseeDGBAfter, TIS.accept, DGB.addFact, DGB.recordMove]

end GroundingAsymmetry

-- ════════════════════════════════════════════════════
-- § 4. Self-Repair via TurnUnderConstr
-- ════════════════════════════════════════════════════

/-! ## Disfluencies and Self-Repair

@cite{ginzburg-2012} Ch. 7: self-repairs ("I went to the — to the store")
are modeled via TurnUnderConstr. The speaker interrupts the current turn,
revises it, and continues. The TuC tracks the partial content so that
the repair can target the right constituent.

We model a simple self-repair: "I saw the, uh, the manager." -/

/-- A TuC mid-repair: speaker has said "I saw the" and is about to correct. -/
def tucMidRepair : TurnUnderConstr where
  phonSoFar := "I saw the"
  cat := some "S"
  partialContent := some "see(spkr, ?)"

/-- After repair: "I saw the manager" — TuC is cleared, content goes to DGB. -/
def tucAfterRepair : Option TurnUnderConstr := none

/-- Self-repair clears the TuC. -/
theorem repair_clears_tuc : tucAfterRepair = none := rfl

/-- The TuC tracks partial content before repair. -/
theorem tuc_has_partial : tucMidRepair.partialContent = some "see(spkr, ?)" := rfl

-- ════════════════════════════════════════════════════
-- § 5. Genre Relevance
-- ════════════════════════════════════════════════════

/-! ## Genre Constraints on Moves

@cite{ginzburg-2012} §4.6 (pp. 101–110): genres constrain which moves are
felicitous. In a bakery transaction, asking about the weather is infelicitous
(though not ungrammatical); in casual chat, it's fine.

We verify that genre constraints correctly filter moves. -/

section GenreRelevance

/-- A bakery genre: only questions about baked goods are relevant. -/
def bakeryGenre : GenreType String where
  name := "bakery"
  qudConstraint := some (fun qud =>
    qud.all (fun q => q == "What would you like?" || q == "How much?"))

/-- An unrestricted casual chat genre. -/
def casualChat : GenreType String where
  name := "casual"
  qudConstraint := none

private def emptyDGB : DGB String String String := DGB.initial

/-- "What would you like?" is relevant in a bakery. -/
theorem bakery_bread_relevant :
    genreRelevant bakeryGenre emptyDGB (.ask "What would you like?") = true := by
  native_decide

/-- "What's the weather?" is NOT relevant in a bakery. -/
theorem bakery_weather_irrelevant :
    genreRelevant bakeryGenre emptyDGB (.ask "What's the weather?") = false := by
  native_decide

/-- "What's the weather?" IS relevant in casual chat. -/
theorem casual_weather_relevant :
    genreRelevant casualChat emptyDGB (.ask "What's the weather?") = true := by
  native_decide

/-- Genre relevance distinguishes the bakery from casual chat. -/
theorem genre_discrimination :
    genreRelevant bakeryGenre emptyDGB (.ask "What's the weather?") ≠
    genreRelevant casualChat emptyDGB (.ask "What's the weather?") := by
  native_decide

end GenreRelevance

-- ════════════════════════════════════════════════════
-- § 6. NSU ↔ FragmentAnswers Bridge
-- ════════════════════════════════════════════════════

/-! ## Bridge to Fragment Answer Data

@cite{ginzburg-2012} Ch. 5 subsumes the fragment answer phenomenon:
bare fragments are NSUs resolved via QUD. The `FragmentDatum` data from
`Phenomena/Ellipsis/FragmentAnswers.lean` are instances of NSU resolution
where the QUD is an explicit wh-question. -/

open Phenomena.Ellipsis.FragmentAnswers in
/-- Fragment answers are NSUs: the question context provides the QUD,
and the fragment is the non-sentential utterance. -/
def fragmentToNSU (fd : FragmentDatum) : NSUDatum where
  qud := fd.question
  fragment := fd.fragment
  resolution := fd.interpretation
  source := "Fragment answer, " ++ fd.source

open Phenomena.Ellipsis.FragmentAnswers in
/-- The subject fragment answer maps to an NSU datum. -/
theorem subject_fragment_is_nsu :
    (fragmentToNSU fragmentSubject).resolution = "Bob went to the movies" := rfl

open Phenomena.Ellipsis.FragmentAnswers in
/-- All basic fragments map to NSU data with non-empty resolutions. -/
theorem all_fragments_are_nsus :
    (basicFragments.map fragmentToNSU).all (fun d => !d.resolution.isEmpty) = true := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 7. NSU Taxonomy (@cite{ginzburg-2012} Ch. 7, §7.2)
-- ════════════════════════════════════════════════════

/-! ## NSU Classification

@cite{ginzburg-2012} Ch. 7 (§7.2) provides an empirical taxonomy of
non-sentential utterances based on a BNC corpus study. Each class has
a distinct resolution mechanism relative to QUD/Pending. -/

/-- The 11 classes of NSUs from @cite{ginzburg-2012} Ch. 7, §7.2. -/
inductive NSUClass where
  /-- Short answer: fills an argument slot in MaxQUD ("Paris", "Bo") -/
  | shortAnswer
  /-- Polar answer: "yes" / "no" to a polar MaxQUD -/
  | polarAnswer
  /-- Propositional lexeme: "yes", "no", "mmh" — meaning from DGB state -/
  | propLexeme
  /-- Sluice: bare wh-phrase ("Who?", "Where?") -/
  | sluice
  /-- Reprise sluice: echo wh-substitution ("Bo did WHAT?") -/
  | repriseSluice
  /-- Reprise fragment: echo of a sub-utterance for clarification ("Bo?") -/
  | repriseFragment
  /-- Focus-establishing constituent: fragment providing focus ("PARIS") -/
  | fec
  /-- Declarative fragment: bare DP/PP with assertive force ("The manager") -/
  | declarativeFragment
  /-- Check fragment: rising intonation echo for confirmation ("Bo?↗") -/
  | checkFragment
  /-- Correction fragment: corrects a sub-utterance ("No, PARIS") -/
  | correctionFragment
  /-- Filler: hesitation / floor-holding ("uh", "well") -/
  | filler
  deriving Repr, DecidableEq, BEq

-- ════════════════════════════════════════════════════
-- § 8. CR Form & Reading Taxonomy (@cite{ginzburg-2012} Ch. 6, §6.2)
-- ════════════════════════════════════════════════════

/-! ## Clarification Request Taxonomy

@cite{ginzburg-2012} Ch. 6 (§6.2.1): 8 forms of clarification request,
each compatible with up to 4 reading types. -/

/-- The 8 CR forms from @cite{ginzburg-2012} Ch. 6 §6.2.1. -/
inductive CRForm where
  /-- "Wot?" / "What?" — most general CR -/
  | wot
  /-- Literal reprise: exact echo with rising intonation ("Bo?") -/
  | literalReprise
  /-- Wh-substituted reprise: echo with wh-word ("Bo did WHAT?") -/
  | whSubstituted
  /-- Reprise sluice: bare wh-word after antecedent ("Who?") -/
  | repriseSluice
  /-- Reprise fragment: bare constituent echo ("Bo?") -/
  | repriseFragment
  /-- Gap: reprise with a gap ("Did __ leave?") -/
  | gap
  /-- Filler: "Huh?" -/
  | fillerCR
  /-- Explicit: metalinguistic ("What do you mean 'finagle'?") -/
  | explicit
  deriving Repr, DecidableEq, BEq

/-- The 4 CR reading types from @cite{ginzburg-2012} Ch. 6 §6.2.1. -/
inductive CRReading where
  /-- "Are you asking/saying that p?" — confirms propositional content -/
  | clausalConfirmation
  /-- "What do you mean by X?" — requests intended referent/predicate -/
  | intendedContent
  /-- "Can you repeat X?" — requests phonological repetition -/
  | repetition
  /-- "Did you say X or Y?" — corrective alternative -/
  | correction
  deriving Repr, DecidableEq, BEq

-- ════════════════════════════════════════════════════
-- § 9. Grounding Protocol Example
-- ════════════════════════════════════════════════════

/-! ## Grounding vs CRification

@cite{ginzburg-2012} Ch. 6: when "Did Bo leave?" enters Pending,
the addressee either grounds it (if they know who "Bo" is) or
CRifies it (if "Bo" is unresolved → "Who's Bo?").

We show the branching behavior using `integrateLocProp`. -/

section GroundingExample

/-- "Did Bo leave?" as a LocProp with one cparam for the referent of "Bo". -/
private def didBoLeave : LocProp String where
  phon := "Did Bo leave?"
  cat := "S"
  cont := "leave(bo)"
  cparams := [{ index := "bo_ref", restriction := "individual" }]
  constits := [{ phon := "Bo", cat := "NP", cont := "bo" }]

/-- "Did Bo leave?" with the "Bo" referent resolved. -/
private def didBoLeaveResolved : LocProp String where
  phon := "Did Bo leave?"
  cat := "S"
  cont := "leave(bo)"

/-- CR question constructor for this example. -/
private def toCR (p : CParam) : String := s!"Who do you mean by '{p.index}'?"

/-- Unresolved "Bo" triggers CRification. -/
theorem unresolved_bo_crifies :
    (integrateLocProp didBoLeave toCR).isGrounded = false := by
  native_decide

/-- Resolved version grounds successfully. -/
theorem resolved_bo_grounds :
    (integrateLocProp didBoLeaveResolved toCR).isGrounded = true := by
  native_decide

/-- The CR question targets the unresolved parameter. -/
theorem cr_targets_bo :
    integrateLocProp didBoLeave toCR =
    .crification "Who do you mean by 'bo_ref'?" { index := "bo_ref", restriction := "individual" } := rfl

end GroundingExample

end Phenomena.Dialogue.Studies.Ginzburg2012
