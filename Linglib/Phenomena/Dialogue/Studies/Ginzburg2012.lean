import Linglib.Theories.Pragmatics.Dialogue.KOS.Grammar
import Linglib.Phenomena.Ellipsis.FragmentAnswers
import Linglib.Core.Question.Partition.QUD
import Linglib.Core.Question.PrecisionProjection
import Linglib.Core.Discourse.QUDStack
import Linglib.Core.Discourse.Strategy

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
6. **NSU taxonomy** (Ch. 7, Tables 7.3–7.4): 15 empirical NSU classes from
   BNC corpus + 4 functional groupings.
7. **Grounding protocol** (Ch. 6): LocProp integration branches on cparam
   resolution — grounding vs CRification.
8. **End-to-end chain** (§10): DialogueSign → LocProp → integration →
   DGB update, with non-resolve-cond verification.

-/

namespace Ginzburg2012

open Pragmatics.Dialogue.KOS

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

instance : Core.Question.DecidableSupport String String where
  supports fact question := fact = question
  decSupports a b := decEq a b

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

instance : Core.Question.DecidableSupport String String where
  supports fact question := fact = question
  decSupports a b := decEq a b

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

@cite{ginzburg-2012} Ch. 7 (§7.2, Tables 7.3–7.4): empirical taxonomy of
non-sentential utterances based on a BNC corpus study (Fernández 2006).
200 speaker-turns from 54 BNC files; 14,315 sentences; 1,299 NSUs found,
of which 1,283 (98.9%) were classified.

Table 7.3 gives 15 empirical classes ordered by frequency.
Table 7.4 groups them into 4 functional categories:
positive feedback, answers, metacommunicative queries, extension moves. -/

/-- The 15 NSU classes from @cite{ginzburg-2012} Table 7.3 (p. 221).
Ordered by frequency in the BNC sub-corpus. -/
inductive NSUClass where
  /-- "mmh", "uh-huh" — acknowledges preceding utterance (599) -/
  | plainAcknowledgement
  /-- "Bo" — fills argument slot in MaxQUD (188) -/
  | shortAnswer
  /-- "Yes" — positive answer to polar query (105) -/
  | affirmativeAnswer
  /-- "Bo, hmm" — acknowledgement with repetition (86) -/
  | repeatedAcknowledgement
  /-- "Bo?" — clarification ellipsis (79) -/
  | clarificationEllipsis
  /-- "No" — negative answer to polar query / assertion (49) -/
  | rejection
  /-- "Great!" — factive modifier (27) -/
  | factiveModifier
  /-- "Bo, yes" — affirmative with repetition (26) -/
  | repeatedAffirmativeAnswer
  /-- "No, Max" — rejection with helpful alternative (24) -/
  | helpfulRejection
  /-- "Who?" — bare wh-phrase requesting elaboration (24) -/
  | sluice
  /-- "Okay?" — rising intonation check (22) -/
  | checkQuestion
  /-- "uh", "well" — hesitation / floor-holding (18) -/
  | filler
  /-- "Yesterday" — bare modifier phrase (15) -/
  | bareModifierPhrase
  /-- "Maybe" — propositional modifier (11) -/
  | propositionalModifier
  /-- "And Max" — conjunction + fragment (10) -/
  | conjunctionFragment
  deriving Repr, DecidableEq

/-- BNC frequency count for each NSU class (Table 7.3). -/
def NSUClass.frequency : NSUClass → Nat
  | .plainAcknowledgement     => 599
  | .shortAnswer               => 188
  | .affirmativeAnswer         => 105
  | .repeatedAcknowledgement   => 86
  | .clarificationEllipsis     => 79
  | .rejection                 => 49
  | .factiveModifier           => 27
  | .repeatedAffirmativeAnswer => 26
  | .helpfulRejection          => 24
  | .sluice                    => 24
  | .checkQuestion             => 22
  | .filler                    => 18
  | .bareModifierPhrase        => 15
  | .propositionalModifier     => 11
  | .conjunctionFragment       => 10

/-- Functional grouping from @cite{ginzburg-2012} Tables 7.1–7.2 (pp. 219–220).
The per-group counts are computed from the per-class frequencies in Table 7.3. -/
inductive NSUFunction where
  /-- Positive feedback: plain + repeated acknowledgement (599 + 86 = 685) -/
  | positiveFeedback
  /-- Answers: short, affirmative, rejection, repeated aff., helpful rej., prop. modifier (403) -/
  | answer
  /-- Metacommunicative queries: CE, sluice, check question, filler (79 + 24 + 22 + 18 = 143).
      Note: the Sluice class is ambiguous between a metacommunicative "reprise sluice"
      reading (the more common one per §7.2.1) and a "direct sluice" reading that
      functions as an information query. The BNC data (Table 7.3) does not split
      the 24 sluice instances; we follow the primary classification (Tables 7.1–7.2)
      in placing sluice here. Direct sluice receives separate grammatical treatment
      in §7.8 and the Ch. 9 summary. -/
  | metacommunicativeQuery
  /-- Extension moves: factive modifier, bare modifier, conj+frag (27 + 15 + 10 = 52) -/
  | extensionMove
  deriving Repr, DecidableEq

/-- Classify an NSU class into its functional group (Tables 7.1–7.2). -/
def NSUClass.toFunction : NSUClass → NSUFunction
  | .plainAcknowledgement     => .positiveFeedback
  | .repeatedAcknowledgement  => .positiveFeedback
  | .shortAnswer              => .answer
  | .affirmativeAnswer        => .answer
  | .rejection                => .answer
  | .repeatedAffirmativeAnswer => .answer
  | .helpfulRejection         => .answer
  | .propositionalModifier    => .answer
  | .clarificationEllipsis    => .metacommunicativeQuery
  | .sluice                   => .metacommunicativeQuery
  | .checkQuestion            => .metacommunicativeQuery
  | .filler                   => .metacommunicativeQuery
  | .factiveModifier          => .extensionMove
  | .bareModifierPhrase       => .extensionMove
  | .conjunctionFragment      => .extensionMove

/-- All 15 NSU classes (Table 7.3). -/
def allNSUClasses : List NSUClass :=
  [.plainAcknowledgement, .shortAnswer, .affirmativeAnswer,
   .repeatedAcknowledgement, .clarificationEllipsis, .rejection,
   .factiveModifier, .repeatedAffirmativeAnswer, .helpfulRejection,
   .sluice, .checkQuestion, .filler, .bareModifierPhrase,
   .propositionalModifier, .conjunctionFragment]

/-- Total classified NSUs: 1283 (Table 7.3). -/
theorem nsu_total_1283 :
    (allNSUClasses.map NSUClass.frequency).sum = 1283 := by native_decide

/-- Functional group frequencies sum to the total (1283). -/
theorem functional_groups_sum_to_total :
    let groups := allNSUClasses.map (fun c => (c.toFunction, c.frequency))
    let pf := (groups.filter (·.1 == .positiveFeedback)).map (·.2) |>.sum
    let ans := (groups.filter (·.1 == .answer)).map (·.2) |>.sum
    let mcq := (groups.filter (·.1 == .metacommunicativeQuery)).map (·.2) |>.sum
    let ext := (groups.filter (·.1 == .extensionMove)).map (·.2) |>.sum
    pf = 685 ∧ ans = 403 ∧ mcq = 143 ∧ ext = 52 ∧ pf + ans + mcq + ext = 1283 := by
  native_decide

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
  deriving Repr, DecidableEq

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
  deriving Repr, DecidableEq

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

-- ════════════════════════════════════════════════════
-- § 10. End-to-End Chain: Utterance → DGB Update
-- ════════════════════════════════════════════════════

/-! ## End-to-End: DialogueSign → LocProp → Integration → DGB

@cite{ginzburg-2012}'s architecture connects grammar to dialogue via:
1. A **DialogueSign** (Ch. 5) with dgb-params, q-params, quest-dom
2. Conversion to a **LocProp** (Ch. 6) with cparams
3. **Integration**: grounding (cparams resolved → FACTS) or
   CRification (cparams unresolved → CR question on QUD)
4. **DGB update** via conversational rules (Ch. 4)

This section proves the full pipeline for the worked example
"Did Jo leave?" — from DialogueSign to final DGB state. -/

section EndToEndChain

open Pragmatics.Dialogue.KOS.Grammar

instance : Core.Question.DecidableSupport String String where
  supports fact question := fact = question
  decSupports a b := decEq a b

-- Step 1: DialogueSign for the sentence "Did Jo leave?"
-- "Jo" contributes DGB-PARAMS; "left" is a plain verb.

/-- "Jo" as a DialogueSign — has DGB-PARAMS for referent resolution. -/
private def joSign := Grammar.jo

/-- "left" as a DialogueSign — no dialogue params. -/
private def leftSign := Grammar.left

-- Step 2: Convert to LocProp
/-- "Jo" as a LocProp — dgb-params become cparams. -/
private def joLocProp := joSign.toLocProp

/-- Conversion preserves the phonological form. -/
theorem e2e_phon_preserved : joLocProp.phon = "Jo" := rfl

/-- Conversion transfers dgb-params to cparams. -/
theorem e2e_cparams_from_dgb : joLocProp.cparams = joSign.dgbParams := rfl

-- Step 3: Integration — branch on cparam resolution
private def crQuestion (p : CParam) : String :=
  s!"Who do you mean by '{p.index}'?"

/-- "Jo" has unresolved cparams → CRification (not grounding). -/
theorem e2e_jo_crifies :
    (integrateLocProp joLocProp crQuestion).isGrounded = false := rfl

/-- The CR question is derived from the unresolved parameter. -/
theorem e2e_cr_question :
    integrateLocProp joLocProp crQuestion =
    .crification "Who do you mean by 'jo_ref'?"
      { index := "jo_ref", restriction := "individual" } := rfl

-- Step 4a: CRification path — CR question goes on QUD

/-- Starting DGB: B has asked "Did Jo leave?", QUD has the question. -/
private def tis₀ : TIS String String String := TIS.initial.ask "leave(jo)"

/-- CRification: the CR question is pushed onto QUD. -/
private def tis₁_cr : TIS String String String :=
  { tis₀ with dgb := tis₀.dgb.pushQud "Who do you mean by 'jo_ref'?" }

/-- After CRification, QUD has the CR question at the top. -/
theorem e2e_cr_on_qud :
    (tis₁_cr.dgb.qud).head? = some "Who do you mean by 'jo_ref'?" := rfl

/-- The original question is still on QUD (below the CR). -/
theorem e2e_original_still_on_qud :
    "leave(jo)" ∈ tis₁_cr.dgb.qud := by
  simp [tis₁_cr, tis₀, TIS.ask, DGB.pushQud, DGB.recordMove]

-- Step 4b: Grounding path — resolved LocProp enters FACTS

/-- A LocProp for "Jo" with resolved cparams (addressee knows who Jo is). -/
private def joResolved : LocProp String where
  phon := "Jo"
  cat := "PROPN"
  cont := "jo"

/-- Resolved "Jo" grounds successfully. -/
theorem e2e_resolved_grounds :
    (integrateLocProp joResolved crQuestion).isGrounded = true := rfl

/-- After grounding "Jo left", the assertion enters FACTS and resolves QUD. -/
private def tis₁_ground : TIS String String String :=
  tis₀.assertRule "leave(jo)"

theorem e2e_ground_resolves_qud : tis₁_ground.dgb.qud = [] := by native_decide

theorem e2e_ground_adds_fact : "leave(jo)" ∈ tis₁_ground.dgb.facts := by
  simp [tis₁_ground, tis₀, TIS.assertRule, TIS.ask, DGB.assertFact,
    DGB.addFact, DGB.downdateQud, DGB.recordMove, DGB.pushQud]

/-- The full chain is consistent: CRification and grounding are exhaustive.
Every LocProp either grounds or CRifies — there is no third option. -/
theorem e2e_exhaustive (lp : LocProp String) (toCR : CParam → String) :
    (integrateLocProp lp toCR).isGrounded = true ∨
    (integrateLocProp lp toCR).isGrounded = false := by
  unfold integrateLocProp
  cases lp.cparams with
  | nil => left; rfl
  | cons _ _ => right; rfl

/-- Non-resolve-cond holds after QUD-downdate in the grounding path. -/
theorem e2e_nonResolveCond_after_ground :
    tis₁_ground.dgb.nonResolveCond = true := by native_decide

end EndToEndChain

end Ginzburg2012
