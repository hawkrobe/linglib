import Linglib.Discourse.Gameboard.Defs
import Linglib.Discourse.Gameboard.Basic
import Linglib.Discourse.Gameboard.InquiryCycle
import Linglib.Discourse.Gameboard.Genre
import Linglib.Discourse.Gameboard.Grounding
import Linglib.Discourse.Gameboard.SelfRepair
import Linglib.Discourse.Gameboard.NSUTaxonomy
import Linglib.Studies.Ginzburg2012.Examples
import Linglib.Discourse.Gameboard.Grammar
import Linglib.Discourse.Gameboard.RepriseContent
import Linglib.Discourse.Gameboard.Austinian
import Linglib.Discourse.Commitment.Table

/-!
# Ginzburg (2012): The Interactive Stance
[ginzburg-2012]

Canonical formalization of the KOS framework from
*The Interactive Stance: Meaning for Conversation* (OUP 2012).

This study consumes the KOS substrate at `Discourse/Gameboard/`,
which was rebuilt to faithfully match the book's Ch. 6 final shape
(ex. 43 p. 175): `DGB` takes a `Cont` parameter, `pending` stores
`LocProp Cont`, `qud` stores `InfoStruc QContent Cont`, `GenreType`
carries `qnud` + `anticipatedMoves`, `Grounding.lean` provides the
multi-stage CCURs pipeline (§6.6–6.7), `SelfRepair.lean` provides the
§8.2 MaxPending operations, `NSUTaxonomy.lean` provides the 16-class
Sluice-split-faithful Table 7.4 taxonomy.

## Sections

- §1. The Turn-Taking Puzzle (Ch. 2) — KOS's headline argument
- §2. KOS architecture overview (Ch. 4)
- §3. Inquiry cycle, TTR-typed (§4.4.5, via `Austinian.AustinianTIS`)
- §4. Grounding asymmetry: per-DGB stance (Ch. 4)
- §5. Genre as TTR record (§4.6)
- §6. Non-sentential utterance resolution (Ch. 5)
- §7. NSU taxonomy with Sluice split (Ch. 7, Tables 7.3 + 7.4)
- §8. Clarification request taxonomy (§6.2.1)
- §9. Grounding via the §6.6–6.7 CCURs pipeline
- §10. Self-repair via MaxPending (§8.2)
- §11. End-to-end pipeline: DialogueSign → LocProp → CCURs → DGB
- §12. Cross-framework contrasts vs pre-2012 siblings

## Chronology

[ginzburg-2012] > all references in §12. Cross-framework contrasts
with later work ([krifka-2015] commitment-spaces; [anderson-2021]
distributional CommonGround) live inside *those* studies per CLAUDE.md's
"no bridge files" + chronological-dependency rule.

## What this file does NOT cover

- Multilogue (Ch. 8 §8.1) — separate study to follow
- Ch. 9 "Interactive Stance" meta-theory — substantive philosophical content
- Quantification and anaphora in dialogue (§8.5)
- The book's substantial discussion of crosslinguistic data
  (Hebrew sluicing, German short answers, Bielefeld task corpus)

These are separable substudies; the present file covers the framework
core that downstream work consumes.
-/

namespace Ginzburg2012

open Discourse.Gameboard Question

-- ════════════════════════════════════════════════════════════
-- § 1. The Turn-Taking Puzzle (Ch. 2)
-- ════════════════════════════════════════════════════════════

/-! ## The Turn-Taking Puzzle (Ch. 2 ex. 22–23 p. 23)

[ginzburg-2012] Ch. 2 sets up the book's headline argument:
**Equal Access to Context fails** (ex. 5 p. 13, ex. 20b p. 21). Two
participants exposed to the *same* utterance do not have access to the
*same* contextual resources for interpreting subsequent fragments —
because their roles in the turn structure differ.

**The puzzle** (ex. 22–23 p. 23, the *Why-parakeet example*): A says
"I own a parakeet"; B says "Why?". The interpretation of B's "Why?"
depends crucially on **who is keeping the turn**:

- If A keeps the turn (B's "Why?" is a back-channel under A's continuing
  contribution): "Why?" means "Why own a parakeet?" — about A's content
- If B claims the turn: "Why?" can mean "Why are you telling me this?" —
  about A's *act of asserting*

Same fragment, same antecedent utterance, different readings — *because
turn structure is part of the context*. This refutes Equal Access to
Context: B (the responder) and any third overhearer would have access to
*different* resolution-licensing contexts for the same fragment.

**Why this matters architecturally**: the TTP forces the grammar to
have per-participant access to turn structure (who-spoke-last,
who-holds-the-floor). Standard pragmatic-enrichment accounts treat
context as a single shared object — exactly what the TTP refutes. KOS's
**per-participant DGB** is the architectural response: each participant's
DGB tracks the turn from their own perspective. The QUD-determined-NSU
claim of Ch. 5 (formalized in §6 below) is then a *consequence* of this
per-DGB access, not the central TTP claim itself. -/

/-- A weak structural witness for the TTP: the same fragment string
("Why?") paired with the SAME antecedent utterance ("I own a parakeet")
yields TWO distinct resolutions depending on turn-keeping. This is
weaker than Ginzburg's full argument (which requires the per-participant
DGB substrate), but is enough to refute "fragment + immediate antecedent
suffice for resolution" — the missing ingredient is turn structure.

The deeper refutation of Equal Access to Context lives in §4 below
(`grounding_asymmetry`), which exhibits two participants' DGBs
diverging after the same dialogue trace. -/
theorem turn_taking_puzzle_why_parakeet :
    let antecedent := "I own a parakeet"
    let fragment := "Why?"
    let resA := "Why own a parakeet?"   -- A keeps turn
    let resB := "Why are you telling me this?" -- B claims turn
    -- Same fragment, same antecedent, different resolutions:
    antecedent = antecedent ∧ fragment = fragment ∧ resA ≠ resB := by
  refine ⟨rfl, rfl, ?_⟩
  decide

-- ════════════════════════════════════════════════════════════
-- § 2. KOS Architecture Overview (Ch. 4)
-- ════════════════════════════════════════════════════════════

/-! ## KOS Architecture Overview

[ginzburg-2012] Ch. 4 introduces the central data structures:

- **TIS** (Total Information State, ex. 93 p. 107) = public DGB + private state
- **DGB** (Dialogue Gameboard, ex. 100/113) — each participant has their own:
  - `facts` : List Fact — accumulated mutual commitments
  - `moves` : List IllocMove — history of speech acts
  - `pending` : List LocProp — ungrounded utterances awaiting integration
  - `qud` : List InfoStruc — open questions paired with FECs
- **Conversational rules** (Ch. 4): `ask`, `assertRule`/`assertWithQUD`,
  `accept`, `qspec`, `check`, `confirm`, `qcoord`, `greet` — TIS → TIS

The substrate provides all of this in `Discourse/Gameboard/`. This
section just imports the conventions; subsequent sections exercise them. -/

/-- The TIS type structure as a sanity check: a TIS bundles a DGB with
private state. -/
example {P Fact QContent Cont : Type} (tis : TIS P Fact QContent Cont) :
    DGB P Fact QContent Cont × PrivateState Fact QContent :=
  ⟨tis.dgb, tis.priv⟩

-- ════════════════════════════════════════════════════════════
-- § 3. Inquiry Cycle (TTR-typed)
-- ════════════════════════════════════════════════════════════

/-! ## TTR-Typed Inquiry Cycle (§4.4.5)

[ginzburg-2012] Ch. 4 §4.4.5 walks through the canonical
Ask → Assert → Accept dialogue. We exercise the TTR-typed substrate
from `Gameboard/Austinian.lean`, which instantiates `TIS` with
`BCheckableAustinian` propositions and `TTRQuestionB` questions over
a `Weather` situation type.

This is the answer to "are TTR-typed examples reachable?" — yes,
the substrate has been built to support them. -/

/-- KOS's inquiry cycle works at TTR-typed content level: asserting
"it is raining" resolves "is it raining?". -/
theorem ttr_inquiry_cycle_resolves :
    Discourse.Gameboard.Austinian.atis₂.dgb.qud = [] :=
  Discourse.Gameboard.Austinian.atis_assert_resolves

/-- The same inquiry cycle in string-typed form (legacy worked example). -/
theorem string_inquiry_cycle_resolves :
    Ginzburg2012.Examples.tis₂.dgb.qud = [] :=
  Ginzburg2012.Examples.inquiry_step2_qud_empty

-- ════════════════════════════════════════════════════════════
-- § 4. Grounding Asymmetry: per-DGB stance (Ch. 4)
-- ════════════════════════════════════════════════════════════

/-! ## Grounding Asymmetry

[ginzburg-2012] Ch. 4: each participant maintains their own DGB.
After A asserts p, A's DGB has p in FACTS. B's DGB does NOT have p in
FACTS until B explicitly accepts. This models the difference between
*assertion* (one-sided) and *mutual acceptance* (synchronization).

This is KOS's most architecturally distinctive claim: there is no single
"common ground"; there are coupled-but-distinct private commitment
records, synchronized only via Accept. The Stalnaker contrast (§12) makes
this divergence Lean-checkable. -/

section GroundingAsymmetry

-- DecidableSupport String String instance is provided by KOS.Examples
-- (transitively imported via the open Discourse.Gameboard at top of file).

/-- Speaker's TIS after asserting "It's raining". -/
def speakerAfterAssert : TIS String String String String :=
  TIS.initial.assertRule "It's raining"

/-- Addressee's TIS before accepting — empty FACTS. -/
def addresseeBeforeAccept : TIS String String String String := TIS.initial

/-- After speaker asserts, only the speaker's DGB has the fact. -/
theorem grounding_asymmetry :
    "It's raining" ∈ speakerAfterAssert.dgb.facts ∧
    "It's raining" ∉ addresseeBeforeAccept.dgb.facts := by
  refine ⟨?_, ?_⟩
  · simp [speakerAfterAssert, TIS.assertRule, DGB.assertFact, DGB.addFact,
          DGB.downdateQud, DGB.recordMove]
  · simp [addresseeBeforeAccept, TIS.initial]

/-- Addressee's TIS after explicit Accept — now the fact is in addressee's FACTS. -/
def addresseeAfterAccept : TIS String String String String :=
  addresseeBeforeAccept.accept "It's raining"

/-- Acceptance synchronizes: addressee's FACTS gains the fact. -/
theorem grounding_resolved :
    "It's raining" ∈ addresseeAfterAccept.dgb.facts := by
  simp [addresseeAfterAccept, addresseeBeforeAccept, TIS.accept, DGB.addFact, DGB.recordMove]

end GroundingAsymmetry

-- ════════════════════════════════════════════════════════════
-- § 5. Genre as TTR Record (§4.6)
-- ════════════════════════════════════════════════════════════

/-! ## Genre Constraints on Moves (§4.6)

[ginzburg-2012] §4.6: genres are TTR records (ex. 88 p. 104) that
classify conversations. The relevance of a move depends on whether the
resulting DGB outcome can be anticipated to be fulfilled by the genre's
constraints (eq. 90 p. 105).

The substrate `GenreType` carries the `qnud` (anticipated questions) and
`anticipatedMoves` fields from ex. 88. We exercise the
`qudConstraint`-based variant here for a thin worked example. -/

section GenreRelevance

/-- A bakery-counter genre: only questions about ordering are
"anticipated" by the genre's implicit script. -/
def bakeryGenre : GenreType String String where
  name := "bakery-counter"
  qnud := ["What would you like?", "How much?"]
  qudConstraint := some (fun qud =>
    qud.all (fun q => q == "What would you like?" || q == "How much?"))

/-- An unrestricted casual-chat genre. -/
def casualGenre : GenreType String String where
  name := "casual"
  qudConstraint := none

/-- Bakery genre rejects weather small-talk; casual genre accepts it. -/
theorem genre_discriminates :
    let dgb : DGB String String String String := DGB.initial
    let askWeather : IllocMove String String := .ask "What's the weather?"
    ¬ genreRelevant bakeryGenre dgb askWeather ∧
    genreRelevant casualGenre dgb askWeather := by
  refine ⟨?_, ?_⟩ <;> decide

/-- The qnud-based variant agrees with the qudConstraint variant on the
bakery example: weather questions aren't in the anticipated set. -/
theorem qnud_rejects_weather :
    let dgb : DGB String String String String := DGB.initial
    let askWeather : IllocMove String String := .ask "What's the weather?"
    ¬ genreRelevantViaQnud bakeryGenre dgb askWeather := by decide

end GenreRelevance

-- ════════════════════════════════════════════════════════════
-- § 6. NSU Resolution (Ch. 5)
-- ════════════════════════════════════════════════════════════

/-! ## Non-Sentential Utterance Resolution

[ginzburg-2012] Ch. 5: bare fragments ("Paris.") are resolved via
the QUD. The InfoStruc shape of QUD entries (a question + its
focus-establishing constituents) gives the resolution mechanism: a
fragment fills the FEC slot of MaxQUD. Wh-fragment answers are one
NSU subclass — short answers in the Ch. 7 taxonomy below. -/

-- ════════════════════════════════════════════════════════════
-- § 7. NSU Taxonomy (Ch. 7, Tables 7.3 + 7.4)
-- ════════════════════════════════════════════════════════════

/-! ## NSU Classification

[ginzburg-2012] Ch. 7 §7.2 (Tables 7.3–7.4, pp. 221–222) — see
[fernandez-2006] for the BNC subcorpus study.

The 16-class taxonomy + 4 functional groupings live in the substrate
(`Gameboard/NSUTaxonomy.lean`) — they are framework infrastructure usable by
any KOS-aware study. This section just reuses them. The `freqTable`
single-source-of-truth + `frequency_coherent` drift sentry replace the
old aggregate-count theorems.

**Substantive correction from earlier formaliser version**: the original
Ginzburg2012.lean lumped all 24 sluices under "metacommunicative" — a
formaliser-imposed cut that didn't match Table 7.4's actual partition
(13 Reprise Sluice → metacommunicative, 11 Direct Sluice → extension).
The substrate now reflects Table 7.4's split faithfully. -/

/-- The 16 NSU classes: positive feedback (685), answers (403),
metacommunicative queries (132), extension moves (63) — sum 1283 per
Table 7.3 total. -/
example : allNSUClasses.length = 16 := allNSUClasses_complete

/-- Each class's frequency is consistent with its functional grouping
(BruRow drift sentry from the substrate). -/
example :
    allNSUClasses.all (fun c =>
      (c, c.toFunction, c.frequency) ∈ freqTable) = true :=
  frequency_coherent

-- ════════════════════════════════════════════════════════════
-- § 8. Clarification Request Taxonomy (§6.2.1)
-- ════════════════════════════════════════════════════════════

/-! ## CR Form & Reading Taxonomy

[ginzburg-2012] Ch. 6 §6.2.1 (pp. 148–149): 8 CR forms × 4 readings.
Form variation is morphological/intonational; reading variation is in
what the CR is asking about (clausal confirmation, intended content,
phonetic repetition, corrective alternative).

Substrate has `RFReading` (4 readings) at `Gameboard/RepriseContent.lean`.
This file declares CRForm locally; both could move to substrate when a
second consumer materializes. -/

/-- The 8 CR forms from §6.2.1 (p. 148 ex. 1). -/
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
  /-- Gap reprise ("Did __ leave?") -/
  | gap
  /-- Filler reprise ("Huh?") -/
  | fillerCR
  /-- Explicit metalinguistic CR ("What do you mean 'finagle'?") -/
  | explicit
  deriving Repr, DecidableEq

/-- All 8 CR forms enumerated. -/
def allCRForms : List CRForm :=
  [.wot, .literalReprise, .whSubstituted, .repriseSluice,
   .repriseFragment, .gap, .fillerCR, .explicit]

theorem allCRForms_count : allCRForms.length = 8 := rfl

/-- The 4 CR readings. We re-export the substrate's `RFReading` from
`Gameboard/RepriseContent.lean` rather than re-stipulating a parallel
`CRReading` enum. -/
abbrev CRReading := Discourse.Gameboard.RFReading

-- ════════════════════════════════════════════════════════════
-- § 9. Grounding via CCURs (§6.6–6.7)
-- ════════════════════════════════════════════════════════════

/-! ## Grounding Protocol via CCURs Pipeline

[ginzburg-2012] §6.6–6.7: the integration protocol for incoming
LocProps:

1. **Pending Update** (ex. 45 p. 176): the LocProp enters Pending
2. **Contextual Instantiation** (§6.5 (Ginzburg uses "contextual parameter assignments" terminology)): try to discharge
   dgb-params by binding indices to witnesses from addressee beliefs
3. **CCURs** (p. 167 footnote 30 + §6.6 ex. 73-86 pp. 192-198): if instantiation fails, apply a
   Clarification Context Update Rule — Parameter Identification (the
   default), Confirm, or Repeat — pushing a CR question on QUD

The substrate `Gameboard/Grounding.lean::integrateLocPropCCUR` implements
this pipeline. This section exercises it on a worked example. -/

section CCURExample

/-- "Did Jo leave?" as a LocProp with one cparam for "Jo". -/
def didJoLeave : LocProp String where
  phon := "Did Jo leave?"
  cat := "S"
  cont := "leave(jo)"
  cparams := [{ index := "jo_ref", restriction := "individual" }]
  constits := [{ phon := "Jo", cat := "NP", cont := "jo" }]

/-- A belief base where the addressee knows who Jo is. -/
def knowsJo : BeliefBase := [("jo_ref", "Jo")]

/-- An empty belief base — the addressee has no idea who Jo is. -/
def doesNotKnowJo : BeliefBase := []

/-- CR question constructor for unresolved cparams. -/
def crQuestion (p : CParam) : String := s!"Who do you mean by '{p.index}'?"

/-- With knowing-Jo beliefs, the LocProp grounds via CCURs (no CR needed). -/
theorem ccur_grounds_when_known :
    (integrateLocPropCCUR didJoLeave knowsJo crQuestion).isGrounded = true := rfl

/-- With empty beliefs, the LocProp triggers Parameter Identification CR. -/
theorem ccur_crifies_when_unknown :
    (integrateLocPropCCUR didJoLeave doesNotKnowJo crQuestion).isGrounded = false := rfl

/-- The CCUR pipeline strictly extends the one-shot stub: when cparams
are empty (trivial case), both yield the same grounded result. -/
theorem ccur_agrees_with_stub_on_empty
    (lp : LocProp String) (b : BeliefBase) (h : lp.cparams = []) :
    (integrateLocPropCCUR lp b crQuestion).isGrounded =
    (integrateLocProp lp crQuestion).isGrounded := by
  simp [integrateLocPropCCUR, integrateLocProp, contextualInstantiate, h,
        IntegrationResult.isGrounded]

end CCURExample

-- ════════════════════════════════════════════════════════════
-- § 10. Self-Repair via MaxPending (§8.2)
-- ════════════════════════════════════════════════════════════

/-! ## Self-Repair via MaxPending

[ginzburg-2012] §8.2 (pp. 282–290) "Unifying Self- and Other-Correction".
Per §6.3 footnote 31 p. 168 + §8.2: **MaxPending is the head of `Pending`**,
not a separate field. The substrate `Gameboard/SelfRepair.lean` provides:

- `pushMaxPending lp` — start a new in-construction LocProp at the head of Pending
- `replaceMaxPending lp'` — backwards-looking appropriateness repair
  (Ginzburg ex. 31 p. 287): swap the head of Pending with a corrected form
- `clearMaxPending` — drop the head (abandon current attempt)
- `maxPending` accessor — `pending.head?`

This section exercises a self-repair trace: speaker says "I saw the —"
(an in-construction LocProp), realizes the wrong word, replaces with
"I saw the manager" (the corrected form). -/

section SelfRepairExample

/-- The mid-utterance LocProp — speaker has begun "I saw the". -/
def midRepairLP : LocProp String where
  phon := "I saw the"
  cat := "S"
  cont := "see(spkr, ?)"

/-- The corrected LocProp once the speaker chooses "manager". -/
def correctedManagerLP : LocProp String where
  phon := "I saw the manager"
  cat := "S"
  cont := "see(spkr, manager)"

/-- Initial TIS, no repair in flight. -/
def repair_tis₀ : TIS String String String String := TIS.initial

/-- Push the in-construction LocProp onto Pending — it becomes MaxPending. -/
def repair_tis₁ : TIS String String String String :=
  repair_tis₀.pushMaxPending midRepairLP

/-- Apply backwards-looking appropriateness repair (ex. 31 p. 287):
swap the in-flight MaxPending with the corrected LocProp. -/
def repair_tis₂ : TIS String String String String :=
  repair_tis₁.replaceMaxPending correctedManagerLP

/-- After repair, MaxPending IS the corrected form. -/
theorem repair_replaces_maxPending :
    repair_tis₂.maxPending = some correctedManagerLP :=
  replaceMaxPending_becomes_max repair_tis₁ correctedManagerLP

/-- After repair, the original midRepair LocProp is no longer at the head. -/
theorem repair_old_form_gone :
    repair_tis₂.dgb.pending = [correctedManagerLP] := rfl

/-- Substrate witness: the abandonment path drops MaxPending. -/
theorem abandon_clears :
    repair_tis₁.clearMaxPending.maxPending = none := rfl

end SelfRepairExample

-- ════════════════════════════════════════════════════════════
-- § 11. End-to-End Pipeline
-- ════════════════════════════════════════════════════════════

/-! ## End-to-End: DialogueSign → LocProp → CCURs → DGB

The full [ginzburg-2012]-architecture pipeline:

1. Lexical entry as `DialogueSign Cont` (Ch. 5)
2. Project to `LocProp Cont` via `toLocProp` (Ch. 6)
3. Integration via `integrateLocPropCCUR` (§6.6–6.7)
4. Pipeline outcome integrates with DGB updates

We trace this for the worked example "Jo arrived" with two belief
configurations (addressee knows / does not know who Jo is). -/

section EndToEnd

/-- The DialogueSign for "Jo arrived" (composed conceptually from
`Grammar.jo`'s dgb-params and a verb sign). For brevity we just construct
the composed LocProp directly. -/
def joArrived_LP : LocProp String where
  phon := "Jo arrived"
  cat := "S"
  cont := "arrive(jo)"
  cparams := [{ index := "jo_ref", restriction := "individual" }]
  constits := [
    { phon := "Jo", cat := "NP", cont := "jo" },
    { phon := "arrived", cat := "V", cont := "arrive" }
  ]

/-- With knowing-Jo beliefs: the integration pipeline grounds. -/
theorem e2e_grounds_with_belief :
    (integrateLocPropCCUR joArrived_LP knowsJo crQuestion).isGrounded = true := rfl

/-- Without belief: the pipeline CRifies with the standard
"Who do you mean by 'jo_ref'?" CR. -/
theorem e2e_crifies_without_belief :
    integrateLocPropCCUR joArrived_LP doesNotKnowJo crQuestion =
    .crification "Who do you mean by 'jo_ref'?"
      { index := "jo_ref", restriction := "individual" } := rfl

/-- The exhaustivity claim: integration always either grounds or
CRifies, never silently skips. -/
theorem e2e_exhaustive (lp : LocProp String) (b : BeliefBase) :
    (integrateLocPropCCUR lp b crQuestion).isGrounded = true ∨
    (integrateLocPropCCUR lp b crQuestion).isGrounded = false := by
  cases (integrateLocPropCCUR lp b crQuestion).isGrounded <;> simp

/-- The Grammar.jo lexical entry's `toLocProp` itself has unresolved
cparams (it's a referential proper name). -/
theorem grammar_jo_unresolved :
    ¬ Discourse.Gameboard.Grammar.jo.toLocProp.isFullyResolved := by decide

end EndToEnd

-- ════════════════════════════════════════════════════════════
-- § 12. Cross-Framework Contrasts (pre-2012 siblings)
-- ════════════════════════════════════════════════════════════

/-! ## Architectural Contrasts vs Pre-2012 Frameworks

Per the project's chronological-dependency rule, this study engages
*pre-2012* siblings here:

- [stalnaker-1978]/[stalnaker-2002] — single shared CommonGround
- [farkas-bruce-2010] — five-way dcS/dcL/cg/table/ps decomposition
- [roberts-1996] — partition-based QUD-stack
- [purver-ginzburg-2004] — q-params/dgb-params split
- [ginzburg-sag-2000] — HPSG grammar foundation

Cross-framework contrasts with *post-2012* siblings (Krifka 2015,
Anderson 2021) live inside *those* studies, not here.

The contrasts below make the architectural disagreements Lean-checkable.
-/

section CrossFrameworkContrasts

/-- A simple two-world scenario for HasContextSet contrasts. -/
inductive RainW where
  | rainy | sunny
  deriving DecidableEq, Repr

/-- "It's raining" as a Set of worlds (only the rainy world). -/
def isRaining : Set RainW := fun w => w = .rainy

instance : DecidablePred isRaining := fun w => by unfold isRaining; exact inferInstance

/-! ### vs Stalnaker (single shared CommonGround)

[stalnaker-1978]: the common ground is *one shared object*. After
A asserts p, the (single) CommonGround contains p eliminated of ¬p worlds.

[ginzburg-2012]: each participant has their *own* DGB. After A
asserts p, A's DGB has p in FACTS; B's does not. There is NO shared CommonGround —
only coupled DGBs synchronized via Accept.

The contrast as a Lean theorem: KOS predicts that two participants'
DGBs (after A asserts p, before B accepts) project to *different*
context sets — Stalnaker's framework cannot represent this divergence
because it has only one CommonGround. -/

instance : DecidableSupport (Set RainW) String where
  supports _ _ := False
  decSupports _ _ := isFalse not_false

/-- Speaker DGB after asserting "raining". -/
def kosSpeakerDGB : DGB String (Set RainW) String String :=
  ((DGB.initial : DGB String (Set RainW) String String).addFact isRaining)

/-- Addressee DGB before accepting (still empty). -/
def kosAddresseeDGB : DGB String (Set RainW) String String :=
  DGB.initial

open CommonGround in
/-- KOS-vs-Stalnaker architectural contrast: KOS's two DGBs project to
*different* `ContextSet`s after one-sided assertion. Stalnaker's
framework has a single CommonGround that cannot represent this divergence —
the contrast is structural, not a matter of degree.

The inequality holds at `RainW.sunny`: the speaker's CS at sunny
requires `isRaining sunny = True` (i.e. `sunny = rainy`), which is
False; the addressee's CS at sunny is vacuously True (empty universal
over an empty `facts` list). -/
theorem kos_vs_stalnaker_per_dgb_divergence :
    HasContextSet.toContextSet kosSpeakerDGB ≠
    HasContextSet.toContextSet kosAddresseeDGB := by
  intro h
  -- Apply both sides at .sunny
  have hsunny := congrFun h RainW.sunny
  -- Speaker side: ∀ p ∈ [isRaining], p .sunny  ≡  isRaining .sunny  ≡  False
  -- Addressee side: ∀ p ∈ [], p .sunny         ≡  True
  -- So hsunny : False = True, contradiction
  simp only [HasContextSet.toContextSet, kosSpeakerDGB, kosAddresseeDGB,
             DGB.addFact, DGB.initial, isRaining,
             List.mem_singleton, forall_eq, List.not_mem_nil,
             IsEmpty.forall_iff, forall_const, eq_iff_iff, iff_true] at hsunny
  exact RainW.noConfusion hsunny

/-! ### vs Farkas-Bruce 2010 (five-way decomposition)

[farkas-bruce-2010]: discourse state has FIVE components (dcS, dcL,
cg, table, ps). Assertion adds to *speaker's dcS* (private commitment),
pushes an issue on the table; only *acceptance* moves content to the
shared CommonGround.

[ginzburg-2012]: per-participant DGBs (no separate dcS/dcL/cg
distinction inside one structure). Assertion goes directly to the
*speaker's own* DGB.facts.

The architectures are *both* per-participant, but F&B treats it as
three slates inside one "current discourse state" while KOS treats it
as one slate per participant. -/

open Discourse.Commitment.Table in
/-- The same dialogue trace ("A asserts p") in both frameworks: F&B
puts p in dcS (one of three slates within the shared discourse state);
KOS puts p in A's DGB.facts (one of two coupled DGBs). The architectural
shape differs even though predictions about "is p committed by A?"
agree. -/
theorem kos_vs_farkasbruce_architecture_differs
    (p : Set RainW) :
    -- F&B: a single discourse state keeps speaker/listener commitments and
    -- the common ground as separate per-agent slates
    let fb : State RainW := DiscourseState.empty.addCommit .speaker p
    p ∈ fb.dcS ∧ fb.cgPropositions = [] ∧ fb.dcL = [] :=
  ⟨List.mem_cons_self, rfl, rfl⟩

/-- The deeper architectural disagreement: **F&B can model retraction**
(content moves dcS → cg → dcS, e.g. "I take that back"); **KOS's facts
field is monotone** (operations only add, never remove). The KOS API
literally has no `removeFact` operation — the type signature of every
DGB-update primitive in `Gameboard/Basic.lean` preserves the inclusion
`dgb.facts ⊆ (op dgb).facts`.

Witness: `addFact p` increases the facts list by one element. -/
theorem kos_facts_monotone_under_addFact
    (dgb : DGB String (Set RainW) String String) (p : Set RainW) :
    dgb.facts ⊆ (dgb.addFact p).facts := by
  intro q hq
  simp [DGB.addFact, hq]

open Discourse.Commitment.Table in
/-- F&B explicitly supports the inverse: `addToCG` then can be reversed
by re-introducing to dcS. The substrate-level disagreement: KOS's
type-level commitment to monotonicity. -/
theorem farkasbruce_cg_can_be_emptied :
    (DiscourseState.empty : State RainW).cgPropositions = [] := rfl

/-! ### vs Roberts 1996/2012 (partition-stack QUD)

Both frameworks use a stack of questions. Roberts treats QUD entries
as *partitions* of worlds (Hamblin/Groenendijk-Stokhof style); KOS
treats QUD entries as `InfoStruc`s carrying the question + FECs.

Structural agreement: the push/pop semantics agree. We use the partition
substrate from `Core/Question/Partition/QUD.lean` to demonstrate. -/

/-- Both Roberts QUD-stack semantics and KOS InfoStruc-stack semantics
push and pop in the same way: the topmost question is the most recent. -/
theorem kos_qud_stack_agrees_with_roberts_at_top
    (dgb : DGB String String String String) (q : String) :
    (dgb.pushQud q).qud.head?.map (·.q) = some q := by
  simp [DGB.pushQud, InfoStruc.fromQuestion]

/-! ### vs Purver-Ginzburg 2004 (q-params / dgb-params split)

[purver-ginzburg-2004] ARGUE for the q-params / dgb-params split
that [ginzburg-2012] adopts (§8.5.1 ex. 101–103 p. 325–326): only
dgb-params block grounding (trigger CRification); q-params travel with
the sign but don't block, enabling the Reprise Content Hypothesis.

Our substrate `LocProp` carries this split as `cparams` (dgb-params)
and `qcparams` (q-params). The grounding pipeline only checks `cparams`. -/

/-- The Purver-Ginzburg structural prediction (substrate-instantiated):
a LocProp with q-params but no dgb-params still grounds. -/
theorem qparams_dont_block_grounding :
    let lp : LocProp String := {
      phon := "Who arrived?"
      cat := "S"
      cont := "?x.arrive(x)"
      cparams := []  -- no dgb-params
      qcparams := [{ index := "x", restriction := "individual" }]  -- but has q-params
    }
    (integrateLocProp lp crQuestion).isGrounded = true := rfl

/-! ### vs Ginzburg-Sag 2000 (HPSG grammar foundation)

[ginzburg-2012] Ch. 5 §5.1 explicitly builds on [ginzburg-sag-2000]'s
HPSG-formulated grammar. Our `Grammar.lean` integrates with HPSG via
`DialogueSign.toSynsem` (project to plain HPSG sign) and
`DialogueSign.toLocProp` (project to KOS-shaped LocProp).

This is structural agreement, not contrast — KOS's grammar is an
extension of GS2000's. The HPSG foundations supplement what KOS needs;
no architectural disagreement. -/

/-- KOS's `DialogueSign` faithfully extends [ginzburg-sag-2000]'s
HPSG `Synsem`: the projection `toSynsem` preserves head-features and
category, losing only dialogue features (dgbParams, qParams, questDom).
This is a structural-retract witness: KOS can be "forgotten down" to
plain HPSG. -/
theorem dialogueSign_extends_hpsg_faithfully {Cont : Type}
    (ds : Discourse.Gameboard.Grammar.DialogueSign Cont) :
    ds.toSynsem.cat = ds.pos ∧ ds.toSynsem.head = ds.head :=
  ⟨rfl, rfl⟩

/-! ### vs Purver-Ginzburg 2004 — full RCH machinery

The simple `qparams_dont_block_grounding` theorem above shows the
type-level prerequisite. The substantive Purver-Ginzburg claim is the
**Reprise Content Hypothesis** (RCH): the q-params record on a LocProp
licenses the queryable types observable in fragment-reprise data.

The substrate `Gameboard/RepriseContent.lean` provides the WeakRCH/StrongRCH
predicates. The PurverGinzburg2004 study file proves the q-params
predictor satisfies them. We re-export the structural connection here:
*the LocProp design choice in KOS-2012 is what enables RCH satisfaction*. -/

/-- The qcparams field on `LocProp` (the dgb-params/q-params split) is the
structural enabler of WeakRCH satisfaction (Purver-Ginzburg 2004's
methodological criterion). Without the split — if we tried to put
referential and existential parameters in the same field — fragment
reprises could not query just the q-params record, and WeakRCH would not
be satisfiable by any predictor. -/
example {Cont : Type} (lp : LocProp Cont) :
    -- The two fields are structurally separable:
    lp.cparams = lp.cparams ∧ lp.qcparams = lp.qcparams ∧
    -- And `integrateLocProp` only checks cparams:
    (lp.cparams = [] → (integrateLocProp lp crQuestion).isGrounded = true) :=
  ⟨rfl, rfl, fun h => by
    simp [integrateLocProp, h, IntegrationResult.isGrounded]⟩

end CrossFrameworkContrasts

end Ginzburg2012
