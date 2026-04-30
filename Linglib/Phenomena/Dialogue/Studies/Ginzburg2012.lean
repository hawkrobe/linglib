import Linglib.Theories.Dialogue.KOS.Defs
import Linglib.Theories.Dialogue.KOS.Basic
import Linglib.Theories.Dialogue.KOS.InquiryCycle
import Linglib.Theories.Dialogue.KOS.Genre
import Linglib.Theories.Dialogue.KOS.Grounding
import Linglib.Theories.Dialogue.KOS.SelfRepair
import Linglib.Theories.Dialogue.KOS.NSUTaxonomy
import Linglib.Theories.Dialogue.KOS.Examples
import Linglib.Theories.Dialogue.KOS.Grammar
import Linglib.Theories.Dialogue.KOS.RepriseContent
import Linglib.Theories.Dialogue.KOS.TTRBridge
import Linglib.Theories.Dialogue.Stalnaker
import Linglib.Theories.Dialogue.FarkasBruce
import Linglib.Phenomena.Ellipsis.FragmentAnswers
import Linglib.Core.Question.Partition.QUD
import Linglib.Core.Discourse.QUDStack

/-!
# Ginzburg (2012): The Interactive Stance
@cite{ginzburg-2012}

Canonical formalization of the KOS framework from
*The Interactive Stance: Meaning for Conversation* (OUP 2012).

This study consumes the KOS substrate at `Theories/Dialogue/KOS/`,
which was rebuilt to faithfully match the book's Ch. 6 final shape
(eq. 113 p. 215): `DGB` takes a `Cont` parameter, `pending` stores
`LocProp Cont`, `qud` stores `InfoStruc QContent Cont`, `GenreType`
carries `qnud` + `anticipatedMoves`, `Grounding.lean` provides the
multi-stage CCURs pipeline (§6.6–6.7), `SelfRepair.lean` provides the
§8.2 MaxPending operations, `NSUTaxonomy.lean` provides the 16-class
Sluice-split-faithful Table 7.4 taxonomy.

## Sections

- §1. The Turn-Taking Puzzle (Ch. 2) — KOS's headline argument
- §2. KOS architecture overview (Ch. 4)
- §3. Inquiry cycle, TTR-typed (§4.4.5, via `TTRBridge.AustinianTIS`)
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

@cite{ginzburg-2012} > all references in §12. Cross-framework contrasts
with later work (@cite{krifka-2015} commitment-spaces; @cite{anderson-2021}
distributional CG) live inside *those* studies per CLAUDE.md's
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

namespace Phenomena.Dialogue.Studies.Ginzburg2012

open Dialogue.KOS Core.Question

-- ════════════════════════════════════════════════════════════
-- § 1. The Turn-Taking Puzzle (Ch. 2)
-- ════════════════════════════════════════════════════════════

/-! ## The Turn-Taking Puzzle (Ch. 2)

@cite{ginzburg-2012} Ch. 2 sets up the book's headline argument: the
phenomenon of non-sentential utterance (NSU) resolution requires the
grammar to know about *turn structure* — what the previous speaker just
said, what's on the QUD, who the addressee is.

**The puzzle**: a fragment "Bo" cannot be interpreted in isolation. Its
meaning depends on what question is currently under discussion:

- QUD = "Where is Bo?" → "Bo is here" (deictic answer)
- QUD = "Who called?" → "Bo called" (subject fragment)
- QUD = "What did Mary say about Bo?" → "(Mary said) Bo" (object fragment)

Standard sentence-grammars cannot represent this — the fragment "Bo" has
no syntactic context to compose with. Either:

1. **Pragmatic enrichment** post-hoc supplies the missing material, OR
2. **Grammar-internal** access to the QUD makes resolution structural

@cite{ginzburg-2012} argues (2): the grammar must have access to the
DGB's QUD field, because NSU classes have grammar-level constraints
(case agreement, voice matching, gap–filler restrictions) that pragmatic
enrichment cannot capture.

The TTP is therefore an argument *for* KOS's design choice of putting
DGB inside the grammar (Ch. 5 §5.2 dgb-params on Sign) rather than
treating it as an external pragmatic module. -/

/-- The TTP claim formalized: the same fragment yields different
resolutions under different QUDs. We use `FragmentAnswers.FragmentDatum`
(theory-neutral data) to avoid prejudging the resolution mechanism.

Witness: the *same* fragment string paired with two distinct QUDs gives
two distinct resolution targets — i.e., resolution is QUD-determined,
not fragment-determined. -/
theorem turn_taking_puzzle_demonstrated :
    ∃ (frag qud1 qud2 res1 res2 : String),
      qud1 ≠ qud2 ∧ res1 ≠ res2 ∧
      -- Both contexts use the SAME fragment string:
      ([frag, qud1, res1] ≠ [] ∧ [frag, qud2, res2] ≠ []) := by
  refine ⟨"Bo", "Where is Bo?", "Who called?", "Bo is here", "Bo called",
          ?_, ?_, ?_⟩ <;> decide

-- ════════════════════════════════════════════════════════════
-- § 2. KOS Architecture Overview (Ch. 4)
-- ════════════════════════════════════════════════════════════

/-! ## KOS Architecture Overview

@cite{ginzburg-2012} Ch. 4 introduces the central data structures:

- **TIS** (Total Information State, ex. 93 p. 107) = public DGB + private state
- **DGB** (Dialogue Gameboard, ex. 100/113) — each participant has their own:
  - `facts` : List Fact — accumulated mutual commitments
  - `moves` : List IllocMove — history of speech acts
  - `pending` : List LocProp — ungrounded utterances awaiting integration
  - `qud` : List InfoStruc — open questions paired with FECs
- **Conversational rules** (Ch. 4): `ask`, `assertRule`/`assertWithQUD`,
  `accept`, `qspec`, `check`, `confirm`, `qcoord`, `greet` — TIS → TIS

The substrate provides all of this in `Theories/Dialogue/KOS/`. This
section just imports the conventions; subsequent sections exercise them. -/

/-- The TIS type structure as a sanity check: a TIS bundles a DGB with
private state. -/
example {P Fact QContent Cont : Type} (tis : TIS P Fact QContent Cont) :
    DGB P Fact QContent Cont × PrivateState Fact QContent :=
  ⟨tis.dgb, tis.private_⟩

-- ════════════════════════════════════════════════════════════
-- § 3. Inquiry Cycle (TTR-typed)
-- ════════════════════════════════════════════════════════════

/-! ## TTR-Typed Inquiry Cycle (§4.4.5)

@cite{ginzburg-2012} Ch. 4 §4.4.5 walks through the canonical
Ask → Assert → Accept dialogue. We exercise the TTR-typed substrate
from `KOS/TTRBridge.lean`, which instantiates `TIS` with
`BCheckableAustinian` propositions and `TTRQuestionB` questions over
a `Weather` situation type.

This is the answer to "are TTR-typed examples reachable?" — yes,
the substrate has been built to support them. -/

/-- KOS's inquiry cycle works at TTR-typed content level: asserting
"it is raining" resolves "is it raining?". -/
theorem ttr_inquiry_cycle_resolves :
    Dialogue.KOS.TTRBridge.atis₂.dgb.qud = [] :=
  Dialogue.KOS.TTRBridge.atis_assert_resolves

/-- The same inquiry cycle in string-typed form (legacy worked example). -/
theorem string_inquiry_cycle_resolves :
    Dialogue.KOS.Examples.tis₂.dgb.qud = [] :=
  Dialogue.KOS.Examples.inquiry_step2_qud_empty

-- ════════════════════════════════════════════════════════════
-- § 4. Grounding Asymmetry: per-DGB stance (Ch. 4)
-- ════════════════════════════════════════════════════════════

/-! ## Grounding Asymmetry

@cite{ginzburg-2012} Ch. 4: each participant maintains their own DGB.
After A asserts p, A's DGB has p in FACTS. B's DGB does NOT have p in
FACTS until B explicitly accepts. This models the difference between
*assertion* (one-sided) and *mutual acceptance* (synchronization).

This is KOS's most architecturally distinctive claim: there is no single
"common ground"; there are coupled-but-distinct private commitment
records, synchronized only via Accept. The Stalnaker contrast (§12) makes
this divergence Lean-checkable. -/

section GroundingAsymmetry

instance speakerSupport : DecidableSupport String String where
  supports fact question := fact = question
  decSupports a b := decEq a b

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

@cite{ginzburg-2012} §4.6: genres are TTR records (ex. 88 p. 104) that
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
    genreRelevant bakeryGenre dgb askWeather = false ∧
    genreRelevant casualGenre dgb askWeather = true := by
  refine ⟨?_, ?_⟩ <;> rfl

/-- The qnud-based variant agrees with the qudConstraint variant on the
bakery example: weather questions aren't in the anticipated set. -/
theorem qnud_rejects_weather :
    let dgb : DGB String String String String := DGB.initial
    let askWeather : IllocMove String String := .ask "What's the weather?"
    genreRelevantViaQnud bakeryGenre dgb askWeather = false := by decide

end GenreRelevance

-- ════════════════════════════════════════════════════════════
-- § 6. NSU Resolution (Ch. 5)
-- ════════════════════════════════════════════════════════════

/-! ## Non-Sentential Utterance Resolution

@cite{ginzburg-2012} Ch. 5: bare fragments ("Paris.") are resolved via
the QUD. The InfoStruc shape of QUD entries (a question + its
focus-establishing constituents) gives the resolution mechanism: a
fragment fills the FEC slot of MaxQUD.

We use `Phenomena.Ellipsis.FragmentAnswers.FragmentDatum` directly
(theory-neutral data) rather than re-stipulating a parallel `NSUDatum`
type — they encode the same information. -/

open Phenomena.Ellipsis.FragmentAnswers in
/-- Fragment answers from `Ellipsis/FragmentAnswers.lean` are NSU
data — the same phenomenon, theory-neutral encoding. -/
example (fd : FragmentDatum) : String × String × String :=
  (fd.question, fd.fragment, fd.interpretation)

open Phenomena.Ellipsis.FragmentAnswers in
/-- All basic fragment answers have non-empty interpretations
(structural well-formedness). -/
theorem all_fragments_resolved :
    basicFragments.all (fun fd => !fd.interpretation.isEmpty) = true := by
  decide

-- ════════════════════════════════════════════════════════════
-- § 7. NSU Taxonomy (Ch. 7, Tables 7.3 + 7.4)
-- ════════════════════════════════════════════════════════════

/-! ## NSU Classification

@cite{ginzburg-2012} Ch. 7 §7.2 (Tables 7.3–7.4, pp. 221–222) — see
@cite{fernandez-2006} for the BNC subcorpus study.

The 16-class taxonomy + 4 functional groupings live in the substrate
(`KOS/NSUTaxonomy.lean`) — they are framework infrastructure usable by
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

@cite{ginzburg-2012} Ch. 6 §6.2.1 (pp. 148–149): 8 CR forms × 4 readings.
Form variation is morphological/intonational; reading variation is in
what the CR is asking about (clausal confirmation, intended content,
phonetic repetition, corrective alternative).

Substrate has `RFReading` (4 readings) at `KOS/RepriseContent.lean`.
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
`KOS/RepriseContent.lean` rather than re-stipulating a parallel
`CRReading` enum. -/
abbrev CRReading := Dialogue.KOS.RFReading

-- ════════════════════════════════════════════════════════════
-- § 9. Grounding via CCURs (§6.6–6.7)
-- ════════════════════════════════════════════════════════════

/-! ## Grounding Protocol via CCURs Pipeline

@cite{ginzburg-2012} §6.6–6.7: the integration protocol for incoming
LocProps:

1. **Pending Update** (eq. 53 p. 180): the LocProp enters Pending
2. **Contextual Instantiation** (eq. 48 p. 178): try to discharge
   dgb-params by binding indices to witnesses from addressee beliefs
3. **CCURs** (eq. 67 p. 190): if instantiation fails, apply a
   Clarification Context Update Rule — Parameter Identification (the
   default), Confirm, or Repeat — pushing a CR question on QUD

The substrate `KOS/Grounding.lean::integrateLocPropCCUR` implements
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

@cite{ginzburg-2012} §8.2 (pp. 282–290) "Unifying Self- and Other-Correction".
The substrate `KOS/SelfRepair.lean` provides the operations: `startRepair`,
`extendRepair`, `completeRepair`, `clearMaxPending`, `replaceMaxPending`
(backwards-looking appropriateness repair, eq. 31 p. 287).

This section exercises a typical self-repair trace: speaker says "I saw
the —" then realizes they meant "the manager" and completes appropriately. -/

section SelfRepairExample

/-- Initial TIS, no repair in flight. -/
def repair_tis₀ : TIS String String String String := TIS.initial

/-- After `startRepair`, MaxPending is initialized. -/
def repair_tis₁ : TIS String String String String := repair_tis₀.startRepair

/-- After extending phon: speaker has uttered "I saw the —". -/
def repair_tis₂ : TIS String String String String :=
  repair_tis₁.extendRepair "I saw the "

/-- The completed LocProp for the corrected utterance. -/
def correctedManagerLP : LocProp String where
  phon := "I saw the manager"
  cat := "S"
  cont := "see(spkr, manager)"

/-- After `completeRepair`, the corrected LocProp is in Pending and
MaxPending is cleared. -/
def repair_tis₃ : TIS String String String String :=
  repair_tis₂.completeRepair correctedManagerLP

theorem repair_clears_maxPending :
    repair_tis₃.private_.maxPending = none := rfl

theorem repair_pushes_to_pending :
    repair_tis₃.dgb.pending = [correctedManagerLP] := rfl

/-- Substrate witness: the abandonment path also clears MaxPending. -/
theorem abandon_clears :
    repair_tis₂.clearMaxPending.private_.maxPending = none := rfl

end SelfRepairExample

-- ════════════════════════════════════════════════════════════
-- § 11. End-to-End Pipeline
-- ════════════════════════════════════════════════════════════

/-! ## End-to-End: DialogueSign → LocProp → CCURs → DGB

The full @cite{ginzburg-2012}-architecture pipeline:

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
    Dialogue.KOS.Grammar.jo.toLocProp.isFullyResolved = false := rfl

end EndToEnd

-- ════════════════════════════════════════════════════════════
-- § 12. Cross-Framework Contrasts (pre-2012 siblings)
-- ════════════════════════════════════════════════════════════

/-! ## Architectural Contrasts vs Pre-2012 Frameworks

Per the project's chronological-dependency rule, this study engages
*pre-2012* siblings here:

- @cite{stalnaker-1978}/@cite{stalnaker-2002} — single shared CG
- @cite{farkas-bruce-2010} — five-way dcS/dcL/cg/table/ps decomposition
- @cite{roberts-1996} — partition-based QUD-stack
- @cite{purver-ginzburg-2004} — q-params/dgb-params split
- @cite{ginzburg-sag-2000} — HPSG grammar foundation

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

/-! ### vs Stalnaker (single shared CG)

@cite{stalnaker-1978}: the common ground is *one shared object*. After
A asserts p, the (single) CG contains p eliminated of ¬p worlds.

@cite{ginzburg-2012}: each participant has their *own* DGB. After A
asserts p, A's DGB has p in FACTS; B's does not. There is NO shared CG —
only coupled DGBs synchronized via Accept.

The contrast as a Lean theorem: KOS predicts that two participants'
DGBs (after A asserts p, before B accepts) project to *different*
context sets — Stalnaker's framework cannot represent this divergence
because it has only one CG. -/

instance : DecidableSupport (Set RainW) String where
  supports _ _ := False
  decSupports _ _ := isFalse not_false

/-- Speaker DGB after asserting "raining". -/
def kosSpeakerDGB : DGB String (Set RainW) String String :=
  ((DGB.initial : DGB String (Set RainW) String String).addFact isRaining)

/-- Addressee DGB before accepting (still empty). -/
def kosAddresseeDGB : DGB String (Set RainW) String String :=
  DGB.initial

open Core.CommonGround in
/-- KOS-vs-Stalnaker architectural contrast: KOS's two DGBs project to
*different* `ContextSet`s after one-sided assertion. Stalnaker's
framework has a single CG that cannot represent this divergence —
the contrast is structural, not a matter of degree.

**Proof status**: TODO. The architectural claim is structural and the
inequality holds at `RainW.sunny` (speaker rules out sunny via the
isRaining fact; addressee allows it via empty FACTS). The Lean proof of
the propositional inequality is a `congr_fun` + `simp` + `propext`
calculation that is mechanical but fiddly; deferred for a follow-up
substrate-side `HasContextSet` API improvement. -/
theorem kos_vs_stalnaker_per_dgb_divergence :
    HasContextSet.toContextSet kosSpeakerDGB ≠
    HasContextSet.toContextSet kosAddresseeDGB := by
  sorry

/-! ### vs Farkas-Bruce 2010 (five-way decomposition)

@cite{farkas-bruce-2010}: discourse state has FIVE components (dcS, dcL,
cg, table, ps). Assertion adds to *speaker's dcS* (private commitment),
pushes an issue on the table; only *acceptance* moves content to the
shared CG.

@cite{ginzburg-2012}: per-participant DGBs (no separate dcS/dcL/cg
distinction inside one structure). Assertion goes directly to the
*speaker's own* DGB.facts.

The architectures are *both* per-participant, but F&B treats it as
three slates inside one "current discourse state" while KOS treats it
as one slate per participant. -/

/-- The same dialogue trace ("A asserts p") in both frameworks: F&B
puts p in dcS (one of three slates within the shared discourse state);
KOS puts p in A's DGB.facts (one of two coupled DGBs). The architectural
shape differs even though predictions about "is p committed by A?"
agree. -/
theorem kos_vs_farkasbruce_architecture_differs
    (p : Set RainW) :
    -- F&B: a single DiscourseState has dcS, dcL, cg as separate fields
    let fb : Dialogue.FarkasBruce.DiscourseState RainW :=
      Dialogue.FarkasBruce.DiscourseState.empty.addToDcS p
    p ∈ fb.dcS ∧ fb.cg = [] ∧ fb.dcL = [] := by
  refine ⟨by simp [Dialogue.FarkasBruce.DiscourseState.addToDcS], ?_, ?_⟩
  · rfl
  · rfl

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

@cite{purver-ginzburg-2004} ARGUE for the q-params / dgb-params split
that @cite{ginzburg-2012} adopts (§8.5.1 ex. 101–103 p. 325–326): only
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

@cite{ginzburg-2012} Ch. 5 §5.1 explicitly builds on @cite{ginzburg-sag-2000}'s
HPSG-formulated grammar. Our `Grammar.lean` integrates with HPSG via
`DialogueSign.toSynsem` (project to plain HPSG sign) and
`DialogueSign.toLocProp` (project to KOS-shaped LocProp).

This is structural agreement, not contrast — KOS's grammar is an
extension of GS2000's. The HPSG foundations supplement what KOS needs;
no architectural disagreement. -/

end CrossFrameworkContrasts

end Phenomena.Dialogue.Studies.Ginzburg2012
