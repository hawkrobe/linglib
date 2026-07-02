import Linglib.Features.Aktionsart
import Linglib.Features.Attitudes
import Linglib.Features.Causation
import Linglib.Semantics.Lexical.LevinClass
import Linglib.Semantics.Lexical.MeaningComponents
import Linglib.Semantics.Verb.Root.Signature
import Linglib.Semantics.Lexical.EventStructure

/-!
# Levin Verb Class Theory
[levin-1993] [dowty-1991] [beavers-koontz-garboden-2020]

The `LevinClass` enum and its classification data (`meaningComponents`,
`predictsUnaccusative`, `isVerbOfCreation`) live in
`Semantics/Lexical/LevinClass.lean`; `MeaningComponents` in
`Semantics/Lexical/MeaningComponents.lean`.

This file provides the theoretical content that depends on `Root.Kinds`:
the root signature label, the root–MC comparison enums, and the universal
consistency/divergence theorems that ground them. `LevinClass` is a *lossy
realization label*, not a source of truth (that is `Verb.Root.kinds`); the
theorems below are the non-decorative grounding — each holds for every class
and breaks if a table row changes, so per-class `rfl` spot-checks are not
restated.

## § 1. Root entailment label ([beavers-koontz-garboden-2020])

The `rootEntailments` signature label and its universal soundness theorem.

## § 2. Root–MC comparison

Classification enums (CausationSource, ResultKind, MannerKind) naming the
systematic divergences between B&KG root features and Levin meaning
components, plus the universal consistency theorems and divergence witnesses.
-/

-- ════════════════════════════════════════════════════
-- § 1. Root Entailment Mapping ([beavers-koontz-garboden-2020])
-- ════════════════════════════════════════════════════

section LevinClassMethods
open Semantics.Lexical
open Verb
open Root.Kinds
namespace Semantics.Lexical

/-- Root kind signature for each Levin class.

    Assignments marked (B&KG) are directly from [beavers-koontz-garboden-2020] Table 12 and Chapters 2–5. Others are inferred from class
    semantics following B&KG's framework:
    - Externally caused CoS → `causativeResult` (√CRACK pattern)
    - Internally caused CoS → `pureResult` (√BLOSSOM pattern)
    - Action/manner verbs → `pureManner` (√JOG pattern)
    - MRC violators → `fullSpec` (√HAND/√DROWN pattern)
    - Stative/psychological → `propertyConcept` (√FLAT pattern)

    Classes marked (default) use `minimal` as a conservative placeholder
    pending detailed study under B&KG's framework. -/
def LevinClass.rootEntailments : LevinClass → Root.Kinds
  -- §9 Putting: template provides CAUSE+BECOME; root content varies
  | .put => minimal                -- (default)
  | .funnel => pureManner          -- manner of channeling
  | .pour => pureManner            -- manner of pouring
  | .coil => pureManner            -- manner of arranging
  | .sprayLoad => minimal          -- (default)
  -- §10 Removing
  | .remove => minimal             -- (default)
  | .clear => causativeResult      -- externally caused cleared state
  | .wipe => pureManner            -- manner of surface action
  | .steal => minimal              -- (default)
  -- §11 Sending and Carrying
  | .send => minimal               -- (default)
  | .carry => pureManner           -- manner of transport
  | .drive => pureManner           -- manner via vehicle
  -- §12 Exerting Force
  | .pushPull => pureManner        -- manner of force application
  -- §13 Change of Possession
  | .give => fullSpec              -- (B&KG Ch.3) √HAND: manner + caused possession change
  | .contribute => minimal         -- (default) less specified than give
  | .getObtain => minimal          -- (default)
  | .exchange => minimal           -- (default)
  -- §14–16
  | .learn => minimal              -- (default)
  | .hold => propertyConcept       -- state of holding
  | .conceal => causativeResult    -- externally caused hidden state
  -- §17 Throwing
  | .throw => fullSpec             -- manner of propulsion + caused arrival
  -- §18 Contact by Impact
  | .hit => pureManner             -- (B&KG Ch.4) impact manner, no state entailed
  | .swat => pureManner            -- like hit
  -- §19 Poking
  | .poke => pureManner            -- manner of contact
  -- §20 Contact: Touch
  | .touch => minimal              -- (B&KG) no structural entailments
  -- §21 Cutting
  | .cut => fullSpec               -- (B&KG Ch.4) cutting manner + caused separation
  | .carve => fullSpec             -- like cut
  -- §22 Combining and Attaching
  | .mix => causativeResult        -- externally caused combined state
  | .amalgamate => causativeResult
  -- §23 Separating
  | .separate => causativeResult   -- externally caused separated state
  | .split => fullSpec             -- instrument manner + caused separation
  -- §24 Coloring
  | .color => causativeResult      -- externally caused colored state
  -- §25 Image Creation
  | .imageCreation => fullSpec     -- etching manner + caused image
  -- §26 Creation and Transformation
  | .build => causativeResult      -- externally caused creation
  | .grow => pureResult            -- internally caused growth
  | .create => causativeResult     -- externally caused creation
  | .knead => fullSpec             -- kneading manner + caused shape change
  | .turn => causativeResult       -- externally caused transformation
  | .performance => pureManner     -- performance manner
  -- §27–28
  | .engender => causativeResult   -- root entails causation
  | .calve => pureResult           -- internally caused biological process
  -- §29 Predicative Complements
  | .appoint => causativeResult    -- externally caused status change
  | .characterize => minimal       -- (default)
  | .declare => causativeResult    -- externally caused status change
  -- §30 Perception
  | .see => minimal                -- (default)
  | .sight => minimal              -- (default)
  -- §31 Psych-Verbs
  | .amuse => causativeResult      -- stimulus causes psychological CoS
  | .admire => propertyConcept     -- psychological state
  | .marvel => propertyConcept     -- psychological state
  -- §32–34
  | .want => propertyConcept       -- desiderative state
  | .judgment => minimal           -- (default)
  | .assessment => minimal         -- (default)
  -- §35 Searching
  | .search => pureManner          -- searching manner
  -- §36 Social Interaction
  | .socialInteraction => minimal  -- (default)
  -- §37 Communication
  | .say => minimal                -- (default)
  | .tell => minimal               -- (default)
  | .mannerOfSpeaking => pureManner -- manner of speaking
  -- §38 Animal Sounds
  | .animalSound => pureManner     -- specific sound manner
  -- §39 Ingesting
  | .eat => causativeResult        -- caused consumption, no specific manner
  | .devour => fullSpec            -- vigorous manner + caused consumption
  | .dine => pureManner            -- social activity manner
  -- §40 Body
  | .bodyProcess => minimal        -- (default)
  | .flinch => minimal             -- (default)
  -- §41 Grooming
  | .dress => causativeResult      -- externally caused dressed state
  -- §42 Killing
  | .murder => causativeResult     -- (B&KG) root entails caused death
  | .poison => fullSpec            -- (B&KG) poisoning manner + caused death (√DROWN-type)
  -- §43 Emission
  | .lightEmission => propertyConcept  -- emitting state
  | .soundEmission => propertyConcept
  | .substanceEmission => propertyConcept
  -- §44 Destroy
  | .destroy => causativeResult    -- (B&KG) root entails caused total destruction
  -- §45 Change of State
  | .break_ => causativeResult     -- (B&KG Ch.2,5) √CRACK: externally caused CoS
  | .bend => causativeResult       -- externally caused shape change
  | .cooking => fullSpec           -- (B&KG) cooking manner + caused CoS
  | .otherCoS => causativeResult   -- √MELT/√FREEZE: externally caused CoS
  | .entitySpecificCoS => pureResult -- √BLOSSOM/√RUST: internally caused
  | .calibratableCoS => pureResult -- internally driven scalar change
  -- §46 Lodge
  | .lodge => minimal              -- (default)
  -- §47 Existence
  | .exist => minimal              -- (B&KG) pure stative, no root content
  -- §48 Appearance, Disappearance
  | .appear => pureResult          -- internally caused appearance
  | .disappearance => pureResult   -- internally caused going out of existence
  -- §49 Body-Internal Motion
  | .bodyInternalMotion => pureManner -- fidgeting manner
  -- §50 Assuming a Position
  | .assumePosition => pureResult  -- internally caused position change
  -- §51 Motion
  | .inherentlyDirectedMotion => pureResult -- internally caused directed motion
  | .leave => pureResult           -- internally caused departure
  | .mannerOfMotion => pureManner  -- (B&KG) √JOG: motion manner
  | .vehicleMotion => pureManner   -- vehicle manner
  | .chase => pureManner           -- chasing manner
  -- §52 Avoid
  | .avoid => minimal              -- (default)
  -- §53 Lingering and Rushing
  | .linger => pureManner          -- temporal manner
  | .rush => pureManner            -- temporal manner
  -- §54 Measure
  | .measure => propertyConcept    -- measurement state
  -- §55 Aspectual
  | .aspectual => minimal          -- (default) template-level
  -- §57 Weather
  | .weather => minimal            -- (default)

/-! ### Table soundness (universal)

`rootEntailments` is a lossy realization *label*, not a source of truth. It
earns its place via a theorem that holds for *every* class and breaks if a
row is changed: every assigned signature is well-formed (collocationally
closed). Invert any row to an unclosed signature and this fails — the
grounding is not decorative. Manner/result complementarity of these
signatures is covered by the canonical kinds-layer theory
(`Roots/Closure.lean`, `closed_violatesBifurcation_iff`), which quantifies
over all `Root.Kinds`, so no per-class MRC spot-check is restated here. -/

/-- Every Levin class is assigned a well-formed (closed) root signature. -/
theorem rootEntailments_wellFormed (c : LevinClass) :
    c.rootEntailments.WellFormed := by cases c <;> decide

-- ════════════════════════════════════════════════════
-- § 2. Root–MC Comparison ([beavers-koontz-garboden-2020], [levin-1993])
-- ════════════════════════════════════════════════════

/-! ### Root–MC comparison

[levin-1993]'s meaning components and [beavers-koontz-garboden-2020]'s root
entailments are two independently-motivated lexical decompositions; they are
NOT isomorphic — they conceptualize different levels of granularity:

| B&KG concept | Levin concept | Relationship |
|---|---|---|
| `result` | `changeOfState` | B&KG broader: includes location/possession change |
| `manner` | `mannerSpec` ∨ `instrumentSpec` | B&KG broader: includes contact-manner (hit) |
| `cause` | `causation` | Distinct: root-level vs event-level causation |

Because B&KG `result`/`manner` are *coarser* than the Levin features, neither
table is a function of the other (`give` carries `result` but
`changeOfState = false`; `hit` carries `manner` but `mannerSpec = false`), so
the two are related by the consistency/divergence theorems below, not by a
derivation — a morphism `meaningComponents = f rootEntailments` is not just
absent from the literature but mathematically impossible here, and the
manner/result-complementarity dispute ([beavers-koontz-garboden-2020] vs the
Rappaport Hovav & Levin tradition) is exactly over this independence. The three
`*Kind` enums name the specific divergences, making them grep-able and testable. -/

/-- Where a verb class's event-level causation originates.

    B&KG's root-level `cause` and Levin's event-level `causation` are
    distinct concepts ([beavers-koontz-garboden-2020] Ch. 5;
    [levin-1993] pp. 9–10). -/
inductive CausationSource where
  | rootExternal
  | rootNonDetachable
  | template
  | none
  deriving DecidableEq, Repr

/-- Derive the causation source from the root signature and meaning components. -/
def LevinClass.causationSource (c : LevinClass) : CausationSource :=
  let re := c.rootEntailments
  let mc := c.meaningComponents
  if .cause ∈ re then
    if mc.causation then .rootExternal else .rootNonDetachable
  else
    if mc.causation then .template else .none

/-- What kind of result the root entails (refines B&KG `result`).

    Levin's `changeOfState` corresponds to `stateChange` only —
    change of location (throw, arrive) and change of possession (give)
    carry `result` in B&KG but `changeOfState = false` in Levin. -/
inductive ResultKind where
  | stateChange
  | locationChange
  | possessionChange
  | none
  deriving DecidableEq, Repr

/-- Derive result kind from the root signature and meaning components. -/
def LevinClass.resultKind (c : LevinClass) : ResultKind :=
  let re := c.rootEntailments
  let mc := c.meaningComponents
  if .result ∉ re then .none
  else if mc.changeOfState then .stateChange
  else if mc.motion then .locationChange
  else .possessionChange

/-- How root manner maps to Levin's MC spec features.

    B&KG's `manner` subsumes three Levin-level distinctions:
    - **mannerSpec**: how the action proceeds (cooking, running)
    - **instrumentSpec**: what tool is used (cutting, poking)
    - **unspecified**: manner verb without a Levin spec flag (hit, push) -/
inductive MannerKind where
  | mannerSpec
  | instrumentSpec
  | unspecified
  | none
  deriving DecidableEq, Repr

/-- Derive manner kind from the root signature and meaning components. -/
def LevinClass.mannerKind (c : LevinClass) : MannerKind :=
  let re := c.rootEntailments
  let mc := c.meaningComponents
  if .manner ∉ re then .none
  else if mc.instrumentSpec then .instrumentSpec
  else if mc.mannerSpec then .mannerSpec
  else .unspecified

/-! The `causationSource`/`resultKind`/`mannerKind` classifiers are grounded
not by per-class `rfl` confirmations (which merely restate a row of the
`def` and break in lockstep when the row changes) but by the universal
consistency theorems below, which relate them to the root signature and the
event template and break under a genuine table change. -/

/-! ### Root-structural MC contribution -/

/-- Root structural contribution to meaning components.
    Maps result → changeOfState and manner → mannerSpec. -/
def _root_.Verb.Root.Kinds.structuralMC (re : Root.Kinds) : MeaningComponents :=
  { changeOfState := decide (.result ∈ re)
  , contact := false
  , motion := false
  , causation := false
  , instrumentSpec := false
  , mannerSpec := decide (.manner ∈ re) }

/-! ### Universal consistency theorems

These hold for ALL 78 LevinClass constructors and are proved by
exhaustive case analysis. -/

/-- Levin spec implies B&KG manner. -/
theorem levin_spec_implies_bkg_manner (c : LevinClass) :
    c.meaningComponents.mannerSpec = true ∨ c.meaningComponents.instrumentSpec = true →
    .manner ∈ c.rootEntailments := by
  cases c <;> decide

/-- CausativeResult roots always have changeOfState. -/
theorem causativeResult_always_cos (c : LevinClass) :
    c.rootEntailments = causativeResult →
    c.meaningComponents.changeOfState = true := by
  cases c <;> decide

/-- Root cause implies either event causation or non-detachable causation. -/
theorem root_cause_accounted_for (c : LevinClass) :
    .cause ∈ c.rootEntailments →
    c.meaningComponents.causation = true ∨
    c.causationSource = .rootNonDetachable := by
  cases c <;> decide

/-- `.stateChange` resultKind implies Template-level result-state. -/
theorem resultKind_stateChange_imp_template_resultState (c : LevinClass) :
    c.resultKind = .stateChange → c.eventTemplate.HasResultState := by
  cases c <;> decide

/-- The converse fails: aspectual verbs have HasResultState (via the
achievement template) but `resultKind ≠ .stateChange`. -/
theorem template_resultState_not_iff_resultKind_stateChange :
    ∃ c : LevinClass,
      c.eventTemplate.HasResultState ∧ c.resultKind ≠ .stateChange := by
  refine ⟨.aspectual, ?_⟩
  decide

/-- The naive structural prediction `structuralMC ∘ rootEntailments` is *not*
    a refinement of the hand-specified `meaningComponents`: a class can carry
    `result` in its root signature (so `structuralMC` predicts `changeOfState`)
    yet have Levin `changeOfState = false` — change of possession/location
    carries `result` in B&KG but is not a change *of state* for Levin. This
    divergence witness is why the bridge enums (`ResultKind` et al.) exist and
    `meaningComponents` is not just `structuralMC ∘ rootEntailments`. -/
theorem structuralMC_diverges_from_meaningComponents :
    ∃ c : LevinClass,
      (Verb.Root.Kinds.structuralMC c.rootEntailments).changeOfState = true ∧
      c.meaningComponents.changeOfState = false :=
  ⟨.give, by decide⟩

end Semantics.Lexical
