import Linglib.Core.Lexical.VerbClass
import Linglib.Core.Lexical.RootFeatures

/-!
# Levin Verb Class Theory
@cite{levin-1993} @cite{dowty-1991} @cite{beavers-koontz-garboden-2020}

The `LevinClass` enum and its classification data (`MeaningComponents`,
`meaningComponents`, `predictsUnaccusative`, `isVerbOfCreation`) are
defined in `Core/Lexical/VerbClass.lean`.

This file provides the theoretical content that depends on `RootEntailments`:
root entailment mapping, root–MC bridge enums, and universal consistency
theorems.

## § 1. Root entailment mapping (@cite{beavers-koontz-garboden-2020})

Root structural entailments, well-formedness verification, and MRC tests.

## § 2. Root–MC bridge

Classification enums (CausationSource, ResultKind, MannerKind) naming the
systematic divergences between B&KG root features and Levin meaning
components, plus universal consistency theorems.
-/

-- ════════════════════════════════════════════════════
-- § 1. Root Entailment Mapping (@cite{beavers-koontz-garboden-2020})
-- ════════════════════════════════════════════════════

section LevinClassMethods
open Core.Verbs
namespace Core.Verbs

/-- Root structural entailments for each Levin class.

    Assignments marked (B&KG) are directly from @cite{beavers-koontz-garboden-2020} Table 12 and Chapters 2–5. Others are inferred from class
    semantics following B&KG's framework:
    - Externally caused CoS → `causativeResult` (√CRACK pattern)
    - Internally caused CoS → `pureResult` (√BLOSSOM pattern)
    - Action/manner verbs → `pureManner` (√JOG pattern)
    - MRC violators → `fullSpec` (√HAND/√DROWN pattern)
    - Stative/psychological → `propertyConcept` (√FLAT pattern)

    Classes marked (default) use `minimal` as a conservative placeholder
    pending detailed study under B&KG's framework. -/
def LevinClass.rootEntailments : LevinClass → RootEntailments
  -- §9 Putting: template provides CAUSE+BECOME; root content varies
  | .put => .minimal                -- (default)
  | .funnel => .pureManner          -- manner of channeling
  | .pour => .pureManner            -- manner of pouring
  | .coil => .pureManner            -- manner of arranging
  | .sprayLoad => .minimal          -- (default)
  -- §10 Removing
  | .remove => .minimal             -- (default)
  | .clear => .causativeResult      -- externally caused cleared state
  | .wipe => .pureManner            -- manner of surface action
  | .steal => .minimal              -- (default)
  -- §11 Sending and Carrying
  | .send => .minimal               -- (default)
  | .carry => .pureManner           -- manner of transport
  | .drive => .pureManner           -- manner via vehicle
  -- §12 Exerting Force
  | .pushPull => .pureManner        -- manner of force application
  -- §13 Change of Possession
  | .give => .fullSpec              -- (B&KG Ch.3) √HAND: manner + caused possession change
  | .contribute => .minimal         -- (default) less specified than give
  | .getObtain => .minimal          -- (default)
  | .exchange => .minimal           -- (default)
  -- §14–16
  | .learn => .minimal              -- (default)
  | .hold => .propertyConcept       -- state of holding
  | .conceal => .causativeResult    -- externally caused hidden state
  -- §17 Throwing
  | .throw => .fullSpec             -- manner of propulsion + caused arrival
  -- §18 Contact by Impact
  | .hit => .pureManner             -- (B&KG Ch.4) impact manner, no state entailed
  | .swat => .pureManner            -- like hit
  -- §19 Poking
  | .poke => .pureManner            -- manner of contact
  -- §20 Contact: Touch
  | .touch => .minimal              -- (B&KG) no structural entailments
  -- §21 Cutting
  | .cut => .fullSpec               -- (B&KG Ch.4) cutting manner + caused separation
  | .carve => .fullSpec             -- like cut
  -- §22 Combining and Attaching
  | .mix => .causativeResult        -- externally caused combined state
  | .amalgamate => .causativeResult
  -- §23 Separating
  | .separate => .causativeResult   -- externally caused separated state
  | .split => .fullSpec             -- instrument manner + caused separation
  -- §24 Coloring
  | .color => .causativeResult      -- externally caused colored state
  -- §25 Image Creation
  | .imageCreation => .fullSpec     -- etching manner + caused image
  -- §26 Creation and Transformation
  | .build => .causativeResult      -- externally caused creation
  | .grow => .pureResult            -- internally caused growth
  | .create => .causativeResult     -- externally caused creation
  | .knead => .fullSpec             -- kneading manner + caused shape change
  | .turn => .causativeResult       -- externally caused transformation
  | .performance => .pureManner     -- performance manner
  -- §27–28
  | .engender => .causativeResult   -- root entails causation
  | .calve => .pureResult           -- internally caused biological process
  -- §29 Predicative Complements
  | .appoint => .causativeResult    -- externally caused status change
  | .characterize => .minimal       -- (default)
  | .declare => .causativeResult    -- externally caused status change
  -- §30 Perception
  | .see => .minimal                -- (default)
  | .sight => .minimal              -- (default)
  -- §31 Psych-Verbs
  | .amuse => .causativeResult      -- stimulus causes psychological CoS
  | .admire => .propertyConcept     -- psychological state
  | .marvel => .propertyConcept     -- psychological state
  -- §32–34
  | .want => .propertyConcept       -- desiderative state
  | .judgment => .minimal           -- (default)
  | .assessment => .minimal         -- (default)
  -- §35 Searching
  | .search => .pureManner          -- searching manner
  -- §36 Social Interaction
  | .socialInteraction => .minimal  -- (default)
  -- §37 Communication
  | .say => .minimal                -- (default)
  | .tell => .minimal               -- (default)
  | .mannerOfSpeaking => .pureManner -- manner of speaking
  -- §38 Animal Sounds
  | .animalSound => .pureManner     -- specific sound manner
  -- §39 Ingesting
  | .eat => .causativeResult        -- caused consumption, no specific manner
  | .devour => .fullSpec            -- vigorous manner + caused consumption
  | .dine => .pureManner            -- social activity manner
  -- §40 Body
  | .bodyProcess => .minimal        -- (default)
  | .flinch => .minimal             -- (default)
  -- §41 Grooming
  | .dress => .causativeResult      -- externally caused dressed state
  -- §42 Killing
  | .murder => .causativeResult     -- (B&KG) root entails caused death
  | .poison => .fullSpec            -- (B&KG) poisoning manner + caused death (√DROWN-type)
  -- §43 Emission
  | .lightEmission => .propertyConcept  -- emitting state
  | .soundEmission => .propertyConcept
  | .substanceEmission => .propertyConcept
  -- §44 Destroy
  | .destroy => .causativeResult    -- (B&KG) root entails caused total destruction
  -- §45 Change of State
  | .break_ => .causativeResult     -- (B&KG Ch.2,5) √CRACK: externally caused CoS
  | .bend => .causativeResult       -- externally caused shape change
  | .cooking => .fullSpec           -- (B&KG) cooking manner + caused CoS
  | .otherCoS => .causativeResult   -- √MELT/√FREEZE: externally caused CoS
  | .entitySpecificCoS => .pureResult -- √BLOSSOM/√RUST: internally caused
  | .calibratableCoS => .pureResult -- internally driven scalar change
  -- §46 Lodge
  | .lodge => .minimal              -- (default)
  -- §47 Existence
  | .exist => .minimal              -- (B&KG) pure stative, no root content
  -- §48 Appearance
  | .appear => .pureResult          -- internally caused appearance
  -- §49 Body-Internal Motion
  | .bodyInternalMotion => .pureManner -- fidgeting manner
  -- §50 Assuming a Position
  | .assumePosition => .pureResult  -- internally caused position change
  -- §51 Motion
  | .inherentlyDirectedMotion => .pureResult -- internally caused directed motion
  | .leave => .pureResult           -- internally caused departure
  | .mannerOfMotion => .pureManner  -- (B&KG) √JOG: motion manner
  | .vehicleMotion => .pureManner   -- vehicle manner
  | .chase => .pureManner           -- chasing manner
  -- §52 Avoid
  | .avoid => .minimal              -- (default)
  -- §53 Lingering and Rushing
  | .linger => .pureManner          -- temporal manner
  | .rush => .pureManner            -- temporal manner
  -- §54 Measure
  | .measure => .propertyConcept    -- measurement state
  -- §55 Aspectual
  | .aspectual => .minimal          -- (default) template-level
  -- §57 Weather
  | .weather => .minimal            -- (default)

/-! ### Well-formedness verification -/

theorem break_root_wf : (LevinClass.rootEntailments .break_).WellFormed := by decide
theorem cut_root_wf : (LevinClass.rootEntailments .cut).WellFormed := by decide
theorem hit_root_wf : (LevinClass.rootEntailments .hit).WellFormed := by decide
theorem touch_root_wf : (LevinClass.rootEntailments .touch).WellFormed := by decide
theorem give_root_wf : (LevinClass.rootEntailments .give).WellFormed := by decide
theorem destroy_root_wf : (LevinClass.rootEntailments .destroy).WellFormed := by decide
theorem murder_root_wf : (LevinClass.rootEntailments .murder).WellFormed := by decide
theorem poison_root_wf : (LevinClass.rootEntailments .poison).WellFormed := by decide

/-! ### MRC violation verification -/

theorem cut_violates_MRC :
    (LevinClass.rootEntailments .cut).ViolatesMRC := by decide
theorem cooking_violates_MRC :
    (LevinClass.rootEntailments .cooking).ViolatesMRC := by decide
theorem poison_violates_MRC :
    (LevinClass.rootEntailments .poison).ViolatesMRC := by decide
theorem break_respects_MRC :
    ¬ (LevinClass.rootEntailments .break_).ViolatesMRC := by decide
theorem hit_respects_MRC :
    ¬ (LevinClass.rootEntailments .hit).ViolatesMRC := by decide

/-! ### VOC–root entailment theorems -/

/-- Core creation classes have causativeResult root entailments. -/
theorem build_class_causative :
    LevinClass.build.rootEntailments = .causativeResult := rfl
theorem create_class_causative :
    LevinClass.create.rootEntailments = .causativeResult := rfl

-- ════════════════════════════════════════════════════
-- § 2. Root–MC Bridge (@cite{beavers-koontz-garboden-2020})
-- ════════════════════════════════════════════════════

/-! ### Root–MC correspondence (2026 consensus)

The 2026 consensus in lexical semantics (@cite{beavers-koontz-garboden-2020},
@cite{rappaport-hovav-levin-2024}) treats root entailments as primary:
verb behavior at the Levin diagnostic level is determined by root content
plus semantic field membership plus template structure.

But the B&KG root features and the Levin meaning components are NOT
isomorphic — they conceptualize different levels of granularity:

| B&KG concept | Levin concept | Relationship |
|---|---|---|
| `result` | `changeOfState` | B&KG broader: includes location/possession change |
| `manner` | `mannerSpec` ∨ `instrumentSpec` | B&KG broader: includes contact-manner (hit) |
| `cause` | `causation` | Distinct: root-level vs event-level causation |

The three `*Kind` enums below name the specific cases where the two
frameworks diverge, making the divergences grep-able and testable. -/

/-- Where a verb class's event-level causation originates.

    B&KG's root-level `cause` and Levin's event-level `causation` are
    distinct concepts (@cite{beavers-koontz-garboden-2020} Ch. 5;
    @cite{levin-1993} pp. 9–10). -/
inductive CausationSource where
  | rootExternal
  | rootNonDetachable
  | template
  | none
  deriving DecidableEq, Repr

/-- Derive the causation source from root entailments and meaning components. -/
def LevinClass.causationSource (c : LevinClass) : CausationSource :=
  let re := c.rootEntailments
  let mc := c.meaningComponents
  if re.cause then
    if mc.causation then .rootExternal else .rootNonDetachable
  else
    if mc.causation then .template else .none

/-- What kind of result the root entails (refines B&KG `result`).

    Levin's `changeOfState` corresponds to `stateChange` only —
    change of location (throw, arrive) and change of possession (give)
    have `result = true` in B&KG but `changeOfState = false` in Levin. -/
inductive ResultKind where
  | stateChange
  | locationChange
  | possessionChange
  | none
  deriving DecidableEq, Repr

/-- Derive result kind from root entailments and meaning components. -/
def LevinClass.resultKind (c : LevinClass) : ResultKind :=
  let re := c.rootEntailments
  let mc := c.meaningComponents
  if !re.result then .none
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

/-- Derive manner kind from root entailments and meaning components. -/
def LevinClass.mannerKind (c : LevinClass) : MannerKind :=
  let re := c.rootEntailments
  let mc := c.meaningComponents
  if !re.manner then .none
  else if mc.instrumentSpec then .instrumentSpec
  else if mc.mannerSpec then .mannerSpec
  else .unspecified

/-! #### Causation source verification -/

theorem break_causation_rootExternal :
    LevinClass.causationSource .break_ = .rootExternal := rfl
theorem destroy_causation_rootExternal :
    LevinClass.causationSource .destroy = .rootExternal := rfl
theorem murder_causation_rootExternal :
    LevinClass.causationSource .murder = .rootExternal := rfl
theorem eat_causation_rootNonDetachable :
    LevinClass.causationSource .eat = .rootNonDetachable := rfl
theorem devour_causation_rootNonDetachable :
    LevinClass.causationSource .devour = .rootNonDetachable := rfl
theorem put_causation_template :
    LevinClass.causationSource .put = .template := rfl
theorem send_causation_template :
    LevinClass.causationSource .send = .template := rfl
theorem grow_causation_template :
    LevinClass.causationSource .grow = .template := rfl
theorem hit_causation_none :
    LevinClass.causationSource .hit = .none := rfl
theorem mannerOfMotion_causation_none :
    LevinClass.causationSource .mannerOfMotion = .none := rfl

/-! #### Result kind verification -/

theorem break_result_stateChange :
    LevinClass.resultKind .break_ = .stateChange := rfl
theorem destroy_result_stateChange :
    LevinClass.resultKind .destroy = .stateChange := rfl
theorem throw_result_locationChange :
    LevinClass.resultKind .throw = .locationChange := rfl
theorem inherentlyDirectedMotion_result_locationChange :
    LevinClass.resultKind .inherentlyDirectedMotion = .locationChange := rfl
theorem leave_result_locationChange :
    LevinClass.resultKind .leave = .locationChange := rfl
theorem give_result_possessionChange :
    LevinClass.resultKind .give = .possessionChange := rfl
theorem hit_result_none :
    LevinClass.resultKind .hit = .none := rfl

/-! #### Manner kind verification -/

theorem cooking_manner_mannerSpec :
    LevinClass.mannerKind .cooking = .mannerSpec := rfl
theorem mannerOfMotion_manner_mannerSpec :
    LevinClass.mannerKind .mannerOfMotion = .mannerSpec := rfl
theorem cut_manner_instrumentSpec :
    LevinClass.mannerKind .cut = .instrumentSpec := rfl
theorem poke_manner_instrumentSpec :
    LevinClass.mannerKind .poke = .instrumentSpec := rfl
theorem hit_manner_unspecified :
    LevinClass.mannerKind .hit = .unspecified := rfl
theorem pushPull_manner_unspecified :
    LevinClass.mannerKind .pushPull = .unspecified := rfl
theorem break_manner_none :
    LevinClass.mannerKind .break_ = .none := rfl

/-! ### Root-structural MC contribution -/

/-- Root structural contribution to meaning components.
    Maps result → changeOfState and manner → mannerSpec. -/
def RootEntailments.structuralMC (re : RootEntailments) : MeaningComponents :=
  { changeOfState := re.result
  , contact := false
  , motion := false
  , causation := false
  , instrumentSpec := false
  , mannerSpec := re.manner }

/-! ### Universal consistency theorems

These hold for ALL 78 LevinClass constructors and are proved by
exhaustive case analysis. -/

/-- Levin spec implies B&KG manner. -/
theorem levin_spec_implies_bkg_manner (c : LevinClass) :
    c.meaningComponents.mannerSpec = true ∨ c.meaningComponents.instrumentSpec = true →
    c.rootEntailments.manner = true := by
  cases c <;> decide

/-- CausativeResult roots always have changeOfState. -/
theorem causativeResult_always_cos (c : LevinClass) :
    c.rootEntailments = .causativeResult →
    c.meaningComponents.changeOfState = true := by
  cases c <;> decide

/-- Root cause implies either event causation or non-detachable causation. -/
theorem root_cause_accounted_for (c : LevinClass) :
    c.rootEntailments.cause = true →
    c.meaningComponents.causation = true ∨
    c.causationSource = .rootNonDetachable := by
  cases c <;> decide

end Core.Verbs
