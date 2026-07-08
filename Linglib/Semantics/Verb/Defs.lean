import Linglib.Features.Complementation
import Linglib.Syntax.Clause.Frame
import Linglib.Semantics.ArgumentStructure.EntailmentProfile
import Linglib.Semantics.Presupposition.Basic
import Linglib.Features.Aktionsart
import Linglib.Features.Attitudes
import Linglib.Features.Causation
import Linglib.Semantics.ArgumentStructure.LevinClass
import Linglib.Semantics.NaturalLogic
import Linglib.Semantics.Aspect.ChangeOfState
import Linglib.Semantics.Causation.Implicative
import Linglib.Semantics.ArgumentStructure.Linking
import Linglib.Semantics.Causation.Psych
import Linglib.Semantics.Aspect.DegreeAchievement
import Linglib.Semantics.Aspect.Incremental
import Linglib.Semantics.ArgumentStructure.LevinClassProfiles
import Linglib.Semantics.Verb.Root.Basic
import Linglib.Semantics.Verb.Root.Profile

/-! # Verb entry — core type

Framework-agnostic types for verb semantics: the selectional/inflectional enums
(`VoiceType`, `SenseTag`, …; complementation enums live in
`Features/Complementation.lean`) and the `Verb` structure that bundles the
semantic fields shared across languages.

`Verb` is the **semantic spine** of a verb entry. Its fields are organised
into facet structures under the `Verb` namespace — `Verb.ArgStructure`,
`Verb.Aspect`, `Verb.Presupposition`, `Verb.Causation`, `Verb.Attitude`
— which `Verb` composes via `extends`. Flat field access
(`v.frames`, `v.attitude`, …) is preserved by `extends`-flattening, and
language fragments extend `Verb` with their own inflectional paradigms.
Complement selection is a list of typed `Frame`s
(`Syntax/Clause/Frame.lean`); frame-conditioned
attitude/opacity/control lives on `Verb.Reading` rows; the legacy flat
readers (`v.complementType`, `v.controlType`, …) are derived accessors
over `frames`/`readings`.

Verb classification (factive, causative, attitude, …) is DERIVED from these
primitive fields in `Semantics/Verb/Basic.lean`, not stipulated as an enum.

## Main declarations
* `Verb` — the composed verb entry spine
* `Verb.ArgStructure`, `Verb.Aspect`, `Verb.Presupposition`, `Verb.Causation`,
  `Verb.Attitude` — the field facets

## Design
[bale-schwarz-2026] [dayal-2025] [heim-1992] [icard-2012] [kennedy-2007] [maier-2015] [qing-uegaki-2025] [rappaport-hovav-levin-2024] [solstad-bott-2024] [rappaport-hovav-levin-1998]
-/

open Semantics.Presupposition
open Features
open ArgumentStructure
open Features.ChangeOfState
open NaturalLogic (EntailmentSig)
open Causation.Psych (CausalSource)
open ArgumentStructure (EntailmentProfile)
open Features.DegreeAchievement (DegreeAchievementScale)
open Semantics.Aspect.Incremental (VerbIncClass)
open ArgumentStructure

/-! ### Selectional and inflectional enums -/

/-- Framework-neutral voice type for deriving argument structure properties.

    Captures the external-argument dimension of the verb's syntactic frame
    without committing to a specific syntactic framework. Maps to
    `Minimalist.Voice.Flavor` via bridge theorems in interface files.

    - `agentive`: External argument introduced (transitive/unergative)
    - `nonThematic`: No external argument (unaccusative/anticausative)
    - `expletive`: No specifier, no semantics (middle voice)
    - `reflexive`: Agent that binds internal argument ([wood-2015])
    - `experiencer`: Experiencer external argument ([wood-2015]) -/
inductive VoiceType where
  | agentive     -- External argument introduced
  | nonThematic  -- No external argument (unaccusative)
  | expletive    -- No specifier, no semantics (middle)
  | reflexive    -- Agent binds internal argument ([wood-2015])
  | experiencer  -- Experiencer external argument ([wood-2015])
  deriving DecidableEq, Repr

/-- Does this voice type introduce an external argument? -/
def VoiceType.assignsTheta : VoiceType → Bool
  | .agentive | .reflexive | .experiencer => true
  | .nonThematic | .expletive => false

/--
Presupposition trigger type ([tonhauser-beaver-roberts-simons-2013] classification).

- Hard triggers: Always project (too, again, also)
- Soft triggers: Context-sensitive projection (stop, know)
-/
inductive PresupTriggerType where
  | hardTrigger        -- Projective in all contexts
  | softTrigger        -- Factive: complement truth presupposed, locally accommodatable
  | prerequisiteSoft   -- Prerequisite: causal prerequisite presupposed ([nadathur-2023-implicatives])
  deriving DecidableEq, Repr

/-- Is this trigger locally accommodatable (soft)?
    Both factive and prerequisite triggers are soft. -/
def PresupTriggerType.isSoft : PresupTriggerType → Bool
  | .hardTrigger => false
  | .softTrigger => true
  | .prerequisiteSoft => true

/--
Complement presupposition projection behavior ([karttunen-1973]).

Orthogonal to `PresupTriggerType` (whether the verb *triggers* presuppositions):
this classifies what the verb does with presuppositions *of its complement*.

- `plug`: blocks all complement presuppositions (*say*, *tell*, *promise*)
- `hole`: lets all complement presuppositions project (*know*, *regret*, *stop*)
- `filter`: conditionally cancels some complement presuppositions (*if...then*, *and*, *or*)
-/
inductive ProjectionBehavior where
  | plug    -- Blocks complement presuppositions
  | hole    -- Passes complement presuppositions through
  | filter  -- Conditionally cancels complement presuppositions
  deriving DecidableEq, Repr

/--
Disambiguates polysemous verb entries that share a citation form.

When a verb has multiple lexical entries (e.g., "remember" as implicative
vs. "remember" as factive question-embedding), the `SenseTag` records
*why* multiple entries exist:
- `.default`: primary/unmarked sense
- `.rogative`: question-embedding sense
- `.causative`: causative use of otherwise non-causative verb
- `.instrumental`: instrument-specific sense
- `.occasion`: occasion verb sense with experiencer subject
-/
inductive SenseTag where
  | default       -- Primary/unmarked sense
  | rogative      -- Question-embedding sense
  | causative     -- Causative use of otherwise non-causative verb
  | instrumental  -- Instrument-specific sense
  | occasion      -- Occasion verb sense ([solstad-bott-2024]): agent-evocator subject
  | stative       -- Stative reading of a polysemous verb (e.g., *suivre* 'follow' positional)
  deriving DecidableEq, Repr

/-- Interpretation of an implicit (unexpressed) argument.

    Cross-linguistic: applies to any argument position where the verb allows
    the argument to be absent. The distinction captures whether the missing
    referent must be pragmatically recoverable (definite) or can be
    unspecified (indefinite). [bruening-2021], [fillmore-1986]. -/
inductive ImplicitInterp where
  | indef   -- Existentially bound: unspecified "someone/something"
  | def     -- Pragmatically recoverable definite
  deriving DecidableEq, Repr

/-! ### Field facets

Each facet groups a concern's fields; `Verb` composes them via `extends`,
so flat access (`v.complementType`) is preserved. -/

namespace Verb

/-- Argument structure and realization: complement selection, control,
    proto-role entailments, voice, and implicit arguments. -/
structure ArgStructure where
  /-- Complement frames, citation frame first. `[]` for intransitives.
      The legacy `ComplementType` cells are the `Frame.np`,
      `Frame.finiteClause`, … smart constructors
      (`Syntax/Clause/Frame.lean`). -/
  frames : List Frame
  /-- Proto-role entailment profile for the subject (external argument).
      The authoritative representation of argument semantics
      ([dowty-1991], [grimm-2011], [levin-2019]).
      Convenience role labels can be derived via `EntailmentProfile.toRole`. -/
  subjectEntailments : Option EntailmentProfile := none
  /-- Proto-role entailment profile for the first object (internal argument). -/
  objectEntailments : Option EntailmentProfile := none
  /-- Is the verb unaccusative? (subject is underlying object)
      When `voiceType` is present, prefer `derivedUnaccusative` which
      derives this from Voice selection ([kratzer-1996]). -/
  unaccusative : Bool := false
  /-- Framework-neutral voice type: determines whether an external argument
      is introduced. When set, `derivedUnaccusative` derives unaccusativity
      from this field, connecting the Fragment entry to Voice theory. -/
  voiceType : Option VoiceType := none
  /-- Can the verb passivize? -/
  passivizable : Bool := true
  /-- Can the direct object (theme/patient) be left unexpressed?
      Applies to monotransitives (*eat* vs *devour*) and the theme of
      ditransitives. `none` = object always required. [bruening-2021] -/
  implicitObj : Option ImplicitInterp := none
  /-- Can the goal/recipient argument be left unexpressed?
      Applies to the IO of double object constructions and the PP
      of dative frames. `none` = goal always required. -/
  implicitGoal : Option ImplicitInterp := none
  deriving Repr, BEq

/-- Aspectual class: Vendler class, degree-achievement scale, incrementality,
    and change-of-state type. -/
structure Aspect where
  /-- [vendler-1957] aspectual class of the verb's base VP.
      For verbs whose class depends on the object NP (eat apples = activity,
      eat two apples = accomplishment), record the class with a quantized
      (bounded) object. `none` for verbs where Vendler class is inapplicable
      (e.g., clause-embedding verbs). -/
  vendlerClass : Option VendlerClass := none
  /-- For degree achievements: the scale structure from
      which default vendlerClass is derived. When present, vendlerClass should
      agree with degreeAchievementScale.defaultVendlerClass. -/
  degreeAchievementScale : Option DegreeAchievementScale := none
  /-- [krifka-1998] incrementality class of the object/theme role.
      `.sinc` = strictly incremental (eat, build); `.inc` = incremental
      with backups (read); `.cumOnly` = cumulative only (push, carry).
      `none` for intransitives and clause-embedding verbs. -/
  verbIncClass : Option VerbIncClass := none
  /-- For CoS verbs: which type (cessation, inception, continuation)? -/
  cosType : Option CoSType := none
  deriving Repr, BEq

/-- Presupposition profile: trigger type and complement-projection behavior. -/
structure Presupposition where
  /-- Is the verb a presupposition trigger? -/
  presupType : Option PresupTriggerType := none
  /-- How does the verb treat presuppositions of its complement?
      Orthogonal to `presupType`. [karttunen-1973] -/
  projectionBehavior : Option ProjectionBehavior := none
  deriving Repr, BEq

/-- Causal/implicative semantics: implicative polarity, causative mechanism,
    and psych-causative source. -/
structure Causation where
  /-- For implicative verbs: complement entailment polarity (links to compositional semantics). -/
  implicative : Option Implicative := none
  /-- For causative verbs: force-dynamic mechanism (links to compositional semantics). -/
  causative : Option Causative := none
  /-- Source of causation for psych causatives ([kim-2024] UPH).
      `.external` = mind-external percept, `.internal` = mind-internal representation. -/
  causalSource : Option CausalSource := none
  deriving Repr, BEq

/-- One frame-conditioned reading of a verb ([bondarenko-2022] §4.4.3
    *hanaxa*; Greek *thimame*): per-frame overrides of the lexeme-level
    attitude and opacity (`none` = inherit `Verb.attitude` /
    `Verb.opaqueContext`), and the frame's control type. -/
structure Reading where
  /-- The frame this reading is conditioned on (one of the verb's
      `frames`; `Verb.readingsWF`). -/
  frame : Frame
  /-- Frame-conditioned attitude override. -/
  attitude : Option Features.Attitude := none
  /-- Frame-conditioned opacity override. -/
  opaqueContext : Option Bool := none
  /-- Control type for this frame. -/
  control : Option ControlType := none
  deriving DecidableEq, Repr

/-- Attitudinal and intensional properties: attitude classification, opacity,
    question-embedding, and complement monotonicity. -/
structure Attitude where
  /-- Does the verb create an opaque context for its complement? -/
  opaqueContext : Bool := false
  /-- Unified attitude classification covering doxastic and preferential attitudes.
      Theoretical properties (C-distributivity, parasitic, etc.) are DERIVED. -/
  attitude : Option Features.Attitude := none
  /-- Frame-conditioned readings ([bondarenko-2022] §4.4.3): per-frame
      attitude/opacity overrides and control, keyed to `frames` entries. -/
  readings : List Reading := []
  /-- For non-preferential question-embedding verbs (know, wonder, ask) -/
  takesQuestionBase : Bool := false
  /-- Entailment signature of the complement position.
      Classifies this verb's monotonicity w.r.t. its clausal complement.
      `.mono` = upward monotone: the report is closed under entailment of
      the complement, as in Hintikka-style doxastic semantics
      ([hintikka-1962]). Set only where the classification is textbook
      consensus (believe, think, know); preferential attitudes (want, hope)
      are contested ([heim-1992]) and stay `none`. -/
  complementSig : Option EntailmentSig := none
  deriving Repr, BEq

end Verb

section
-- Open the `Verb` namespace so the `root` field below resolves `Root` as
-- `Verb.Root`: inside the `structure Verb` body the `Verb` *type* shadows the
-- `Verb` *namespace*, so a bare `Verb.Root` mis-parses as a field projection.
open _root_.Verb
/--
Cross-linguistic verb core: all semantic fields shared across languages.

Composes the `Verb.*` facets (argument structure, aspect, presupposition,
causation, attitude, root) plus the citation form, speech-act status, and a
polysemy disambiguator. Language-specific fragments extend this with
morphological fields appropriate to their inflectional system.
-/
structure Verb extends
    Verb.ArgStructure, Verb.Aspect, Verb.Presupposition,
    Verb.Causation, Verb.Attitude where
  /-- [levin-1993] verb class (§§ 9–57). -/
  levinClass : Option LevinClass := none
  /-- The verb's lexical root — its entailment atoms, derived B&KG kind
      signature, and [bhadra-2024] outcome axis. The content carrier the Verb
      API integrates around (P-HUB): the verb's signature / outcome / change-type
      are read off *this* root rather than the `levinClass` table. Total, with
      the trivial root `{}` (no annotation) as the `⊥`. -/
  root : Root := {}
  /-- Citation form (cross-linguistic) -/
  form : String
  /-- Does the verb denote the performance of an illocutionary act?
      True for speech-act verbs (say, tell, claim, ask). This is a genuine
      semantic primitive that cannot be derived from other fields. -/
  speechActVerb : Bool := false
  /-- Disambiguates entries that share a citation form.
      Most verbs use `.default`; polysemous entries use descriptive tags. -/
  senseTag : SenseTag := .default
  deriving Repr, BEq

end

/-! ### Frame accessors

Flat readers over `Verb.frames`/`Verb.readings`, preserving the legacy
enum-based call syntax: the citation frame's complement/control type and
the alternate frame's, when present. -/

/-- The citation (first) frame's legacy `ComplementType` cell. -/
def Verb.complementType (v : Verb) : ComplementType :=
  (v.frames.head?.bind Frame.toComplementType).getD .none

/-- The alternate (second) frame's legacy `ComplementType` cell. -/
def Verb.altComplementType (v : Verb) : Option ComplementType :=
  v.frames[1]?.bind Frame.toComplementType

/-- The control type of the reading keyed to the citation frame. -/
def Verb.controlType (v : Verb) : ControlType :=
  (v.frames.head?.bind fun fr =>
    (v.readings.find? (·.frame == fr)).bind (·.control)).getD .none

/-- The control type of the reading keyed to the alternate frame. -/
def Verb.altControlType (v : Verb) : ControlType :=
  (v.frames[1]?.bind fun fr =>
    (v.readings.find? (·.frame == fr)).bind (·.control)).getD .none

/-- The effective attitude on frame `fr`: reading override, else lexeme
    default. -/
def Verb.attitudeOn (v : Verb) (fr : Frame) : Option Features.Attitude :=
  ((v.readings.find? (·.frame == fr)).bind (·.attitude)).orElse
    fun _ => v.attitude

/-- Every reading is keyed to one of the verb's frames. -/
def Verb.readingsWF (v : Verb) : Prop :=
  ∀ r ∈ v.readings, r.frame ∈ v.frames

/-- All [noonan-2007] codings across the verb's frames. -/
def Verb.codings (v : Verb) : List NoonanCompType :=
  v.frames.flatMap Frame.codings

/-- Some frame of the verb records clause form `cf`. -/
def Verb.takesClauseForm (v : Verb) (cf : Features.ClauseForm) : Prop :=
  ∃ fr ∈ v.frames, fr.hasClauseForm cf
