import Linglib.Core.Valence
import Linglib.Semantics.ArgumentStructure.EntailmentProfile
import Linglib.Semantics.Presupposition.Basic
import Linglib.Features.Aktionsart
import Linglib.Features.Attitudes
import Linglib.Features.Causation
import Linglib.Semantics.Lexical.LevinClass
import Linglib.Core.Logic.NaturalLogic
import Linglib.Semantics.Aspect.ChangeOfState
import Linglib.Semantics.Causation.Implicative
import Linglib.Semantics.ArgumentStructure.Linking
import Linglib.Semantics.Causation.Psych
import Linglib.Semantics.Aspect.DegreeAchievement
import Linglib.Semantics.Aspect.Incremental
import Linglib.Semantics.Lexical.LevinClassProfiles

/-! # Verb entry — core type

Framework-agnostic types for verb semantics: the selectional/inflectional enums
(`ComplementType`, `VoiceType`, …) and the `Verb` structure that bundles the
semantic fields shared across languages.

`Verb` is the **semantic spine** of a verb entry. Its fields are organised
into facet structures under the `Verb` namespace — `Verb.ArgStructure`,
`Verb.Aspect`, `Verb.Presupposition`, `Verb.Causation`, `Verb.Attitude`,
`Verb.Root` — which `Verb` composes via `extends`. Flat field access
(`v.complementType`, `v.attitude`, …) is preserved by `extends`-flattening, and
language fragments extend `Verb` with their own inflectional paradigms.

Verb classification (factive, causative, attitude, …) is DERIVED from these
primitive fields in `Semantics/Verb/Basic.lean`, not stipulated as an enum.

## Main declarations
* `Verb` — the composed verb entry spine
* `Verb.ArgStructure`, `Verb.Aspect`, `Verb.Presupposition`, `Verb.Causation`,
  `Verb.Attitude`, `Verb.Root` — the field facets

## Design
@cite{bale-schwarz-2026} @cite{dayal-2025} @cite{heim-1992} @cite{icard-2012} @cite{kennedy-2007} @cite{maier-2015} @cite{qing-uegaki-2025} @cite{rappaport-hovav-levin-2024} @cite{solstad-bott-2024} @cite{rappaport-hovav-levin-1998}
-/

open Semantics.Presupposition
open Features
open Semantics.Lexical
open Semantics.Lexical.Roots
open Features.ChangeOfState
open Core.NaturalLogic (EntailmentSig)
open Semantics.Causation.Psych (CausalSource)
open Semantics.ArgumentStructure.EntailmentProfile (EntailmentProfile)
open Features.DegreeAchievement (DegreeAchievementScale)
open Semantics.Aspect.Incremental (VerbIncClass)
open Features.LevinClassProfiles

/-! ### Selectional and inflectional enums -/

/-- Framework-neutral voice type for deriving argument structure properties.

    Captures the external-argument dimension of the verb's syntactic frame
    without committing to a specific syntactic framework. Maps to
    `Minimalist.VoiceFlavor` via bridge theorems in interface files.

    - `agentive`: External argument introduced (transitive/unergative)
    - `nonThematic`: No external argument (unaccusative/anticausative)
    - `expletive`: No specifier, no semantics (middle voice)
    - `reflexive`: Agent that binds internal argument (@cite{wood-2015})
    - `experiencer`: Experiencer external argument (@cite{wood-2015}) -/
inductive VoiceType where
  | agentive     -- External argument introduced
  | nonThematic  -- No external argument (unaccusative)
  | expletive    -- No specifier, no semantics (middle)
  | reflexive    -- Agent binds internal argument (@cite{wood-2015})
  | experiencer  -- Experiencer external argument (@cite{wood-2015})
  deriving DecidableEq, Repr

/-- Does this voice type introduce an external argument? -/
def VoiceType.assignsTheta : VoiceType → Bool
  | .agentive | .reflexive | .experiencer => true
  | .nonThematic | .expletive => false

/--
Presupposition trigger type (@cite{tonhauser-beaver-roberts-simons-2013} classification).

- Hard triggers: Always project (too, again, also)
- Soft triggers: Context-sensitive projection (stop, know)
-/
inductive PresupTriggerType where
  | hardTrigger        -- Projective in all contexts
  | softTrigger        -- Factive: complement truth presupposed, locally accommodatable
  | prerequisiteSoft   -- Prerequisite: causal prerequisite presupposed (@cite{nadathur-2024})
  deriving DecidableEq, Repr

/-- Is this trigger locally accommodatable (soft)?
    Both factive and prerequisite triggers are soft. -/
def PresupTriggerType.isSoft : PresupTriggerType → Bool
  | .hardTrigger => false
  | .softTrigger => true
  | .prerequisiteSoft => true

/--
Complement presupposition projection behavior (@cite{karttunen-1973}).

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
  | occasion      -- Occasion verb sense (@cite{solstad-bott-2024}): agent-evocator subject
  | stative       -- Stative reading of a polysemous verb (e.g., *suivre* 'follow' positional)
  deriving DecidableEq, Repr

/--
Complement type that the verb selects.

- Finite: "that" clauses ("John knows that Mary left")
- Infinitival: "to" complements ("John managed to leave")
- Gerund: "-ing" complements ("John stopped smoking")
- NP: Direct object ("John kicked the ball")
- None: Intransitive ("John slept")
-/
inductive ComplementType where
  | none            -- Intransitive
  | np              -- Transitive with NP object
  | np_np           -- Ditransitive: "give X Y"
  | np_pp           -- NP + PP: "put X on Y"
  | finiteClause    -- "that" clause
  | infinitival     -- "to" VP
  | gerund          -- "-ing" VP
  | smallClause     -- "consider X happy"
  | question        -- Embedded question "wonder who"
  deriving DecidableEq, Repr

/-- Is this complement type finite (i.e., does it contain a tense head)?

    Finite complements (.finiteClause,.question) have independent tense
    morphology; non-finite complements (.infinitival,.gerund,.smallClause)
    do not. -/
def ComplementType.isFinite : ComplementType → Bool
  | .finiteClause | .question => true
  | _ => false

/-- Is this complement type a nominal (DP) argument?

    Nominal complements project DP: the verb selects a noun phrase
    in object position. Relevant to c-selection in coordination:
    a verb that only selects nominal complements cannot independently
    license a CP conjunct (@cite{schwarzer-2026}). -/
def ComplementType.isNominal : ComplementType → Bool
  | .np | .np_np | .np_pp => true
  | _ => false

/-- Is this complement type a clausal (CP) argument?

    Clausal complements project CP or reduced clausal structure.
    This covers finite clauses (*dass*-clauses), infinitivals,
    gerunds, small clauses, and embedded questions. -/
def ComplementType.isClausal : ComplementType → Bool
  | .finiteClause | .infinitival | .gerund | .smallClause | .question => true
  | _ => false

/--
Control type for verbs with infinitival complements.
-/
inductive ControlType where
  | subjectControl  -- "John tried to leave" (John = leaver)
  | objectControl   -- "John persuaded Mary to leave" (Mary = leaver)
  | raising         -- "John seems to be happy" (no theta role for matrix subject)
  | none            -- Not applicable
  deriving DecidableEq, Repr

/-- Interpretation of an implicit (unexpressed) argument.

    Cross-linguistic: applies to any argument position where the verb allows
    the argument to be absent. The distinction captures whether the missing
    referent must be pragmatically recoverable (definite) or can be
    unspecified (indefinite). @cite{bruening-2021}, @cite{fillmore-1986}. -/
inductive ImplicitInterp where
  | indef   -- Existentially bound: unspecified "someone/something"
  | def     -- Pragmatically recoverable definite
  deriving DecidableEq, Repr

/-- Map complement type to syntactic valence.
    Clause-embedding types (.finiteClause,.infinitival,.gerund,.question,
.smallClause) map to `.clausal` — they take xcomp/ccomp, not obj.
    `checkVerbSubcat` skips `.clausal` verbs (their frames require
    different validation than NP-argument counting). -/
def complementToValence : ComplementType → Valence
  | .none => .intransitive
  | .np => .transitive
  | .np_np => .ditransitive
  | .np_pp => .locative
  | _ => .clausal

/-! ### Field facets

Each facet groups a concern's fields; `Verb` composes them via `extends`,
so flat access (`v.complementType`) is preserved. -/

namespace Verb

/-- Argument structure and realization: complement selection, control,
    proto-role entailments, voice, and implicit arguments. -/
structure ArgStructure where
  /-- What complement does the verb select? -/
  complementType : ComplementType
  /-- Proto-role entailment profile for the subject (external argument).
      The authoritative representation of argument semantics
      (@cite{dowty-1991}, @cite{grimm-2011}, @cite{levin-2019}).
      Convenience role labels can be derived via `EntailmentProfile.toRole`. -/
  subjectEntailments : Option EntailmentProfile := none
  /-- Proto-role entailment profile for the first object (internal argument). -/
  objectEntailments : Option EntailmentProfile := none
  /-- Control type for infinitival complements -/
  controlType : ControlType := .none
  /-- Alternate complement frame, for verbs with two complement types.
      E.g., "hope" primarily takes.finiteClause ("hope that...") but
      also takes.infinitival ("hope to...") with subject control.
      When set, `altControlType` specifies the control type for this frame. -/
  altComplementType : Option ComplementType := none
  /-- Control type for the alternate complement frame. -/
  altControlType : ControlType := .none
  /-- Is the verb unaccusative? (subject is underlying object)
      When `voiceType` is present, prefer `derivedUnaccusative` which
      derives this from Voice selection (@cite{kratzer-1996}). -/
  unaccusative : Bool := false
  /-- Framework-neutral voice type: determines whether an external argument
      is introduced. When set, `derivedUnaccusative` derives unaccusativity
      from this field, connecting the Fragment entry to Voice theory. -/
  voiceType : Option VoiceType := none
  /-- Can the verb passivize? -/
  passivizable : Bool := true
  /-- Can the direct object (theme/patient) be left unexpressed?
      Applies to monotransitives (*eat* vs *devour*) and the theme of
      ditransitives. `none` = object always required. @cite{bruening-2021} -/
  implicitObj : Option ImplicitInterp := none
  /-- Can the goal/recipient argument be left unexpressed?
      Applies to the IO of double object constructions and the PP
      of dative frames. `none` = goal always required. -/
  implicitGoal : Option ImplicitInterp := none
  deriving Repr, BEq

/-- Aspectual class: Vendler class, degree-achievement scale, incrementality,
    and change-of-state type. -/
structure Aspect where
  /-- @cite{vendler-1957} aspectual class of the verb's base VP.
      For verbs whose class depends on the object NP (eat apples = activity,
      eat two apples = accomplishment), record the class with a quantized
      (bounded) object. `none` for verbs where Vendler class is inapplicable
      (e.g., clause-embedding verbs). -/
  vendlerClass : Option VendlerClass := none
  /-- For degree achievements: the scale structure from
      which default vendlerClass is derived. When present, vendlerClass should
      agree with degreeAchievementScale.defaultVendlerClass. -/
  degreeAchievementScale : Option DegreeAchievementScale := none
  /-- @cite{krifka-1998} incrementality class of the object/theme role.
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
      Orthogonal to `presupType`. @cite{karttunen-1973} -/
  projectionBehavior : Option ProjectionBehavior := none
  deriving Repr, BEq

/-- Causal/implicative semantics: implicative polarity, causative mechanism,
    and psych-causative source. -/
structure Causation where
  /-- For implicative verbs: complement entailment polarity (links to compositional semantics). -/
  implicative : Option Implicative := none
  /-- For causative verbs: force-dynamic mechanism (links to compositional semantics). -/
  causative : Option Causative := none
  /-- Source of causation for psych causatives (@cite{kim-2024} UPH).
      `.external` = mind-external percept, `.internal` = mind-internal representation. -/
  causalSource : Option CausalSource := none
  deriving Repr, BEq

/-- Attitudinal and intensional properties: attitude classification, opacity,
    question-embedding, and complement monotonicity. -/
structure Attitude where
  /-- Does the verb create an opaque context for its complement? -/
  opaqueContext : Bool := false
  /-- Unified attitude classification covering doxastic and preferential attitudes.
      Theoretical properties (C-distributivity, parasitic, etc.) are DERIVED. -/
  attitude : Option Features.Attitude := none
  /-- For non-preferential question-embedding verbs (know, wonder, ask) -/
  takesQuestionBase : Bool := false
  /-- Entailment signature of the complement position.
      Classifies this verb's monotonicity w.r.t. its clausal complement.
      `.mono` = upward monotone (believe, know); `.mult` = multiplicative only
      (be surprised). Used to derive conjunction distribution and neg-raising.
      See @cite{bondarenko-elliott-2026}. -/
  complementSig : Option EntailmentSig := none
  deriving Repr, BEq

/-- Root content: Levin class and root-specific quality profile
    (@cite{levin-1993}; @cite{spalek-mcnally-2026}). -/
structure Root where
  /-- @cite{levin-1993} verb class (§§ 9–57). -/
  levinClass : Option LevinClass := none
  /-- Root-specific quality dimensions (within-class variation). -/
  rootProfile : Option RootProfile := none
  deriving Repr, BEq

end Verb

/--
Cross-linguistic verb core: all semantic fields shared across languages.

Composes the `Verb.*` facets (argument structure, aspect, presupposition,
causation, attitude, root) plus the citation form, speech-act status, and a
polysemy disambiguator. Language-specific fragments extend this with
morphological fields appropriate to their inflectional system.
-/
structure Verb extends
    Verb.ArgStructure, Verb.Aspect, Verb.Presupposition,
    Verb.Causation, Verb.Attitude, Verb.Root where
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
