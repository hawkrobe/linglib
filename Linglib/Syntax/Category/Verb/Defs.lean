import Linglib.Syntax.Clause.Complementation
import Linglib.Syntax.Category.Verb.ArgumentFrame.Basic
import Linglib.Semantics.ArgumentStructure.EntailmentProfile
import Linglib.Semantics.Presupposition.Basic
import Linglib.Semantics.Presupposition.TriggerTypology
import Linglib.Semantics.Aspect.Basic
import Linglib.Semantics.Attitudes.Basic
import Linglib.Semantics.Causation.VerbClass
import Linglib.Semantics.ArgumentStructure.LevinClass
import Linglib.Logic.Natural.Basic
import Linglib.Semantics.Aspect.ChangeOfState
import Linglib.Semantics.Causation.Implicative
import Linglib.Semantics.ArgumentStructure.Linking
import Linglib.Semantics.Causation.Psych
import Linglib.Semantics.Aspect.DegreeAchievement
import Linglib.Semantics.Aspect.Incremental
import Linglib.Semantics.ArgumentStructure.RoleList
import Linglib.Semantics.Root.Defs

/-! # Verb entry — core type

The framework-neutral verb entry: the selectional and inflectional enums (`VoiceType`,
`SenseTag`) and the `Verb` structure, whose fields are grouped into the
facets `Verb.ArgStructure`, `Verb.Aspect`, `Verb.Presupposition`, `Verb.Causation` and
`Verb.Attitude` and shared by every language's fragment. Complement selection is a list of
typed frames, and a frame-conditioned attitude, opacity or control lives on a `Verb.Reading`
row. The classifications of an entry, factive, causative, trigger and so on, are read off
these fields in `Syntax/Category/Verb/Basic.lean`.

## Implementation notes

* `Verb` composes its facets by `extends`, so a field is reached flat, as `v.frames`, and a
  language fragment extends `Verb` with its inflectional paradigm.
* The facets share their names with the theory namespaces whose values they hold, so a
  facet field names its type with `_root_`.

## References

* [bale-schwarz-2026]
* [dayal-2025]
* [heim-1992]
* [icard-2012]
* [kennedy-2007]
* [maier-2015]
* [qing-uegaki-2025]
* [rappaport-hovav-levin-2024]
* [rappaport-hovav-levin-1998]
* [solstad-bott-2024]
-/

open Aspect ArgumentStructure Presupposition
open NaturalLogic (Signature)
open Causation.Psych (CausalSource)

/-! ### Selectional and inflectional enums -/

/-- The external-argument dimension of a verb's frame, neutral between syntactic frameworks. -/
inductive VoiceType where
  /-- An external argument is introduced: transitives and unergatives. -/
  | agentive
  /-- No external argument: unaccusatives and anticausatives. -/
  | nonThematic
  /-- No specifier and no semantics: the middle voice. -/
  | expletive
  /-- An agent that binds the internal argument ([wood-2015]). -/
  | reflexive
  /-- An experiencer external argument ([wood-2015]). -/
  | experiencer
  deriving DecidableEq, Repr

/-- The voice type introduces an external argument. -/
def VoiceType.AssignsTheta (vt : VoiceType) : Prop :=
  vt = .agentive ∨ vt = .reflexive ∨ vt = .experiencer

instance : DecidablePred VoiceType.AssignsTheta := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The sense that distinguishes polysemous entries sharing a citation form, as *remember* the
implicative and *remember* the question-embedding factive. -/
inductive SenseTag where
  /-- The primary sense. -/
  | default
  /-- The question-embedding sense. -/
  | rogative
  /-- The causative use of an otherwise non-causative verb. -/
  | causative
  /-- The instrument-specific sense. -/
  | instrumental
  /-- The occasion sense, with an agent-evocator subject ([solstad-bott-2024]). -/
  | occasion
  /-- The stative reading of a polysemous verb, as positional *suivre* 'follow'. -/
  | stative
  deriving DecidableEq, Repr

/-! ### Field facets

Each facet groups a concern's fields; `Verb` composes them via `extends`,
so flat access (`v.complementType`) is preserved. -/

namespace Verb

/-- Argument structure and realization: complement selection, control,
    proto-role entailments, voice, and implicit arguments. -/
structure ArgStructure where
  /-- Argument frames, citation frame first: `ArgumentFrame.intransitive`, `ArgumentFrame.np`,
      `ArgumentFrame.finiteClause`, … (`Syntax/Category/Verb/ArgumentFrame/Basic.lean`). `[]`
      records no frame. -/
  frames : List ArgumentFrame
  /-- Proto-role entailment profile for the subject (external argument).
      The authoritative representation of argument semantics
      ([dowty-1991], [grimm-2011], [levin-2019]).
      Convenience role labels can be derived via `EntailmentProfile.toRole`. -/
  subjectEntailments : Option EntailmentProfile := none
  /-- Proto-role entailment profile for the first object (internal argument). -/
  objectEntailments : Option EntailmentProfile := none
  /-- The verb is unaccusative, its subject an underlying object; `Verb.IsUnaccusative` reads
      the voice type first when one is recorded ([kratzer-1996]). -/
  unaccusative : Bool := false
  /-- The voice type, which fixes whether an external argument is introduced. -/
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

/-- Presupposition profile: factivity class and complement-projection behavior. Whether the
    verb triggers a presupposition, and of which kind, is derived (`Verb.triggerType`). -/
structure Presupposition where
  /-- The [karttunen-1971b] factivity class of a factive predicate; `none` for a
      non-factive. -/
  factivity : Option _root_.Presupposition.Factivity := none
  /-- How does the verb treat presuppositions of its complement?
      Orthogonal to `Verb.triggerType`. [karttunen-1973] -/
  projectionBehavior : Option _root_.Presupposition.ProjectionBehavior := none
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
  /-- The frame this reading is conditioned on: it applies to every frame of the verb
      refining it, in the refinement order on `ArgumentFrame`. -/
  frame : ArgumentFrame
  /-- Frame-conditioned attitude override. -/
  attitude : Option _root_.Attitude := none
  /-- Frame-conditioned opacity override. -/
  opaqueContext : Option Bool := none
  /-- Control type for this frame. -/
  control : Option ControlType := none
  /-- The semantic sort of the complement on this frame
      ([wurmbrand-lohninger-2023]). -/
  size : Option Clause.Size := none
  deriving DecidableEq, Repr

/-- Attitudinal and intensional properties: attitude classification, opacity,
    question-embedding, and complement monotonicity. -/
structure Attitude where
  /-- Does the verb create an opaque context for its complement? -/
  opaqueContext : Bool := false
  /-- Unified attitude classification covering doxastic and preferential attitudes.
      Theoretical properties (C-distributivity, parasitic, etc.) are DERIVED. -/
  attitude : Option _root_.Attitude := none
  /-- Frame-conditioned readings ([bondarenko-2022] §4.4.3): per-frame
      attitude/opacity overrides and control, keyed to `frames` entries. -/
  readings : List Reading := []
  /-- Entailment signature of the complement position.
      Classifies this verb's monotonicity w.r.t. its clausal complement.
      `.mono` = upward monotone: the report is closed under entailment of
      the complement, as in Hintikka-style doxastic semantics
      ([hintikka-1962]). Set only where the classification is textbook
      consensus (believe, think, know); preferential attitudes (want, hope)
      are contested ([heim-1992]) and stay `none`. -/
  complementSig : Option Signature := none
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
    Verb.Causation, Verb.Attitude where
  /-- [levin-1993] verb class (§§ 9–57). -/
  levinClass : Option LevinClass := none
  /-- The verb's lexical root, from which its kind signature and change type are
      read rather than from the `levinClass` table. The default `{}` is the
      unannotated root. -/
  root : Semantics.Root := {}
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

/-! ### ArgumentFrame accessors

Flat readers over `Verb.frames`/`Verb.readings`, preserving the flat
enum-based call syntax: the citation frame's complement/control type and
the alternate frame's, when present. -/

/-- The citation frame, the first of the entry's frames. -/
def Verb.citationFrame? (v : Verb) : Option ArgumentFrame := v.frames.head?

/-- The reading keyed to frame `fr`: the first whose frame `fr` refines. -/
def Verb.reading? (v : Verb) (fr : ArgumentFrame) : Option Verb.Reading :=
  v.readings.find? fun r ↦ decide (r.frame ≤ fr)

/-- The citation frame's flat `ComplementType` cell; `.none` for an
    intransitive and for a frame shape the enum has no cell for. -/
def Verb.complementType (v : Verb) : ComplementType :=
  (v.citationFrame?.bind ArgumentFrame.complementType?).getD .none

/-- Every frame of the verb is intransitive. -/
def Verb.IsIntransitive (v : Verb) : Prop := ∀ fr ∈ v.frames, fr.IsIntransitive

instance (v : Verb) : Decidable v.IsIntransitive :=
  inferInstanceAs (Decidable (∀ fr ∈ v.frames, _))

/-- The alternate (second) frame's flat `ComplementType` cell, `none` when
    there is no second frame or it has a shape outside the enum. -/
def Verb.altComplementType (v : Verb) : Option ComplementType :=
  v.frames[1]?.bind ArgumentFrame.complementType?

/-- The control type of the reading keyed to the citation frame. -/
def Verb.controlType (v : Verb) : ControlType :=
  (v.citationFrame?.bind fun fr ↦ (v.reading? fr).bind (·.control)).getD .none

/-- The control type of the reading keyed to the alternate frame. -/
def Verb.altControlType (v : Verb) : ControlType :=
  (v.frames[1]?.bind fun fr ↦ (v.reading? fr).bind (·.control)).getD .none

/-- The effective attitude on frame `fr`: reading override, else lexeme
    default. -/
def Verb.attitudeOn (v : Verb) (fr : ArgumentFrame) : Option _root_.Attitude :=
  ((v.reading? fr).bind (·.attitude)).orElse fun _ ↦ v.attitude

/-- All [noonan-2007] codings across the verb's frames. -/
def Verb.codings (v : Verb) : List Complement.Coding :=
  v.frames.flatMap ArgumentFrame.codings

/-- Some frame of the verb records force `f`. -/
def Verb.TakesForce (v : Verb) (f : Mood.Illocutionary) : Prop :=
  ∃ fr ∈ v.frames, fr.hasForce f

instance (v : Verb) (f : Mood.Illocutionary) : Decidable (v.TakesForce f) :=
  inferInstanceAs (Decidable (∃ fr ∈ v.frames, _))

/-- The verb records an interrogative frame, as the responsives and rogatives *know*, *wonder*
and *ask* do. -/
abbrev Verb.TakesQuestion (v : Verb) : Prop := v.TakesForce .interrogative

/-- Some frame of the verb has a clausal position: the verb selects a CP or
    reduced clause ([schwarzer-2026]'s CP-selecting verbs). -/
def Verb.TakesClausal (v : Verb) : Prop := ∃ fr ∈ v.frames, fr.HasClausal

instance (v : Verb) : Decidable v.TakesClausal :=
  inferInstanceAs (Decidable (∃ fr ∈ v.frames, _))

/-- Some frame of the verb has a nominal position: the verb selects a DP. -/
def Verb.TakesNominal (v : Verb) : Prop := ∃ fr ∈ v.frames, fr.HasNominal

instance (v : Verb) : Decidable v.TakesNominal :=
  inferInstanceAs (Decidable (∃ fr ∈ v.frames, _))
