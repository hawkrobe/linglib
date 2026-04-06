import Linglib.Core.Lexical.Word
import Linglib.Theories.Semantics.Lexical.Verb.EntailmentProfile
import Linglib.Core.Semantics.Presupposition
import Linglib.Core.Lexical.LevinClass
import Linglib.Core.Logic.NaturalLogic
import Linglib.Theories.Semantics.Lexical.Verb.ChangeOfState.Theory
import Linglib.Theories.Semantics.Probabilistic.Measurement.Basic
import Linglib.Theories.Semantics.Attitudes.Doxastic
import Linglib.Theories.Semantics.Attitudes.Preferential
import Linglib.Theories.Semantics.Causation.Basic
import Linglib.Theories.Semantics.Causation.Implicative
import Linglib.Theories.Semantics.Causation.PsychCausation
import Linglib.Theories.Semantics.Tense.Aspect.LexicalAspect
import Linglib.Theories.Semantics.Lexical.Verb.DegreeAchievement
import Linglib.Theories.Semantics.Events.Krifka1998
import Linglib.Theories.Semantics.Lexical.Verb.LevinClassProfiles

/-! # Cross-Linguistic Verb Infrastructure

Framework-agnostic types for verb semantics: complement type, control type,
attitude/causative builders, and the `VerbCore` structure that bundles all
semantic fields shared across languages.

English-specific morphology (3sg, past, participles) lives in
`Fragments/English/Predicates/Verbal.lean`; other languages extend
`VerbCore` with their own inflectional paradigms.

## Design
@cite{bale-schwarz-2026} @cite{dayal-2025} @cite{heim-1992} @cite{icard-2012} @cite{kennedy-2007} @cite{maier-2015} @cite{qing-uegaki-2025} @cite{rappaport-hovav-levin-2024} @cite{solstad-bott-2024} @cite{rappaport-hovav-levin-1998}

`VerbCore` is the **semantic spine** of a verb entry. It carries:
- Argument structure (theta roles, complement type, control)
- Primitive semantic features (factivity, opacity, speech-act status, …)
- Links to compositional semantics (attitude builder, causative builder, …)

Verb classification (factive, causative, attitude, etc.) is DERIVED from
these primitive fields, not stipulated as an enum.

Language-specific fragments extend `VerbCore` with morphological fields:
- English: `form3sg`, `formPast`, `formPastPart`, `formPresPart`
- Japanese: `form3sg` (nonpast), `formPast`, `formGerund`, `formProgressive`
- Mandarin: (none — isolating language)
-/

namespace Core.Verbs

open Core.Presupposition
-- LevinClass, RootProfile from Core.Lexical.LevinClass (root namespace)
open Semantics.Lexical.Verb.ChangeOfState
open Semantics.Probabilistic.Measurement (Dimension)
open Semantics.Attitudes.Doxastic (Veridicality)
open Semantics.Attitudes.Preferential (AttitudeValence NVPClass PreferentialPredicate)
open Core.NaturalLogic (EntailmentSig)
open Semantics.Causation.PsychCausation (CausalSource)
open Semantics.Lexical.Verb.EntailmentProfile (EntailmentProfile)
open Semantics.Tense.Aspect.LexicalAspect (VendlerClass)
open Semantics.Lexical.Verb.DegreeAchievement (DegreeAchievementScale)
open Semantics.Events.Krifka1998 (VerbIncClass)
open Semantics.Lexical.Verb.LevinClassProfiles

/-- Framework-neutral voice type for deriving argument structure properties.

    Captures the external-argument dimension of the verb's syntactic frame
    without committing to a specific syntactic framework. Maps to
    `Minimalism.VoiceFlavor` via bridge theorems in interface files.

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
Which Montague predicate builder this verb uses.

This links the Fragment entry to the compositional semantics in
`Semantics.Attitudes.Preferential`. Properties like C-distributivity
are DERIVED from the builder via theorems, not stipulated.

- `degreeComparison`: Uses `mkDegreeComparisonPredicate` → C-distributive (PROVED)
- `uncertaintyBased`: Uses `worry` constructor → NOT C-distributive (PROVED)
- `relevanceBased`: Uses `qidai` constructor → NOT C-distributive

The connection to Montague is:
- `degreeComparison.positive` → `Preferential.hope`, `Preferential.expect`, etc.
- `degreeComparison.negative` → `Preferential.fear`, `Preferential.dread`
- `uncertaintyBased` → `Preferential.worry`
- `relevanceBased.positive` → `Preferential.qidai`
-/
inductive PreferentialBuilder where
  /-- Degree comparison semantics: ⟦x V Q⟧ = ∃p ∈ Q. μ(x,p) > θ. C-distributive. -/
  | degreeComparison (valence : AttitudeValence)
  /-- Uncertainty-based semantics (worry): involves global uncertainty. NOT C-distributive. -/
  | uncertaintyBased
  /-- Relevance-based semantics (qidai, care): involves resolution. NOT C-distributive. -/
  | relevanceBased (valence : AttitudeValence)
  deriving DecidableEq, Repr

/-- Get the valence from the builder -/
def PreferentialBuilder.valence : PreferentialBuilder → AttitudeValence
  | .degreeComparison v => v
  | .uncertaintyBased => .negative  -- worry is negative
  | .relevanceBased v => v

/--
Unified builder for all attitude verbs, covering both doxastic (believe, know)
and preferential (hope, fear) attitudes.

This is the **minimal basis** from which theoretical properties are derived:
1. **Doxastic attitudes**: Use accessibility relations (Hintikka semantics)
2. **Preferential attitudes**: Use degree/uncertainty semantics (Villalta)

Derived properties (in Theory layer):
- C-distributivity: from PreferentialBuilder structure
- NVP class: from C-distributivity + valence
- Parasitic on belief: from being preferential
- Presupposition projection: from veridicality + attitude type
-/
inductive AttitudeBuilder where
  /-- Doxastic attitude (believe, know, think) with accessibility semantics -/
  | doxastic (veridicality : Veridicality)
  /-- Preferential attitude (hope, fear, worry) with degree/uncertainty semantics -/
  | preferential (builder : PreferentialBuilder)
  deriving DecidableEq, Repr

/-- Get veridicality from an attitude builder -/
def AttitudeBuilder.veridicality : AttitudeBuilder → Veridicality
  | .doxastic v => v
  | .preferential _ => .nonVeridical  -- Preferential attitudes are non-veridical

/-- Is this a doxastic attitude? -/
def AttitudeBuilder.isDoxastic : AttitudeBuilder → Bool
  | .doxastic _ => true
  | .preferential _ => false

/-- Is this a preferential attitude? -/
def AttitudeBuilder.isPreferential : AttitudeBuilder → Bool
  | .doxastic _ => false
  | .preferential _ => true

/-- Get the preferential builder if this is a preferential attitude -/
def AttitudeBuilder.getPreferentialBuilder : AttitudeBuilder → Option PreferentialBuilder
  | .doxastic _ => none
  | .preferential b => some b

/-- Get valence for preferential attitudes -/
def AttitudeBuilder.valence : AttitudeBuilder → Option AttitudeValence
  | .doxastic _ => none
  | .preferential b => some b.valence

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
Postsupposition type: output-context constraint distinct from presuppositions.

@cite{glass-2025} argues that Mandarin yǐwéi has a postsupposition ◇¬p —
after accepting "x yǐwéi p", the CG must be compatible with ¬p.
This cannot be derived from veridicality alone.

The concrete `Core.Postsupposition.Postsupposition W` is parameterized
by the world type; this enum is the world-type-independent tag stored
in `VerbCore`.
-/
inductive PostsupType where
  /-- Output context must be compatible with ¬p: ◇¬p (@cite{glass-2025}). -/
  | weakContrafactive
  /-- Output context must entail ¬p: ⊨¬p (hypothetical, UNATTESTED). -/
  | strongContrafactive
  deriving DecidableEq, Repr

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

-- CausativeBuilder is imported from NadathurLauer2020.Builder
-- (via Causative.Basic). Like PreferentialBuilder for attitude verbs,
-- it links lexical entries to their compositional semantics. Properties
-- like "asserts sufficiency" are DERIVED from the builder via theorems.
open NadathurLauer2020.Builder (CausativeBuilder)

-- ImplicativeBuilder follows the same pattern for implicative verbs (manage, fail).
open Nadathur2024.Implicative (ImplicativeBuilder)

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

/--
Cross-linguistic verb core: all semantic fields shared across languages.

Bundles argument structure, semantic class, and links to compositional
semantics. Language-specific fragments extend this with morphological
fields appropriate to their inflectional system.
-/
structure VerbCore where
  -- === Citation Form ===
  /-- Citation form (cross-linguistic) -/
  form : String

  -- === Argument Structure ===
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

  -- === Implicit Arguments (@cite{bruening-2021}) ===
  /-- Can the direct object (theme/patient) be left unexpressed?
      Applies to monotransitives (*eat* vs *devour*) and the theme of
      ditransitives. `none` = object always required. -/
  implicitObj : Option ImplicitInterp := none
  /-- Can the goal/recipient argument be left unexpressed?
      Applies to the IO of double object constructions and the PP
      of dative frames. `none` = goal always required. -/
  implicitGoal : Option ImplicitInterp := none

  -- === Semantic Class ===
  /-- Does the verb denote the performance of an illocutionary act?
      True for speech-act verbs (say, tell, claim, ask). This is a genuine
      semantic primitive that cannot be derived from other fields. -/
  speechActVerb : Bool := false
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
  /-- Is the verb a presupposition trigger? -/
  presupType : Option PresupTriggerType := none
  /-- Output-context constraint (postsupposition), distinct from
      presuppositions. @cite{glass-2025}: yǐwéi has ◇¬p postsupposition. -/
  postsupType : Option PostsupType := none
  /-- How does the verb treat presuppositions of its complement?
      Orthogonal to `presupType`. @cite{karttunen-1973} -/
  projectionBehavior : Option ProjectionBehavior := none
  /-- For measure predicates: which dimension this verb selects for.
      Determines *per*-phrase interpretation:
      simplex dimension → compositional, quotient → math speak. -/
  selectsDimension : Option Dimension := none

  -- === Class-Specific Features ===
  /-- For CoS verbs: which type (cessation, inception, continuation)? -/
  cosType : Option CoSType := none
  /-- For implicative verbs: which semantic builder (links to compositional semantics). -/
  implicativeBuilder : Option ImplicativeBuilder := none
  /-- For causative verbs: which semantic builder (links to compositional semantics). -/
  causativeBuilder : Option CausativeBuilder := none
  /-- Source of causation for psych causatives (@cite{kim-2024} UPH).
      `.external` = mind-external percept, `.internal` = mind-internal representation. -/
  causalSource : Option CausalSource := none

  -- === Intensionality ===
  /-- Does the verb create an opaque context for its complement? -/
  opaqueContext : Bool := false

  -- === Attitude-Specific Properties ===
  /-- Unified attitude builder covering doxastic and preferential attitudes.
      Theoretical properties (C-distributivity, parasitic, etc.) are DERIVED. -/
  attitudeBuilder : Option AttitudeBuilder := none
  /-- For non-preferential question-embedding verbs (know, wonder, ask) -/
  takesQuestionBase : Bool := false
  /-- Entailment signature of the complement position.
      Classifies this verb's monotonicity w.r.t. its clausal complement.
      `.mono` = upward monotone (believe, know); `.mult` = multiplicative only
      (be surprised). Used to derive conjunction distribution and neg-raising.
      See @cite{bondarenko-elliott-2026}. -/
  complementSig : Option EntailmentSig := none

  -- === Polysemy ===
  /-- Disambiguates entries that share a citation form.
      Most verbs use `.default`; polysemous entries use descriptive tags. -/
  senseTag : SenseTag := .default

  -- === Root Content (@cite{levin-1993}; @cite{spalek-mcnally-2026}) ===
  /-- @cite{levin-1993} verb class (§§ 9–57). -/
  levinClass : Option LevinClass := none
  /-- Root-specific quality dimensions (within-class variation). -/
  rootProfile : Option RootProfile := none
  deriving Repr, BEq

/-- Derive unaccusativity from voice type when present, falling back
    to the stored `unaccusative` field. A verb is unaccusative iff its
    Voice does not introduce an external argument (@cite{kratzer-1996}). -/
def VerbCore.derivedUnaccusative (v : VerbCore) : Bool :=
  match v.voiceType with
  | some vt => !vt.assignsTheta
  | none => v.unaccusative

/-- Derive vendlerClass from degreeAchievementScale if present.
    Falls back to the stipulated vendlerClass field. -/
def VerbCore.derivedVendlerClass (v : VerbCore) : Option VendlerClass :=
  v.vendlerClass <|> v.degreeAchievementScale.map (·.defaultVendlerClass)

/-- Effective subject entailment profile: verb-level override if present,
    otherwise falls back to the Levin class–level profile
    (@cite{levin-1993}, @cite{dowty-1991}). -/
def VerbCore.effectiveSubjectEntailments (v : VerbCore) : Option EntailmentProfile :=
  v.subjectEntailments <|> v.levinClass.bind (·.subjectProfile)

/-- Effective object entailment profile: verb-level override if present,
    otherwise falls back to the Levin class–level profile. -/
def VerbCore.effectiveObjectEntailments (v : VerbCore) : Option EntailmentProfile :=
  v.objectEntailments <|> v.levinClass.bind (·.objectProfile)

/-- Veridicality is DERIVED from the attitude builder -/
def VerbCore.veridicality (v : VerbCore) : Option Veridicality :=
  v.attitudeBuilder.map (·.veridicality)

/-- Is this verb a doxastic attitude? -/
def VerbCore.isDoxastic (v : VerbCore) : Bool :=
  v.attitudeBuilder.map (·.isDoxastic) |>.getD false

/-- Is this verb a preferential attitude? -/
def VerbCore.isPreferential (v : VerbCore) : Bool :=
  v.attitudeBuilder.map (·.isPreferential) |>.getD false

/-- Does this attitude distribute over conjunction?
    DERIVED from complementSig: any signature that refines `.mono`
    (mono, additive, mult, addMult, all) distributes. -/
def VerbCore.distribOverConj (v : VerbCore) : Bool :=
  v.complementSig.map (·.refines .mono) |>.getD false

/-- Is the complement position upward-entailing?
    DERIVED from complementSig. -/
def VerbCore.isComplementUE (v : VerbCore) : Bool :=
  v.complementSig.map (·.refines .mono) |>.getD false

/-- Valence is DERIVED from the attitude builder (for preferential attitudes) -/
def VerbCore.preferentialValence (v : VerbCore) : Option AttitudeValence :=
  v.attitudeBuilder.bind (·.valence)

-- Note: VerbCore.cDistributive, VerbCore.nvpClass, and VerbCore.takesQuestion
-- are derived properties defined in Theories/Semantics.Intensional/Attitude/BuilderProperties.lean

/--
Get the CoS semantics for a verb (if it's a CoS verb).

Returns `some (cosSemantics t P)` if the verb has a CoS type,
where `P` is the activity predicate (complement denotation).
-/
def VerbCore.getCoSSemantics {W : Type*} (v : VerbCore) (P : W → Bool) :
    Option (PrProp W) :=
  v.cosType.map λ t => cosSemantics t P

/-- Does this verb presuppose its complement via factivity?
    DERIVED from attitudeBuilder: true iff the verb is doxastic veridical. -/
def VerbCore.factivePresup (v : VerbCore) : Bool :=
  match v.attitudeBuilder with
  | some (.doxastic .veridical) => true
  | _ => false

/-- Does this verb presuppose its complement? -/
def VerbCore.presupposesComplement (v : VerbCore) : Bool :=
  v.factivePresup || v.cosType.isSome

/-- Is this verb a presupposition trigger? -/
def VerbCore.isPresupTrigger (v : VerbCore) : Bool :=
  v.presupType.isSome

/-- Does this verb have a postsupposition (output-context constraint)?
    DERIVED from `postsupType`. -/
def VerbCore.hasPostsupposition (v : VerbCore) : Bool :=
  v.postsupType.isSome

/-- Presupposition trigger type DERIVED from event structure rather than
    stipulated. @cite{roberts-simons-2024} argue that presupposition status
    follows from a verb's event structure (factivity, CoS type), not from
    a lexically specified trigger type. This accessor derives the prediction:
    verbs with factive or CoS event structure are presupposition triggers.

    Note: R&S (p. 705) argue that the soft/hard trigger distinction "has
    never been clearly operationalized." We use `.softTrigger` here as a
    placeholder, not as an endorsement of a binary soft/hard taxonomy. -/
def VerbCore.derivedPresupType (v : VerbCore) : Option PresupTriggerType :=
  if v.presupposesComplement then some .softTrigger else none

/-- Is this verb a causative? DERIVED from causativeBuilder. -/
def VerbCore.isCausative (v : VerbCore) : Bool :=
  v.causativeBuilder.isSome

/-- Does this causative verb assert sufficiency (like "make")?

    DERIVED from the builder: delegates to `CausativeBuilder.assertsSufficiency`. -/
def VerbCore.assertsSufficiency (v : VerbCore) : Bool :=
  v.causativeBuilder.map (·.assertsSufficiency) |>.getD false

/-- Does this verb's semantics predict it is an expletive negation trigger?

    DERIVED from attitude, implicative, and causative builders. Captures
    the propositional attitude licensing condition from
    @cite{jin-koenig-2021} §5.5, ex. 13a:

    - **FEAR class**: negative-valence preferential attitudes activate
      p (feared content) and ¬p (desired alternative).
    - **FORGET class**: negative implicative verbs entail ¬p in w₀.
    - **STOP/PREVENT**: causative preventatives entail ¬p in w₀.

    DENY class triggers (doubt, question) are excluded — their
    EN-triggering requires matrix negation/questioning (pragmatic,
    via neg-raising), not purely lexical semantics. Temporal, logical,
    and comparative triggers are operators/connectives, not verbs. -/
def VerbCore.isENTrigger (v : VerbCore) : Bool :=
  -- FEAR class: negative-valence preferential attitudes
  (v.preferentialValence == some .negative) ||
  -- FORGET class: negative implicative verbs
  (v.implicativeBuilder == some .negative) ||
  -- STOP/PREVENT: causative prevent verbs
  (v.causativeBuilder == some .prevent)

/-- Does this causative verb assert necessity (like "cause")?

    DERIVED from the builder: delegates to `CausativeBuilder.assertsNecessity`. -/
def VerbCore.assertsNecessity (v : VerbCore) : Bool :=
  v.causativeBuilder.map (·.assertsNecessity) |>.getD false

/-- Does success of this implicative verb entail the complement?

    DERIVED from the builder: delegates to `ImplicativeBuilder.entailsComplement`.
    Returns `some true` for positive implicatives (*manage*, *remember*),
    `some false` for negative (*fail*, *forget*), `none` for non-implicatives. -/
def VerbCore.entailsComplement (v : VerbCore) : Option Bool :=
  v.implicativeBuilder.map (·.entailsComplement)

/-- Is this verb a preferential attitude predicate? -/
def VerbCore.isPreferentialAttitude (v : VerbCore) : Bool :=
  v.preferentialValence.isSome

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

/-- Look up a verb core by citation form and sense tag. -/
def lookupSense (verbs : List VerbCore) (form : String) (tag : SenseTag := .default) :
    Option VerbCore :=
  verbs.find? (λ v => v.form == form && v.senseTag == tag)

end Core.Verbs
