import Linglib.Core.Lexical.Word
import Linglib.Theories.Semantics.Events.ThematicRoles
import Linglib.Core.Semantics.Presupposition
import Linglib.Core.RootDimensions
import Linglib.Core.Logic.NaturalLogic
import Linglib.Theories.Semantics.Lexical.Verb.ChangeOfState.Theory
import Linglib.Theories.Semantics.Probabilistic.Measurement.Basic
import Linglib.Theories.Semantics.Attitudes.Doxastic
import Linglib.Theories.Semantics.Attitudes.Preferential
import Linglib.Theories.Semantics.Causation.Basic
import Linglib.Theories.Semantics.Causation.Implicative
import Linglib.Theories.Semantics.Causation.PsychCausation
import Linglib.Theories.Semantics.Lexical.Verb.Aspect
import Linglib.Theories.Semantics.Lexical.Verb.DegreeAchievement
import Linglib.Theories.Semantics.Events.Krifka1998

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
-- LevinClass, RootProfile from Core.RootDimensions (root namespace)
open Semantics.Lexical.Verb.ChangeOfState
open Semantics.Probabilistic.Measurement (Dimension)
open Semantics.Attitudes.Doxastic (Veridicality)
open Semantics.Attitudes.Preferential (AttitudeValence NVPClass PreferentialPredicate)
open Core.NaturalLogic (EntailmentSig)
open Semantics.Causation.PsychCausation (CausalSource)
open Semantics.Lexical.Verb.Aspect (VendlerClass)
open Semantics.Lexical.Verb.DegreeAchievement (DegreeAchievementScale)
open Semantics.Events.Krifka1998 (VerbIncClass)

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
  deriving DecidableEq, Repr, BEq

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
  deriving DecidableEq, Repr, BEq

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
  | hardTrigger     -- Projective in all contexts
  | softTrigger     -- Can be locally accommodated
  deriving DecidableEq, Repr, BEq

-- CausativeBuilder is imported from NadathurLauer2020.Builder
-- (via Causative.Basic). Like PreferentialBuilder for attitude verbs,
-- it links lexical entries to their compositional semantics. Properties
-- like "asserts sufficiency" are DERIVED from the builder via theorems.
open NadathurLauer2020.Builder (CausativeBuilder)

-- ImplicativeBuilder follows the same pattern for implicative verbs (manage, fail).
open Nadathur2023.Implicative (ImplicativeBuilder)

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
  deriving DecidableEq, BEq, Repr

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
  deriving DecidableEq, Repr, BEq

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
  deriving DecidableEq, Repr, BEq

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
  /-- Theta role of external argument (subject) -/
  subjectTheta : Option ThetaRole := none
  /-- Theta role of internal argument (object) -/
  objectTheta : Option ThetaRole := none
  /-- Theta role of second internal argument (indirect object) -/
  object2Theta : Option ThetaRole := none
  /-- Control type for infinitival complements -/
  controlType : ControlType := .none
  /-- Alternate complement frame, for verbs with two complement types.
      E.g., "hope" primarily takes.finiteClause ("hope that...") but
      also takes.infinitival ("hope to...") with subject control.
      When set, `altControlType` specifies the control type for this frame. -/
  altComplementType : Option ComplementType := none
  /-- Control type for the alternate complement frame. -/
  altControlType : ControlType := .none
  /-- Is the verb unaccusative? (subject is underlying object) -/
  unaccusative : Bool := false
  /-- Can the verb passivize? -/
  passivizable : Bool := true

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
  /-- For measure predicates: which dimension this verb selects for.
      Determines *per*-phrase interpretation:
      simplex dimension → compositional, quotient → math speak. -/
  selectsDimension : Option Dimension := none

  -- === Class-Specific Features ===
  /-- For CoS verbs: which type (cessation, inception, continuation)? -/
  cosType : Option CoSType := none
  /-- For factive verbs: what does it presuppose about its complement? -/
  factivePresup : Bool := false
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

  -- === Root Content (@cite{levin-1993}; Spalek & McNally) ===
  /-- @cite{levin-1993} verb class (§§ 9–57). -/
  levinClass : Option LevinClass := none
  /-- Root-specific quality dimensions (within-class variation). -/
  rootProfile : Option RootProfile := none
  deriving Repr, BEq

/-- Derive vendlerClass from degreeAchievementScale if present.
    Falls back to the stipulated vendlerClass field. -/
def VerbCore.derivedVendlerClass (v : VerbCore) : Option VendlerClass :=
  v.vendlerClass <|> v.degreeAchievementScale.map (·.defaultVendlerClass)

/-- Lexicalist prediction (@cite{levin-1993}; Rappaport @cite{rappaport-hovav-levin-1998}):
    the verb's lexical semantics determines the external argument's theta role.

    This is the lexicalist/projectionist alternative to the severing prediction
    (Voice flavor → theta role, see `VoiceFlavor.thetaRole` in VoiceTheta.lean).
    The lexicalist account derives the theta role from verb-internal
    semantic properties, bypassing Voice entirely.

    The derivation uses independently motivated properties:
    - Syntactic: `controlType` (raising → no θ), `unaccusative` (→ theme)
    - Semantic builders: `causalSource` (@cite{kim-2024} → stimulus),
      `attitudeBuilder` (→ experiencer)
    - Presupposition: `factivePresup` without attitude builder (→ experiencer)
    - Polysemy: `senseTag =.occasion` (@cite{solstad-bott-2024} → experiencer)
    - Verb class: `levinClass` (.weather → none,.flinch/.learn → experiencer,
.measure → theme)

    Matches hand-annotated `subjectTheta` for ~94% of English verb entries.
    Remaining mismatches (e.g., *remember*, *dare*) have genuinely irreducible
    theta role assignments not predictable from other VerbCore fields. -/
def VerbCore.predictedSubjectTheta (v : VerbCore) : Option ThetaRole :=
  if v.controlType == .raising then none
  else if v.levinClass == some .weather then none
  else if v.causalSource.isSome then some .stimulus
  else if v.objectTheta == some .stimulus then some .experiencer
  else if v.attitudeBuilder.isSome then some .experiencer
  else if v.factivePresup && v.attitudeBuilder.isNone then some .experiencer
  else if v.senseTag == .occasion then some .experiencer
  else if v.levinClass == some .flinch then some .experiencer
  else if v.levinClass == some .learn then some .experiencer
  else if v.unaccusative then some .theme
  else if v.levinClass == some .measure then some .theme
  else some .agent

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

/-- Does this verb presuppose its complement? -/
def VerbCore.presupposesComplement (v : VerbCore) : Bool :=
  v.factivePresup || v.cosType.isSome

/-- Is this verb a presupposition trigger? -/
def VerbCore.isPresupTrigger (v : VerbCore) : Bool :=
  v.presupType.isSome

/-- Is this verb a causative? DERIVED from causativeBuilder. -/
def VerbCore.isCausative (v : VerbCore) : Bool :=
  v.causativeBuilder.isSome

/-- Does this causative verb assert sufficiency (like "make")?

    DERIVED from the builder: delegates to `CausativeBuilder.assertsSufficiency`. -/
def VerbCore.assertsSufficiency (v : VerbCore) : Bool :=
  v.causativeBuilder.map (·.assertsSufficiency) |>.getD false

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
