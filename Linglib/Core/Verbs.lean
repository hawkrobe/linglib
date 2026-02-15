import Linglib.Core.Basic
import Linglib.Core.Presupposition
import Linglib.Core.RootDimensions
import Linglib.Theories.TruthConditional.Verb.ChangeOfState.Theory
import Linglib.Theories.TruthConditional.Measurement.Basic
import Linglib.Theories.IntensionalSemantics.Attitude.Doxastic
import Linglib.Theories.IntensionalSemantics.Attitude.Preferential
import Linglib.Theories.IntensionalSemantics.Causative.Basic
import Linglib.Theories.IntensionalSemantics.Causative.Implicative

/-! # Cross-Linguistic Verb Infrastructure

Framework-agnostic types for verb semantics: complement type, control type,
attitude/causative builders, and the `VerbCore` structure that bundles all
semantic fields shared across languages.

English-specific morphology (3sg, past, participles) lives in
`Fragments/English/Predicates/Verbal.lean`; other languages extend
`VerbCore` with their own inflectional paradigms.

## Design

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
open TruthConditional.Verb.ChangeOfState
open TruthConditional.Measurement (Dimension)
open IntensionalSemantics.Attitude.Doxastic (Veridicality)
open IntensionalSemantics.Attitude.Preferential (AttitudeValence NVPClass PreferentialPredicate)

/--
Which Montague predicate builder this verb uses.

This links the Fragment entry to the compositional semantics in
`IntensionalSemantics.Attitude.Preferential`. Properties like C-distributivity
are DERIVED from the builder via theorems, not stipulated.

- `degreeComparison`: Uses `mkDegreeComparisonPredicate` → C-distributive (PROVED)
- `uncertaintyBased`: Uses `worry` constructor → NOT C-distributive (PROVED)
- `relevanceBased`: Uses `qidai` constructor → NOT C-distributive

The connection to Montague is:
- `degreeComparison .positive` → `Preferential.hope`, `Preferential.expect`, etc.
- `degreeComparison .negative` → `Preferential.fear`, `Preferential.dread`
- `uncertaintyBased` → `Preferential.worry`
- `relevanceBased .positive` → `Preferential.qidai`
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
- C-distributivity: from PreferentialBuilder structure (Qing et al. 2025)
- NVP class: from C-distributivity + valence
- Parasitic on belief: from being preferential (Maier 2015)
- Presupposition projection: from veridicality + attitude type (Heim 1992)
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
Presupposition trigger type (Tonhauser et al. 2013 classification).

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
- `.rogative`: question-embedding sense (Dayal 2025)
- `.causative`: causative use of otherwise non-causative verb
- `.instrumental`: instrument-specific sense (Rappaport Hovav & Levin 2024)
-/
inductive SenseTag where
  | default       -- Primary/unmarked sense
  | rogative      -- Question-embedding sense
  | causative     -- Causative use of otherwise non-causative verb
  | instrumental  -- Instrument-specific sense
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
  /-- Is the verb unaccusative? (subject is underlying object) -/
  unaccusative : Bool := false
  /-- Can the verb passivize? -/
  passivizable : Bool := true

  -- === Semantic Class ===
  /-- Does the verb denote the performance of an illocutionary act?
      True for speech-act verbs (say, tell, claim, ask). This is a genuine
      semantic primitive that cannot be derived from other fields. -/
  speechActVerb : Bool := false
  /-- Is the verb a presupposition trigger? -/
  presupType : Option PresupTriggerType := none
  /-- For measure predicates: which dimension this verb selects for.
      Determines *per*-phrase interpretation (Bale & Schwarz 2026):
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

  -- === Intensionality ===
  /-- Does the verb create an opaque context for its complement? -/
  opaqueContext : Bool := false

  -- === Attitude-Specific Properties ===
  /-- Unified attitude builder covering doxastic and preferential attitudes.
      Theoretical properties (C-distributivity, parasitic, etc.) are DERIVED. -/
  attitudeBuilder : Option AttitudeBuilder := none
  /-- For non-preferential question-embedding verbs (know, wonder, ask) -/
  takesQuestionBase : Bool := false

  -- === Polysemy ===
  /-- Disambiguates entries that share a citation form.
      Most verbs use `.default`; polysemous entries use descriptive tags. -/
  senseTag : SenseTag := .default

  -- === Root Content (Levin 1993; Spalek & McNally) ===
  /-- Levin (1993) verb class (§§ 9–57). -/
  levinClass : Option LevinClass := none
  /-- Root-specific quality dimensions (within-class variation). -/
  rootProfile : Option RootProfile := none
  deriving Repr, BEq

/-- Veridicality is DERIVED from the attitude builder -/
def VerbCore.veridicality (v : VerbCore) : Option Veridicality :=
  v.attitudeBuilder.map (·.veridicality)

/-- Is this verb a doxastic attitude? -/
def VerbCore.isDoxastic (v : VerbCore) : Bool :=
  v.attitudeBuilder.map (·.isDoxastic) |>.getD false

/-- Is this verb a preferential attitude? -/
def VerbCore.isPreferential (v : VerbCore) : Bool :=
  v.attitudeBuilder.map (·.isPreferential) |>.getD false

/-- Valence is DERIVED from the attitude builder (for preferential attitudes) -/
def VerbCore.preferentialValence (v : VerbCore) : Option AttitudeValence :=
  v.attitudeBuilder.bind (·.valence)

-- Note: VerbCore.cDistributive, VerbCore.nvpClass, and VerbCore.takesQuestion
-- are derived properties defined in Theories/IntensionalSemantics/Attitude/BuilderProperties.lean

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

/-- Map complement type to syntactic valence. -/
def complementToValence : ComplementType → Valence
  | .none => .intransitive
  | .np => .transitive
  | .np_np => .ditransitive
  | _ => .transitive  -- Clause-embedding verbs are syntactically transitive

/-- Look up a verb core by citation form and sense tag. -/
def lookupSense (verbs : List VerbCore) (form : String) (tag : SenseTag := .default) :
    Option VerbCore :=
  verbs.find? (λ v => v.form == form && v.senseTag == tag)

end Core.Verbs
