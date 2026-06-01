import Linglib.Semantics.Verb.Defs

/-! # Verb entry — derived API

Classification accessors DERIVED from the primitive `VerbCore` fields:
unaccusativity from voice, veridicality from the attitude builder, presupposition
status from event structure, theta-role linking, and so on. Verb classification
is computed here, not stipulated as enum fields on `VerbCore`.
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
  v.attitude.map (·.veridicality)

/-- Is this verb a doxastic attitude? -/
def VerbCore.isDoxastic (v : VerbCore) : Bool :=
  v.attitude.map (·.isDoxastic) |>.getD false

/-- Is this verb a preferential attitude? -/
def VerbCore.isPreferential (v : VerbCore) : Bool :=
  v.attitude.map (·.isPreferential) |>.getD false

/-- Does this attitude distribute over conjunction?
    DERIVED from complementSig: any signature that refines `.mono`
    (mono, additive, mult, addMult, all) distributes. -/
def VerbCore.distribOverConj (v : VerbCore) : Bool :=
  v.complementSig.map (fun s => decide (s ≤ .mono)) |>.getD false

/-- Is the complement position upward-entailing?
    DERIVED from complementSig. -/
def VerbCore.isComplementUE (v : VerbCore) : Bool :=
  v.complementSig.map (fun s => decide (s ≤ .mono)) |>.getD false

/-- Valence is DERIVED from the attitude builder (for preferential attitudes) -/
def VerbCore.preferentialValence (v : VerbCore) : Option AttitudeValence :=
  v.attitude.bind (·.valence)

-- Note: VerbCore.cDistributive, VerbCore.nvpClass, and VerbCore.takesQuestion
-- are derived properties defined in Semantics.Intensional/Attitude/BuilderProperties.lean

/--
Get the CoS semantics for a verb (if it's a CoS verb).

Returns `some (cosSemantics t P)` if the verb has a CoS type,
where `P` is the activity predicate (complement denotation).
-/
def VerbCore.getCoSSemantics {W : Type*} (v : VerbCore) (P : W → Prop) :
    Option (PrProp W) :=
  v.cosType.map λ t => cosSemantics t P

/-- Does this verb presuppose its complement via factivity?
    DERIVED from attitude: true iff the verb is doxastic veridical. -/
def VerbCore.factivePresup (v : VerbCore) : Bool :=
  match v.attitude with
  | some (.doxastic .veridical) => true
  | _ => false

/-- Does this verb presuppose its complement? -/
def VerbCore.presupposesComplement (v : VerbCore) : Bool :=
  v.factivePresup || v.cosType.isSome

/-- Is this verb a presupposition trigger? -/
def VerbCore.isPresupTrigger (v : VerbCore) : Bool :=
  v.presupType.isSome

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

/-- Is this verb a causative? DERIVED from causative field. -/
def VerbCore.isCausative (v : VerbCore) : Bool :=
  v.causative.isSome

/-- Does this causative verb assert sufficiency (like "make")?

    DERIVED: delegates to `Causative.assertsSufficiency`. -/
def VerbCore.assertsSufficiency (v : VerbCore) : Bool :=
  v.causative.map (·.assertsSufficiency) |>.getD false

/-- Lexicalist prediction of the external argument's theta role
    (@cite{levin-1993}, @cite{rappaport-hovav-levin-1998}), based solely
    on verb-internal properties.

    The cascade mirrors traditional linking rules:
    - raising / weather → no external role
    - external causal source → stimulus (Class II psych, @cite{kim-2024})
    - attitude builder or factive presupposition → experiencer
    - occasion sense (manage-to) → experiencer
    - Levin class flinch / learn → experiencer
    - unaccusative / measure → theme
    - default → agent

    Contrasts with the Kratzer severing prediction (`VoiceFlavor.thetaRole`),
    which derives the role from Voice flavor rather than verb-internal
    semantics. Studies comparing the two accounts can apply both to the
    same `VerbCore` and inspect divergence. -/
def VerbCore.predictedSubjectTheta (v : VerbCore) : Option ThetaRole :=
  if v.controlType == .raising then none
  else if v.levinClass == some .weather then none
  else if v.causalSource.isSome then some .stimulus
  else if v.attitude.isSome then some .experiencer
  else if v.factivePresup && v.attitude.isNone then some .experiencer
  else if v.senseTag == .occasion then some .experiencer
  else if v.levinClass == some .flinch then some .experiencer
  else if v.levinClass == some .learn then some .experiencer
  else if v.unaccusative then some .theme
  else if v.levinClass == some .measure then some .theme
  else some .agent

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
  (v.implicative == some .negative) ||
  -- STOP/PREVENT: causative prevent verbs
  (v.causative == some .prevent)

/-- Does this causative verb assert necessity (like "cause")?

    DERIVED: delegates to `Causative.assertsNecessity`. -/
def VerbCore.assertsNecessity (v : VerbCore) : Bool :=
  v.causative.map (·.assertsNecessity) |>.getD false

/-- Does success of this implicative verb entail the complement?

    DERIVED: delegates to `Implicative.entailsComplement`.
    Returns `some true` for positive implicatives (*manage*, *remember*),
    `some false` for negative (*fail*, *forget*), `none` for non-implicatives. -/
def VerbCore.entailsComplement (v : VerbCore) : Option Bool :=
  v.implicative.map (·.entailsComplement)

/-- Is this verb a preferential attitude predicate? -/
def VerbCore.isPreferentialAttitude (v : VerbCore) : Bool :=
  v.preferentialValence.isSome

/-- Can this verb take a clausal (CP) complement?

    Checks both primary and alternate complement frames. Used to classify
    verbs as CP-selecting vs non-CP-selecting for coordination studies
    (@cite{schwarzer-2026}). -/
def VerbCore.canTakeClausalComplement (v : VerbCore) : Bool :=
  v.complementType.isClausal ||
  match v.altComplementType with | some ct => ct.isClausal | none => false

/-- Can this verb take a nominal (DP) complement?

    Checks both primary and alternate complement frames. -/
def VerbCore.canTakeNominalComplement (v : VerbCore) : Bool :=
  v.complementType.isNominal ||
  match v.altComplementType with | some ct => ct.isNominal | none => false

/-- Look up a verb core by citation form and sense tag. -/
def lookupSense (verbs : List VerbCore) (form : String) (tag : SenseTag := .default) :
    Option VerbCore :=
  verbs.find? (λ v => v.form == form && v.senseTag == tag)
