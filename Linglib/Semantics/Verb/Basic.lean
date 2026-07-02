import Linglib.Semantics.Verb.Defs
import Linglib.Semantics.Verb.Root.Closure

/-! # Verb entry — derived API

Classification accessors DERIVED from the primitive `Verb` fields:
unaccusativity from voice, veridicality from the attitude builder, presupposition
status from event structure, theta-role linking, and so on. Verb classification
is computed here, not stipulated as enum fields on `Verb`.
-/

open Semantics.Presupposition
open Features
open Semantics.Lexical
open Features.ChangeOfState
open NaturalLogic (EntailmentSig)
open Causation.Psych (CausalSource)
open ArgumentStructure (EntailmentProfile)
open Features.DegreeAchievement (DegreeAchievementScale)
open Semantics.Aspect.Incremental (VerbIncClass)
open Features.LevinClassProfiles

/-- Derive unaccusativity from voice type when present, falling back
    to the stored `unaccusative` field. A verb is unaccusative iff its
    Voice does not introduce an external argument ([kratzer-1996]). -/
def Verb.derivedUnaccusative (v : Verb) : Bool :=
  match v.voiceType with
  | some vt => !vt.assignsTheta
  | none => v.unaccusative

/-- Derive vendlerClass from degreeAchievementScale if present.
    Falls back to the stipulated vendlerClass field. -/
def Verb.derivedVendlerClass (v : Verb) : Option VendlerClass :=
  v.vendlerClass <|> v.degreeAchievementScale.map (·.defaultVendlerClass)

/-- The verb's within-class quality profile ([spalek-mcnally-2026]), read off its
    `root` (where the profile is carried). -/
def Verb.rootProfile (v : Verb) : Verb.Root.Profile :=
  v.root.profile

/-- The verb's raw kind signature ([beavers-koontz-garboden-2020]): the
    un-closed atom-kinds of its root, the source of truth for what the verb
    structurally entails. `Verb.closedKinds` is its collocational closure and
    `Verb.classKinds` the coarse class-derived view (an independent provenance). -/
def Verb.kinds (v : Verb) : Verb.Root.Kinds :=
  v.root.kinds

/-- The verb's closed kind signature ([beavers-koontz-garboden-2020]): the
    collocational closure of `Verb.kinds` (`cause ⟹ result ⟹ state`), which the
    event-structure spine (`Verb.Root.template`, `CosModel.denote`) runs on. -/
def Verb.closedKinds (v : Verb) : Verb.Root.Kinds :=
  v.root.closedKinds

/-- Effective subject entailment profile: verb-level override if present,
    otherwise falls back to the Levin class–level profile
    ([levin-1993], [dowty-1991]). -/
def Verb.effectiveSubjectEntailments (v : Verb) : Option EntailmentProfile :=
  v.subjectEntailments <|> v.levinClass.bind (·.subjectProfile)

/-- Effective object entailment profile: verb-level override if present,
    otherwise falls back to the Levin class–level profile. -/
def Verb.effectiveObjectEntailments (v : Verb) : Option EntailmentProfile :=
  v.objectEntailments <|> v.levinClass.bind (·.objectProfile)

/-- Veridicality is DERIVED from the attitude builder -/
def Verb.veridicality (v : Verb) : Option Veridicality :=
  v.attitude.map (·.veridicality)

/-- Is this verb a doxastic attitude? -/
def Verb.isDoxastic (v : Verb) : Bool :=
  v.attitude.map (·.isDoxastic) |>.getD false

/-- Is this verb a preferential attitude? -/
def Verb.isPreferential (v : Verb) : Bool :=
  v.attitude.map (·.isPreferential) |>.getD false

/-- Valence is DERIVED from the attitude builder (for preferential attitudes) -/
def Verb.preferentialValence (v : Verb) : Option AttitudeValence :=
  v.attitude.bind (·.valence)

-- Note: Verb.cDistributive, Verb.nvpClass, and Verb.takesQuestion
-- are derived properties defined in Semantics.Intensional/Attitude/BuilderProperties.lean

/-- Does this verb presuppose its complement via factivity?
    DERIVED from attitude: true iff the verb is doxastic veridical. -/
def Verb.factivePresup (v : Verb) : Bool :=
  match v.attitude with
  | some (.doxastic .veridical) => true
  | _ => false

/-- Does this verb presuppose its complement? -/
def Verb.presupposesComplement (v : Verb) : Bool :=
  v.factivePresup || v.cosType.isSome

/-- Is this verb a presupposition trigger? -/
def Verb.isPresupTrigger (v : Verb) : Bool :=
  v.presupType.isSome

/-- Presupposition trigger type DERIVED from event structure rather than
    stipulated. [roberts-simons-2024] argue that presupposition status
    follows from a verb's event structure (factivity, CoS type), not from
    a lexically specified trigger type. This accessor derives the prediction:
    verbs with factive or CoS event structure are presupposition triggers.

    Note: R&S (p. 705) argue that the soft/hard trigger distinction "has
    never been clearly operationalized." We use `.softTrigger` here as a
    placeholder, not as an endorsement of a binary soft/hard taxonomy. -/
def Verb.derivedPresupType (v : Verb) : Option PresupTriggerType :=
  if v.presupposesComplement then some .softTrigger else none

/-- Is this verb a causative? DERIVED from causative field. -/
def Verb.isCausative (v : Verb) : Bool :=
  v.causative.isSome

/-- Does this causative verb assert sufficiency (like "make")?

    DERIVED: delegates to `Causative.assertsSufficiency`. -/
def Verb.assertsSufficiency (v : Verb) : Bool :=
  v.causative.map (·.assertsSufficiency) |>.getD false

/-- Lexicalist prediction of the external argument's theta role
    ([levin-1993], [rappaport-hovav-levin-1998]), based solely
    on verb-internal properties.

    The cascade mirrors traditional linking rules:
    - raising / weather → no external role
    - external causal source → stimulus (Class II psych, [kim-2024])
    - attitude builder or factive presupposition → experiencer
    - occasion sense (manage-to) → experiencer
    - Levin class flinch / learn → experiencer
    - unaccusative / measure → theme
    - default → agent

    Contrasts with the Kratzer severing prediction (`VoiceFlavor.thetaRole`),
    which derives the role from Voice flavor rather than verb-internal
    semantics. Studies comparing the two accounts can apply both to the
    same `Verb` and inspect divergence. -/
def Verb.predictedSubjectTheta (v : Verb) : Option ThetaRole :=
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
    [jin-koenig-2021] §5.5, ex. 13a:

    - **FEAR class**: negative-valence preferential attitudes activate
      p (feared content) and ¬p (desired alternative).
    - **FORGET class**: negative implicative verbs entail ¬p in w₀.
    - **STOP/PREVENT**: causative preventatives entail ¬p in w₀.

    DENY class triggers (doubt, question) are excluded — their
    EN-triggering requires matrix negation/questioning (pragmatic,
    via neg-raising), not purely lexical semantics. Temporal, logical,
    and comparative triggers are operators/connectives, not verbs. -/
def Verb.isENTrigger (v : Verb) : Bool :=
  -- FEAR class: negative-valence preferential attitudes
  (v.preferentialValence == some .negative) ||
  -- FORGET class: negative implicative verbs
  (v.implicative == some .negative) ||
  -- STOP/PREVENT: causative prevent verbs
  (v.causative == some .prevent)

/-- Does this causative verb assert necessity (like "cause")?

    DERIVED: delegates to `Causative.assertsNecessity`. -/
def Verb.assertsNecessity (v : Verb) : Bool :=
  v.causative.map (·.assertsNecessity) |>.getD false

/-- Does success of this implicative verb entail the complement?

    DERIVED: delegates to `Implicative.entailsComplement`.
    Returns `some true` for positive implicatives (*manage*, *remember*),
    `some false` for negative (*fail*, *forget*), `none` for non-implicatives. -/
def Verb.entailsComplement (v : Verb) : Option Bool :=
  v.implicative.map (·.entailsComplement)

/-- Is this verb a preferential attitude predicate? -/
def Verb.isPreferentialAttitude (v : Verb) : Bool :=
  v.preferentialValence.isSome

/-- Can this verb take a clausal (CP) complement?

    Checks both primary and alternate complement frames. Used to classify
    verbs as CP-selecting vs non-CP-selecting for coordination studies
    ([schwarzer-2026]). -/
def Verb.canTakeClausalComplement (v : Verb) : Bool :=
  v.complementType.isClausal ||
  match v.altComplementType with | some ct => ct.isClausal | none => false

/-- Can this verb take a nominal (DP) complement?

    Checks both primary and alternate complement frames. -/
def Verb.canTakeNominalComplement (v : Verb) : Bool :=
  v.complementType.isNominal ||
  match v.altComplementType with | some ct => ct.isNominal | none => false

/-- Look up a verb core by citation form and sense tag. -/
def lookupSense (verbs : List Verb) (form : String) (tag : SenseTag := .default) :
    Option Verb :=
  verbs.find? (λ v => v.form == form && v.senseTag == tag)
