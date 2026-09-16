import Linglib.Syntax.Category.Verb.Defs
import Linglib.Semantics.Root.Defs

/-! # Verb entry — derived API

The classifications of a verb entry, read off its primitive fields rather than stored:
unaccusativity from voice, veridicality from the attitude, factivity from the factivity class,
trigger status from event structure, and the linking of the external argument.
-/

open Aspect
open Presupposition

open ArgumentStructure
open Aspect
open NaturalLogic (Signature)
open Causation.Psych (CausalSource)
open ArgumentStructure (EntailmentProfile)
open Aspect (DegreeAchievementScale)
open Aspect (VerbIncClass)
open ArgumentStructure

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

/-- The verb's within-class root content ([spalek-mcnally-2026]), read off its `root`. -/
def Verb.rootContent (v : Verb) : Semantics.Root.Content :=
  v.root.content

/-- The verb's raw kind signature ([beavers-koontz-garboden-2020]): the
    un-closed atom-kinds of its root, the source of truth for what the verb
    structurally entails. `Verb.closedKinds` is its collocational closure and
    the root the sole provenance of the kind signature. -/
def Verb.kinds (v : Verb) : Semantics.Root.Kinds :=
  v.root.kinds

/-- The verb's closed kind signature ([beavers-koontz-garboden-2020]): the
    collocational closure of `Verb.kinds` (`cause ⟹ result ⟹ state`), which the
    event-structure spine (`Semantics.Root.template`, `CosModel.denote`) runs on. -/
def Verb.closedKinds (v : Verb) : Semantics.Root.Kinds :=
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

/-- The veridicality of the verb's attitude, if it has one. -/
def Verb.veridicality (v : Verb) : Option Doxastic.Veridicality :=
  v.attitude.map (·.veridicality)

/-- The verb is a doxastic attitude. -/
def Verb.IsDoxastic (v : Verb) : Prop :=
  match v.attitude with
  | some (.doxastic _) => True
  | _ => False

instance : DecidablePred Verb.IsDoxastic := fun v ↦ by
  unfold Verb.IsDoxastic; split <;> infer_instance

/-- The verb is a preferential attitude. -/
def Verb.IsPreferential (v : Verb) : Prop :=
  match v.attitude with
  | some (.preferential _) => True
  | _ => False

instance : DecidablePred Verb.IsPreferential := fun v ↦ by
  unfold Verb.IsPreferential; split <;> infer_instance

/-- The valence of the verb's preferential attitude, if it has one. -/
def Verb.preferentialValence (v : Verb) : Option Preferential.Valence :=
  v.attitude.bind (·.valence)

/-- The verb is factive: it carries a [karttunen-1971b] factivity class. Veridicality is an
    entailment and does not make a verb factive. -/
def Verb.IsFactive (v : Verb) : Prop := v.factivity ≠ none

instance : DecidablePred Verb.IsFactive := fun v ↦
  inferInstanceAs (Decidable (v.factivity ≠ none))

/-- The verb presupposes its complement, by factivity or as a change of state. -/
def Verb.PresupposesComplement (v : Verb) : Prop := v.IsFactive ∨ v.cosType ≠ none

instance : DecidablePred Verb.PresupposesComplement := fun v ↦
  inferInstanceAs (Decidable (v.IsFactive ∨ v.cosType ≠ none))

/-- The kind of presupposition trigger a verb is, derived from its event structure rather than
    stipulated ([roberts-simons-2024]): a verb that presupposes its complement, by factivity or
    a change of state, is a soft trigger; an implicative presupposes its causal prerequisite
    ([nadathur-2023-implicatives]); and an occasion verb presupposes the occasion it evokes
    ([solstad-bott-2024]). The soft/hard distinction is not operationalized, so `.softTrigger`
    is the placeholder for the first and third. -/
def Verb.triggerType (v : Verb) : Option Presupposition.TriggerType :=
  if v.PresupposesComplement then some .softTrigger
  else if v.implicative.isSome then some .prerequisiteSoft
  else if v.senseTag = .occasion then some .softTrigger
  else none

/-- The verb is a presupposition trigger. -/
def Verb.IsTrigger (v : Verb) : Prop := v.triggerType ≠ none

instance : DecidablePred Verb.IsTrigger := fun v ↦
  inferInstanceAs (Decidable (v.triggerType ≠ none))

/-- The verb is a causative. -/
def Verb.IsCausative (v : Verb) : Prop := v.causative ≠ none

instance : DecidablePred Verb.IsCausative := fun v ↦
  inferInstanceAs (Decidable (v.causative ≠ none))

/-- Does this causative verb assert sufficiency (like "make")?

    DERIVED: delegates to `Causative.AssertsSufficiency`. -/
def Verb.AssertsSufficiency (v : Verb) : Prop :=
  match v.causative with
  | some c => c.AssertsSufficiency
  | none => False

instance : DecidablePred Verb.AssertsSufficiency := fun v => by
  unfold Verb.AssertsSufficiency; split <;> infer_instance

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

    Contrasts with the Kratzer severing prediction (`Voice.Flavor.thetaRole`),
    which derives the role from Voice flavor rather than verb-internal
    semantics. Studies comparing the two accounts can apply both to the
    same `Verb` and inspect divergence. -/
def Verb.predictedSubjectTheta (v : Verb) : Option ThetaRole :=
  if v.controlType == .raising then none
  else if v.levinClass == some .weather then none
  else if v.causalSource.isSome then some .stimulus
  else if v.attitude.isSome then some .experiencer
  else if v.IsFactive ∧ v.attitude.isNone then some .experiencer
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


/-- Look up a verb core by citation form and sense tag. -/
def lookupSense (verbs : List Verb) (form : String) (tag : SenseTag := .default) :
    Option Verb :=
  verbs.find? (λ v => v.form == form && v.senseTag == tag)
