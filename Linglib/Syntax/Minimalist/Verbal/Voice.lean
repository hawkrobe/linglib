import Linglib.Syntax.Minimalist.Agree.Basic
import Linglib.Syntax.Minimalist.Verbal.Decomposition
import Linglib.Semantics.ArgumentStructure.Linking
import Linglib.Syntax.Voice.Alternation
import Linglib.Syntax.Reciprocal

/-!
# Voice Head Flavors
[chomsky-2001] [coon-2019] [cuervo-2003] [harley-2014] [kratzer-1996]
[legate-2003] [martin-schaefer-kastner-2025] [schaefer-2008] [siloni-2012]
[wood-2015]

Voice heads introduce (or fail to introduce) external arguments
([kratzer-1996]).

## Main definitions

* `Flavor` — the guise typology (after [schaefer-2008]), with projections
  onto neighboring substrates: `alternation` ([creissels-2025] coding-frame
  operation), `thetaRole`, `defaultPhasal`, `recipFormation` ([siloni-2012]).
* `Head` — a flavor plus featural and per-construction properties, with the
  predicate API `IsPhasal`/`AssignsTheta`/`HasSemantics`.
* `buildDecomposition` — the Voice–VerbHead bridge: Voice contributes vDO
  when it assigns θ; CAUSE belongs to the root ([cuervo-2003],
  [pylkkanen-2008]).
* `Params` + `Flavor.toParams` — the ±D/±λx parametric decomposition
  ([alexiadou-schaefer-2015]); `ProjectionLocus` — which projection an
  exponent spells out.

## Implementation notes

[wood-2015] uses a single v head whose interpretation introduces CAUSE; the
multi-headed decomposition here follows [cuervo-2003] and captures the same
Voice–CAUSE independence. See `Wood2015` for the Icelandic -st apparatus.
-/

namespace Minimalist
namespace Voice

/-! ### Flavors -/

/-- Typology of Voice head flavors (after [schaefer-2008]). -/
inductive Flavor where
  /-- Introduces an agent external argument ([kratzer-1996] Voice_AG). -/
  | agentive
  /-- Introduces a causer ([schaefer-2008] Voice_CAUSE). -/
  | causer
  /-- Semantically vacuous, no θ-role, [D] for PF marking (Romance
      anticausative SE, Chuj *-j*; [munoz-perez-2026]). -/
  | nonThematic
  /-- No specifier, no semantics (dispositional middles). -/
  | expletive
  /-- Demotes the agent to an implicit generic human (Finnish "passive"). -/
  | impersonal
  /-- Checks Case but does not assign θ ([collins-2005]: *by* heads VoiceP). -/
  | passive
  /-- Introduces an agent with absolutive (not ergative) case; demotes the
      object to oblique ([scott-2023]). -/
  | antipassive
  /-- [+θ, +D]: agent binds the internal argument (Romance *se*;
      [martin-schaefer-kastner-2025]). -/
  | reflexive
  /-- [+θ, +D]: agent in the mutual relation with the internal argument —
      [siloni-2012]'s syntactic reciprocalization (Romance/Slavic
      reciprocal *se*). -/
  | reciprocal
  /-- [+θ, +D]: introduces an experiencer external argument
      (psych causatives). -/
  | experiencer
  deriving DecidableEq, Repr

/-! ### Flavor projections -/

/-- The [creissels-2025] valency alternation each flavor realizes; `none`
    when the coding frame is untouched or the effect is not a valency
    operation. -/
def Flavor.alternation : Flavor → Option _root_.Voice.ValencyAlternation
  | .causer      => some _root_.Voice.causativization
  | .nonThematic => some _root_.Voice.decausativization
  | .impersonal  => some _root_.Voice.iPassivization
  | .passive     => some _root_.Voice.passivization
  | .antipassive => some _root_.Voice.antipassivization
  | .reflexive   => some _root_.Voice.reflexivization
  | .reciprocal  => some _root_.Voice.reciprocalization
  | .agentive | .expletive | .experiencer => none

/-- The external θ-role a flavor assigns ([kratzer-1996] severing).
    `ThetaRole` has no dedicated causer, so causer Voice maps to
    `stimulus`, its closest interface role. -/
def Flavor.thetaRole : Flavor → Option ThetaRole
  | .agentive     => some .agent
  | .causer       => some .stimulus
  | .antipassive  => some .agent        -- agent present, with ABS case
  | .reflexive    => some .agent        -- binds the internal argument
  | .reciprocal   => some .agent        -- in the mutual relation ([siloni-2012])
  | .experiencer  => some .experiencer  -- subject-experiencer ([wood-2015])
  | .nonThematic | .expletive | .impersonal | .passive => none

/-- Default phasehood ([collins-2005]/[chomsky-2001] baseline):
    θ-assigning, specifier-projecting Voice is phasal. Antipassive is the
    documented anomaly (θ-assigning yet non-phasal, per [scott-2023]);
    per-construction divergences go via `Head.phaseOverride`. -/
def Flavor.defaultPhasal : Flavor → Bool
  | .agentive | .causer | .reflexive | .reciprocal | .experiencer => true
  | .nonThematic | .expletive | .impersonal | .passive | .antipassive => false

/-- The [siloni-2012] formation locus a flavor realizes: reciprocal Voice
    IS syntactic reciprocalization; no flavor realizes lexical formation. -/
def Flavor.recipFormation : Flavor → Option _root_.Reciprocal.Formation
  | .reciprocal => some .syntactic
  | _ => none

/-- Voice-formed reciprocals license no discontinuous construction
    ([siloni-2012] §7: *\*Jean s'est embrassé avec Marie*). -/
theorem reciprocal_voice_no_discontinuous :
    (Flavor.reciprocal.recipFormation.map
      _root_.Reciprocal.Formation.allowsDiscontinuous) = some false := rfl

/-! ### The Voice head -/

/-- A Voice head: a flavor plus featural and per-construction properties. -/
structure Head where
  /-- The flavor determining argument introduction and semantics. -/
  flavor : Flavor
  /-- [D] subcategorization feature: requires a specifier at PF. -/
  hasD : Bool
  /-- Per-construction override of `flavor.defaultPhasal` — the locus for
      per-paper divergence ([erlewine-sommerlot-2025] Malayic passive,
      [coon-2019] Chol `v_w`/`v_ch`, [coon-mateo-pedro-preminger-2014]
      Mam Agent Focus). -/
  phaseOverride : Option Bool := none
  /-- Case-checking ([collins-2005] p. 96 feature dissociation: passive
      Voice/*by* checks Case). Default false. -/
  checksCase : Bool := false
  /-- Agree-relevant features (e.g., [uOblique] for Mam *=(y)a'*).
      Default empty. -/
  features : FeatureBundle := ⊥
  deriving DecidableEq, Repr

/-! ### Predicate API

Prop predicates with `Decidable` instances; the data fields `hasD` and
`checksCase` are exposed in Prop form by `HasD` and `ChecksCase`. -/

/-- Phasal: the per-construction override if present, else the flavor
    default. -/
def Head.IsPhasal (v : Head) : Prop :=
  v.phaseOverride.getD v.flavor.defaultPhasal = true

instance (v : Head) : Decidable v.IsPhasal :=
  inferInstanceAs (Decidable (v.phaseOverride.getD v.flavor.defaultPhasal = true))

/-- Assigns a θ-role to its specifier (`flavor.thetaRole.isSome`).
    Narrower than `Params.assignsTheta?`, which also counts impersonal
    Voice's ∃-bound implicit agent. -/
def Head.AssignsTheta (v : Head) : Prop :=
  v.flavor.thetaRole.isSome = true

instance (v : Head) : Decidable v.AssignsTheta :=
  inferInstanceAs (Decidable (_ = true))

/-- Characterization: exactly the agentive, causer, antipassive,
    reflexive, reciprocal, and experiencer flavors assign θ. -/
theorem Head.assignsTheta_iff (v : Head) :
    v.AssignsTheta ↔
      v.flavor = .agentive ∨ v.flavor = .causer ∨ v.flavor = .antipassive ∨
      v.flavor = .reflexive ∨ v.flavor = .reciprocal ∨
      v.flavor = .experiencer := by
  cases hv : v.flavor <;> simp [Head.AssignsTheta, Flavor.thetaRole, hv]

/-- Has semantic content — everything except `nonThematic` (purely PF)
    and `expletive` (vacuous middle). -/
def Head.HasSemantics (v : Head) : Prop :=
  v.flavor ≠ .nonThematic ∧ v.flavor ≠ .expletive

instance (v : Head) : Decidable v.HasSemantics := by
  unfold Head.HasSemantics; infer_instance

/-- θ-assignment entails semantic content. The converse fails — passive
    Voice has semantics without θ (`passive_has_semantics`,
    `passive_no_theta`). -/
theorem Head.AssignsTheta.hasSemantics {v : Head} (h : v.AssignsTheta) :
    v.HasSemantics := by
  cases hv : v.flavor <;>
    simp_all [Head.AssignsTheta, Head.HasSemantics, Flavor.thetaRole]

/-- Subcategorizes for a specifier (Prop form of `hasD`). -/
def Head.HasD (v : Head) : Prop := v.hasD = true

instance (v : Head) : Decidable v.HasD :=
  inferInstanceAs (Decidable (v.hasD = true))

/-- Checks Case (Prop form of `checksCase`). -/
def Head.ChecksCase (v : Head) : Prop := v.checksCase = true

instance (v : Head) : Decidable v.ChecksCase :=
  inferInstanceAs (Decidable (v.checksCase = true))

/-! ### Canonical heads -/

/-- Agentive Voice (transitive/unergative): introduces an agent, phasal. -/
def agentive : Head :=
  { flavor := .agentive, hasD := true }

/-- Causer Voice: introduces a causer, phasal. -/
def causer : Head :=
  { flavor := .causer, hasD := true }

/-- Non-thematic Voice (anticausative): no θ-role, [D] for PF marking. -/
def anticausative : Head :=
  { flavor := .nonThematic, hasD := true }

/-- Expletive Voice (middle): no specifier, no semantics. -/
def middle : Head :=
  { flavor := .expletive, hasD := false }

/-- Impersonal Voice (Finnish "passive"): ∃-closes the agent; no θ-marked
    specifier. -/
def impersonal : Head :=
  { flavor := .impersonal, hasD := false }

/-- Passive Voice: *by* checks Case without assigning θ ([collins-2005];
    v assigns the external θ-role in Spec,vP), and is non-phasal — which
    keeps PartP accessible for smuggling. Contested by [legate-2003]. -/
def passive : Head :=
  { flavor := .passive, hasD := true, checksCase := true }

/-- Reflexive Voice: agent coreferent with the internal argument (Romance
    *se*, [martin-schaefer-kastner-2025]). [wood-2015]'s Icelandic *-st*
    is a SpecpP clitic, not an exponent of this head. -/
def reflexive : Head :=
  { flavor := .reflexive, hasD := true }

/-- Reciprocal Voice: agent in the mutual relation with the internal
    argument — [siloni-2012]'s syntactic reciprocalization (Romance/Slavic
    reciprocal *se*), twin of `reflexive`. Lexicon-formed reciprocal verbs
    enter the syntax already symmetric and are not exponents of this head. -/
def reciprocal : Head :=
  { flavor := .reciprocal, hasD := true }

/-- Experiencer Voice: experiencer external argument in Spec,VoiceP.
    Distinct from [wood-2015]'s Icelandic dative-subject experiencers,
    where Voice is non-thematic and the experiencer an applied dative. -/
def experiencer : Head :=
  { flavor := .experiencer, hasD := true }

/-! ### Verification theorems -/

/-- Agentive Voice assigns a θ-role. -/
theorem agentive_assigns_theta : agentive.AssignsTheta := by decide

/-- Non-thematic Voice does NOT assign a θ-role ([munoz-perez-2026]). -/
theorem nonThematic_no_theta : ¬ anticausative.AssignsTheta := by decide

/-- Non-thematic Voice has no semantic contribution — the core claim of
    [munoz-perez-2026]: SE is a PF phenomenon. -/
theorem nonThematic_no_semantics : ¬ anticausative.HasSemantics := by decide

/-- Agentive Voice is a phase head (v* = Voice_AG). -/
theorem agentive_is_phase : agentive.IsPhasal := by decide

/-- Non-thematic Voice is NOT a phase head. -/
theorem anticausative_not_phase : ¬ anticausative.IsPhasal := by decide

/-- Impersonal Voice does NOT assign a θ-role (the agent is existentially
    closed, not projected to a specifier). -/
theorem impersonal_no_theta : ¬ impersonal.AssignsTheta := by decide

/-- Impersonal Voice HAS semantics: existential closure over the agent,
    unlike vacuous non-thematic Voice. -/
theorem impersonal_has_semantics : impersonal.HasSemantics := by decide

/-- Passive Voice does NOT assign a θ-role (v does). -/
theorem passive_no_theta : ¬ passive.AssignsTheta := by decide

/-- Passive Voice is NOT a phase head. -/
theorem passive_not_phase : ¬ passive.IsPhasal := by decide

/-- Passive Voice HAS semantic content (*by* mediates Case-checking). -/
theorem passive_has_semantics : passive.HasSemantics := by decide

/-- Passive Voice checks Case ([collins-2005], p. 96). -/
theorem passive_checks_case : passive.ChecksCase := by decide

/-- Reflexive Voice assigns a θ-role ([wood-2015]). -/
theorem reflexive_assigns_theta : reflexive.AssignsTheta := by decide

/-- Reciprocal Voice assigns a θ-role ([siloni-2012]: parasitic assignment
    gives the subject both roles). -/
theorem reciprocal_assigns_theta : reciprocal.AssignsTheta := by decide

/-- Experiencer Voice assigns a θ-role ([wood-2015]). -/
theorem experiencer_assigns_theta : experiencer.AssignsTheta := by decide

/-! ### Voice–VerbHead bridge ([kratzer-1996] in [cuervo-2003] terms) -/

/-- The full verbal decomposition: Voice prepends vDO when it assigns θ;
    the root supplies the lower structure, including vCAUSE for
    change-of-state roots ([wood-2015], [pylkkanen-2008]). -/
def buildDecomposition (voice : Head) (rootStructure : List VerbHead) :
    List VerbHead :=
  if voice.AssignsTheta then .vDO :: rootStructure
  else rootStructure

/-- θ-assigning Voice prepends vDO to the root structure. -/
theorem theta_voice_prepends_vDO (v : Head) (root : List VerbHead)
    (h : v.AssignsTheta) :
    buildDecomposition v root = .vDO :: root := by
  simp [buildDecomposition, h]

/-- Non-θ Voice leaves the root structure unchanged. -/
theorem no_theta_passthrough (v : Head) (root : List VerbHead)
    (h : ¬ v.AssignsTheta) :
    buildDecomposition v root = root := by
  simp [buildDecomposition, h]

/-- Causative pattern: agentive Voice + [vCAUSE, vGO, vBE] is causative. -/
theorem agent_plus_change_is_causative :
    isCausative (buildDecomposition agentive [.vCAUSE, .vGO, .vBE]) = true := by
  decide

/-- Inchoative pattern: non-thematic Voice + [vCAUSE, vGO, vBE] stays
    inchoative. -/
theorem nonthematic_plus_change_is_inchoative :
    isInchoative (buildDecomposition anticausative [.vCAUSE, .vGO, .vBE]) = true := by
  decide

/-- Activity pattern: agentive Voice + [] yields an activity. -/
theorem agent_plus_nothing_is_activity :
    isActivity (buildDecomposition agentive []) = true := by
  decide

/-- State pattern: non-thematic Voice + [vBE] yields a state. -/
theorem nonthematic_plus_state_is_state :
    isState (buildDecomposition anticausative [.vBE]) = true := by
  decide

/-- The causative alternation: [vCAUSE, vGO, vBE] is causative under
    agentive Voice, inchoative under non-thematic Voice — only vDO
    differs. -/
theorem causative_alternation :
    isCausative (buildDecomposition agentive [.vCAUSE, .vGO, .vBE]) = true ∧
    isInchoative (buildDecomposition anticausative [.vCAUSE, .vGO, .vBE]) = true := by
  decide

/-- Voice determines causativity: over the root structure
    [vCAUSE, vGO, vBE], the result is causative iff Voice assigns θ. -/
theorem voice_determines_causativity (v : Head) :
    isCausative (buildDecomposition v [.vCAUSE, .vGO, .vBE]) = true ↔
    v.AssignsTheta := by
  cases v with | mk flavor _ _ _ _ =>
  cases flavor <;>
    simp [buildDecomposition, isCausative, Head.AssignsTheta, Flavor.thetaRole]

/-- CAUSE is present in both causative and anticausative decompositions —
    the independence claim: CAUSE is part of the root, not Voice. -/
theorem cause_independent_of_voice :
    hasCause (buildDecomposition agentive [.vCAUSE, .vGO, .vBE]) = true ∧
    hasCause (buildDecomposition anticausative [.vCAUSE, .vGO, .vBE]) = true := by
  decide

/-! ### Feature dissociation ([collins-2005] §4) -/

/-- In active, v (= agentive Voice) assigns θ AND controls Case-checking. -/
theorem active_theta_and_case_unified :
    agentive.AssignsTheta ∧ ¬ agentive.ChecksCase := by decide

/-- Passive dissociates them: Voice does NOT assign θ (v does), but Voice
    DOES check Case. -/
theorem passive_theta_case_dissociated :
    ¬ passive.AssignsTheta ∧ passive.ChecksCase := by decide

/-- UTAH: the external-argument position is present in both active and
    passive. -/
theorem utah_active_passive :
    agentive.HasD ∧ passive.HasD := by decide

/-- Passive Voice does not prepend vDO: no θ, so `buildDecomposition`
    passes the root structure through unchanged. -/
theorem passive_no_vDO (root : List VerbHead) :
    buildDecomposition passive root = root := by
  simp [buildDecomposition, passive_no_theta]

/-! ### Voice–phase bridge -/

/-- Agentive Voice corresponds to traditional v* (phase head); both
    agentive and causer Voice are phasal. -/
theorem agentive_voice_is_phase_head :
    agentive.IsPhasal ∧ causer.IsPhasal := by decide

/-- Non-thematic and expletive Voice are NOT phase heads. -/
theorem nonthematic_voice_not_phase_head :
    ¬ anticausative.IsPhasal ∧ ¬ middle.IsPhasal := by decide

-- Voice phasehood does NOT track θ-assignment in general.
-- [erlewine-sommerlot-2025] (Malayic) treats every Voice — including passive
-- and bare passive — as a phase head; [coon-2019] (Chol) treats certain
-- agentive Voice heads (the intransitive `v_w`/`v_ch` variants) as non-phasal
-- despite assigning a θ-role. The `phaseOverride` field is the
-- per-construction locus where such divergences are made explicit.

/-! ### Parametric decomposition ([alexiadou-schaefer-2015], [schaefer-2017]) -/

/-- How Voice introduces an external argument semantically: [+λx]
    λ-abstraction (`thematicArgument`), [+∃x] existential binding
    (`thematicExistential`, [schaefer-2017] medio-passive), or none
    (`expletive`). -/
inductive ExternalArgSemantics where
  | thematicArgument
  | thematicExistential
  | expletive
  deriving DecidableEq, Repr

/-- The ±D/±λx decomposition ([alexiadou-schaefer-2015],
    [schaefer-2017]); `none` = underspecified (Indonesian *ber-* is
    ⟨none, none⟩, [beavers-udayana-2022]). -/
structure Params where
  /-- Does Voice select a syntactic specifier (DP)? `some true` = [+D],
      `some false` = [−D], `none` = underspecified. -/
  selectsSpecifier : Option Bool
  /-- Does Voice introduce semantic agentivity/causation?
      `none` = underspecified. -/
  extArgSemantics : Option ExternalArgSemantics
  deriving DecidableEq, Repr

/-- Map each named flavor to its cell in the ±D/±λx parameter space.

    | Flavor | ±D | ±λx | Example |
    |--------|----|-----|---------|
    | agentive | +D | +λx (arg) | English active |
    | causer | +D | +λx (arg) | Psych causative |
    | antipassive | +D | +λx (arg) | Mayan antipassive |
    | reflexive | +D | +λx (arg) | Icelandic -st reflexive |
    | reciprocal | +D | +λx (arg) | Romance reciprocal se |
    | experiencer | +D | +λx (arg) | Icelandic subject-exp -st |
    | nonThematic | +D | −λx | Romance anticausative SE |
    | expletive | −D | −λx | English dispositional middle |
    | impersonal | −D | +∃x | Finnish impersonal |
    | passive | +D | −λx | English passive (*by*) |

    `nonThematic` and `passive` occupy the same cell [+D, −λx]; they
    differ in Case-checking (`Head.checksCase`), a property of the full
    `Head`, not of the parametric decomposition. -/
def Flavor.toParams : Flavor → Params
  | .agentive     => { selectsSpecifier := some true,  extArgSemantics := some .thematicArgument }
  | .causer       => { selectsSpecifier := some true,  extArgSemantics := some .thematicArgument }
  | .antipassive  => { selectsSpecifier := some true,  extArgSemantics := some .thematicArgument }
  | .reflexive    => { selectsSpecifier := some true,  extArgSemantics := some .thematicArgument }
  | .reciprocal   => { selectsSpecifier := some true,  extArgSemantics := some .thematicArgument }
  | .experiencer  => { selectsSpecifier := some true,  extArgSemantics := some .thematicArgument }
  | .nonThematic  => { selectsSpecifier := some true,  extArgSemantics := some .expletive }
  | .expletive    => { selectsSpecifier := some false, extArgSemantics := some .expletive }
  | .impersonal   => { selectsSpecifier := some false, extArgSemantics := some .thematicExistential }
  | .passive      => { selectsSpecifier := some true,  extArgSemantics := some .expletive }

/-- The parametric decomposition of a Head, derived from its flavor. -/
def Head.params (v : Head) : Params := v.flavor.toParams

/-- Semantic external-argument presence; `none` when underspecified.
    Broader than `Head.AssignsTheta` — impersonal's ∃-bound agent counts. -/
def Params.assignsTheta? (p : Params) : Option Bool :=
  match p.extArgSemantics with
  | some .thematicArgument    => some true
  | some .thematicExistential => some true
  | some .expletive           => some false
  | none                      => none

/-- Compatible iff agreeing on all specified dimensions. -/
def Params.isCompatibleWith (p q : Params) : Bool :=
  (p.selectsSpecifier.isNone || q.selectsSpecifier.isNone ||
   p.selectsSpecifier == q.selectsSpecifier) &&
  (p.extArgSemantics.isNone || q.extArgSemantics.isNone ||
   p.extArgSemantics == q.extArgSemantics)

/-- Is this parameter setting fully specified? -/
def Params.isFullySpecified (p : Params) : Bool :=
  p.selectsSpecifier.isSome && p.extArgSemantics.isSome

/-! ### Parametric bridge theorems -/

/-- All named flavors produce fully specified params. -/
theorem flavor_params_fully_specified (f : Flavor) :
    f.toParams.isFullySpecified = true := by
  cases f <;> rfl

/-- Semantic external-argument presence per flavor: the θ-assigning
    flavors plus impersonal. -/
theorem flavor_params_theta_consistent (f : Flavor) :
    f.toParams.assignsTheta? = some (match f with
      | .agentive | .causer | .antipassive | .reflexive | .reciprocal
      | .experiencer | .impersonal => true
      | .nonThematic | .expletive | .passive => false) := by
  cases f <;> rfl

/-- Compatibility is reflexive. -/
theorem params_compatible_refl (p : Params) :
    p.isCompatibleWith p = true := by
  cases p with | mk s e =>
  cases s with
  | none => cases e with | none => rfl | some e => cases e <;> rfl
  | some s => cases s <;> (cases e with | none => rfl | some e => cases e <;> rfl)

/-- A fully underspecified Params is compatible with every named flavor —
    the key property for Indonesian *ber-* ([beavers-udayana-2022]). -/
theorem underspecified_compatible_with_all (f : Flavor) :
    let ber : Params := { selectsSpecifier := none, extArgSemantics := none }
    ber.isCompatibleWith f.toParams = true := by
  cases f <;> rfl

/-! ### Projection locus -/

/-- The projection a non-active exponent (Romance *se*, Icelandic *-st*,
    Hebrew *hit-*) spells out: Voice_{D}, Voice_{∅}
    ([alexiadou-schaefer-2015], [wood-marantz-2017]), or v itself
    ([wood-2015] on Icelandic *-ka*). Complement of `Params`, which
    parameterizes the head's own settings. -/
inductive ProjectionLocus where
  /-- Voice carrying a [D] feature; projects a specifier
      ([wood-2015] Voice_{D}). -/
  | voiceD
  /-- Specifierless Voice; no [D] feature ([wood-2015] Voice_{∅}). -/
  | voiceBare
  /-- Underspecified: compatible with either `voiceD` or `voiceBare`. -/
  | voiceDOrBare
  /-- Exponent of v, not Voice (e.g., Icelandic *-ka* per [wood-2015]). -/
  | vHead
  deriving DecidableEq, Repr

end Voice
end Minimalist
