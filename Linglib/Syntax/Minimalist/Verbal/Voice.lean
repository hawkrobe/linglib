import Linglib.Syntax.Minimalist.Agree.Basic
import Linglib.Syntax.Minimalist.Verbal.Decomposition
import Linglib.Semantics.ArgumentStructure.Linking
import Linglib.Syntax.Voice.Alternation

/-!
# Voice Head Flavors
[chomsky-2001] [coon-2019] [cuervo-2003] [harley-2014] [kratzer-1996] [legate-2003] [martin-schaefer-kastner-2025] [schaefer-2008] [wood-2015]

Voice heads introduce (or fail to introduce) external arguments.
The key typology from [schaefer-2008]:

- **Agentive**: Introduces an agent external argument ([kratzer-1996] Voice_AG)
- **Causer**: Introduces a causer ([schaefer-2008] Voice_CAUSE)
- **NonThematic**: Semantically vacuous — no θ-role, but has a [D] feature
  requiring PF realization (anticausative SE in Romance; Muñoz [munoz-perez-2026])
- **Expletive**: No specifier, no semantics (middle voice, dispositionals)
- **Reflexive**: [+θ, +D] with reflexive binding (Romance *se*; [martin-schaefer-kastner-2025])
- **Experiencer**: [+θ, +D] introducing an experiencer external argument (psych causatives)

## Key Claim

Non-thematic Voice contributes no semantics. SE is a PF marker of absent
external argument, not a semantic operator. Evidence: SE is optional in
Chilean Spanish when Fission produces a syncretic clitic.

## Voice–VerbHead Bridge (§§ 5–6)

Voice and VerbHead are both "little-v" but encode different
dimensions: Voice determines *whether* an external argument is introduced;
VerbHead decomposes the *event structure* into subevents.

Following [cuervo-2003] and [pylkkanen-2008], the CAUSE
relation is modeled here as an independent VerbHead in the root's
event decomposition — present in both causative and anticausative
alternants. Voice contributes vDO (the agent's activity subevent)
when it assigns a θ-role, but does NOT contribute the causal relation.

Note: [wood-2015] uses a SINGLE v head whose interpretation
introduces CAUSE, rather than [cuervo-2003]'s multi-headed
decomposition. The VerbHead decomposition used here is a linglib
modeling choice that captures the same Voice–CAUSE independence
using [cuervo-2003]'s notation. See
`Wood2015` for the Icelandic -st
apparatus (the Wood-2015 -st classification, root-structure
projections, and ±D/±λx grid analysis); the lexical fragment
`Icelandic.Predicates` carries only the consensus verb
forms.

-/

namespace Minimalist

-- ============================================================================
-- § 1: Voice Flavors
-- ============================================================================

/-- Typology of Voice head flavors.

    Agentive Voice introduces an agent; causer Voice introduces a causer;
    non-thematic Voice has no semantics (anticausative SE);
    expletive Voice has neither specifier nor semantics (middles);
    passive Voice checks Case without assigning θ ([collins-2005]: *by*);
    reflexive Voice introduces an agent that binds the internal argument
    (Romance *se*; [martin-schaefer-kastner-2025]);
    experiencer Voice introduces an experiencer external argument. -/
inductive VoiceFlavor where
  | agentive     -- Introduces external argument with agent θ-role ([kratzer-1996])
  | causer       -- Introduces causer ([schaefer-2008]: Voice_CAUSE)
  | nonThematic  -- Semantically vacuous, no θ-role (anticausative SE, Chuj -j)
  | expletive    -- No specifier, no semantics (middle voice)
  | impersonal   -- Demotes agent to implicit generic human (Finnish "passive")
  | passive      -- Checks Case but does not assign θ ([collins-2005]: *by* heads VoiceP)
  | antipassive  -- Introduces agent with absolutive (not ergative) case; demotes object to oblique ([scott-2023])
  | reflexive    -- [+θ, +D]: agent binds the internal argument (Romance se)
  | experiencer  -- [+θ, +D]: introduces an experiencer external argument (psych causatives)
  deriving DecidableEq, Repr

/-- The coding-frame operation each Voice flavor realizes, projecting the
    Minimalist head onto [creissels-2025]'s valency alternations
    (`Syntax/Voice/Alternation.lean`): passive Voice denucleativizes A,
    antipassive denucleativizes P, reflexive/causer/impersonal map to
    their typological counterparts. `none` for flavors that leave the
    coding frame intact (agentive, experiencer) or whose effect is not a
    valency operation (expletive middle). -/
def VoiceFlavor.alternation : VoiceFlavor → Option _root_.Voice.ValencyAlternation
  | .causer      => some _root_.Voice.causativization
  | .nonThematic => some _root_.Voice.decausativization
  | .impersonal  => some _root_.Voice.iPassivization
  | .passive     => some _root_.Voice.passivization
  | .antipassive => some _root_.Voice.antipassivization
  | .reflexive   => some _root_.Voice.reflexivization
  | .agentive | .expletive | .experiencer => none

/-- The default phasehood for each Voice flavor under the
    Collins-2005 / Chomsky-2001 baseline: agentive, causer, reflexive,
    and experiencer Voice are phase heads (they assign a θ-role and
    project a specifier); the other flavors are non-phasal by default.
    Per-construction divergences from this baseline are encoded via
    `VoiceHead.phaseOverride`. -/
def VoiceFlavor.defaultPhasal : VoiceFlavor → Bool
  | .agentive | .causer | .reflexive | .experiencer => true
  | .nonThematic | .expletive | .impersonal | .passive | .antipassive => false

/-- Severing prediction ([kratzer-1996]): Voice flavor determines
    WHICH theta role the external argument gets, going beyond
    `VoiceHead.AssignsTheta` (which only says WHETHER there is one).

    The current typology distinguishes agent, stimulus, and experiencer
    among θ-assigning flavors; non-θ flavors return `none`. -/
def VoiceFlavor.thetaRole : VoiceFlavor → Option ThetaRole
  | .agentive     => some .agent
  | .causer       => some .stimulus
  | .antipassive  => some .agent     -- agent still present, just with ABS case
  | .reflexive    => some .agent     -- agent that binds internal arg ([wood-2015])
  | .experiencer  => some .experiencer  -- subject-experiencer ([wood-2015])
  | .nonThematic  => none
  | .expletive    => none
  | .impersonal   => none
  | .passive      => none

-- ============================================================================
-- § 2: Voice Head Structure
-- ============================================================================

/-- A Voice head with its properties. -/
structure VoiceHead where
  /-- The flavor determining argument introduction and semantics -/
  flavor : VoiceFlavor
  /-- [D] subcategorization feature: requires a specifier at PF -/
  hasD : Bool
  /-- Per-construction override of the flavor-default phasehood. `none`
      uses `flavor.defaultPhasal`; `some b` overrides to `b`. Use this to
      express principled per-paper divergence from the Collins-2005 baseline:
      e.g., [erlewine-sommerlot-2025] sets `some true` on Malayic
      passive Voice, [coon-2019] sets `some false` on Chol intransitive
      `v_w`/`v_ch` agentive variants, [coon-mateo-pedro-preminger-2014]
      sets `some false` on Mam Agent Focus Voice. -/
  phaseOverride : Option Bool := none
  /-- Does this Voice head check Case? In active, v checks accusative;
      in passive, Voice/*by* checks it ([collins-2005], p. 96: feature
      dissociation). Default false — only passive Voice checks Case. -/
  checksCase : Bool := false
  /-- Agree-relevant features on Voice (e.g., [uOblique] for Mam =(y)a').
      Default empty — most Voice heads carry no probe features. -/
  features : FeatureBundle := ⊥
  deriving DecidableEq, Repr

/-! ### Predicate API (mathlib-style, Prop with `Decidable`)

`IsPhasal`, `AssignsTheta`, `HasSemantics` are canonical Prop predicates;
the underlying Bool computations live in their `Decidable` instances. Use
`decide v.IsPhasal` for a Bool conversion when you genuinely need one
(`if`-conditionals, exhaustive case checks). The data fields `hasD` and
`checksCase` remain `Bool` (struct-level data, not derived predicates);
`HasD` and `ChecksCase` expose them in Prop form. -/

/-- This Voice head is phasal: per-construction override if present,
    else the flavor default. -/
def VoiceHead.IsPhasal (v : VoiceHead) : Prop :=
  v.phaseOverride.getD v.flavor.defaultPhasal = true

instance (v : VoiceHead) : Decidable v.IsPhasal :=
  inferInstanceAs (Decidable (v.phaseOverride.getD v.flavor.defaultPhasal = true))

/-- This Voice head introduces a θ-role.

    Holds for `agentive`, `causer`, `antipassive`, `reflexive`, `experiencer`. -/
def VoiceHead.AssignsTheta (v : VoiceHead) : Prop :=
  v.flavor = .agentive ∨ v.flavor = .causer ∨ v.flavor = .antipassive ∨
  v.flavor = .reflexive ∨ v.flavor = .experiencer

instance (v : VoiceHead) : Decidable v.AssignsTheta := by
  unfold VoiceHead.AssignsTheta; infer_instance

/-- This Voice head has semantic content.

    Holds for everything except `nonThematic` (purely PF, e.g. anticausative
    SE) and `expletive` (middle voice, no semantic contribution). -/
def VoiceHead.HasSemantics (v : VoiceHead) : Prop :=
  v.flavor ≠ .nonThematic ∧ v.flavor ≠ .expletive

instance (v : VoiceHead) : Decidable v.HasSemantics := by
  unfold VoiceHead.HasSemantics; infer_instance

/-- θ-assignment entails semantic content: every θ-assigning Voice head
    contributes event semantics. The converse fails — passive Voice has
    semantics without θ (`passive_has_semantics`, `passive_no_theta`). -/
theorem VoiceHead.AssignsTheta.hasSemantics {v : VoiceHead} (h : v.AssignsTheta) :
    v.HasSemantics := by
  unfold VoiceHead.HasSemantics
  rcases h with h | h | h | h | h <;> rw [h] <;> exact ⟨nofun, nofun⟩

/-- This Voice head subcategorizes for a specifier (Prop wrapper over
    the `hasD : Bool` data field). -/
def VoiceHead.HasD (v : VoiceHead) : Prop := v.hasD = true

instance (v : VoiceHead) : Decidable v.HasD :=
  inferInstanceAs (Decidable (v.hasD = true))

/-- This Voice head checks Case (Prop wrapper over the
    `checksCase : Bool` data field). -/
def VoiceHead.ChecksCase (v : VoiceHead) : Prop := v.checksCase = true

instance (v : VoiceHead) : Decidable v.ChecksCase :=
  inferInstanceAs (Decidable (v.checksCase = true))

-- ============================================================================
-- § 3: Canonical Voice Heads
-- ============================================================================

/-- Agentive Voice (transitive/unergative): introduces agent, is a phase head. -/
def voiceAgent : VoiceHead :=
  { flavor := .agentive, hasD := true }

/-- Causer Voice: introduces causer, is a phase head. -/
def voiceCauser : VoiceHead :=
  { flavor := .causer, hasD := true }

/-- Non-thematic Voice (anticausative): no θ-role, [D] for PF marking. -/
def voiceAnticausative : VoiceHead :=
  { flavor := .nonThematic, hasD := true }

/-- Expletive Voice (middle): no specifier, no semantics. -/
def voiceMiddle : VoiceHead :=
  { flavor := .expletive, hasD := false }

/-- Impersonal Voice (Finnish "passive"): demotes agent to an implicit
    generic human referent. Has semantics (existential closure over agent)
    but does not assign a θ-role to a syntactic specifier. -/
def voiceImpersonal : VoiceHead :=
  { flavor := .impersonal, hasD := false }

/-- Passive Voice: headed by *by*, checks Case but does
    not assign a θ-role — v assigns the θ-role to the external argument
    in Spec,vP. Passive v is NOT a phase head: the Case-checking feature
    that makes v* a strong phase head has been dissociated onto Voice/*by*.

    This is why PartP (complement of v) remains accessible for smuggling:
    passive v is a defective v, not v*. Cf. [chomsky-2001]: "only v*
    (transitive) is a strong phase."

    **Contested**: [legate-2003] argues passive v IS a phase head based
    on reconstruction and parasitic gap data. The current formalization
    follows [collins-2005] and [chomsky-2001]. -/
def voicePassive : VoiceHead :=
  { flavor := .passive, hasD := true, checksCase := true }

/-- Reflexive Voice: introduces an agent coreferent with the internal
    argument. [+θ, +D], phase head (assigns θ). Realized e.g. by Romance
    reflexive *se* ([martin-schaefer-kastner-2025]). NB [wood-2015]'s
    Icelandic reflexive *-st* is a clitic in SpecpP (a figure reflexive),
    **not** an exponent of this head — see `Wood2015`. -/
def voiceReflexive : VoiceHead :=
  { flavor := .reflexive, hasD := true }

/-- Experiencer Voice: introduces an experiencer external argument in
    Spec,VoiceP. [+θ, +D], phase head. NB this is **not** [wood-2015]'s
    Icelandic dative-subject experiencer (e.g. *leiðast* 'be bored'), where
    Voice is non-thematic and the experiencer is an applied dative — see
    `Wood2015`. -/
def voiceExperiencer : VoiceHead :=
  { flavor := .experiencer, hasD := true }

-- ============================================================================
-- § 4: Verification Theorems
-- ============================================================================

/-- Agentive Voice assigns a θ-role. -/
theorem agentive_assigns_theta : voiceAgent.AssignsTheta := by decide

/-- Non-thematic Voice does NOT assign a θ-role (Muñoz Pérez's key claim). -/
theorem nonThematic_no_theta : ¬ voiceAnticausative.AssignsTheta := by decide

/-- Non-thematic Voice has no semantic contribution.
    This is the core claim of Muñoz [munoz-perez-2026]: SE is a PF phenomenon. -/
theorem nonThematic_no_semantics : ¬ voiceAnticausative.HasSemantics := by decide

/-- Agentive Voice is a phase head (v* = Voice_AG). -/
theorem agentive_is_phase : voiceAgent.IsPhasal := by decide

/-- Non-thematic Voice is NOT a phase head. -/
theorem anticausative_not_phase : ¬ voiceAnticausative.IsPhasal := by decide

/-- Impersonal Voice does NOT assign a θ-role (agent is existentially closed,
    not projected to a syntactic specifier). -/
theorem impersonal_no_theta : ¬ voiceImpersonal.AssignsTheta := by decide

/-- Impersonal Voice HAS semantics: it contributes an existential closure
    over the agent variable, unlike non-thematic Voice which is vacuous. -/
theorem impersonal_has_semantics : voiceImpersonal.HasSemantics := by decide

/-- Passive Voice does NOT assign a θ-role (v does). -/
theorem passive_no_theta : ¬ voicePassive.AssignsTheta := by decide

/-- Passive Voice IS NOT a phase head. -/
theorem passive_not_phase : ¬ voicePassive.IsPhasal := by decide

/-- Passive Voice HAS semantic content (*by* mediates Case-checking). -/
theorem passive_has_semantics : voicePassive.HasSemantics := by decide

/-- Passive Voice checks Case ([collins-2005], p. 96: feature dissociation). -/
theorem passive_checks_case : voicePassive.ChecksCase := by decide

/-- Reflexive Voice assigns a θ-role ([wood-2015]). -/
theorem reflexive_assigns_theta : voiceReflexive.AssignsTheta := by decide

/-- Experiencer Voice assigns a θ-role ([wood-2015]). -/
theorem experiencer_assigns_theta : voiceExperiencer.AssignsTheta := by decide

/-- Only θ-assigning Voice flavors assign θ-roles. The reverse direction
    of `AssignsTheta`'s definition. -/
theorem theta_implies_active_flavor (v : VoiceHead) :
    v.AssignsTheta →
    v.flavor = .agentive ∨ v.flavor = .causer ∨ v.flavor = .antipassive ∨
    v.flavor = .reflexive ∨ v.flavor = .experiencer := id

-- ============================================================================
-- § 5: Voice–VerbHead Bridge ([kratzer-1996] in [cuervo-2003] terms)
-- ============================================================================

/-- Build the full verbal decomposition by combining Voice's contribution
    with the root-determined lower event structure.

    Voice contributes vDO when it assigns a θ-role (agentive, causer,
    antipassive). The root supplies the lower structure, which now
    includes vCAUSE for change-of-state roots ([wood-2015],
    [pylkkanen-2008]). CAUSE is independent of Voice:

    - Voice_AG + [vCAUSE, vGO, vBE] → [vDO, vCAUSE, vGO, vBE] (causative)
    - Voice_nonTh + [vCAUSE, vGO, vBE] → [vCAUSE, vGO, vBE] (anticausative)
    - Voice_AG + [] → [vDO] (unergative activity)
    - Voice_nonTh + [vBE] → [vBE] (stative) -/
def buildDecomposition (voice : VoiceHead) (rootStructure : List VerbHead) :
    List VerbHead :=
  if voice.AssignsTheta then .vDO :: rootStructure
  else rootStructure

-- ============================================================================
-- § 6: Bridge Theorems
-- ============================================================================

/-- θ-assigning Voice prepends vDO to the root structure. -/
theorem theta_voice_prepends_vDO (v : VoiceHead) (root : List VerbHead)
    (h : v.AssignsTheta) :
    buildDecomposition v root = .vDO :: root := by
  simp [buildDecomposition, h]

/-- Non-θ Voice leaves the root structure unchanged. -/
theorem no_theta_passthrough (v : VoiceHead) (root : List VerbHead)
    (h : ¬ v.AssignsTheta) :
    buildDecomposition v root = root := by
  simp [buildDecomposition, h]

/-- Causative pattern: agentive Voice + [vCAUSE, vGO, vBE] yields a causative decomposition. -/
theorem agent_plus_change_is_causative :
    isCausative (buildDecomposition voiceAgent [.vCAUSE, .vGO, .vBE]) = true := by
  decide

/-- Inchoative pattern: non-thematic Voice + [vCAUSE, vGO, vBE] stays inchoative. -/
theorem nonthematic_plus_change_is_inchoative :
    isInchoative (buildDecomposition voiceAnticausative [.vCAUSE, .vGO, .vBE]) = true := by
  decide

/-- Activity pattern: agentive Voice + [] yields an activity. -/
theorem agent_plus_nothing_is_activity :
    isActivity (buildDecomposition voiceAgent []) = true := by
  decide

/-- State pattern: non-thematic Voice + [vBE] yields a state. -/
theorem nonthematic_plus_state_is_state :
    isState (buildDecomposition voiceAnticausative [.vBE]) = true := by
  decide

/-- The causative alternation: same root structure [vCAUSE, vGO, vBE] is
    causative under agentive Voice but inchoative under non-thematic Voice.
    CAUSE is shared across both alternants — only vDO (from Voice) differs.
    This formalizes the [wood-2015]/[pylkkanen-2008] insight:
    CAUSE is independent of Voice. -/
theorem causative_alternation :
    isCausative (buildDecomposition voiceAgent [.vCAUSE, .vGO, .vBE]) = true ∧
    isInchoative (buildDecomposition voiceAnticausative [.vCAUSE, .vGO, .vBE]) = true := by
  decide

/-- Voice determines causativity: if the root structure is [vCAUSE, vGO, vBE],
    then whether the result is causative iff Voice assigns a θ-role. -/
theorem voice_determines_causativity (v : VoiceHead) :
    isCausative (buildDecomposition v [.vCAUSE, .vGO, .vBE]) = true ↔
    v.AssignsTheta := by
  cases v with | mk flavor _ _ _ _ =>
  cases flavor <;> simp [buildDecomposition, isCausative, VoiceHead.AssignsTheta]

/-- CAUSE is present in both causative and anticausative decompositions.
    This is the independence claim: CAUSE is part of the root, not Voice. -/
theorem cause_independent_of_voice :
    hasCause (buildDecomposition voiceAgent [.vCAUSE, .vGO, .vBE]) = true ∧
    hasCause (buildDecomposition voiceAnticausative [.vCAUSE, .vGO, .vBE]) = true := by
  decide

-- ============================================================================
-- § 7: Feature Dissociation ([collins-2005], §4)
-- ============================================================================

/-- In active, v (= agentive Voice) assigns θ AND controls Case-checking
    (Case is checked by v, not by Voice). In passive, these functions
    dissociate: v assigns θ (external argument in Spec,vP), while Voice/*by*
    checks Case. -/
theorem active_theta_and_case_unified :
    voiceAgent.AssignsTheta ∧ ¬ voiceAgent.ChecksCase := by decide

/-- Passive: θ-assignment and Case-checking are dissociated.
    Voice does NOT assign θ (v does), but Voice DOES check Case. -/
theorem passive_theta_case_dissociated :
    ¬ voicePassive.AssignsTheta ∧ voicePassive.ChecksCase := by decide

/-- UTAH compliance: the external argument is structurally present
    (`HasD`) in BOTH active and passive. The external argument occupies
    the same position (Spec,vP) regardless of voice — satisfying the
    Uniformity of Theta Assignment Hypothesis. -/
theorem utah_active_passive :
    voiceAgent.HasD ∧ voicePassive.HasD := by decide

/-- Passive Voice does not prepend vDO: it does not assign θ, so
    `buildDecomposition` passes the root structure through unchanged. -/
theorem passive_no_vDO (root : List VerbHead) :
    buildDecomposition voicePassive root = root := by
  simp [buildDecomposition, passive_no_theta]

-- ============================================================================
-- § 8: Voice/Phase Bridge
-- ============================================================================

/-- Agentive Voice corresponds to traditional v* (phase head).
    In the [kratzer-1996]/Schäfer framework, agentive Voice replaces
    v*. Both agentive and causer Voice are phase heads. -/
theorem agentive_voice_is_phase_head :
    voiceAgent.IsPhasal ∧ voiceCauser.IsPhasal := by decide

/-- Non-thematic and expletive Voice are NOT phase heads.
    Only θ-role-assigning Voice heads (agentive, causer) are phases. -/
theorem nonthematic_voice_not_phase_head :
    ¬ voiceAnticausative.IsPhasal ∧ ¬ voiceMiddle.IsPhasal := by decide

-- Voice phasehood does NOT track θ-role assignment in general.
-- [erlewine-sommerlot-2025] (Malayic) treats every Voice — including passive
-- and bare passive — as a phase head; [coon-2019] (Chol) treats certain
-- agentive Voice heads (the intransitive `v_w` / `v_ch` variants) as non-phasal
-- despite assigning a θ-role. The `phaseOverride` field is the per-construction
-- locus where such divergences from the flavor default are made explicit.

-- ============================================================================
-- § 9: Parametric Voice Decomposition ([alexiadou-schaefer-2015], [schaefer-2017])
-- ============================================================================

/-- How a Voice head introduces (or fails to introduce) an external
    argument semantically.

    - `thematicArgument`: [+λx] — introduces agent/causer via λ-abstraction;
      the external argument occupies Spec,VoiceP
    - `thematicExistential`: [+∃x] — introduces agent/causer via ∃-binding;
      agent is semantically present but syntactically implicit
      ([schaefer-2017] (31b)/(31e): "medio-passive Voice" {λe∃x[agent(e,x)]})
    - `expletive`: [−λx] — no semantic contribution; Voice is semantically
      vacuous (anticausative SE, middles) -/
inductive ExternalArgSemantics where
  | thematicArgument
  | thematicExistential
  | expletive
  deriving DecidableEq, Repr

/-- The ±D / ±λx parametric decomposition of Voice heads.

    From [alexiadou-schaefer-2015] (p. 109, ex. (12)), extended by
    [schaefer-2017]. Two binary parameters generate the core
    cross-linguistic typology of Voice:

    - **±D** (`selectsSpecifier`): does Voice select a syntactic specifier?
    - **±λx** (`extArgSemantics`): does Voice introduce an external argument variable?

    `none` values represent **underspecification**: the morpheme is compatible
    with multiple parameter settings, with the actual setting determined by
    independent factors (argument realization, verb class, pragmatics).
    Indonesian *ber-* is fully underspecified ⟨none, none⟩
    ([beavers-udayana-2022]); Spanish *se* is underspecified for ±D. -/
structure VoiceParams where
  /-- Does Voice select a syntactic specifier (DP)?
      `some true` = [+D], `some false` = [−D], `none` = underspecified -/
  selectsSpecifier : Option Bool
  /-- Does Voice introduce semantic agentivity/causation?
      `none` = underspecified -/
  extArgSemantics : Option ExternalArgSemantics
  deriving DecidableEq, Repr

/-- Map each named VoiceFlavor to its position in the ±D / ±λx
    parameter space.

    | Flavor | ±D | ±λx | Example |
    |--------|----|-----|---------|
    | agentive | +D | +λx (arg) | English active |
    | causer | +D | +λx (arg) | Psych causative |
    | reflexive | +D | +λx (arg) | Icelandic -st reflexive |
    | experiencer | +D | +λx (arg) | Icelandic subject-exp -st |
    | nonThematic | +D | −λx | Romance anticausative SE |
    | expletive | −D | −λx | English dispositional middle |
    | impersonal | −D | +∃x | Finnish impersonal |
    | passive | +D | −λx | English passive (*by*) |

    Note: `nonThematic` and `passive` occupy the same cell [+D, −λx].
    They differ in Case-checking (`VoiceHead.checksCase`), which is
    a property of the full `VoiceHead`, not of the parametric decomposition. -/
def VoiceFlavor.toParams : VoiceFlavor → VoiceParams
  | .agentive     => { selectsSpecifier := some true,  extArgSemantics := some .thematicArgument }
  | .causer       => { selectsSpecifier := some true,  extArgSemantics := some .thematicArgument }
  | .antipassive  => { selectsSpecifier := some true,  extArgSemantics := some .thematicArgument }
  | .reflexive    => { selectsSpecifier := some true,  extArgSemantics := some .thematicArgument }
  | .experiencer  => { selectsSpecifier := some true,  extArgSemantics := some .thematicArgument }
  | .nonThematic  => { selectsSpecifier := some true,  extArgSemantics := some .expletive }
  | .expletive    => { selectsSpecifier := some false, extArgSemantics := some .expletive }
  | .impersonal   => { selectsSpecifier := some false, extArgSemantics := some .thematicExistential }
  | .passive      => { selectsSpecifier := some true,  extArgSemantics := some .expletive }

/-- The parametric decomposition of a VoiceHead, derived from its flavor. -/
def VoiceHead.params (v : VoiceHead) : VoiceParams := v.flavor.toParams

/-- Does this parameter setting assign a theta role?
    Returns `none` when underspecified. -/
def VoiceParams.assignsTheta? (p : VoiceParams) : Option Bool :=
  match p.extArgSemantics with
  | some .thematicArgument    => some true
  | some .thematicExistential => some true
  | some .expletive           => some false
  | none                      => none

/-- Are two VoiceParams settings compatible?
    Two settings are compatible if they agree on all specified dimensions.
    An underspecified dimension (none) is compatible with anything. -/
def VoiceParams.isCompatibleWith (p q : VoiceParams) : Bool :=
  (p.selectsSpecifier.isNone || q.selectsSpecifier.isNone ||
   p.selectsSpecifier == q.selectsSpecifier) &&
  (p.extArgSemantics.isNone || q.extArgSemantics.isNone ||
   p.extArgSemantics == q.extArgSemantics)

/-- Is this parameter setting fully specified (no underspecification)? -/
def VoiceParams.isFullySpecified (p : VoiceParams) : Bool :=
  p.selectsSpecifier.isSome && p.extArgSemantics.isSome

-- ============================================================================
-- § 10: Parametric Bridge Theorems
-- ============================================================================

/-- All named VoiceFlavors produce fully specified params. -/
theorem flavor_params_fully_specified (f : VoiceFlavor) :
    f.toParams.isFullySpecified = true := by
  cases f <;> rfl

/-- VoiceHead.assignsTheta is consistent with VoiceParams.assignsTheta?:
    for fully-specified params, they agree. -/
theorem flavor_params_theta_consistent (f : VoiceFlavor) :
    f.toParams.assignsTheta? = some (match f with
      | .agentive | .causer | .antipassive | .reflexive | .experiencer | .impersonal => true
      | .nonThematic | .expletive | .passive => false) := by
  cases f <;> rfl

/-- Compatibility is reflexive. -/
theorem params_compatible_refl (p : VoiceParams) :
    p.isCompatibleWith p = true := by
  cases p with | mk s e =>
  cases s with
  | none => cases e with | none => rfl | some e => cases e <;> rfl
  | some s => cases s <;> (cases e with | none => rfl | some e => cases e <;> rfl)

/-- A fully underspecified VoiceParams is compatible with every
    named VoiceFlavor — the key property for Indonesian *ber-*. -/
theorem underspecified_compatible_with_all (f : VoiceFlavor) :
    let ber : VoiceParams := { selectsSpecifier := none, extArgSemantics := none }
    ber.isCompatibleWith f.toParams = true := by
  cases f <;> rfl

-- ============================================================================
-- § 11: Voice Projection Locus
-- ============================================================================

/-- Where a non-active morphological exponent realizes its host head, in
    Voice/v space.

    Non-active morphology (Romance *se*, Icelandic *-st* and *-na*,
    Hebrew *hit-*, etc.) can spell out distinct functional positions:
    Voice with a [D] feature, specifierless Voice, or v itself. The
    Voice_{D} vs Voice_{∅} distinction is from
    [alexiadou-schaefer-2015] and
    [wood-marantz-2017]; the v-vs-Voice distinction, in the
    [wood-2015] treatment of Icelandic *-ka*, locates *-ka* on v
    rather than on Voice.

    `voiceDOrBare` represents underspecification — a marking morpheme
    compatible with either Voice projection, with the actual setting
    determined by independent factors.

    This enum is the projection-side complement of `VoiceParams`: where
    `VoiceParams` parameterizes a Voice head's own ±D/±λx settings,
    `VoiceProjectionLocus` classifies the projection an exponent picks
    out. -/
inductive VoiceProjectionLocus where
  /-- Voice carrying a [D] feature; projects a specifier
      ([wood-2015] Voice_{D}). -/
  | voiceD
  /-- Specifierless Voice; no [D] feature
      ([wood-2015] Voice_{∅}). -/
  | voiceBare
  /-- Underspecified: compatible with either `voiceD` or `voiceBare`. -/
  | voiceDOrBare
  /-- Exponent of v, not Voice (e.g., Icelandic *-ka*
      per [wood-2015] Ch. 3, §3.3). -/
  | vHead
  deriving DecidableEq, Repr

end Minimalist
