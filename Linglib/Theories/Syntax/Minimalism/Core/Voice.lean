import Linglib.Theories.Syntax.Minimalism.Core.Basic

/-!
# Voice Head Flavors (Kratzer 1996; Schäfer 2008)

Voice heads introduce (or fail to introduce) external arguments.
The key typology from Schäfer (2008):

- **Agentive**: Introduces an agent external argument (Kratzer 1996 Voice_AG)
- **Causer**: Introduces a causer (Schäfer 2008 Voice_CAUSE)
- **NonThematic**: Semantically vacuous — no θ-role, but has a [D] feature
  requiring PF realization (anticausative SE in Romance; Muñoz Pérez 2026)
- **Expletive**: No specifier, no semantics (middle voice, dispositionals)

## Key Claim (Muñoz Pérez 2026)

Non-thematic Voice contributes no semantics. SE is a PF marker of absent
external argument, not a semantic operator. Evidence: SE is optional in
Chilean Spanish when Fission produces a syncretic clitic.

## References

- Kratzer, A. (1996). Severing the external argument from its verb.
  In *Phrase Structure and the Lexicon*, 109–137.
- Schäfer, F. (2008). *The Syntax of (Anti-)Causatives*.
  John Benjamins.
- Muñoz Pérez, C. (2026). Stylistic applicatives: A lens into the
  nature of anticausative SE. *Glossa* 11(1).
-/

namespace Minimalism

-- ============================================================================
-- § 1: Voice Flavors
-- ============================================================================

/-- Typology of Voice head flavors.

    Agentive Voice introduces an agent; causer Voice introduces a causer;
    non-thematic Voice has no semantics (anticausative SE);
    expletive Voice has neither specifier nor semantics (middles). -/
inductive VoiceFlavor where
  | agentive     -- Introduces external argument with agent θ-role (Kratzer 1996)
  | causer       -- Introduces causer (Schäfer 2008: Voice_CAUSE)
  | nonThematic  -- Semantically vacuous, [D] feature only (anticausative SE)
  | expletive    -- No specifier, no semantics (middle voice)
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Voice Head Structure
-- ============================================================================

/-- A Voice head with its properties. -/
structure VoiceHead where
  /-- The flavor determining argument introduction and semantics -/
  flavor : VoiceFlavor
  /-- [D] subcategorization feature: requires a specifier at PF -/
  hasD : Bool
  /-- Is this Voice head a phase head? (v* = agentive Voice) -/
  phaseHead : Bool
  deriving DecidableEq, BEq, Repr

/-- Does this Voice head introduce a θ-role? -/
def VoiceHead.assignsTheta (v : VoiceHead) : Bool :=
  match v.flavor with
  | .agentive | .causer => true
  | .nonThematic | .expletive => false

/-- Does this Voice head have semantic content? -/
def VoiceHead.hasSemantics (v : VoiceHead) : Bool :=
  match v.flavor with
  | .agentive | .causer => true
  | .nonThematic | .expletive => false

-- ============================================================================
-- § 3: Canonical Voice Heads
-- ============================================================================

/-- Agentive Voice (transitive/unergative): introduces agent, is a phase head. -/
def voiceAgent : VoiceHead :=
  { flavor := .agentive, hasD := true, phaseHead := true }

/-- Causer Voice: introduces causer, is a phase head. -/
def voiceCauser : VoiceHead :=
  { flavor := .causer, hasD := true, phaseHead := true }

/-- Non-thematic Voice (anticausative): no θ-role, [D] for PF marking. -/
def voiceAnticausative : VoiceHead :=
  { flavor := .nonThematic, hasD := true, phaseHead := false }

/-- Expletive Voice (middle): no specifier, no semantics. -/
def voiceMiddle : VoiceHead :=
  { flavor := .expletive, hasD := false, phaseHead := false }

-- ============================================================================
-- § 4: Verification Theorems
-- ============================================================================

/-- Agentive Voice assigns a θ-role. -/
theorem agentive_assigns_theta : voiceAgent.assignsTheta = true := rfl

/-- Non-thematic Voice does NOT assign a θ-role (Muñoz Pérez's key claim). -/
theorem nonThematic_no_theta : voiceAnticausative.assignsTheta = false := rfl

/-- Non-thematic Voice has no semantic contribution.
    This is the core claim of Muñoz Pérez (2026): SE is a PF phenomenon. -/
theorem nonThematic_no_semantics : voiceAnticausative.hasSemantics = false := rfl

/-- Agentive Voice is a phase head (v* = Voice_AG). -/
theorem agentive_is_phase : voiceAgent.phaseHead = true := rfl

/-- Non-thematic Voice is NOT a phase head. -/
theorem anticausative_not_phase : voiceAnticausative.phaseHead = false := rfl

/-- Only agentive and causer Voice assign θ-roles. -/
theorem theta_implies_agentive_or_causer (v : VoiceHead) :
    v.assignsTheta = true → v.flavor = .agentive ∨ v.flavor = .causer := by
  cases v with | mk flavor _ _ =>
  cases flavor <;> simp [VoiceHead.assignsTheta]

end Minimalism
