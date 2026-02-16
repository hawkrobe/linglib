import Linglib.Theories.Syntax.Minimalism.Core.Voice
import Linglib.Theories.Syntax.Minimalism.Core.Applicative
import Linglib.Phenomena.Syntax.Minimalism.Bridge.EventStructureBridge
import Linglib.Theories.Semantics.Causation.ProductionDependence
import Linglib.Phenomena.Causatives.ThickThinBridge

/-!
# Causative Alternation: Cross-Theory Bridge

Connects four independent formalizations of the causative alternation:

1. **Semantic** (`Semantics.Intensional/Causative/`): CausativeBuilder,
   production/dependence distinction
2. **Event-structural** (`Semantics.Events/EventStructure`): Templates
   (accomplishment vs achievement)
3. **Syntactic** (`Minimalism/Core/Voice + Applicative`): VoiceFlavor
   (agentive vs nonThematic) + VerbHead (vDO, vGO, vBE)
4. **Empirical** (`Phenomena/Causatives/ThickThin`): alternating,
   thick/thin classification

## Key Bridge Results

- Accomplishment templates map to causative VerbHead decomposition
- Achievement templates map to inchoative VerbHead decomposition
- Thick verbs (production causation) pattern with agentive Voice
- Alternating verbs have both agentive and non-thematic Voice variants

## References

- Kratzer, A. (1996). Severing the external argument from its verb.
- Rappaport Hovav, M. & Levin, B. (1998). Building verb meanings.
- Cuervo, M. C. (2003). Datives at Large.
- Schäfer, F. (2008). The Syntax of (Anti-)Causatives.
- Martin, Rose & Nichols (2025). Burning facts: thick and thin causatives.
-/

namespace Comparisons.CausativeAlternation

open Minimalism
open Minimalism.Bridge
open Semantics.Events.EventStructure
open MartinRoseNichols2025
open Phenomena.Causatives.ThickThin

-- ============================================================================
-- § 1: Template ↔ Syntactic Structure
-- ============================================================================

/-- Accomplishment templates (external cause) map to causative structure
    with agentive Voice. -/
theorem accomplishment_has_agentive_voice :
    -- Semantic: accomplishment has external causer
    Template.hasExternalCauser .accomplishment = true ∧
    -- Syntactic: maps to causative heads (vDO + vGO + vBE)
    isCausative (templateToHeads .accomplishment) = true ∧
    -- Voice: agentive Voice assigns θ-role
    voiceAgent.assignsTheta = true := ⟨rfl, by native_decide, rfl⟩

/-- Achievement templates (no external cause) map to inchoative structure
    with non-thematic Voice. -/
theorem achievement_has_nonthematic_voice :
    -- Semantic: achievement lacks external causer
    Template.hasExternalCauser .achievement = false ∧
    -- Syntactic: maps to inchoative heads (vGO + vBE)
    isInchoative (templateToHeads .achievement) = true ∧
    -- Voice: non-thematic Voice has no semantics
    voiceAnticausative.hasSemantics = false := ⟨rfl, by native_decide, rfl⟩

-- ============================================================================
-- § 2: Thick/Thin ↔ Causation Type ↔ Voice
-- ============================================================================

/-- Thick manner verbs have the production constraint. -/
theorem thick_is_production :
    productionConstraint ThickThinClass.thickManner = .production := rfl

/-- Thin verbs have the dependence constraint. -/
theorem thin_is_dependence :
    productionConstraint ThickThinClass.thin = .dependence := rfl

/-- Production causation (thick verbs) aligns with agentive Voice:
    both require a concrete external argument. -/
theorem production_aligns_agentive :
    -- Production requires concrete causer
    productionConstraint ThickThinClass.thickManner = .production ∧
    -- Agentive Voice introduces external argument
    voiceAgent.assignsTheta = true ∧
    voiceAgent.hasD = true := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 3: Alternation ↔ Voice Alternation
-- ============================================================================

/-- The causative alternation IS a Voice alternation:
    transitive = agentive Voice, anticausative = non-thematic Voice.
    The VP-internal structure (vGO + vBE) is shared. -/
theorem alternation_is_voice_alternation :
    -- Achievement heads are a subset of accomplishment heads
    (templateToHeads .achievement).all
      ((templateToHeads .accomplishment).contains ·) = true ∧
    -- The difference is whether Voice introduces an external argument
    voiceAgent.assignsTheta = true ∧
    voiceAnticausative.assignsTheta = false := ⟨by native_decide, rfl, rfl⟩

-- ============================================================================
-- § 4: Empirical Bridge: ThickThin Data
-- ============================================================================

/-- Most thick verbs alternate (have both Voice variants). -/
theorem thick_mostly_alternate_bridge :
    let thickVerbs := allEntries.filter (·.thick)
    let altThick := thickVerbs.filter (·.alternating)
    altThick.length * 100 / thickVerbs.length ≥ 70 := by native_decide

/-- Alternating thick verbs: the transitive form has agentive Voice,
    the anticausative has non-thematic Voice. Example: break.
    - "John broke the vase" = Voice_AG + vDO + vGO + vBE
    - "The vase broke"      = Voice_∅  + vGO + vBE -/
theorem break_alternation :
    break_.alternating = true ∧ break_.thick = true := ⟨rfl, rfl⟩

/-- Non-alternating thick verbs (cut) only have the agentive Voice form. -/
theorem cut_no_anticausative :
    cut.alternating = false ∧ cut.thick = true := ⟨rfl, rfl⟩

end Comparisons.CausativeAlternation
