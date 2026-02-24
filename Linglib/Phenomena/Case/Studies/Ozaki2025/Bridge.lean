import Linglib.Phenomena.Case.Studies.Ozaki2025.Data
import Linglib.Theories.Syntax.Minimalism.Core.DependentCase
import Linglib.Theories.Syntax.Minimalism.VoiceAppl
import Linglib.Fragments.Japanese.Predicates

/-!
# Ozaki (2025) — Bridge: Dependent Case × Minimalist Syntax

Connects the empirical data from Ozaki (2025) to:
1. **Dependent case theory** (Marantz 1991; Baker 2015) — explains the
   ACC/ABL alternation without appealing to a transitive Voice head
2. **Minimalist Voice decomposition** (Kratzer 1996; Schäfer 2025) —
   departure verbs select non-thematic Voice (no agent, no phase head)
3. **Fragment entries** — Japanese verb entries in `Fragments.Japanese.Predicates`

## Key Bridge Claims

- Alternation verbs are dyadic unaccusatives: non-thematic Voice, two
  internal arguments, inchoative event structure (vGO + vBE)
- ACC *-o* arises from dependent case (two caseless NPs in TP domain),
  not from a transitive v/Voice head
- ABL *kara* is lexical case from P, which bleeds dependent accusative
- Standard Agree-based case faces a gap: no phase head (v*) to assign
  structural ACC, yet ACC is grammatical

## The Accusative Unaccusative Paradox

Under Agree, unaccusatives should never take ACC arguments — there is
no v* to assign it. Yet these verbs grammatically do. Dependent case
dissolves this paradox: ACC is configural, arising whenever two caseless
NPs share a Spell-Out domain, regardless of Voice/v flavor.

## References

- Ozaki, S. (2025). Dependent case in Japanese accusative/ablative
  alternation verbs. *CLS 61*.
- Baker, M. (2015). *Case: Its Principles and Its Parameters*. CUP.
- Marantz, A. (1991). Case and licensing. *ESCOL* 1991, 234–253.
-/

namespace Phenomena.Case.Ozaki2025.Bridge

open Minimalism
open Minimalism.Phenomena.VoiceAppl
open Fragments.Japanese.Predicates
open Phenomena.Case.Ozaki2025.Data

-- ============================================================================
-- § 1: Argument Structure
-- ============================================================================

/-! Departure verbs are unaccusative with inchoative structure:
    [VoiceP [Voice_∅ [vP_GO [vP_BE [VP V DP_source]]]]]

    Non-thematic Voice introduces no external argument. The leaver NP
    originates as an internal argument (Spec-vP or second complement)
    and raises to Spec-TP for EPP. Both arguments are VP-internal;
    `hasTheme` is `false` because the theme (leaver) raises out of VP,
    matching the pattern of other anticausative/unaccusative derivations. -/

/-- Derivation for departure verbs: non-thematic Voice, inchoative,
    two internal arguments (leaver + source), no external argument. -/
def departureVerbDerivation : VoiceApplDerivation where
  voice := some voiceAnticausative
  appl := none
  verbHeads := [.vGO, .vBE]
  hasExternalArg := false
  hasAppliedArg := false
  hasTheme := false

/-- Departure verbs predict no external argument. -/
theorem departure_no_external :
    predictsExternalArg departureVerbDerivation = false := rfl

/-- Departure verbs have inchoative event structure (vGO + vBE, no vDO). -/
theorem departure_is_inchoative :
    isInchoativeDerivation departureVerbDerivation = true := by native_decide

/-- Non-thematic Voice assigns no θ-role. -/
theorem departure_voice_no_theta :
    voiceAnticausative.assignsTheta = false := rfl

/-- Departure verb derivation matches the anticausative pattern:
    same Voice, same verbal heads, same predictions. The only
    difference is that departure verbs have two internal arguments
    (leaver + source) rather than one. -/
theorem departure_matches_anticausative_core :
    departureVerbDerivation.voice = anticausative_break.voice ∧
    departureVerbDerivation.verbHeads = anticausative_break.verbHeads := ⟨rfl, rfl⟩

-- ============================================================================
-- § 2: Dependent Case Derivation
-- ============================================================================

/-! The dependent case algorithm correctly derives both alternation variants.
    These results are proved in DependentCase.lean; we re-export the key
    connections here for the bridge. -/

/-- ACC variant produces dependent ACC on source, unmarked NOM on leaver. -/
theorem acc_derivation_correct :
    getCaseOf "source" accVariantResult = some .acc ∧
    getCaseOf "leaver" accVariantResult = some .nom := by native_decide

/-- ABL variant produces lexical ABL on source, unmarked NOM on leaver. -/
theorem abl_derivation_correct :
    getCaseOf "source" ablVariantResult = some .abl ∧
    getCaseOf "leaver" ablVariantResult = some .nom := by native_decide

/-- In the ACC variant, source case is dependent — it arises from
    configuration, not from a specific functional head. -/
theorem acc_source_from_configuration :
    getSourceOf "source" accVariantResult = some .dependent := by native_decide

/-- In the ABL variant, source case is lexical — assigned by the P head
    *kara*, which bleeds dependent case assignment. -/
theorem abl_source_from_lexical_p :
    getSourceOf "source" ablVariantResult = some .lexical := by native_decide

-- ============================================================================
-- § 3: Agree Contrast — The Accusative Unaccusative Paradox
-- ============================================================================

/-! Standard Agree-based case assignment faces a puzzle with these verbs.
    Structural ACC requires a phase head (v*) to probe for and assign
    accusative case. But unaccusative/anticausative Voice is NOT a phase
    head — only agentive Voice (v*) is.

    This means Agree predicts no ACC assigner for unaccusatives, yet
    *hanareru* and *deru* grammatically take ACC *-o* on the source.
    Dependent case theory dissolves this paradox: ACC arises from the
    configuration of two caseless NPs, independent of Voice flavor. -/

/-- Anticausative Voice is not a phase head — standard Agree-based ACC
    has no assigner in this configuration. -/
theorem agree_acc_needs_phase_head :
    voiceAnticausative.phaseHead = false := rfl

/-- Agentive Voice IS a phase head — ACC assignment works for transitives
    under Agree, but these verbs lack agentive Voice. -/
theorem agentive_has_phase_head :
    voiceAgent.phaseHead = true := rfl

/-- The accusative unaccusative paradox: these verbs are unaccusative
    (no θ-assigning Voice, no phase head) yet grammatically take ACC.
    Under Agree, this is contradictory. Under dependent case, it follows
    from configuration alone. -/
theorem accusative_unaccusative_paradox :
    -- Voice is non-thematic (no agent θ-role)
    voiceAnticausative.assignsTheta = false ∧
    -- Voice is not a phase head (no v* for structural ACC under Agree)
    voiceAnticausative.phaseHead = false ∧
    -- Yet dependent case correctly assigns ACC to the source
    getCaseOf "source" accVariantResult = some .acc ∧
    -- And the ACC is dependent (configural), not from any head
    getSourceOf "source" accVariantResult = some .dependent := by
  exact ⟨rfl, rfl, by native_decide, by native_decide⟩

-- ============================================================================
-- § 4: Per-Datum Verification
-- ============================================================================

/-! Connect each empirical datum from Data.lean to the theoretical
    predictions from DependentCase.lean and VoiceAppl. -/

/-- Fragment entry for *hanareru* is marked unaccusative. -/
theorem hanareru_is_unaccusative :
    Fragments.Japanese.Predicates.hanareru.unaccusative = true := rfl

/-- Fragment entry for *deru* is marked unaccusative. -/
theorem deru_is_unaccusative :
    Fragments.Japanese.Predicates.deru.unaccusative = true := rfl

/-- Fragment entry for *hanareru* is not passivizable (no direct passive). -/
theorem hanareru_not_passivizable :
    Fragments.Japanese.Predicates.hanareru.passivizable = false := rfl

/-- Fragment entry for *deru* is not passivizable. -/
theorem deru_not_passivizable :
    Fragments.Japanese.Predicates.deru.passivizable = false := rfl

/-- Fragment *hanareru* assigns source θ-role to object — the source
    is a true internal argument, not an adjunct. -/
theorem hanareru_source_theta :
    Fragments.Japanese.Predicates.hanareru.objectTheta = some .source := rfl

/-- Fragment *deru* assigns source θ-role to object. -/
theorem deru_source_theta :
    Fragments.Japanese.Predicates.deru.objectTheta = some .source := rfl

/-- Fragment *hanareru* assigns theme θ-role to subject — the leaver
    is a theme raised from VP-internal position. -/
theorem hanareru_theme_subject :
    Fragments.Japanese.Predicates.hanareru.subjectTheta = some .theme := rfl

/-- Fragment *deru* assigns theme θ-role to subject. -/
theorem deru_theme_subject :
    Fragments.Japanese.Predicates.deru.subjectTheta = some .theme := rfl

/-- Non-passivizability (fragment) aligns with direct passive being
    ungrammatical (data): both reflect absence of agentive Voice. -/
theorem passive_data_matches_fragment :
    hanareru_direct_passive.grammatical = false ∧
    Fragments.Japanese.Predicates.hanareru.passivizable = false := ⟨rfl, rfl⟩

/-- Non-passivizability follows from Voice theory: anticausative Voice
    assigns no θ-role, so there is no agent to demote in a passive. -/
theorem passive_follows_from_voice :
    voiceAnticausative.assignsTheta = false ∧
    Fragments.Japanese.Predicates.hanareru.passivizable = false := ⟨rfl, rfl⟩

/-- Verb forms in Data match Fragment entries. -/
theorem hanareru_form_matches :
    hanareru_acc.verb = Fragments.Japanese.Predicates.hanareru.form := rfl

theorem deru_form_matches :
    deru_acc.verb = Fragments.Japanese.Predicates.deru.form := rfl

-- ============================================================================
-- § 5: Source is an Argument in Both Variants
-- ============================================================================

/-! A key empirical claim: the source is an *argument* (not an adjunct)
    regardless of whether it surfaces with ACC or ABL. The argumenthood
    diagnostics (ellipsis, scrambling) succeed in both case frames.
    This is what makes dependent case the right analysis — if ABL *kara*
    made the source an adjunct, it would fail argumenthood tests. -/

/-- All argumenthood diagnostics succeed: ellipsis and scrambling work
    for both ACC and ABL sources. -/
theorem source_is_argument_both_frames :
    argumenthoodData.all (·.grammatical) = true := by native_decide

/-- The source's θ-role (from fragment) is invariant across case frames:
    it is `.source` regardless of morphological case realization. -/
theorem source_theta_invariant :
    Fragments.Japanese.Predicates.hanareru.objectTheta = some .source ∧
    Fragments.Japanese.Predicates.deru.objectTheta = some .source := ⟨rfl, rfl⟩

end Phenomena.Case.Ozaki2025.Bridge
