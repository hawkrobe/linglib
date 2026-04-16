import Linglib.Theories.Syntax.Minimalism.Core.CMH
import Linglib.Theories.Syntax.Minimalism.Core.MCommand
import Linglib.Theories.Syntax.Minimalism.Core.Voice
import Linglib.Theories.Syntax.Minimalism.Core.Features
import Linglib.Theories.Syntax.Minimalism.Core.ObligatoryOperations

/-!
# Newman (2024) — When Arguments Merge @cite{newman-2024}

Elise Newman (2024). *When Arguments Merge*. MIT Press (Linguistic
Inquiry Monographs 88). ISBN 9780262379960.

## Overview

The Categorial Merge Hypothesis (CMH) proposes that all elements of
category V share the same Merge features, with only three
argument-introducing features: `[·D·]` (DP-specific), `[·X·]`
(category-unspecified), and `[·V·]` (VP-merge, v only). Combined with
Feature Maximality, Weak Economy, and Generalized Tucking In
(@cite{paille-2020}), the CMH derives:

1. **Non-DP First**: XPs merge before DPs when V bears both features
2. **VP-as-specifier**: When v bears `[·X·]`, VP is forced to be a
   specifier of v (not complement)
3. **Symmetric passives**: In "high IO" ditransitives, neither internal
   argument c-commands the other, so either can passivize
4. **DOMA**: Weak Economy forces IO to be passive subject when IO is
   a wh-phrase (checks more features)
5. **No IO passives with inherent case**: KPs can't check `[·D·]`, so
   they can't A-move to subject (Greek, Tamil, German, Turkish, Spanish)
6. **Agent Focus in Mayan**: Anti-redundancy deletes lower agreement
   copies when both probes target the same extracted argument

## Formalized Predictions

This file formalizes the verb type space, structural predictions about
VP-specifierhood and its consequences, the KP/DP distinction for
passive accessibility, and anti-redundancy for agreement.

-/

namespace Newman2024

open Minimalism Minimalism.CMH

-- ============================================================================
-- § 1: The Space of Possible vPs
-- ============================================================================

-- The CMH predicts exactly which verb types exist based on feature
-- combinations on V and v. We verify the basic inventory.

/-- Weather verbs have zero arguments. -/
theorem weather_zero_args : weatherVerb.totalArgs = 0 := rfl

/-- Unergatives have exactly one argument (the subject from v). -/
theorem unergative_one_arg : unergative.totalArgs = 1 := rfl
theorem unergative_subject_only : unergative.totalDP = 1 ∧ unergative.totalXP = 0 :=
  ⟨rfl, rfl⟩

/-- Unaccusatives have exactly one argument (the object from V). -/
theorem unaccusative_one_arg : unaccusative.totalArgs = 1 := rfl
theorem unaccusative_object_only : unaccusative.totalDP = 1 ∧ unaccusative.totalXP = 0 :=
  ⟨rfl, rfl⟩

/-- Transitives have exactly two DP arguments. -/
theorem transitive_two_args : transitive.totalArgs = 2 := rfl
theorem transitive_two_dps : transitive.totalDP = 2 ∧ transitive.totalXP = 0 :=
  ⟨rfl, rfl⟩

/-- Ditransitives with an XP argument have three arguments. -/
theorem ditrans_xp_three_args : ditransitiveXP.totalArgs = 3 := rfl

/-- DOC ditransitives also have three arguments. -/
theorem ditrans_doc_three_args : ditransitiveDOC.totalArgs = 3 := rfl

/-- Raising verbs have exactly one argument (the XP complement). -/
theorem raising_one_arg : raising.totalArgs = 1 := rfl

/-- Maximal verbs ("bet") have four arguments. -/
theorem maximal_four_args : maximalVerb.totalArgs = 4 := rfl

-- ============================================================================
-- § 2: VP-as-Specifier Consequences
-- ============================================================================

/-- In a low-XP ditransitive (V: [·D·][·X·], v: [·D·][·V·]),
    VP is NOT a specifier of v because v lacks [·X·]. -/
theorem low_xp_vp_is_complement :
    vpIsSpecifier (mkVLittleHead true false) = false := rfl

/-- In a high-XP / DOC ditransitive (v: [·D·][·X·][·V·]),
    VP IS a specifier of v because v bears [·X·]. -/
theorem high_xp_vp_is_specifier :
    vpIsSpecifier (mkVLittleHead true true) = true := rfl

/-- When VP is a specifier, V and v do NOT form a complex head.
    This predicts VP-ellipsis mismatches: Voice mismatches are
    tolerated in simple transitives (V-v complex) but not in DOC
    ditransitives (VP as specifier). -/
theorem doc_no_complex_head :
    vAndVFormComplex (mkVLittleHead true true) = false := rfl

theorem transitive_forms_complex :
    vAndVFormComplex (mkVLittleHead true false) = true := rfl

-- ============================================================================
-- § 3: Entailment Hierarchy and KP Blocks Passive
-- ============================================================================

-- The entailment hierarchy wh-DP ⊇ DP ⊇ non-DP determines which
-- nominals can undergo A-movement. KPs (inherent case shells) behave
-- as non-DPs: they cannot check [·D·] on T, so they cannot A-move
-- to subject. This explains why languages with inherent case on
-- indirect objects (Greek, Tamil, German, Turkish, Spanish) lack
-- IO passives.

/-- non-DPs (KPs) cannot check [·D·]. -/
theorem nonDP_cannot_check_D : NominalType.checksMerge .nonDP .D = false := rfl
theorem nonDP_can_check_X : NominalType.checksMerge .nonDP .X = true := rfl

/-- DPs can check both [·D·] and [·X·]. -/
theorem dp_checks_D : NominalType.checksMerge .dp .D = true := rfl
theorem dp_checks_X : NominalType.checksMerge .dp .X = true := rfl

/-- wh-DPs additionally check [·wh·] on C. -/
theorem whDP_checks_wh : NominalType.checksWh .whDP = true := rfl
theorem dp_no_wh : NominalType.checksWh .dp = false := rfl

/-- The entailment hierarchy is a total preorder. -/
theorem whDP_subsumes_dp : NominalType.subsumes .whDP .dp = true := rfl
theorem dp_subsumes_nonDP : NominalType.subsumes .dp .nonDP = true := rfl
theorem nonDP_not_subsumes_dp : NominalType.subsumes .nonDP .dp = false := rfl

/-- A-movement accessibility: DPs and wh-DPs can A-move; non-DPs cannot.
    This is the core of the no-IO-passive explanation for languages
    with inherent case on indirect objects. -/
theorem nonDP_cannot_amove : NominalType.canAMove .nonDP = false := rfl
theorem dp_can_amove : NominalType.canAMove .dp = true := rfl
theorem whDP_can_amove : NominalType.canAMove .whDP = true := rfl

-- ============================================================================
-- § 4: Symmetric Passives
-- ============================================================================

-- In a high-IO ditransitive where VP is a specifier of v, neither
-- internal argument c-commands the other. The IO (merged as XP
-- complement of v) and the DO (merged as DP complement of V, inside
-- VP which is a specifier of v) are in separate branches.
--
-- This structure predicts that EITHER argument can passivize —
-- attested in Norwegian, Zulu, and (with morphological complications)
-- English. We verify the structural prerequisite: VP-as-specifier
-- means the two internal arguments are in non-c-commanding positions.

/-- The high-IO structure has VP as specifier. -/
theorem high_io_has_vp_spec :
    vpIsSpecifier (mkVLittleHead true true) = true := rfl

-- ============================================================================
-- § 5: DOMA (Double Object Movement Asymmetry)
-- ============================================================================

-- DOMA: when IO is a wh-phrase in a passive, IO must be the passive
-- subject (not DO). Weak Economy explains this: IO-to-subject checks
-- more features because the IO is a wh-DP (checking [·D·] + [·wh·])
-- while DO is a plain DP (checking [·D·] only).
-- Feature counts are derived from the NominalType hierarchy.

/-- IO-to-subject in wh-passive: IO is a wh-DP.
    Feature count derived from `NominalType.aMovementFeatures .whDP`.
    Unlike Greek CD (§7), DOMA operations are pure alternatives at the
    same derivational step — not in a bleeding relation. -/
def ioToSubjectWh : PendingOp where
  featuresChecked := NominalType.aMovementFeatures .whDP
  bleeds := []

/-- DO-to-subject in wh-passive: DO is a plain DP.
    Feature count derived from `NominalType.aMovementFeatures .dp`. -/
def doToSubjectWh : PendingOp where
  featuresChecked := NominalType.aMovementFeatures .dp
  bleeds := []

/-- Weak Economy prefers IO-to-subject (checks more features). -/
theorem doma_prefers_io : weakEconomyValid [ioToSubjectWh, doToSubjectWh] 0 = true := by
  native_decide

/-- Weak Economy disprefers DO-to-subject when IO checks more. -/
theorem doma_disprefers_do : weakEconomyValid [ioToSubjectWh, doToSubjectWh] 1 = false := by
  native_decide

-- ============================================================================
-- § 6: Anti-Redundancy and Agent Focus
-- ============================================================================

-- In Mayan AF configurations, the agent moves to Spec,CP for
-- Ā-extraction. Both v (φ-probe) and C (φ-probe) agree with the
-- agent. Anti-redundancy deletes the lower copy (on v), yielding
-- the surface pattern: no ergative (Set A) agreement, AF morphology
-- surfaces as an elsewhere form on Voice.
-- We model this with two Agree copies targeting the same goal.

/-- Two probes (C at height 3, v at height 1) agree with the same
    agent (goal 0). -/
def mayanAFCopies : List AgreeCopy :=
  [⟨3, 0⟩,  -- C probe copies agent's φ
   ⟨1, 0⟩]  -- v probe copies agent's φ (redundant)

/-- Anti-redundancy identifies the lower copy as redundant. -/
theorem af_lower_is_redundant :
    (redundantCopies mayanAFCopies).length = 1 := by native_decide

/-- After anti-redundancy, only the higher copy (C's agreement)
    survives. -/
theorem af_surviving_copy :
    (applyAntiRedundancy mayanAFCopies).length = 1 := by native_decide

/-- The surviving copy is the one on C (height 3). -/
theorem af_c_probe_survives :
    (applyAntiRedundancy mayanAFCopies).head? = some ⟨3, 0⟩ := by native_decide

-- ============================================================================
-- § 7: Weak Economy and Optional Clitic Doubling (Greek)
-- ============================================================================

/-- In Greek active transitives, three operations compete after IO
    merges as XP:
    1. Clitic double the IO (checks [·D_weak·] + [uφ] = 2 features)
    2. Merge VP (checks [·V·] = 1 feature)
    3. Merge transitive subject DP (checks [·D·] = 1 feature)

    Weak Economy prefers (1) over (2) but NOT over (3): merging the
    subject checks [·D·] which also checks [·D_weak·], bleeding clitic
    doubling. Since (1) and (3) stand in a bleeding relation, Weak
    Economy allows either order — making clitic doubling optional. -/

def cliticDouble : PendingOp where
  featuresChecked := 2  -- [·D_weak·] + [uφ]
  bleeds := []

def mergeVP : PendingOp where
  featuresChecked := 1  -- [·V·]
  bleeds := []

def mergeSubject : PendingOp where
  featuresChecked := 1  -- [·D·]
  bleeds := [0]  -- merging subject bleeds clitic doubling

/-- Clitic doubling is valid under Weak Economy. -/
theorem greek_cd_valid :
    weakEconomyValid [cliticDouble, mergeVP, mergeSubject] 0 = true := by native_decide

/-- Merging the subject is also valid (bleeding licenses either order). -/
theorem greek_subject_valid :
    weakEconomyValid [cliticDouble, mergeVP, mergeSubject] 2 = true := by native_decide

-- ============================================================================
-- § 8: Feature Bundle Comparison with Existing Voice Typology
-- ============================================================================

-- The CMH's [·D·] on v is an argument-introducing Merge feature:
-- it causes a DP to merge as a thematic external argument. Voice's
-- hasD is a PF subcategorization feature (requires specifier at PF).
-- These are distinct: anticausative Voice has hasD = true (PF marking
-- of SE) but does not assign a θ-role.
--
-- The CMH's binary partition (v ± [·D·]) corresponds to Voice's
-- assignsTheta, not to Voice's hasD.

/-- CMH v with [·D·] introduces an external argument (thematic). -/
theorem agentive_has_D :
    (mkVLittleHead true false).features.hasD = true := rfl

/-- CMH v without [·D·] does not introduce an external argument. -/
def passiveV : CMHHead := mkVLittleHead false false
theorem passive_lacks_D : passiveV.features.hasD = false := rfl

/-- Voice's hasD (PF subcategorization) and assignsTheta (θ-role
    assignment) do NOT always coincide — confirming that these are
    distinct features. The CMH's [·D·] corresponds to assignsTheta,
    not to hasD. Anticausative and passive Voice have hasD = true
    (anticausative for SE marking, passive for *by*-phrase licensing)
    but assignsTheta = false (no θ-role). -/
theorem voice_hasD_ne_assignsTheta :
    voiceAnticausative.hasD = true ∧ voiceAnticausative.assignsTheta = false ∧
    voicePassive.hasD = true ∧ voicePassive.assignsTheta = false :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 9: Feature Failure (Assumption 19c)
-- ============================================================================

-- Newman adopts @cite{preminger-2014}'s obligatory-no-crash model for
-- Merge features: [·D·], [·X·], [·V·] can go unchecked without
-- crashing the derivation. This extends Preminger's insight from
-- φ-agreement to structure-building.
--
-- This matters for:
-- - Impersonal passives: T's [·D·] may go unchecked (no DP moves
--   to subject) without crashing
-- - Pro-drop weather verbs: T's EPP goes unchecked (no expletive)
-- - Robust convergence: the grammar attempts Merge but tolerates
--   failure, yielding default (expletive or pro) rather than crash

/-- The CMH adopts the obligatory-no-crash model for Merge features.
    This is @cite{newman-2024}'s Assumption 19c: features can go
    unchecked without crashing. -/
def cmhFeatureModel : AgreementModel := .obligatoryNocrash

/-- Under Feature Failure, unchecked Merge features do not crash. -/
theorem feature_failure_converges (outcome : ProbeOutcome) :
    derivationConverges cmhFeatureModel outcome = true :=
  obligatory_always_converges outcome

/-- The crash model would reject derivations with unchecked features.
    Feature Failure is what separates the CMH from standard Minimalism
    on this point. -/
theorem feature_failure_vs_crash :
    derivationConverges cmhFeatureModel .unvalued = true ∧
    derivationConverges .crashOnFailure .unvalued = false := ⟨rfl, rfl⟩

/-- Weather verbs introduce zero DP arguments. In pro-drop languages
    without expletives, T's [·D·] goes unchecked — Feature Failure
    prevents a crash. Under the crash model, an expletive would be
    required to check T's [·D·]. -/
theorem weather_needs_feature_failure :
    weatherVerb.totalDP = 0 ∧
    derivationConverges cmhFeatureModel .unvalued = true := ⟨rfl, rfl⟩

/-- Passive v lacks [·D·], so no external argument merges. If no
    internal argument is available for A-movement to Spec,TP (impersonal
    passives), T's [·D·] goes unchecked — tolerated by Feature Failure. -/
theorem impersonal_passive_converges :
    passiveV.features.hasD = false ∧
    derivationConverges cmhFeatureModel .unvalued = true := ⟨rfl, rfl⟩

-- ============================================================================
-- § 10: Binding Predictions from VP-as-Specifier
-- ============================================================================

-- The CMH's VP-as-specifier prediction has direct consequences for
-- binding. In the low-XP structure (VP is complement of v), DO
-- asymmetrically c-commands XP → binding asymmetry. In the DOC
-- structure (VP is specifier of v), neither internal argument
-- c-commands the other → symmetric binding (either can passivize).

-- Low-XP ditransitive: V: [·D·][·X·], v: [·D·][·V·]
-- Structure: [vP agent [v' v [VP DO [V' V XP]]]]
-- VP is complement of v because v lacks [·X·].

private def v₁ := mkLeafPhon .v [] "v" 10
private def V₁ := mkLeafPhon .V [] "V" 11
private def agent₁ := mkLeafPhon .D [] "agent" 12
private def DO₁ := mkLeafPhon .D [] "DO" 13
private def XP₁ := mkLeafPhon .P [] "to-Mary" 14

def lowXPTree : SyntacticObject :=
  .node agent₁ (.node v₁ (.node DO₁ (.node V₁ XP₁)))

-- DOC ditransitive: V: [·D·], v: [·D·][·X·][·V·]
-- Structure: [vP VP [vP agent [v' v IO]]]
-- VP is specifier of v because v bears [·X·].
-- Agent tucks in below VP (Generalized Tucking In).

private def v₂ := mkLeafPhon .v [] "v" 20
private def V₂ := mkLeafPhon .V [] "V" 21
private def agent₂ := mkLeafPhon .D [] "agent" 22
private def DO₂ := mkLeafPhon .D [] "DO" 23
private def IO₂ := mkLeafPhon .D [] "IO" 24

private def VP₂ : SyntacticObject := .node V₂ DO₂

def docTree : SyntacticObject :=
  .node VP₂ (.node agent₂ (.node v₂ IO₂))

-- § 10a: Internal argument binding asymmetry

/-- Low-XP: DO asymmetrically c-commands XP — binding asymmetry.
    DO (specifier of V, by Non-DP First) c-commands into the
    complement position. -/
theorem low_xp_DO_ccommands_XP :
    cCommandsInB lowXPTree DO₁ XP₁ = true := by native_decide

theorem low_xp_XP_not_ccommands_DO :
    cCommandsInB lowXPTree XP₁ DO₁ = false := by native_decide

/-- DOC: neither internal argument c-commands the other — symmetric.
    DO is inside VP (outer specifier), IO is complement of v.
    They are in separate branches. -/
theorem doc_DO_not_ccommands_IO :
    cCommandsInB docTree DO₂ IO₂ = false := by native_decide

theorem doc_IO_not_ccommands_DO :
    cCommandsInB docTree IO₂ DO₂ = false := by native_decide

/-- The structural asymmetry derived from VP-as-specifier:
    VP-as-complement gives binding asymmetry between internal
    arguments; VP-as-specifier gives symmetric binding. -/
theorem binding_asymmetry_iff_vp_complement :
    -- Low-XP (VP complement): DO c-commands XP, not vice versa
    (cCommandsInB lowXPTree DO₁ XP₁ = true ∧
     cCommandsInB lowXPTree XP₁ DO₁ = false) ∧
    -- DOC (VP specifier): neither c-commands the other
    (cCommandsInB docTree DO₂ IO₂ = false ∧
     cCommandsInB docTree IO₂ DO₂ = false) := by
  exact ⟨⟨by native_decide, by native_decide⟩, ⟨by native_decide, by native_decide⟩⟩

-- § 10b: Agent c-command differences

/-- In the low-XP structure, the agent c-commands both internal
    arguments (VP is complement, fully inside agent's sister). -/
theorem low_xp_agent_ccommands_DO :
    cCommandsInB lowXPTree agent₁ DO₁ = true := by native_decide

theorem low_xp_agent_ccommands_XP :
    cCommandsInB lowXPTree agent₁ XP₁ = true := by native_decide

/-- In the DOC structure with Tucking In, the agent (inner specifier)
    c-commands IO (complement of v) but NOT DO (inside VP, the outer
    specifier). The agent and VP are in separate branches — a direct
    consequence of VP being a specifier rather than a complement. -/
theorem doc_agent_ccommands_IO :
    cCommandsInB docTree agent₂ IO₂ = true := by native_decide

theorem doc_agent_not_ccommands_DO :
    cCommandsInB docTree agent₂ DO₂ = false := by native_decide

end Newman2024
