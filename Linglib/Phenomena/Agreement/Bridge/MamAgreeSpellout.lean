import Linglib.Fragments.Mam.Agreement

/-!
# Minimalism Bridge: Agree-Conditioned Pronoun Spellout in Mam

@cite{scott-2023}

Connects the Agree operation (feature valuation, closest-goal locality) to
the empirical distribution of overt vs. null pronouns in SJA Mam.

## The Derivation

In a Mam transitive clause with a 3SG agent and 3SG patient:

1. **v probes for φ**: v has [uPerson, uNumber]. Its c-command domain
   contains the agent (Spec,vP) and the patient (complement of V). The
   agent is *closer* (higher in the structure). v Agrees with the agent,
   valuing [Person:3, Number:sg]. This is spelled out as Set A "t-" on v.

2. **T probes for φ**: T has [uPerson, uNumber, EPP]. After the subject
   moves to Spec,TP (triggered by EPP), T Agrees with it, valuing
   [Person:3, Number:sg]. This is spelled out as Set B "∅" on T.

3. **Patient is not φ-Agreed-with**: v's φ-probe has already targeted
   the agent (closest goal). No other head probes for φ in the patient's
   domain. The patient gets ACC from v (case assignment) but no φ-agreement.

4. **Pronoun realization follows**: Agreed-with arguments (agent, S) can
   be null — agreement morphology recovers their content. The patient,
   lacking φ-agreement, must be an overt pronoun.

## What This Bridge Demonstrates

This is the first derivation in linglib that connects `applyAgree` (narrow
syntax) → `spellout` (PF vocabulary insertion) → pronoun realization
(morphological consequence) in a single pipeline, grounded in a concrete
empirical phenomenon.

## References

- Scott, T. (2023). Pronouns and agreement in San Juan Atitán Mam.
  UC Berkeley dissertation.
-/

namespace Phenomena.Agreement.Bridge.MamAgreeSpellout

open Minimalism Fragments.Mam

-- ============================================================================
-- § 1: Probe Feature Bundles
-- ============================================================================

/-- v's probe features: [uPerson, uNumber].
    Placeholder values (0, false) are irrelevant — `sameType` matching
    ensures any Person/Number goal is found regardless. -/
def vProbe : FeatureBundle :=
  [.unvalued (.phi (.person 0)), .unvalued (.phi (.number false))]

/-- T's probe features: [uPerson, uNumber].
    Same as v — both probe for the full φ-set. -/
def tProbe : FeatureBundle :=
  [.unvalued (.phi (.person 0)), .unvalued (.phi (.number false))]

-- ============================================================================
-- § 2: Goal Feature Bundles (3SG test case)
-- ============================================================================

/-- A 3SG DP's features: [Person:3, Number:sg]. -/
def dp3sg : FeatureBundle :=
  [.valued (.phi (.person 3)), .valued (.phi (.number false))]

-- ============================================================================
-- § 3: Agree Valuation — v agrees with agent
-- ============================================================================

/-- v's [uPerson] is valued as [Person:3] from a 3SG agent. -/
theorem v_agrees_person :
    applyAgree vProbe dp3sg (.phi (.person 0)) =
    some [.valued (.phi (.person 3)), .unvalued (.phi (.number false))] := by
  native_decide

/-- After person agreement, v's [uNumber] is valued as [Number:sg].
    This is the second step of φ-Agree: person first, then number. -/
theorem v_agrees_number :
    let afterPerson := [.valued (.phi (.person 3)), .unvalued (.phi (.number false))]
    applyAgree afterPerson dp3sg (.phi (.number false)) =
    some [.valued (.phi (.person 3)), .valued (.phi (.number false))] := by
  native_decide

/-- Full φ-valuation of v by a 3SG agent: both person and number valued. -/
def vFullyAgreed : FeatureBundle :=
  [.valued (.phi (.person 3)), .valued (.phi (.number false))]

/-- The two-step Agree pipeline produces a fully valued bundle. -/
theorem v_agree_pipeline :
    (applyAgree vProbe dp3sg (.phi (.person 0))).bind
      (λ fb => applyAgree fb dp3sg (.phi (.number false))) =
    some vFullyAgreed := by
  native_decide

-- ============================================================================
-- § 4: Agree Valuation — T agrees with subject
-- ============================================================================

/-- T's full φ-valuation by a 3SG subject: same result as v. -/
theorem t_agree_pipeline :
    (applyAgree tProbe dp3sg (.phi (.person 0))).bind
      (λ fb => applyAgree fb dp3sg (.phi (.number false))) =
    some vFullyAgreed := by
  native_decide

-- ============================================================================
-- § 5: Spellout — Valued features → agreement morphology
-- ============================================================================

/-- Set A spellout: v's valued [Person:3, Number:sg] yields "t-" (A2/3SG). -/
theorem setA_spellout_3sg :
    spellout setAVocab vFullyAgreed (some .v) = some "t-" := by
  native_decide

/-- Set B spellout: T's valued [Person:3, Number:sg] yields "∅" (B2/3SG). -/
theorem setB_spellout_3sg :
    spellout setBVocab vFullyAgreed (some .T) = some "∅" := by
  native_decide

/-- Set A spellout for 1SG: v with [Person:1, Number:sg] yields A1SG marker. -/
theorem setA_spellout_1sg :
    let v1sg : FeatureBundle :=
      [.valued (.phi (.person 1)), .valued (.phi (.number false))]
    spellout setAVocab v1sg (some .v) = some "n-/w-" := by
  native_decide

/-- Set B spellout for 1SG: T with [Person:1, Number:sg] yields B1SG marker. -/
theorem setB_spellout_1sg :
    let t1sg : FeatureBundle :=
      [.valued (.phi (.person 1)), .valued (.phi (.number false))]
    spellout setBVocab t1sg (some .T) = some "chin" := by
  native_decide

-- ============================================================================
-- § 6: Locality — v targets agent, not patient
-- ============================================================================

/-- In a transitive vP, both agent and patient have valued φ-features.
    The agent is structurally higher (Spec,vP vs. complement of V).

    We model this via list position: in a probe's c-command domain,
    earlier = closer to the probe. The agent appears before the patient. -/
def vDomain : List FeatureBundle := [dp3sg, dp3sg]
  -- [agent (closer), patient (farther)]

/-- v's φ-probe finds the first (closest) goal with valued person. -/
theorem v_finds_closest_person :
    let closestGoal := vDomain.head?
    closestGoal.bind (λ fb => getValuedFeature fb (.phi (.person 0))) =
    some (.valued (.phi (.person 3))) := by
  native_decide

/-- The agent has valued φ-features, so it IS a valid goal. -/
theorem agent_is_valid_goal :
    hasValuedFeature dp3sg (.phi (.person 0)) = true := by native_decide

/-- The patient ALSO has valued φ-features — it COULD be a goal.
    But locality blocks it: the agent is closer. -/
theorem patient_could_be_goal :
    hasValuedFeature dp3sg (.phi (.person 0)) = true := by native_decide

/-- The agent has matching features for v's probe → it intervenes
    between v and the patient. Therefore v cannot Agree with the patient
    for φ (even though the patient has the right features).

    This is the closest-goal / Relativized Minimality effect that
    explains why objects lack φ-agreement in Mam. -/
theorem agent_intervenes :
    -- Agent is first in the domain (closest to probe)
    vDomain.head? = some dp3sg ∧
    -- Agent has matching valued φ
    hasValuedFeature dp3sg (.phi (.person 0)) = true ∧
    -- Therefore: v Agrees with agent, patient is blocked
    MamArgPosition.patient.isPhiAgreed = false := by
  exact ⟨rfl, by native_decide, rfl⟩

-- ============================================================================
-- § 7: The Full Pipeline — Agree → Spellout → Pronoun Realization
-- ============================================================================

/-- The complete prediction for a 3SG transitive clause:

    1. v Agrees with agent → [Person:3, Number:sg] on v
    2. [Person:3, Number:sg] on v spells out as Set A "t-"
    3. T Agrees with subject → [Person:3, Number:sg] on T
    4. [Person:3, Number:sg] on T spells out as Set B "∅"
    5. Patient is not φ-Agreed-with → overt pronoun required -/
theorem full_pipeline_3sg_transitive :
    -- Step 1-2: v Agrees and spells out as Set A
    (applyAgree vProbe dp3sg (.phi (.person 0))).bind
      (λ fb => applyAgree fb dp3sg (.phi (.number false))) = some vFullyAgreed ∧
    spellout setAVocab vFullyAgreed (some .v) = some "t-" ∧
    -- Step 3-4: T Agrees and spells out as Set B
    (applyAgree tProbe dp3sg (.phi (.person 0))).bind
      (λ fb => applyAgree fb dp3sg (.phi (.number false))) = some vFullyAgreed ∧
    spellout setBVocab vFullyAgreed (some .T) = some "∅" ∧
    -- Step 5: patient requires overt pronoun
    MamArgPosition.patient.canBeNull = false := by
  exact ⟨by native_decide, by native_decide, by native_decide,
         by native_decide, rfl⟩

/-- The pipeline generalizes: for every argument position, the predicted
    pronoun overtness matches the observed pattern. -/
theorem all_positions_match :
    mamArgPositions.all (λ pos => pos.canBeNull == pos.isPhiAgreed) = true := by
  native_decide

-- ============================================================================
-- § 8: Cross-Paradigm Spellout
-- ============================================================================

/-- Set A and Set B have different contexts: Set A on v, Set B on T.
    The same valued features produce different exponents depending on
    which head hosts them. -/
theorem setA_setB_differ_by_context :
    spellout setAVocab vFullyAgreed (some .v) ≠
    spellout setBVocab vFullyAgreed (some .v) := by
  native_decide

/-- Set A vocabulary does NOT match T context. -/
theorem setA_wrong_context :
    spellout setAVocab vFullyAgreed (some .T) = none := by
  native_decide

/-- Set B vocabulary does NOT match v context. -/
theorem setB_wrong_context :
    spellout setBVocab vFullyAgreed (some .v) = none := by
  native_decide

-- ============================================================================
-- § 9: Connection to Tripartite Case
-- ============================================================================

/-- The agreement asymmetry mirrors the case system: the two positions
    that get φ-agreement (A, S) are exactly the two that get dependent
    case or unmarked case (ERG, ABS). The position that lacks
    φ-agreement (P) is the one that gets ACC — the "orphan" case
    with no corresponding agreement paradigm. -/
theorem agreement_mirrors_case :
    -- Agreed-with positions: agent (ERG) and S (ABS)
    MamArgPosition.agent.isPhiAgreed = true ∧
    MamArgPosition.agent.case = .erg ∧
    MamArgPosition.intranS.isPhiAgreed = true ∧
    MamArgPosition.intranS.case = .abs ∧
    -- Not agreed-with: patient (ACC)
    MamArgPosition.patient.isPhiAgreed = false ∧
    MamArgPosition.patient.case = .acc := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Phenomena.Agreement.Bridge.MamAgreeSpellout
