import Linglib.Theories.Syntax.Minimalism.Core.DependentCase
import Linglib.Theories.Syntax.Minimalism.Core.Voice
import Linglib.Theories.Syntax.Minimalism.Core.CaseFilter
import Linglib.Fragments.Mam.Agreement

/-!
# Case Theories: Agree vs. Dependent Case vs. Voice-Based
@cite{baker-2015} @cite{chomsky-2000} @cite{chomsky-2001} @cite{marantz-1991} @cite{ozaki-2025} @cite{scott-2023} @cite{woolford-1997} @cite{woolford-2006}

Three competing theories of abstract case assignment in Minimalism:

1. **Agree-based case**: Case is a feature valued
   via the Agree operation. T values NOM on its specifier; v* values ACC
   on its complement. Case requires a specific functional head as assigner.
   The Case Filter (`CaseFilter.lean`) enforces that all DPs receive Case.

2. **Dependent case**: Case is determined by
   the configuration of NPs in a Spell-Out domain. An NP c-commanded by
   another caseless NP gets ACC (in accusative languages); unmarked NPs
   get NOM. No specific head is needed.

3. **Inherent/Voice-based case**:
   ERG is inherent case assigned by Voice (tied to the agent θ-role),
   ACC is structural from Voice (object licensing), ABS is structural
   from Infl. Case is directly determined by argument structure, not by
   configuration or feature checking. This gives a tripartite underlying
   system (ERG ≠ ACC ≠ ABS) visible through agreement patterns.

## Key Divergences

**Unaccusatives with ACC** (Agree vs. Dependent):
- Agree predicts a gap: no v* → no ACC assigner
- Dependent case: two caseless NPs suffice regardless of Voice

**Tripartite alignment** (all three):
- Agree: requires two distinct probes (T for NOM, v* for ACC)
- Dependent case: dependent ACC on lower NP, unmarked NOM
- Voice-based: ERG (inherent from Voice), ACC (structural from Voice),
  ABS (structural from Infl) — three heads, three cases

**Voice's role**:
- Agree: v* is a phase head that can probe for ACC
- Dependent case: Voice is irrelevant to the algorithm
- Voice-based: Voice directly assigns ERG/ACC based on θ-role

-/

namespace Comparisons.CaseTheories

open Minimalism

-- ============================================================================
-- § 1: The Divergence Point
-- ============================================================================

/-- Under Agree, ACC requires a phase head (v*). Anticausative Voice
    is not a phase head, so Agree predicts no ACC for unaccusatives. -/
theorem agree_predicts_no_acc_for_unaccusatives :
    voiceAnticausative.phaseHead = false := rfl

/-- Under dependent case, ACC only requires two caseless NPs. Voice
    flavor plays no role in the algorithm. -/
theorem dependent_case_acc_voice_independent :
    let nps : List NPInDomain :=
      [ { label := "higher", lexicalCase := none },
        { label := "lower", lexicalCase := none } ]
    getCaseOf "lower" (assignCases .accusative nps) = some .acc := by
  native_decide

-- ============================================================================
-- § 2: Where They Agree
-- ============================================================================

/-- Both theories correctly assign NOM to the sole argument of a
    simple unaccusative (one NP, no case competitor). -/
theorem single_np_gets_nom :
    let nps : List NPInDomain :=
      [ { label := "sole", lexicalCase := none } ]
    getCaseOf "sole" (assignCases .accusative nps) = some .nom := by
  native_decide

/-- Both theories assign ACC in a standard transitive configuration
    (though they disagree on *why*: Agree says v* probes; dependent
    case says the lower NP gets ACC from configuration). -/
theorem transitive_acc :
    let nps : List NPInDomain :=
      [ { label := "subject", lexicalCase := none },
        { label := "object", lexicalCase := none } ]
    getCaseOf "object" (assignCases .accusative nps) = some .acc ∧
    getCaseOf "subject" (assignCases .accusative nps) = some .nom := by
  native_decide

-- ============================================================================
-- § 3: Voice-Based Case (Woolford / Scott)
-- ============================================================================

/-! @cite{scott-2023} argues for Mam that case is assigned by three different
    heads: Voice assigns ERG (inherent, to agent) and ACC (structural,
    to patient), while Infl assigns ABS (structural, to intransitive S).
    This is neither Agree-based (no probe on T for NOM) nor dependent
    (ERG is inherent, not configurational). -/

/-- Voice-based case produces three distinct underlying cases.
    This is the tripartite system visible through agreement patterns. -/
theorem voice_based_tripartite :
    Fragments.Mam.MamArgPosition.agent.case ≠ Fragments.Mam.MamArgPosition.patient.case ∧
    Fragments.Mam.MamArgPosition.agent.case ≠ Fragments.Mam.MamArgPosition.intranS.case ∧
    Fragments.Mam.MamArgPosition.patient.case ≠ Fragments.Mam.MamArgPosition.intranS.case := by
  exact ⟨by decide, by decide, by decide⟩

/-- Dependent case also produces a tripartite system (ERG + ACC + ABS). -/
theorem dependent_case_tripartite :
    let nps : List NPInDomain :=
      [ { label := "higher", lexicalCase := none },
        { label := "lower", lexicalCase := none } ]
    getCaseOf "higher" (assignCases .tripartite nps) = some .erg ∧
    getCaseOf "lower" (assignCases .tripartite nps) = some .acc := by
  native_decide

-- ============================================================================
-- § 4: Voice's Role — The Three-Way Split
-- ============================================================================

/-- Agree-based: v* (agentive Voice) is a phase head, so can assign ACC. -/
theorem agree_voice_is_phase_head :
    voiceAgent.phaseHead = true := rfl

/-- Agree-based: anticausative Voice is NOT a phase head, so no ACC. -/
theorem agree_anticausative_no_acc :
    voiceAnticausative.phaseHead = false := rfl

/-- Voice-based: Voice assigns case DIRECTLY based on argument position,
    not via probing. The agent gets ERG, the patient gets ACC. -/
theorem voice_assigns_case_by_position :
    Fragments.Mam.MamArgPosition.agent.case = .erg ∧
    Fragments.Mam.MamArgPosition.patient.case = .acc ∧
    Fragments.Mam.MamArgPosition.intranS.case = .abs := ⟨rfl, rfl, rfl⟩

/-- Dependent case: Voice flavor is irrelevant. The algorithm only
    cares about NP configuration (higher vs. lower) and lexical case. -/
theorem dependent_case_ignores_voice :
    -- Same result regardless of whether we "label" the higher NP
    -- as agent or theme — dependent case sees only position
    let transitive : List NPInDomain :=
      [ { label := "agent", lexicalCase := none },
        { label := "theme", lexicalCase := none } ]
    let unaccusative : List NPInDomain :=
      [ { label := "experiencer", lexicalCase := none },
        { label := "theme", lexicalCase := none } ]
    getCaseOf "theme" (assignCases .accusative transitive) =
    getCaseOf "theme" (assignCases .accusative unaccusative) := by
  native_decide

-- ============================================================================
-- § 5: Case Filter Connection
-- ============================================================================

/-- The Case Filter is the Agree-based enforcement:
    every DP must have valued Case at the interfaces. This presupposes
    Agree-based case assignment (DPs start with [uCase]).

    Under dependent case, there is no [uCase] feature — case is
    assigned configurationally, so the Case Filter is unnecessary.

    Under Voice-based case, the filter is implicit: case is inherent
    (from Voice for ERG/ACC) or structural (from Infl for ABS), and
    every argument position receives case by construction. -/
theorem case_filter_example :
    -- A DP with valued NOM satisfies the Case Filter
    satisfiesCaseFilter (DPFeatures.withCase [.person .first, .number false] .nom) = true ∧
    -- A DP without Case fails the Case Filter
    satisfiesCaseFilter (DPFeatures.withUnvaluedCase [.person .first, .number false]) = false :=
  ⟨rfl, rfl⟩

/-- Under dependent case, every NP in a domain receives case — the
    algorithm always assigns (lexical, dependent, or unmarked). -/
theorem dependent_case_always_assigns :
    let nps : List NPInDomain :=
      [ { label := "subj", lexicalCase := none },
        { label := "obj", lexicalCase := none } ]
    (assignCases .accusative nps).all (λ np => np.case != .obl) = true := by
  native_decide

end Comparisons.CaseTheories
