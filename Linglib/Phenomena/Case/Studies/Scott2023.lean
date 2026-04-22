import Linglib.Theories.Syntax.Case.Dependent
import Linglib.Theories.Syntax.Minimalism.Voice
import Linglib.Fragments.Mayan.Mam.Agreement

/-!
# @cite{scott-2023} — Voice-Based Case in Mam
@cite{scott-2023} @cite{woolford-1997} @cite{marantz-1991} @cite{baker-2015}

@cite{scott-2023}'s analysis of San Juan Atitán Mam treats case as assigned
directly by functional heads keyed to argument position, building on
@cite{woolford-1997}'s claim that ergative is lexical/inherent Case
assigned with θ-role rather than configurationally derived.

## Three Heads, Three Cases

In Scott's Mam architecture each case has a dedicated assigner:

- **Voice → ERG** (inherent, to the agent in Spec,VoiceP — extending
  @cite{woolford-1997}'s inherent-ERG claim into a modern Voice-based
  architecture)
- **Voice → ACC** (structural, to the patient — low-abs syntax,
  §3.4)
- **Infl → ABS** (structural, to the intransitive subject)

This produces a tripartite underlying system (ERG ≠ ACC ≠ ABS) visible
through the Mam agreement patterns formalized in
`Phenomena/Agreement/Studies/Scott2023.lean`.

## Contrast with Other Case Theories

The Mam data discriminates between three theories of case assignment:

1. **Agree-based** (@cite{chomsky-2000}, @cite{chomsky-2001}): Case is
   assigned by Agree from a probing functional head. ACC requires v* as a
   *phase head*; non-thematic Voice (e.g., anticausative) is not a phase
   head and cannot assign ACC.

2. **Dependent case** (@cite{marantz-1991}, @cite{baker-2015}): Case is
   determined by the configuration of caseless NPs in a Spell-Out domain;
   Voice flavor is irrelevant to the algorithm.

3. **Voice-based** (this file): Case is keyed to argument position via
   functional heads. Neither phase-hood nor NP configuration is doing
   the work — the Voice head itself selects ERG vs. ACC by θ-role, and
   Infl independently assigns ABS to the intransitive subject.

The theorems below stage the contrast: Voice-based positional assignment,
the Agree-style phase-head sensitivity it sidesteps, and the Voice-blind
behavior of the dependent case algorithm.

## See Also

- `Phenomena/Agreement/Studies/Scott2023.lean` — full Agree/Spellout
  pipeline for the Mam agreement morphology, including the impoverishment
  rule that bleeds reduced pronouns
- `Phenomena/Ergativity/Studies/Scott2023.lean` — super-extended
  ergativity (clause-type-conditioned alignment shift)
- `Phenomena/Case/Studies/Woolford1997.lean` — the predecessor analysis
  treating ERG as inherent Case
-/

namespace Phenomena.Case.Studies.Scott2023

open Minimalism
open Syntax.Case

-- ============================================================================
-- § 1: Voice Assigns Case by Argument Position
-- ============================================================================

/-- Scott 2023's central case-theoretic claim: Voice (and Infl) assign
    case directly based on argument position. Agent → ERG, patient → ACC,
    intransitive subject → ABS — three distinct cases from three different
    heads, with the assignment fixed by θ-position rather than by Agree or
    by NP configuration. -/
theorem voice_assigns_case_by_position :
    Fragments.Mayan.Mam.MamArgPosition.agent.case = .erg ∧
    Fragments.Mayan.Mam.MamArgPosition.patient.case = .acc ∧
    Fragments.Mayan.Mam.MamArgPosition.intranS.case = .abs := ⟨rfl, rfl, rfl⟩

/-- The three argument positions receive three distinct cases — a
    tripartite underlying system (ERG ≠ ACC ≠ ABS) at the case-assignment
    layer, prior to any morphological syncretism. -/
theorem voice_based_tripartite :
    Fragments.Mayan.Mam.MamArgPosition.agent.case ≠
      Fragments.Mayan.Mam.MamArgPosition.patient.case ∧
    Fragments.Mayan.Mam.MamArgPosition.agent.case ≠
      Fragments.Mayan.Mam.MamArgPosition.intranS.case ∧
    Fragments.Mayan.Mam.MamArgPosition.patient.case ≠
      Fragments.Mayan.Mam.MamArgPosition.intranS.case := by
  exact ⟨by decide, by decide, by decide⟩

-- ============================================================================
-- § 2: Contrast with Agree-Based Case
-- ============================================================================

/-! Agree-based case ties ACC to a *phase head* (v*). Voice flavors that
    are not phase heads (anticausative, passive) cannot assign ACC under
    this view, predicting a gap for unaccusative patients. Scott 2023's
    Voice-based assignment makes no such phase-head requirement. -/

/-- Under Agree, anticausative Voice is not a phase head, so it cannot
    serve as an ACC assigner. -/
theorem agree_anticausative_not_phase :
    voiceAnticausative.phaseHead = false := rfl

/-- Under Agree, agentive Voice (v*) is a phase head and can assign ACC. -/
theorem agree_voice_is_phase_head :
    voiceAgent.phaseHead = true := rfl

-- ============================================================================
-- § 3: Contrast with Dependent Case
-- ============================================================================

/-! Dependent case is *Voice-blind* — the algorithm sees only NP
    configuration (higher vs. lower) and lexical case, not θ-role or
    Voice flavor. Two caseless NPs in a domain produce ACC on the lower
    one regardless of whether the higher NP is an agent or a derived
    subject. Scott's Voice-based assignment, by contrast, would only
    assign ACC under transitive Voice with an agent. -/

/-- Dependent case yields ACC for the lower of two caseless NPs whether
    or not the higher NP carries an agent θ-role. The algorithm never
    inspects Voice flavor. -/
theorem dependent_case_ignores_voice :
    let transitive : List NPInDomain :=
      [ { label := "agent", lexicalCase := none },
        { label := "theme", lexicalCase := none } ]
    let unaccusative : List NPInDomain :=
      [ { label := "experiencer", lexicalCase := none },
        { label := "theme", lexicalCase := none } ]
    getCaseOf "theme" (assignCases .accusative transitive) =
      getCaseOf "theme" (assignCases .accusative unaccusative) := by
  decide

/-- Dependent case in tripartite mode produces a parallel ERG/ACC split
    from the same configuration — but assigns it on positional grounds
    (higher NP gets ERG, lower NP gets ACC), not on θ-role grounds.
    Voice-based case derives the same surface pattern via a different
    mechanism, with the assigners keyed to θ-role rather than to NP
    configuration. -/
theorem dependent_case_tripartite :
    let nps : List NPInDomain :=
      [ { label := "higher", lexicalCase := none },
        { label := "lower", lexicalCase := none } ]
    getCaseOf "higher" (assignCases .tripartite nps) = some .erg ∧
    getCaseOf "lower" (assignCases .tripartite nps) = some .acc := by
  decide

end Phenomena.Case.Studies.Scott2023
