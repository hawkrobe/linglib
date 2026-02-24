import Linglib.Theories.Syntax.Minimalism.Core.DependentCase
import Linglib.Theories.Syntax.Minimalism.Core.Voice

/-!
# Case Theories: Agree vs. Dependent Case

Two competing theories of abstract case assignment in Minimalism:

1. **Agree-based case** (Chomsky 2000, 2001): Case is a feature valued
   via the Agree operation. T values NOM on its specifier; v* values ACC
   on its complement. Case requires a specific functional head as assigner.

2. **Dependent case** (Marantz 1991; Baker 2015): Case is determined by
   the configuration of NPs in a Spell-Out domain. An NP c-commanded by
   another caseless NP gets ACC (in accusative languages); unmarked NPs
   get NOM. No specific head is needed.

## Key Divergence: Unaccusatives with ACC

The theories make different predictions for unaccusative verbs that
take accusative-marked arguments (e.g., Japanese *hanareru* 'leave'):

- **Agree predicts a gap**: ACC requires v* (agentive Voice) as the
  assigner, but unaccusatives have non-thematic Voice (not a phase head).
  No phase head → no ACC assigner → ACC should be impossible.

- **Dependent case predicts ACC**: Two caseless NPs in TP suffice.
  The lower NP gets dependent ACC regardless of Voice flavor.
  Voice is irrelevant to case assignment.

## References

- Chomsky, N. (2000). Minimalist inquiries. In *Step by Step*, 89–155.
- Chomsky, N. (2001). Derivation by phase. In *Ken Hale: A Life in
  Language*, 1–52.
- Marantz, A. (1991). Case and licensing. *ESCOL* 1991, 234–253.
- Baker, M. (2015). *Case: Its Principles and Its Parameters*. CUP.
- Ozaki, S. (2025). CLS 61.
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

end Comparisons.CaseTheories
