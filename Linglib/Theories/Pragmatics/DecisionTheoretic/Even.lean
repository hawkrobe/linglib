import Linglib.Theories.Pragmatics.DecisionTheoretic.Core
import Linglib.Theories.Pragmatics.DecisionTheoretic.But

/-!
# Decision-Theoretic Semantics: "Even" (Merin 1999 §5)

Merin's DTS account of the scalar particle "even". The felicity of
"A CONJ even(B)" requires B to be *more* relevant than A, resolving the
dispute between Anscombre (argumentative value), Kay (contextual entailment),
and Francescotti (surprise) under a single relevance ordering.

## Key Definitions

- `evenFelicitous` (Hypothesis 5): felicity conditions for "A CONJ even(B)"

## Main Results

- **Prediction 3** (`but_even_incompatible`): "but" and "even" are
  incompatible — "A but even(B)" is always infelicitous.

## Note on the Dispute

Merin shows that relevance subsumes all three prior analyses:
- Anscombre's "argumentative value" = Bayes factor ordering
- Kay's "contextual entailment" ≈ BF(B) > BF(A) in strong form
- Francescotti's "surprise" ≈ low prior probability ≈ high BF

The DTS account derives all three as special cases of "B is more
relevant than A to the current issue."

## References

- Merin, A. (1999). Information, relevance, and social decisionmaking.
  §5: Even, also, and presupposition.
- Anscombre, J.-C. (1973). Même le roi de France est sage.
- Kay, P. (1990). Even. L&IC 8.
- Francescotti, R. (1995). Even: The conventional implicature approach reconsidered.
-/

namespace Theories.DTS.Even

open Core.Proposition
open Theories.DTS
open Theories.DTS.But

-- ============================================================
-- Section 1: Felicity Conditions for "Even"
-- ============================================================

/-- **Hypothesis 5**: Felicity conditions for "A CONJ even(B)" with VP-focus.

"A and even B" is felicitous iff:
(i) A is positively relevant to some issue H,
(ii) B is positively relevant to H,
(iii) B is *more* relevant than A (BF(B) > BF(A)),
(iv) H ≠ B (the issue is not B itself — that would collapse to "also").

The key innovation: "even" marks B as the *more informative* conjunct,
not merely "surprising" or "unexpected." -/
def evenFelicitous {W : Type*} [Fintype W]
    (ctx : DTSContext W) (a b : BProp W) : Prop :=
  posRelevant ctx a ∧ posRelevant ctx b ∧
  bayesFactor ctx b > bayesFactor ctx a ∧
  ctx.issue.topic ≠ b

-- ============================================================
-- Section 2: Predictions
-- ============================================================

section Predictions

variable {W : Type*} [Fintype W]

/-- **Prediction 3**: "But" and "even" are incompatible.

"A but even(B)" is never felicitous: `butFelicitous` requires B to be
negatively relevant (BF < 1), while `evenFelicitous` requires B to be
positively relevant (BF > 1). These are contradictory. -/
theorem but_even_incompatible (ctx : DTSContext W) (a b : BProp W) :
    butFelicitous ctx a b → ¬ evenFelicitous ctx a b := by
  intro ⟨_, hNegB, _⟩ ⟨_, hPosB, _, _⟩
  simp only [negRelevant, posRelevant] at hNegB hPosB
  linarith

end Predictions

end Theories.DTS.Even
