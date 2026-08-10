import Linglib.Pragmatics.DecisionTheoretic.Basic
import Linglib.Pragmatics.DecisionTheoretic.But

/-!
# Decision-Theoretic Semantics: "Even" ([merin-1999-relevance] §5)

Merin's DTS account of the scalar particle "even". The felicity of
"A CONJ even(B)" requires B to be *more* relevant than A, resolving the
dispute between Anscombre (argumentative value), [kay-1990] (contextual
entailment), and [francescotti-1995] (surprise) under a single relevance
ordering.

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

The DTS account derives all three as special cases of "B is more relevant
than A to the current issue."
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DTS.Even

open DTS DTS.But

variable {W : Type*} [MeasurableSpace W]

/-! ### Felicity conditions for "even" -/

/-- **Hypothesis 5**: Felicity conditions for "A CONJ even(B)" with VP-focus.

"A and even B" is felicitous iff:
(i) A is positively relevant to some issue H,
(ii) B is positively relevant to H,
(iii) B is *more* relevant than A (BF(B) > BF(A)),
(iv) H ≠ B (the issue is not B itself — that would collapse to "also").

The key innovation: "even" marks B as the *more informative* conjunct, not
merely "surprising" or "unexpected." -/
def evenFelicitous (ctx : Context W) (a b : Set W) : Prop :=
  posRelevant ctx a ∧ posRelevant ctx b ∧
  bayesFactor ctx a < bayesFactor ctx b ∧
  ctx.topic ≠ b

/-! ### Predictions -/

/-- **Prediction 3**: "But" and "even" are incompatible.

"A but even(B)" is never felicitous: `butFelicitous` requires B to be
negatively relevant (BF < 1), while `evenFelicitous` requires B to be
positively relevant (BF > 1). These are contradictory. -/
theorem but_even_incompatible (ctx : Context W) (a b : Set W) :
    butFelicitous ctx a b → ¬ evenFelicitous ctx a b := by
  rintro ⟨_, hNegB, _⟩ ⟨_, hPosB, _, _⟩
  exact absurd (hPosB.trans hNegB) (lt_irrefl 1)

end DTS.Even
