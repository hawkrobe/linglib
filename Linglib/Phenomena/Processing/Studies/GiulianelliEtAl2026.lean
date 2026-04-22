import Linglib.Theories.Processing.LanguageModel.Basic
import Linglib.Theories.Processing.PredictiveUncertainty.IAS
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Giulianelli, Wallbridge, Cotterell & Fernández (2026)
@cite{giulianelli-etal-2026}

Incremental alternative sampling as a lens into the temporal and
representational resolution of linguistic prediction.
*Journal of Memory and Language*, 148, 104715.

## What this study contributes

The paper introduces **incremental alternative sampling (IAS)**, a
generalisation of surprisal theory in which a comprehender continually
samples plausible continuations of partial linguistic input and
quantifies predictive uncertainty as the representational distance
between alternatives generated before vs. after observing the next unit.

Two structural claims sit at the formal core:

1. **Standard surprisal is a special case** of the IAS family — the
   instance with warping `−log` and indicator scoring at horizon 1.
   Formalised in `Theories.Processing.PredictiveUncertainty.IAS` as
   `standardSurprisal_denotes_surprisal`.

2. **IAS is strictly more expressive than surprisal** — fixing the
   language model and target, the IAS value depends on the choice of
   distance / representation function in a way that surprisal cannot
   capture. Formalised below as
   `informationValue1_not_determined_by_surprisal`.

## What this file does NOT formalise

The paper's empirical findings — which (forecast horizon, layer)
combinations best predict cloze probability, N400, P600, eye-tracked
reading times, self-paced reading times — are regression-coefficient
maxima from analyses on GPT-2 hidden states. They are not deductive
claims and should not be encoded as Lean theorems.

For the record, the paper reports (with sources cited as
@cite{giulianelli-etal-2026}):

- Explicit predictability measures (cloze probability, predictability
  ratings, cloze surprisal) peak at horizon h = 1 with representations
  closest to lexical identity (embedding and final layers).
- N400 and P600 ERP components peak at h = 2; N400 is best predicted by
  the embedding layer, P600 by intermediate layers.
- Self-paced reading time in multi-sentence stimuli (Natural Stories)
  benefits from substantially longer horizons than sentence-level
  stimuli, and correlates with low-to-intermediate layers.
- The full IAS model outperforms standard surprisal for most measures,
  with particularly strong gains for cloze probability, N400, and
  multi-sentence self-paced reading.
- Under the d^min summary statistic, surprisal correlates most strongly
  with intermediate layers at h = 3–5 (Pearson up to 0.81), suggesting
  surprisal's predictability is closest to a best-case (closest-
  hypothesis) notion.
- The directional hypothesis for P600 was refuted (negative observed
  relationship despite predicted positive).

These findings live in prose because their formal content is the
underlying IAS family — already formalised in `IAS.lean` — together
with the empirical question of which configuration best fits any given
dataset. Linglib formalises the *parameter space* of processing theories,
not the empirical-fit tables produced by analysing them on specific
neural networks.
-/

set_option autoImplicit false

namespace Phenomena.Processing.Studies.GiulianelliEtAl2026

open Theories.Processing.PredictiveUncertainty
open Theories.Processing.LanguageModel (LangModel)

-- ============================================================================
-- §1: IAS is strictly more expressive than surprisal
-- ============================================================================

/-- A trivial language model over `Unit` with point-mass on the unique
symbol. Used as a witness in the strict-generalization theorem below. -/
noncomputable def trivialLM : LangModel Unit where
  next _ := PMF.pure (some ())

/-- **Strict generalization**: fixing the language model, context, and
target, the IAS value at horizon 1 depends on the choice of distance
function. Two distinct distances yield distinct IAS values, while the
classical surprisal of the target is unchanged.

This is the formal content of @cite{giulianelli-etal-2026}'s claim that
"the generalised definition of surprisal exposes two potential limitations
of the standard surprisal model": surprisal collapses representational
structure that IAS preserves. The paper's empirical case for IAS rests
on this structural difference being psycholinguistically meaningful;
this theorem records that the difference exists at the level of the
mathematical objects, independently of any empirical fit. -/
theorem informationValue1_not_determined_by_surprisal :
    ∃ (d₁ d₂ : Option Unit → Unit → ℝ),
      informationValue1 trivialLM d₁ [] () ≠
      informationValue1 trivialLM d₂ [] () := by
  refine ⟨fun _ _ => 0, fun _ _ => 1, ?_⟩
  unfold informationValue1 trivialLM
  simp

end Phenomena.Processing.Studies.GiulianelliEtAl2026
