import Linglib.Phenomena.Entailment.Montague_TruthConditionsBridge
import Linglib.Phenomena.Entailment.Basic

/-!
# Bridge: Compositional Truth Conditions → Entailment Data

Connects Montague compositional semantics derivations to the empirical
truth-condition judgments in `Phenomena.Entailment.Basic`.

Each bridge theorem verifies that the compositional derivation matches
the empirical judgment for a specific sentence.

## References

- Montague (1973). The Proper Treatment of Quantification.
-/


namespace Phenomena.Entailment.CompositionalBridge

open Semantics.Montague
open ToyLexicon
open Phenomena.Entailment

theorem captures_john_sleeps :
    (apply sleeps_sem john_sem = true) ↔ johnSleepsTrue.judgedTrue = true := by
  constructor <;> intro _ <;> rfl

theorem captures_mary_sleeps :
    (apply sleeps_sem mary_sem = false) ↔ marySleepsFalse.judgedTrue = false := by
  constructor <;> intro _ <;> rfl

theorem captures_intransitive_contrast :
    apply sleeps_sem john_sem = johnSleepsTrue.judgedTrue ∧
    apply sleeps_sem mary_sem = marySleepsFalse.judgedTrue := by
  constructor <;> rfl

theorem captures_transitive_seeing :
    apply (apply sees_sem mary_sem) john_sem = johnSeesMaryTrue.judgedTrue ∧
    apply (apply sees_sem john_sem) john_sem = johnSeesJohnFalse.judgedTrue := by
  constructor <;> rfl

end Phenomena.Entailment.CompositionalBridge
