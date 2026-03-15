import Linglib.Phenomena.Entailment.MontagueTruthConditions
import Linglib.Phenomena.Entailment.Basic

/-!
# Bridge: Compositional Truth Conditions → Entailment Data
@cite{montague-1973}

Connects Montague compositional semantics derivations to the empirical
truth-condition judgments in `Phenomena.Entailment.Basic`.

Each bridge theorem verifies that the compositional derivation matches
the empirical judgment for a specific sentence.

-/


namespace Phenomena.Entailment.CompositionalBridge

open Semantics.Montague
open ToyLexicon
open Phenomena.Entailment

theorem captures_john_sleeps :
    (sleeps_sem john_sem = true) ↔ johnSleepsTrue.judgedTrue = true := by
  constructor <;> intro _ <;> rfl

theorem captures_mary_sleeps :
    (sleeps_sem mary_sem = false) ↔ marySleepsFalse.judgedTrue = false := by
  constructor <;> intro _ <;> rfl

theorem captures_intransitive_contrast :
    sleeps_sem john_sem = johnSleepsTrue.judgedTrue ∧
    sleeps_sem mary_sem = marySleepsFalse.judgedTrue := by
  constructor <;> rfl

theorem captures_transitive_seeing :
    sees_sem mary_sem john_sem = johnSeesMaryTrue.judgedTrue ∧
    sees_sem john_sem john_sem = johnSeesJohnFalse.judgedTrue := by
  constructor <;> rfl

end Phenomena.Entailment.CompositionalBridge
