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
    sleeps_sem john_sem ↔ johnSleepsTrue.judgedTrue = true :=
  ⟨fun _ => rfl, fun _ => trivial⟩

theorem captures_mary_sleeps :
    ¬sleeps_sem mary_sem ↔ marySleepsFalse.judgedTrue = false :=
  ⟨fun _ => rfl, fun _ => id⟩

theorem captures_intransitive_contrast :
    sleeps_sem john_sem ∧ ¬sleeps_sem mary_sem :=
  ⟨trivial, id⟩

theorem captures_transitive_seeing :
    sees_sem mary_sem john_sem ∧ ¬sees_sem john_sem john_sem :=
  ⟨trivial, id⟩

end Phenomena.Entailment.CompositionalBridge
