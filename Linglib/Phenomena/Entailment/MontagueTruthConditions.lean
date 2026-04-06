/-
# Montague Semantics Truth Conditions

Proofs that Montague semantics correctly predicts truth conditions
via direct function application.

-/

import Linglib.Theories.Semantics.Montague.Types
import Linglib.Phenomena.Entailment.Basic

namespace Semantics.Montague.TruthConditions

open Semantics.Montague
open ToyLexicon
open Phenomena.Entailment

theorem john_sleeps : sleeps_sem john_sem := trivial
theorem mary_not_sleeps : ¬sleeps_sem mary_sem := id
theorem john_laughs : laughs_sem john_sem := trivial
theorem mary_laughs : laughs_sem mary_sem := trivial

theorem john_sees_mary : sees_sem mary_sem john_sem := trivial
theorem mary_sees_john : sees_sem john_sem mary_sem := trivial
theorem john_not_sees_john : ¬sees_sem john_sem john_sem := id
theorem john_eats_pizza : eats_sem ToyEntity.pizza john_sem := trivial
theorem john_not_eats_mary : ¬eats_sem mary_sem john_sem := id
theorem mary_eats_pizza : eats_sem ToyEntity.pizza mary_sem := trivial
theorem john_reads_book : reads_sem ToyEntity.book john_sem := trivial

theorem captures_john_sleeps :
    sleeps_sem john_sem ↔ johnSleepsTrue.judgedTrue = true :=
  ⟨λ _ => rfl, λ _ => trivial⟩

theorem captures_mary_sleeps :
    ¬sleeps_sem mary_sem ↔ marySleepsFalse.judgedTrue = false := by
  exact ⟨λ _ => rfl, λ _ => id⟩

theorem captures_intransitive_contrast :
    sleeps_sem john_sem ∧
    ¬sleeps_sem mary_sem :=
  ⟨trivial, id⟩

theorem captures_transitive_seeing :
    sees_sem mary_sem john_sem ∧
    ¬sees_sem john_sem john_sem :=
  ⟨trivial, id⟩

end Semantics.Montague.TruthConditions
