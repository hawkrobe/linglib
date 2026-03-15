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

theorem john_sleeps : sleeps_sem john_sem = true := rfl
theorem mary_not_sleeps : sleeps_sem mary_sem = false := rfl
theorem john_laughs : laughs_sem john_sem = true := rfl
theorem mary_laughs : laughs_sem mary_sem = true := rfl

theorem john_sees_mary : sees_sem mary_sem john_sem = true := rfl
theorem mary_sees_john : sees_sem john_sem mary_sem = true := rfl
theorem john_not_sees_john : sees_sem john_sem john_sem = false := rfl
theorem john_eats_pizza : eats_sem ToyEntity.pizza john_sem = true := rfl
theorem john_not_eats_mary : eats_sem mary_sem john_sem = false := rfl
theorem mary_eats_pizza : eats_sem ToyEntity.pizza mary_sem = true := rfl
theorem john_reads_book : reads_sem ToyEntity.book john_sem = true := rfl

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

end Semantics.Montague.TruthConditions
