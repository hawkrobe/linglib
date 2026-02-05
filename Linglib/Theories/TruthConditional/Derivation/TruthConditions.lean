/-
# Montague Semantics Derivations

Proofs that Montague semantics correctly predicts truth conditions.

## Main definitions

None (theorem-only module)

## References

Montague (1973)
-/

import Linglib.Theories.TruthConditional.Basic
import Linglib.Phenomena.Entailment.Basic

namespace TruthConditional.Derivation.TruthConditions

open TruthConditional
open ToyLexicon
open Phenomena.Entailment

theorem john_sleeps : apply sleeps_sem john_sem = true := rfl
theorem mary_not_sleeps : apply sleeps_sem mary_sem = false := rfl
theorem john_laughs : apply laughs_sem john_sem = true := rfl
theorem mary_laughs : apply laughs_sem mary_sem = true := rfl

theorem john_sees_mary : apply (apply sees_sem mary_sem) john_sem = true := rfl
theorem mary_sees_john : apply (apply sees_sem john_sem) mary_sem = true := rfl
theorem john_not_sees_john : apply (apply sees_sem john_sem) john_sem = false := rfl
theorem john_eats_pizza : apply (apply eats_sem ToyEntity.pizza) john_sem = true := rfl
theorem john_not_eats_mary : apply (apply eats_sem mary_sem) john_sem = false := rfl
theorem mary_eats_pizza : apply (apply eats_sem ToyEntity.pizza) mary_sem = true := rfl
theorem john_reads_book : apply (apply reads_sem ToyEntity.book) john_sem = true := rfl

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

example : interpSV toyModel john_sem sleeps_sem = true := rfl
example : interpSV toyModel mary_sem sleeps_sem = false := rfl
example : interpSVO toyModel john_sem sees_sem mary_sem = true := rfl
example : interpSVO toyModel john_sem sees_sem john_sem = false := rfl
example : interpSVO toyModel john_sem eats_sem ToyEntity.pizza = true := rfl

theorem john_sleeps_isTrue : isTrue toyModel (interpSV toyModel john_sem sleeps_sem) := rfl
theorem john_sees_mary_isTrue : isTrue toyModel (interpSVO toyModel john_sem sees_sem mary_sem) := rfl
theorem john_eats_pizza_isTrue : isTrue toyModel (interpSVO toyModel john_sem eats_sem ToyEntity.pizza) := rfl

end TruthConditional.Derivation.TruthConditions

-- Backward compatibility alias
namespace TruthConditional.Derivations
  export TruthConditional.Derivation.TruthConditions (john_sleeps mary_not_sleeps john_laughs mary_laughs
    john_sees_mary mary_sees_john john_not_sees_john john_eats_pizza john_not_eats_mary
    mary_eats_pizza john_reads_book captures_john_sleeps captures_mary_sleeps
    captures_intransitive_contrast captures_transitive_seeing)
end TruthConditional.Derivations
