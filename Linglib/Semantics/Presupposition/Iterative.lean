module

public import Linglib.Logic.Modal.Defs
public import Linglib.Semantics.Presupposition.Defs

/-!
# Repetitive *again*

This file defines the meaning of the repetitive presupposition trigger *again*. Following the
simplification of von Stechow's entry that Beavers and Koontz-Garboden use, *again* takes a
predicate `P` of eventualities, asserts `P` of an eventuality and presupposes that `P` held of an
earlier one. The eventualities may be events ordered by their run times, states, or times
themselves, so the relation `R` of an eventuality to the earlier ones is a parameter.

The presupposition is possibility along `R`, so its theory is that of `◇` in `Logic/Modal`. It is
monotone in the predicate (`ModalLogic.diamond_mono`): the readings of *again* differ in the
constituent it modifies, repetitive on a change-of-state predicate and restitutive on the result
state inside it, and a predicate that entails another gives the stronger presupposition, which
is why the repetitive reading entails the restitutive one. It is monotone in the relation
(`ModalLogic.diamond_restrict`), and where the eventualities are times and `R` relates a time to
the earlier times it is the past of tense logic (`Tense.diamond_toSetRel_past`). The phasal verbs
*stop*, *start* and *continue* presuppose the same possibility of a prior state
(`Semantics/Aspect/Phasal.lean`).

## Main definitions

* `Presupposition.again`: the partial proposition asserting `P` and presupposing an earlier
  eventuality of which `P` holds.

## References

* [von-stechow-1996]
* [beavers-koontz-garboden-2020]
-/

@[expose] public section

namespace Presupposition

open ModalLogic

variable {ι : Type*} {R : SetRel ι ι} {P : ι → Prop}

/-- `again R P` asserts `P` of an eventuality and presupposes that `P` holds of one of the
eventualities that `R` relates it to, the earlier ones. -/
def again (R : SetRel ι ι) (P : ι → Prop) : PartialProp ι where
  presup := ◇[R] P
  assertion := P

@[simp] theorem again_presup : (again R P).presup = ◇[R] P := rfl

@[simp] theorem again_assertion : (again R P).assertion = P := rfl

end Presupposition
