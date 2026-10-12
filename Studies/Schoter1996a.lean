module

public import Linglib.Logic.Trivalent.Four
public import Linglib.Logic.Bilattice.Guard

/-!
# Schöter (1996a): The Computational Application of Bilattice Logic to Natural Reasoning

This file formalizes the thesis's assessment of the guard connective as a presupposition
operator (§6.2.3). Of the two intuitions of [burton-roberts-1989] the thesis weighs, the
truth-gap intuition that a carrier whose presupposition fails is undefined, and the salient
presuppositional intuition that a sentence and its negation presuppose alike, Fitting's guard
`φ : ψ` (`Bilattice.Product.guard`), read as `ψ` presupposing `φ`, encodes both at the value
level. On `FOUR` it passes the carrier through when the presupposition is at least true and
gaps it otherwise (Table 6.1, `guard_table`), presupposition failure gaps the compound whatever
the carrier's value (`guard_undefined_of_failure`), and the guard commutes with negation of
the carrier, so the presuppositional component survives negation (`guard_compl`). The thesis
nevertheless rejects the guard for factive presupposition, since it draws no distinction between
the presuppositions of positive and negative carriers, which are cancellable only under
negation, and analyzes presupposition instead as a bundle of inference links, a strict modus
ponens, a defeasible modus ponens under negation and a modus tollens (Definition 6.5), on the
epistemic-state machinery that `Studies/Schoter1996b` leaves unformalized.

## References

* [schoter-1996a]
* [schoter-1996b]
* [burton-roberts-1989]
* [fitting-1994]
-/

@[expose] public section

open Bilattice
open Bilattice.Product (guard)

namespace Schoter1996a

open FOUR (U T F I)

/-- The guard's four-valued table on `FOUR` (Table 6.1): a true or overdefined presupposition
passes the carrier through; an unknown or false presupposition gaps the compound. -/
theorem guard_table :
    ∀ y : FOUR, guard T y = y ∧ guard U y = U ∧ guard F y = U ∧ guard I y = y := by
  decide

/-- The truth-gap intuition (§6.2.3): when the presupposition is false, the compound is the gap
`U` whatever the carrier's value. -/
theorem guard_undefined_of_failure {S : Type*} [SemilatticeInf S] [BoundedOrder S]
    (ψ : S ⊙ S) : guard (.mk ⊥ ⊤) ψ = .mk ⊥ ⊥ :=
  Product.guard_of_pro_bot rfl ψ

/-- The salient presuppositional intuition (§6.2.3): the guard commutes with negation of the
carrier, so a sentence and its negation carry the same presuppositional component. -/
theorem guard_compl {S : Type*} [SemilatticeInf S] (x y : S ⊙ S) : guard x yᶜ = (guard x y)ᶜ :=
  rfl

end Schoter1996a
