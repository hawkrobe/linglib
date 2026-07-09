import Linglib.Core.Logic.Bilattice.Basic

/-!
# Schöter's thesis: the guard as a presupposition operator
[schoter-1996-thesis]

[schoter-1996-thesis] (the dissertation behind [schoter-1996]) analyzes
presupposition in EBL two ways: as defeasible inference links (the route its
§6.2.3 shares with [schoter-1996] §4), and — in material not carried over to
the paper — through Fitting's guard connective `φ : ψ`
(`Bilattice.Evidential.guard`), read as "`ψ` presupposing `φ`". The guard
encodes Burton-Roberts' *truth-gap intuition*: the compound has a value only
when the presupposition is at least true, and is otherwise the gap `U`,
whatever the carrier's value. Its Table 6.1 gives the guard's four-valued
table on `FOUR`.

The thesis's *salient presuppositional intuition* — a presupposition is
implied equally by a sentence and by its negation — holds for the guard by
construction: negating the carrier commutes with guarding (`guard_neg`, a
definitional equality), so the presuppositional component is untouched by
negation. This is the projection-under-negation test at the value level.

## Main results

* `guard_table` — the guard's four-valued table on `FOUR` (Table 6.1)
* `guard_undefined_of_failure` — presupposition failure yields the gap `U`,
  whatever the carrier (the truth-gap intuition)
* `guard_neg` — the guard commutes with negation of the carrier
  (the salient presuppositional intuition, by `rfl`)
-/

open Bilattice
open Bilattice.Evidential (guard)

namespace Schoter1996Thesis

open FOUR (U T F I)

/-- The guard's four-valued table on `FOUR` ([schoter-1996-thesis] Table 6.1):
a true or overdefined presupposition passes the carrier through; an unknown or
false presupposition gaps the compound. -/
theorem guard_table :
    ∀ y : FOUR, guard T y = y ∧ guard U y = U ∧ guard F y = U ∧ guard I y = y := by
  decide

/-- The truth-gap intuition ([schoter-1996-thesis] §6.2.3): when the
presupposition is false, the compound is the gap `U` whatever the carrier's
value. -/
theorem guard_undefined_of_failure {S : Type*} [SemilatticeInf S] [BoundedOrder S]
    (ψ : Evidential S) : guard (.mk ⊥ ⊤) ψ = .mk ⊥ ⊥ :=
  Evidential.guard_of_pro_bot rfl ψ

/-- The salient presuppositional intuition ([schoter-1996-thesis] §6.2.3): the
guard commutes with negation of the carrier, so a sentence and its negation
carry the same presuppositional component — projection under negation, by
construction. -/
theorem guard_neg {S : Type*} [SemilatticeInf S] (x y : Evidential S) :
    guard x (Product.neg y) = Product.neg (guard x y) := rfl

end Schoter1996Thesis
