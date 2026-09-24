module

public import Linglib.Semantics.Modality.Kratzer.Operators
public import Linglib.Semantics.Conditionals.Basic

/-!
# The restrictor theory of conditionals

This file defines the restrictor conditional. On the restrictor analysis of Lewis and Kratzer an
*if*-clause is not a connective but restricts the modal base of a possibly covert modal, so
*if α, must β* is necessity over the modal base restricted by α and *if α, might β* possibility
over it. The restrictor conditional is the conditional over the best accessible antecedent-worlds
under the preorders the ordering source induces (`orderingImp`), its *might* is the *might* of
that conditional, and with an empty ordering source it is the strict conditional.

## Main definitions

* `Restrictor.conditionalNecessity`, `Restrictor.conditionalPossibility`: *if α, must β* and
  *if α, might β*.

## Main results

* `Restrictor.conditionalNecessity_iff_mem_orderingImp`,
  `Restrictor.conditionalPossibility_iff_mem_might`: the restrictor conditionals are the
  conditional over the best accessible antecedent-worlds and its *might*.
* `Restrictor.restrictor_eq_strict`: with an empty ordering source it is the strict conditional.

## References

* [D. Lewis, *Adverbs of Quantification* (1975)][lewis-1975]
* [A. Kratzer, *Conditionals* (1986)][kratzer-1986]
* [A. Kratzer, *Modals and Conditionals* (2012)][kratzer-2012]
-/

@[expose] public section


namespace Conditional.Restrictor

open Modality.Kratzer

variable {W : Type*} (f : ModalBase W) (g : OrderingSource W) (α β : W → Prop) (w : W)

/-- *If α, must β* on the restrictor analysis is necessity over the modal base restricted by
α. -/
def conditionalNecessity : Prop := necessity (restrictedBase f α) g β w

/-- *If α, might β* on the restrictor analysis is possibility over the modal base restricted by
α. -/
def conditionalPossibility : Prop := possibility (restrictedBase f α) g β w

/-- *If α, must β* is the conditional over the best accessible α-worlds, under the preorders the
ordering source induces. -/
theorem conditionalNecessity_iff_mem_orderingImp :
    conditionalNecessity f g α β w ↔
      w ∈ orderingImp (accessibleWorlds f) (fun w ↦ kratzerPreorder (g w)) {v | α v} {v | β v} := by
  rw [conditionalNecessity, necessity_iff_all, mem_orderingImp, bestWorlds, bestAmong,
    accessibleWorlds_restrictedBase]
  rfl

/-- *If α, might β* is the *might* of the conditional over the best accessible α-worlds. -/
theorem conditionalPossibility_iff_mem_might :
    conditionalPossibility f g α β w ↔
      w ∈ might (orderingImp (accessibleWorlds f) (fun w ↦ kratzerPreorder (g w))) {v | α v}
        {v | β v} := by
  rw [mem_might]
  change _ ↔ w ∉ orderingImp _ _ {v | α v} {v | ¬ β v}
  rw [← conditionalNecessity_iff_mem_orderingImp, conditionalPossibility, conditionalNecessity,
    possibility_iff_any, necessity_iff_all]
  push Not
  rfl

/-- With an empty ordering source, *if α, must β* is the strict conditional over the accessible
worlds. -/
theorem restrictor_eq_strict :
    conditionalNecessity f emptyBackground α β w ↔
      w ∈ strictImp (accessibleWorlds f) {v | α v} {v | β v} := by
  rw [conditionalNecessity_iff_mem_orderingImp, strictImp_eq_orderingImp]
  simp [emptyBackground]

/-- *If α, must β* holds vacuously when no accessible world satisfies α. -/
theorem vacuous_conditional (h : ∀ w', w' ∈ accessibleWorlds f w → ¬ α w') :
    conditionalNecessity f g α β w :=
  (conditionalNecessity_iff_mem_orderingImp f g α β w).2 fun v hv ↦ absurd hv.1.2 (h v hv.1.1)

/-- With the evaluation world as its only accessible world and an empty ordering source, *if α,
must β* is the material conditional. -/
theorem material_from_restrictor (hTotal : accessibleWorlds f w = {w}) :
    conditionalNecessity f emptyBackground α β w ↔ (α w → β w) := by
  rw [restrictor_eq_strict, mem_strictImp_forall, hTotal]
  simp

end Conditional.Restrictor
