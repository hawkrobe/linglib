module

public import Linglib.Semantics.Modality.Kratzer.Operators
public import Linglib.Semantics.Conditionals.Basic

/-!
# The restrictor theory of conditionals

This file defines the restrictor conditional. On the restrictor analysis an *if*-clause is not a
connective but restricts the modal base of a possibly covert modal, so *if α, must β* is
necessity over the modal base restricted by α and *if α, might β* possibility over it. The
restrictor conditional is the conditional over the best accessible antecedent-worlds under the
preorders the ordering source induces (`orderingImp`), and with an empty ordering source it is
the strict conditional.

## Main definitions

* `Restrictor.conditionalNecessity`, `Restrictor.conditionalPossibility`: *if α, must β* and
  *if α, might β*.

## Main results

* `Restrictor.conditionalNecessity_iff_mem_orderingImp`: the restrictor conditional is the
  conditional over the best accessible antecedent-worlds.
* `Restrictor.restrictor_eq_strict`: with an empty ordering source it is the strict conditional.

## References

* [D. Lewis, *Adverbs of Quantification* (1975)][lewis-1975]
* [A. Kratzer, *Conditionals* (1986)][kratzer-1986]
* [A. Kratzer, *Modals and Conditionals* (2012)][kratzer-2012]
-/

@[expose] public section


namespace Conditional.Restrictor

open Modality.Kratzer

variable {W : Type*}

/-! ### Core definitions -/

/-- *If α, must β* on the restrictor analysis, necessity over the modal base restricted by α. -/
def conditionalNecessity (f : ModalBase W) (g : OrderingSource W)
    (α : W → Prop) (β : W → Prop) (w : W) : Prop :=
  necessity (restrictedBase f α) g β w

/-- *If α, might β* on the restrictor analysis, possibility over the modal base restricted by α. -/
def conditionalPossibility (f : ModalBase W) (g : OrderingSource W)
    (α : W → Prop) (β : W → Prop) (w : W) : Prop :=
  possibility (restrictedBase f α) g β w

/-! ### Structural lemma -/

/-- The accessible worlds of the restricted base are the α-worlds among the original accessible
worlds. -/
theorem restricted_accessible_eq (f : ModalBase W) (α : W → Prop) (w : W) :
    accessibleWorlds (restrictedBase f α) w =
    {w' ∈ accessibleWorlds f w | α w'} := by
  ext w'
  unfold accessibleWorlds restrictedBase propIntersection
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro p hp
      exact h p (List.mem_cons_of_mem _ hp)
    · exact h α List.mem_cons_self
  · intro ⟨hAcc, hα⟩ p hp
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact hα
    · exact hAcc p hp'

theorem mem_accessibleWorlds_restrictedBase {f : ModalBase W} {α : W → Prop} {w v : W} :
    v ∈ accessibleWorlds (restrictedBase f α) w ↔ v ∈ accessibleWorlds f w ∧ α v :=
  Set.ext_iff.1 (restricted_accessible_eq f α w) v

/-! ### Main bridge theorems -/

/-- *If α, must β* is the conditional over the best accessible α-worlds, under the preorders the
ordering source induces. -/
theorem conditionalNecessity_iff_mem_orderingImp (f : ModalBase W) (g : OrderingSource W)
    (α β : W → Prop) (w : W) :
    conditionalNecessity f g α β w ↔
      w ∈ orderingImp (accessibleWorlds f) (fun w ↦ kratzerPreorder (g w)) {v | α v} {v | β v} := by
  rw [conditionalNecessity, necessity_iff_all, mem_orderingImp, bestWorlds, bestAmong,
    restricted_accessible_eq]
  rfl

/-- With an empty ordering source, *if α, must β* is the strict conditional over the accessible
worlds. -/
theorem restrictor_eq_strict (f : ModalBase W) (α β : W → Prop) (w : W) :
    conditionalNecessity f emptyBackground α β w ↔
      w ∈ strictImp (accessibleWorlds f) {v | α v} {v | β v} := by
  rw [conditionalNecessity_iff_mem_orderingImp, strictImp_eq_orderingImp]
  simp [emptyBackground]

/-! ### Properties -/

/-- *If α, must β* holds vacuously when no accessible world satisfies α. -/
theorem vacuous_conditional (f : ModalBase W) (g : OrderingSource W)
    (α : W → Prop) (β : W → Prop) (w : W)
    (h : ∀ w', w' ∈ accessibleWorlds f w → ¬ α w') :
    conditionalNecessity f g α β w :=
  (conditionalNecessity_iff_mem_orderingImp f g α β w).2 fun v hv ↦ absurd hv.1.2 (h v hv.1.1)

/-- With the evaluation world as its only accessible world and an empty ordering source, *if α,
must β* is the material conditional. -/
theorem material_from_restrictor (f : ModalBase W)
    (α : W → Prop) (β : W → Prop) (w : W)
    (hTotal : accessibleWorlds f w = {w}) :
    conditionalNecessity f emptyBackground α β w ↔ (α w → β w) := by
  rw [restrictor_eq_strict, mem_strictImp_forall, hTotal]
  simp

/-- Restricting by a stronger antecedent leaves fewer accessible worlds. -/
theorem restrictor_monotone (f : ModalBase W) (α₁ α₂ : W → Prop) (w : W)
    (h : ∀ w', α₂ w' → α₁ w') :
    ∀ w', w' ∈ accessibleWorlds (restrictedBase f α₂) w →
          w' ∈ accessibleWorlds (restrictedBase f α₁) w := by
  intro w' hw'
  rw [restricted_accessible_eq] at hw' ⊢
  exact ⟨hw'.1, h w' hw'.2⟩

/-- Restricting by α₁ and then by α₂ leaves the same accessible worlds as restricting by their
conjunction. -/
theorem double_restriction (f : ModalBase W) (α₁ α₂ : W → Prop) (w : W) :
    accessibleWorlds (restrictedBase (restrictedBase f α₁) α₂) w =
    accessibleWorlds (restrictedBase f (fun w' ↦ α₁ w' ∧ α₂ w')) w := by
  ext w'
  rw [restricted_accessible_eq, restricted_accessible_eq, restricted_accessible_eq]
  constructor
  · intro ⟨⟨hf, hα₁⟩, hα₂⟩
    exact ⟨hf, hα₁, hα₂⟩
  · intro ⟨hf, hα₁, hα₂⟩
    exact ⟨⟨hf, hα₁⟩, hα₂⟩

end Conditional.Restrictor
