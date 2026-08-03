/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Logic.Relator
import Mathlib.Logic.Relation

/-!
# Control Dependencies

The framework-neutral positional stratum of control theory. Control is
pre-theoretically an antecedence relation between the understood
subject of a clause-like complement and the matrix argument that
supplies its interpretation ([mccloskey-2003]; [landau-2013] (74)); a
dependency here is a bare relation `α → α → Prop` over argument
positions, read `r antecedent dependent`. Grammatical dependencies
share the fixed format of the configurational matrix ([koster-1987];
[neeleman-vandekoot-2002]): c-command by the antecedent,
obligatoriness, uniqueness of the antecedent, nonuniqueness of the
dependent, and locality. Movement chains, bound anaphora, and both
control mechanisms instantiate the format, so nothing here chooses
between base-generation and movement.

The matrix clauses are mathlib vocabulary, not new definitions:
uniqueness of the antecedent is `Relator.LeftUnique`; predication
strengthens the format with `Relator.RightUnique` (saturation consumes
its one slot — the nonuniqueness of dependents that the general format
permits is exactly what predication forbids); c-command, locality, and
feature matching are refinements `r ≤ s` in the lattice of relations.
Only obligatoriness needs a definition. The composition lemmas carry
[landau-2024]'s decomposition of logophoric control as binding ∘
predication (`Relation.Comp`): the composite keeps every refinement
and both uniqueness properties of its legs, so control shift and split
control can enter only through a non-functional binding leg, and
feature transmission percolates through the mediating position.
-/

namespace Control

variable {α : Type*} {dependent : α → Prop} {bind pred : α → α → Prop}

/-- Obligatoriness clause of the configurational matrix: every
    dependent takes an antecedent. -/
def Obligatory (dependent : α → Prop) (r : α → α → Prop) : Prop :=
  ∀ ⦃b⦄, dependent b → ∃ a, r a b

/-- A composite dependency is obligatory when its inner leg is and its
    mediating positions all have binders. -/
theorem Obligatory.comp (hp : Obligatory dependent pred)
    (hb : ∀ m, ∃ a, bind a m) :
    Obligatory dependent (Relation.Comp bind pred) := by
  intro c hc
  obtain ⟨m, hm⟩ := hp hc
  obtain ⟨a, ha⟩ := hb m
  exact ⟨a, m, ha, hm⟩

/-- Unique antecedents compose: if the dependent picks a unique
    mediator and the mediator a unique binder, the composite dependent
    picks a unique antecedent. -/
theorem leftUnique_comp (hb : Relator.LeftUnique bind)
    (hp : Relator.LeftUnique pred) :
    Relator.LeftUnique (Relation.Comp bind pred) := by
  rintro a a' c ⟨m, hbm, hmc⟩ ⟨m', hbm', hmc'⟩
  obtain rfl := hp hmc hmc'
  exact hb hbm hbm'

/-- Bi-uniqueness survives composition: an antecedent reaches a unique
    dependent when both legs are functional. Contrapositively, control
    shift and split control ([landau-2024] §5.1) can arise only through
    a binding leg that is not right-unique — the perspectival *pro*
    anchoring to AUTHOR, ADDRESSEE, or their sum — never through
    predication, which saturates a single slot. -/
theorem rightUnique_comp (hb : Relator.RightUnique bind)
    (hp : Relator.RightUnique pred) :
    Relator.RightUnique (Relation.Comp bind pred) := by
  rintro a c c' ⟨m, hbm, hmc⟩ ⟨m', hbm', hmc'⟩
  obtain rfl := hb hbm hbm'
  exact hp hmc hmc'

/-- Refinements percolate through composition: if each leg respects a
    licensing relation (c-command, locality, feature matching — the
    remaining matrix clauses and [landau-2015]'s (60)), so does the
    composite through the mediating position. -/
theorem comp_mono {bind' pred' : α → α → Prop} (hb : bind ≤ bind')
    (hp : pred ≤ pred') :
    Relation.Comp bind pred ≤ Relation.Comp bind' pred' := by
  rintro a c ⟨m, hbm, hmc⟩
  exact ⟨m, hb _ _ hbm, hp _ _ hmc⟩

/-- A transitive licensing relation absorbs composition: dependencies
    whose legs it licenses compose into a dependency it licenses. -/
theorem comp_le_of_trans {s : α → α → Prop} [IsTrans α s]
    (hb : bind ≤ s) (hp : pred ≤ s) :
    Relation.Comp bind pred ≤ s := by
  rintro a c ⟨m, hbm, hmc⟩
  exact IsTrans.trans _ _ _ (hb _ _ hbm) (hp _ _ hmc)

end Control
