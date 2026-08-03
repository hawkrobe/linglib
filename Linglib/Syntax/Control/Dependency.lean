/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Rel
import Mathlib.Logic.Relator

/-!
# Control Dependencies

The framework-neutral positional stratum of control theory. Control is
pre-theoretically an antecedence relation between the understood
subject of a clause-like complement and the matrix argument that
supplies its interpretation ([mccloskey-2003]; [landau-2013] (74)); a
dependency here is a bundled relation `SetRel Pos Pos` over argument
positions, read `antecedent ~[r] dependent`. Grammatical dependencies
share the fixed format of the configurational matrix ([koster-1987];
[neeleman-vandekoot-2002]), and every clause of the matrix is mathlib
vocabulary in the `SetRel` lattice: c-command, locality, and feature
matching are refinements `r ⊆ s`; uniqueness of the antecedent is
`SetRel.IsInjective`; obligatoriness is `dependent ⊆ r.cod`; the
nonuniqueness of dependents that the general format permits is exactly
what predication forbids (`SetRel.IsFunctional` — saturation consumes
its one slot). Movement chains, bound anaphora, and both control
mechanisms instantiate the format, so nothing here chooses between
base-generation and movement.

Composition `○` carries [landau-2024]'s decomposition of logophoric
control as binding ∘ predication: the composite keeps every refinement
(`SetRel.comp_subset_comp`), obligatoriness (`cod_subset_cod_comp`),
and both uniqueness properties (`IsInjective.comp`,
`IsFunctional.comp`) of its legs — so control shift and split control
can enter only through a non-functional binding leg, the perspectival
*pro* anchoring to AUTHOR, ADDRESSEE, or their sum, never through
predication.

The declarations below are general relation algebra that mathlib's
`SetRel` currently lacks; each is marked `[UPSTREAM]`.
-/

namespace SetRel

variable {α β γ : Type*} {R : SetRel α β} {S : SetRel β γ}

/-- `[UPSTREAM]` A relation is functional when it relates each left
    element to at most one right element. -/
protected abbrev IsFunctional (R : SetRel α β) : Prop :=
  R.inv ○ R ⊆ .id

/-- `[UPSTREAM]` A relation is injective when it relates each right
    element to at most one left element. -/
protected abbrev IsInjective (R : SetRel α β) : Prop :=
  R ○ R.inv ⊆ .id

/-- `[UPSTREAM]` Functional relations compose. -/
theorem IsFunctional.comp (hR : R.IsFunctional) (hS : S.IsFunctional) :
    (R ○ S).IsFunctional := by
  rintro ⟨c, c'⟩ ⟨a, hca, hac'⟩
  obtain ⟨b, hab, hbc⟩ := mem_inv.mp hca
  obtain ⟨b', hab', hb'c'⟩ := hac'
  obtain rfl : b = b' := mem_id.mp (hR (prodMk_mem_comp (mem_inv.mpr hab) hab'))
  exact hS (prodMk_mem_comp (mem_inv.mpr hbc) hb'c')

/-- `[UPSTREAM]` Injective relations compose. -/
theorem IsInjective.comp (hR : R.IsInjective) (hS : S.IsInjective) :
    (R ○ S).IsInjective := by
  rintro ⟨a, a'⟩ ⟨c, hac, hca'⟩
  obtain ⟨b, hab, hbc⟩ := hac
  obtain ⟨b', ha'b', hb'c⟩ := mem_inv.mp hca'
  obtain rfl : b = b' := mem_id.mp (hS (prodMk_mem_comp hbc (mem_inv.mpr hb'c)))
  exact hR (prodMk_mem_comp hab (mem_inv.mpr ha'b'))

/-- `[UPSTREAM]` Functionality is right-uniqueness of the underlying
    relation. -/
theorem isFunctional_iff_rightUnique :
    R.IsFunctional ↔ Relator.RightUnique (· ~[R] ·) := by
  constructor
  · intro h a b b' hab hab'
    exact mem_id.mp (h (prodMk_mem_comp (mem_inv.mpr hab) hab'))
  · rintro h ⟨b, b'⟩ ⟨a, hba, hab'⟩
    exact mem_id.mpr (h (mem_inv.mp hba) hab')

/-- `[UPSTREAM]` Injectivity is left-uniqueness of the underlying
    relation. -/
theorem isInjective_iff_leftUnique :
    R.IsInjective ↔ Relator.LeftUnique (· ~[R] ·) := by
  constructor
  · intro h a a' b hab ha'b
    exact mem_id.mp (h (prodMk_mem_comp hab (mem_inv.mpr ha'b)))
  · rintro h ⟨a, a'⟩ ⟨b, hab, hba'⟩
    exact mem_id.mpr (h hab (mem_inv.mp hba'))

/-- `[UPSTREAM]` The codomain of a composite is contained in the second
    leg's codomain. -/
theorem cod_comp_subset : (R ○ S).cod ⊆ S.cod := by
  rintro c ⟨a, b, hab, hbc⟩
  exact ⟨b, hbc⟩

/-- `[UPSTREAM]` The second leg's codomain survives composition when
    its domain is covered by the first leg's codomain. -/
theorem cod_subset_cod_comp (h : S.dom ⊆ R.cod) : S.cod ⊆ (R ○ S).cod := by
  rintro c ⟨b, hbc⟩
  obtain ⟨a, hab⟩ := h ⟨c, hbc⟩
  exact ⟨a, b, hab, hbc⟩

/-- `[UPSTREAM]` The domain of a composite is contained in the first
    leg's domain. -/
theorem dom_comp_subset : (R ○ S).dom ⊆ R.dom := by
  rintro a ⟨c, b, hab, hbc⟩
  exact ⟨b, hab⟩

/-- `[UPSTREAM]` The first leg's domain survives composition when its
    codomain is covered by the second leg's domain. -/
theorem dom_subset_dom_comp (h : R.cod ⊆ S.dom) : R.dom ⊆ (R ○ S).dom := by
  rintro a ⟨b, hab⟩
  obtain ⟨c, hbc⟩ := h ⟨a, hab⟩
  exact ⟨c, b, hab, hbc⟩

end SetRel
