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

The `Control` section adds the referential stratum: a valuation
`val : Pos → Ref` assigns each position its referent, and a dependency
enforces exhaustive argument sharing (`Control.Shares`) when it refines
the valuation's kernel. Partial control ([landau-2000]) is strict
growth `val a < val b` along the dependency — excluded by exhaustive
sharing (`Shares.not_lt`) and localizable to a leg of a composite
(`exists_lt_of_comp_lt`), which is [landau-2024]'s claim that partial
readings enter through the mediating *pro*, never through predication.
Split control (a dependent's referent joining two antecedents') is
excluded the same way: exhaustive sharing forces joint antecedents to
be co-valued (`Shares.eq_of_two`).
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

namespace Control

open SetRel

/-! ### Argument sharing -/

variable {Pos Ref : Type*} {val : Pos → Ref} {ante bind pred : SetRel Pos Pos}
  {a b p c : Pos}

/-- A dependency enforces exhaustive argument sharing when related
    positions are co-valued — the dependency refines the kernel of the
    valuation. -/
def Shares (val : Pos → Ref) (ante : SetRel Pos Pos) : Prop :=
  ∀ ⦃a b⦄, a ~[ante] b → val a = val b

/-- A refinement of a sharing dependency shares. -/
theorem Shares.mono (h : ante ⊆ bind) (hs : Shares val bind) :
    Shares val ante :=
  fun _ _ hab => hs (h hab)

/-- Sharing composes through the mediating position. -/
theorem Shares.comp (hb : Shares val bind) (hp : Shares val pred) :
    Shares val (bind ○ pred) := by
  rintro a c ⟨m, ham, hmc⟩
  exact (hb ham).trans (hp hmc)

/-- Exhaustive sharing excludes partial readings: no strict growth of
    the referent along the dependency ([landau-2000]). -/
theorem Shares.not_lt [Preorder Ref] (hs : Shares val ante)
    (h : a ~[ante] b) : ¬ val a < val b := by
  simp [hs h]

/-- Under exhaustive sharing, joint antecedents are co-valued — split
    control needs a non-exhaustive leg. -/
theorem Shares.eq_of_two (hs : Shares val ante) (ha : a ~[ante] p)
    (hb : b ~[ante] p) : val a = val b :=
  (hs ha).trans (hs hb).symm

/-- A partial reading in a composite localizes to a leg: if referents
    grow monotonely along the binding link and strictly across the
    composite, one of the two links already grows strictly. With an
    exhaustive predication leg this places partial control in the
    binding leg ([landau-2024] §5.1). -/
theorem exists_lt_of_comp_lt [PartialOrder Ref]
    (hb : ∀ ⦃x m⦄, x ~[bind] m → val x ≤ val m)
    (h : a ~[bind ○ pred] c) (hlt : val a < val c) :
    (∃ x m, x ~[bind] m ∧ val x < val m) ∨
      ∃ m x, m ~[pred] x ∧ val m < val x := by
  obtain ⟨m, ham, hmc⟩ := h
  rcases (hb ham).lt_or_eq with hlt' | heq
  · exact Or.inl ⟨a, m, ham, hlt'⟩
  · exact Or.inr ⟨m, c, hmc, heq ▸ hlt⟩

end Control
