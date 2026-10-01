module

public import Mathlib.Data.PFun
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.SupClosed

/-!
# Kinds

This file defines the kinds of [chierchia-1998]. Individuals form a join semilattice ordered by
part-of, (9): Link's model of nonempty sets of atoms is one instance
(`Plurality.Algebra.Individual`), but every law below uses only the order. A property assigns
each situation a set of individuals, and a kind is an individual concept, at each situation the
totality of its instances. A kind may lack instances at a situation, where its concept is
undefined (p. 349), so a kind is a partial function (`Kind`). The operator ∪ takes a kind to the
property of being part of its totality, (15), the principal ideal below the totality where the
kind is defined and nothing elsewhere (`Kind.up`, `Kind.up_eq_Iic`, `Kind.up_eq_empty`). The
operator ∩ takes a property to its largest member at each situation, undefined where there is
none, (16) with the ι of (11a) (`Kind.down`, `Kind.mem_down`): it is an intensionalized ι
(p. 392), and [krifka-2003] and [krifka-2026] define the same operator. The two are inverse in the
sense of (17): ∩∪d = d for any kind (`Kind.down_up`), and ∪∩P = P for a property whose extensions
are closed downward, the mass case, wherever ∩P is defined (`Kind.up_down`). A finite nonempty
cumulative extension has a largest member, [krifka-2026]'s sufficient condition
(`Kind.down_dom_of_supClosed`).

Derived Kind Predication, (31c), applies an object-level predicate to a kind as the existential
over its instances, `Quantifier.GQ.some (k.up s)`, and a kind takes no scope, as a name takes
none, §4.2, by `Quantifier.NP.individual_compl`.

## Main definitions

* `Reference.Kind`: kinds, partial individual concepts.
* `Reference.Kind.up`, `Reference.Kind.down`: ∪ and ∩.

## Main results

* `Reference.Kind.up_eq_Iic`, `Reference.Kind.up_eq_empty`: ∪, (15).
* `Reference.Kind.mem_down`: ∩ is the largest member, (16).
* `Reference.Kind.down_up`, `Reference.Kind.up_down`: (17a), (17b).
* `Reference.Kind.down_dom_of_supClosed`: a finite cumulative extension has a kind.

## Implementation notes

A property is a function from situations to sets of individuals, written out as `S → Set E`.

## TODO

* Chierchia's (17c) for plural properties, ∪∩P = P ∪ AT_P, with the pluralization PL of (10a).

## References

* [chierchia-1998]
* [link-1983]
* [krifka-2003]
* [krifka-2026]
-/

@[expose] public section

namespace Reference

variable {S E : Type*}

/-- A kind: a partial individual concept, at each situation the totality of its instances where
it has any. -/
abbrev Kind (S E : Type*) := S →. E

section Preorder

variable [Preorder E]

/-- ∪, (15): the property of being part of a kind's totality, empty where the kind is
undefined. -/
def Kind.up (k : Kind S E) (s : S) : Set E := {x | ∃ d ∈ k s, x ≤ d}

/-- ∩, (16): at each situation the largest member of the extension, undefined where there is
none. -/
noncomputable def Kind.down (P : S → Set E) : Kind S E :=
  fun s ↦ ⟨∃ d, IsGreatest (P s) d, fun h ↦ h.choose⟩

namespace Kind

variable {k : Kind S E} {s : S} {d : E}

theorem up_eq_Iic (h : d ∈ k s) : k.up s = Set.Iic d :=
  Set.ext fun _ ↦ ⟨fun ⟨_, hd, hx⟩ ↦ Part.mem_unique hd h ▸ hx, fun hx ↦ ⟨d, h, hx⟩⟩

theorem up_eq_empty (h : ¬ (k s).Dom) : k.up s = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨_, hd, _⟩ ↦ h (Part.dom_iff_mem.2 ⟨_, hd⟩)

theorem isLowerSet_up (k : Kind S E) (s : S) : IsLowerSet (k.up s) :=
  fun _ _ hxy ⟨d, hd, hx⟩ ↦ ⟨d, hd, hxy.trans hx⟩

end Kind

theorem Kind.down_dom {P : S → Set E} {s : S} :
    (Kind.down P s).Dom ↔ ∃ d, IsGreatest (P s) d :=
  Iff.rfl

end Preorder

section PartialOrder

variable [PartialOrder E] {P : S → Set E} {s : S} {d : E}

theorem Kind.mem_down : d ∈ Kind.down P s ↔ IsGreatest (P s) d := by
  simp only [Kind.down, Part.mem_mk_iff]
  exact ⟨fun ⟨h, hd⟩ ↦ hd ▸ h.choose_spec, fun h ↦ ⟨⟨d, h⟩, (Exists.choose_spec ⟨d, h⟩).unique h⟩⟩

/-- (17a): ∩∪d = d for any kind. -/
theorem Kind.down_up (k : Kind S E) : Kind.down k.up = k := by
  funext s
  refine Part.ext fun d ↦ ?_
  rw [Kind.mem_down]
  refine ⟨fun ⟨⟨d', hd', hdd'⟩, hmax⟩ ↦ le_antisymm hdd' (hmax ⟨d', hd', le_rfl⟩) ▸ hd',
    fun hd ↦ ?_⟩
  rw [Kind.up_eq_Iic hd]
  exact isGreatest_Iic

/-- (17b): ∪∩P = P for a property whose extensions are closed downward, as the extension of a
mass noun is (p. 351), wherever ∩P is defined at the situations where `P` has instances. -/
theorem Kind.up_down (hP : ∀ s, IsLowerSet (P s))
    (hk : ∀ s, (P s).Nonempty → (Kind.down P s).Dom) : (Kind.down P).up = P := by
  funext s
  by_cases hne : (P s).Nonempty
  · obtain ⟨d, hd⟩ := hk s hne
    rw [Kind.up_eq_Iic (Kind.mem_down.2 hd)]
    exact Set.Subset.antisymm (fun _ hx ↦ hP s hx hd.1) fun _ hx ↦ hd.2 hx
  · rw [Set.not_nonempty_iff_eq_empty.1 hne, Kind.up_eq_empty]
    exact fun ⟨d, hd⟩ ↦ hne ⟨d, hd.1⟩

end PartialOrder

section SemilatticeSup

variable [SemilatticeSup E] {P : S → Set E} {s : S}

/-- A finite, nonempty, cumulative extension has a largest member, the sum of its members, so ∩
is defined there ([krifka-2026]'s sufficient condition, finite case). -/
theorem Kind.down_dom_of_supClosed (hfin : (P s).Finite) (hne : (P s).Nonempty)
    (hcum : SupClosed (P s)) : (Kind.down P s).Dom :=
  have ht : hfin.toFinset.Nonempty := hfin.toFinset_nonempty.2 hne
  ⟨hfin.toFinset.sup' ht id, hcum.finsetSup'_mem ht fun _ hx ↦ hfin.mem_toFinset.1 hx,
    fun _ hx ↦ Finset.le_sup' id (hfin.mem_toFinset.2 hx)⟩

end SemilatticeSup

end Reference
