module

public import Mathlib.Data.PFun
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.SupClosed

/-!
# Kinds

A kind is an individual concept: at each situation it picks out the totality of the kind's
instances, the largest individual they make up. Where a kind has no instances its concept is
undefined, so `Kind S E` is a partial function from situations to individuals. Individuals need
only an order, part-of; Link's nonempty sets of atoms (`Plurality.Algebra.Individual`) are one
model.

A property is a function from situations to sets of individuals. The property `Kind.up k` holds
of the parts of the kind's totality, and the kind `Kind.down P` picks out the largest member of
`P` at each situation that has one. Chierchia writes these operators ∪ and ∩ and shows that they
are inverse on kinds and on properties closed downward.

## Main definitions

* `Reference.Kind`: kinds as partial individual concepts (p. 349).
* `Reference.Kind.up`: ∪, (15).
* `Reference.Kind.down`: ∩, (16), built on the ι of (11a).

## Main results

* `Reference.Kind.up_eq_Iic`, `Reference.Kind.up_eq_empty`: ∪ is an interval or empty.
* `Reference.Kind.mem_down`: ∩ picks out the largest member.
* `Reference.Kind.down_up`: (17a), ∩∪d = d.
* `Reference.Kind.up_down`: (17b), ∪∩P = P for the mass case (p. 351).
* `Reference.Kind.down_dom_of_supClosed`: Krifka's sufficient condition for ∩, finite case.

## Implementation notes

A property is written out as `S → Set E` rather than named. Chierchia calls ∩ an
intensionalized ι (p. 392), and Krifka's ∩ is the same operator. Derived Kind Predication,
(31c), is `Quantifier.GQ.some (k.up s)`, and a kind takes no scope, as a name takes none (§4.2),
by `Quantifier.NP.individual_compl`; neither needs a definition here.

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

/-- A kind is a partial individual concept, which sends each situation where the kind has
instances to their totality. -/
abbrev Kind (S E : Type*) := S →. E

section Preorder

variable [Preorder E]

/-- `k.up s` is the set of parts of the totality of `k` at `s`; it is empty where `k` is
undefined. -/
def Kind.up (k : Kind S E) (s : S) : Set E := {x | ∃ d ∈ k s, x ≤ d}

/-- `Kind.down P` sends each situation to the largest member of `P` there and is undefined where
`P` has no largest member. -/
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

/-- The kind of the property of a kind is that kind. -/
theorem Kind.down_up (k : Kind S E) : Kind.down k.up = k := by
  funext s
  refine Part.ext fun d ↦ ?_
  rw [Kind.mem_down]
  refine ⟨fun ⟨⟨d', hd', hdd'⟩, hmax⟩ ↦ le_antisymm hdd' (hmax ⟨d', hd', le_rfl⟩) ▸ hd',
    fun hd ↦ ?_⟩
  rw [Kind.up_eq_Iic hd]
  exact isGreatest_Iic

/-- If each extension of `P` is closed downward and has a largest member wherever it is
nonempty, then the property of the kind of `P` is `P`. -/
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

/-- A finite, nonempty, cumulative extension has a largest member, the sum of its members, so
`Kind.down` is defined there. -/
theorem Kind.down_dom_of_supClosed (hfin : (P s).Finite) (hne : (P s).Nonempty)
    (hcum : SupClosed (P s)) : (Kind.down P s).Dom :=
  have ht : hfin.toFinset.Nonempty := hfin.toFinset_nonempty.2 hne
  ⟨hfin.toFinset.sup' ht id, hcum.finsetSup'_mem ht fun _ hx ↦ hfin.mem_toFinset.1 hx,
    fun _ hx ↦ Finset.le_sup' id (hfin.mem_toFinset.2 hx)⟩

end SemilatticeSup

end Reference
