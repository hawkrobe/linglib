import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.NAry
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod

/-!
# Phi lattices and their operations
[harbour-2016]

The person lattices of [harbour-2016] and the operations on them, factored out as
reusable substrate. A *phi lattice* is a collection of feature denotations — each
denotation a nonempty set of atoms (`Finset (Finset α)`, the powerset of an atomic
participant domain, p. 73: the author lattice `ℒau`, participant lattice `ℒpt`, and
`π` lattice `ℒπ`). Features denote **operations on** these lattices, not predicates:
`⊕` (`oplus`, disjoint addition) and `⊖` (`ominus`, joint subtraction), with
**Lexical Complementarity** (`lexComp`) the elsewhere-style restriction that keeps
sibling denotations disjoint (p. 80).

This is the shared origin substrate for [harbour-2016]'s person partition
(`Studies.Harbour2016`, which builds the partition *construction* on top) and for
[toosarvandani-2023]'s animacy account (`Studies.Toosarvandani2023`, which reuses
`oplus`/`nePowerset`/`lexComp` for heterogeneous pluralities such as `oplus SPEAKER
ANIMATE`). Generic over the atom type `α`. Sits beside `Phi.Geometry` (the person
feature geometry) and `Phi.Recursion` (the number calculus).

## Main declarations

* `nePowerset` — the nonempty powerset (a phi lattice generated from an atom set).
* `oplus` — disjoint addition (`⊕`): pointwise lattice join of two denotations
  ([harbour-2016] (17); `= Finset.image₂ (· ∪ ·)`).
* `ominus` — joint subtraction (`⊖`): strip a feature lattice's maximum from each
  element ([harbour-2016] (19)).
* `lexComp` — Lexical Complementarity: `G \ F`, restricting `G` away from a more
  specified sibling `F` ([harbour-2016] (31)).
* `act` — apply a signed feature (lattice `F`) to a collection `G`: `+F` is `oplus`,
  `−F` is `ominus`. The `±` sign is genuine bivalent data ([harbour-2016]'s
  bivalence thesis).
* `containing` — the groups containing an atom of a feature, which `⊕` of the feature's
  lattice yields along an entailment chain (`oplus_nePowerset_nePowerset`,
  `oplus_nePowerset_containing`), with Lexical Complementarity between two such
  (`mem_lexComp_containing_iff`).
-/

namespace Minimalist.Phi.Lattice

open Finset

variable {α : Type*} [DecidableEq α]

/-! ### The lattice constructor -/

/-- Nonempty powerset: all nonempty subsets of `atoms`. The phi lattice generated
from an atom set — every nonempty sum of atoms (`ℒπ` when `atoms` is the full
participant domain). Mathlib has no such operation; this mirrors the definitional shape
of `Finset.ssubsets` (`= powerset.erase s`, the *proper* subsets — removing the *top*),
removing the *bottom* `∅` instead. -/
def nePowerset (atoms : Finset α) : Finset (Finset α) := atoms.powerset.erase ∅

/-- Monotonicity of `nePowerset`. -/
theorem nePowerset_mono {s t : Finset α} (h : s ⊆ t) : nePowerset s ⊆ nePowerset t :=
  erase_subset_erase ∅ (powerset_mono.mpr h)

/-- `nePowerset X` is closed under nonempty union. -/
theorem nePowerset_union_mem {X s t : Finset α} (hs : s ∈ nePowerset X)
    (ht : t ∈ nePowerset X) : s ∪ t ∈ nePowerset X := by
  simp only [nePowerset, mem_erase, mem_powerset] at hs ht ⊢
  refine ⟨?_, union_subset hs.2 ht.2⟩
  intro huv
  exact hs.1 (subset_empty.mp (huv ▸ subset_union_left))

/-! ### `⊕` — disjoint addition ([harbour-2016] (17)) -/

/-- Disjoint addition `⊕` (`oplus`): the pointwise lattice join of two feature
denotations ([harbour-2016] (17)) — the Linkian join operator [link-1983] (cf.
[chierchia-1998]'s sum). Generates heterogeneous pluralities: `oplus SPEAKER ANIMATE`
includes `{speaker, animal}`. The body `(F ×ˢ G).image (· ∪ ·)` is mathlib's own
unfolding of `Finset.image₂ (· ∪ ·)` (see `oplus_eq_image₂`), so the `image₂_*`
lemmas transfer by `rfl`. -/
def oplus (F G : Finset (Finset α)) : Finset (Finset α) :=
  (F ×ˢ G).image fun yz => yz.1 ∪ yz.2

/-- `oplus` agrees with `Finset.image₂ (· ∪ ·)` definitionally. -/
theorem oplus_eq_image₂ (F G : Finset (Finset α)) :
    oplus F G = Finset.image₂ (· ∪ ·) F G := rfl

/-- Membership in `oplus`. -/
theorem mem_oplus_iff {F G : Finset (Finset α)} {z : Finset α} :
    z ∈ oplus F G ↔ ∃ x ∈ F, ∃ y ∈ G, x ∪ y = z := by
  rw [oplus_eq_image₂]; exact mem_image₂

/-- Constructor form of `oplus` membership. -/
theorem mem_oplus_of_mem {F G : Finset (Finset α)} {x y : Finset α}
    (hx : x ∈ F) (hy : y ∈ G) : x ∪ y ∈ oplus F G :=
  mem_oplus_iff.mpr ⟨x, hx, y, hy, rfl⟩

/-- Monotonicity of `⊕`. -/
theorem oplus_subset {F F' G G' : Finset (Finset α)} (hF : F ⊆ F') (hG : G ⊆ G') :
    oplus F G ⊆ oplus F' G' :=
  image₂_subset hF hG

/-- Associativity of `⊕`. -/
theorem oplus_assoc (F G H : Finset (Finset α)) :
    oplus (oplus F G) H = oplus F (oplus G H) := by
  show image₂ (· ∪ ·) (image₂ (· ∪ ·) F G) H = image₂ (· ∪ ·) F (image₂ (· ∪ ·) G H)
  exact image₂_assoc fun a b c => union_assoc a b c

/-- `⊕` of two sub-lattices of `nePowerset X` lands back in `nePowerset X`. -/
theorem oplus_subset_nePowerset {X : Finset α} {F G : Finset (Finset α)}
    (hF : F ⊆ nePowerset X) (hG : G ⊆ nePowerset X) : oplus F G ⊆ nePowerset X := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_oplus_iff.mp hz
  exact nePowerset_union_mem (hF hx) (hG hy)

/-- `nePowerset X` is closed under self-`⊕`. -/
theorem oplus_nePowerset_self_subset (X : Finset α) :
    oplus (nePowerset X) (nePowerset X) ⊆ nePowerset X :=
  oplus_subset_nePowerset (Subset.refl _) (Subset.refl _)

/-! ### `⊖` — joint subtraction ([harbour-2016] (19)) -/

/-- Joint subtraction `⊖` (`ominus`): strip the feature lattice `F`'s maximum
(`F.sup id`, its generating set) from every element of the collection `G`. Cumulative
subtraction reduces to subtracting the maximum, since the feature lattices have a
unique maximal element ([harbour-2016] (19)). The empty set may appear and is winnowed
downstream by the variable head `φ`. -/
def ominus (F G : Finset (Finset α)) : Finset (Finset α) := G.image (· \ F.sup id)

/-- Membership in `ominus`. -/
theorem mem_ominus_iff {F G : Finset (Finset α)} {z : Finset α} :
    z ∈ ominus F G ↔ ∃ g ∈ G, g \ F.sup id = z := mem_image

/-- Monotonicity of `⊖` in the acted-on collection. -/
theorem ominus_subset {F G G' : Finset (Finset α)} (h : G ⊆ G') :
    ominus F G ⊆ ominus F G' :=
  image_subset_image h

/-! ### Lexical Complementarity ([harbour-2016] (31)) -/

/-- Lexical Complementarity: when `⟦F⟧ ⊂ ⟦G⟧`, use of `G` is restricted to
`⟦G⟧ \ ⟦F⟧`, forestalling a denotation from covering individuals a more featurally
specified sibling already picks out ([harbour-2016] (31), p. 80). -/
def lexComp (G F : Finset (Finset α)) : Finset (Finset α) := G \ F

theorem lexComp_subset (G F : Finset (Finset α)) : lexComp G F ⊆ G := sdiff_subset

/-- Membership in `lexComp`. -/
theorem mem_lexComp_iff {G F : Finset (Finset α)} {z : Finset α} :
    z ∈ lexComp G F ↔ z ∈ G ∧ z ∉ F := mem_sdiff

/-- A `lexComp` result is disjoint from the more-specified sibling it excludes. -/
theorem lexComp_disjoint (G F : Finset (Finset α)) : Disjoint (lexComp G F) F :=
  sdiff_disjoint

/-- `lexComp` stays within `nePowerset X` (it only removes elements). -/
theorem lexComp_subset_nePowerset {X : Finset α} {G F : Finset (Finset α)}
    (hG : G ⊆ nePowerset X) : lexComp G F ⊆ nePowerset X :=
  (lexComp_subset G F).trans hG

/-! ### Lattices generated by a set of atoms -/

/-- Membership in `nePowerset`. -/
theorem mem_nePowerset_iff {X s : Finset α} : s ∈ nePowerset X ↔ s.Nonempty ∧ s ⊆ X := by
  simp [nePowerset, nonempty_iff_ne_empty]

/-- The groups drawn from `Y` that contain an atom of `X`: what a feature with atoms `X`
denotes once added by `⊕` to the lattice generated by `Y`. -/
def containing (X Y : Finset α) : Finset (Finset α) :=
  (nePowerset Y).filter λ s => (s ∩ X).Nonempty

theorem mem_containing_iff {X Y s : Finset α} :
    s ∈ containing X Y ↔ s ⊆ Y ∧ (s ∩ X).Nonempty := by
  rw [containing, mem_filter, mem_nePowerset_iff]
  exact ⟨λ h => ⟨h.1.2, h.2⟩, λ h => ⟨⟨h.2.mono inter_subset_left, h.1⟩, h.2⟩⟩

/-- More atoms, more groups. -/
theorem containing_mono {X X' Y : Finset α} (h : X ⊆ X') :
    containing X Y ⊆ containing X' Y := λ _ hs =>
  mem_containing_iff.2 ⟨(mem_containing_iff.1 hs).1,
    (mem_containing_iff.1 hs).2.mono (inter_subset_inter (Subset.refl _) h)⟩

/-- `⊕` of the lattice of `X` onto the lattice of `Y ⊇ X` is the groups from `Y` containing an
atom of `X`: heterogeneous groups. -/
theorem oplus_nePowerset_nePowerset {X Y : Finset α} (h : X ⊆ Y) :
    oplus (nePowerset X) (nePowerset Y) = containing X Y := by
  ext s
  rw [mem_oplus_iff, mem_containing_iff]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    rw [mem_nePowerset_iff] at hx hy
    exact ⟨union_subset (hx.2.trans h) hy.2, hx.1.mono (subset_inter subset_union_left hx.2)⟩
  · rintro ⟨hs, hX⟩
    exact ⟨s ∩ X, mem_nePowerset_iff.2 ⟨hX, inter_subset_right⟩, s,
      mem_nePowerset_iff.2 ⟨hX.mono inter_subset_left, hs⟩, union_eq_right.2 inter_subset_left⟩

/-- Along an entailment chain `X ⊆ Y ⊆ Z`, `⊕` absorbs: adding the lattice of `X` to the
groups from `Z` containing a `Y`-atom gives the groups containing an `X`-atom. -/
theorem oplus_nePowerset_containing {X Y Z : Finset α} (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) :
    oplus (nePowerset X) (containing Y Z) = containing X Z := by
  ext s
  rw [mem_oplus_iff, mem_containing_iff]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    rw [mem_nePowerset_iff] at hx
    rw [mem_containing_iff] at hy
    exact ⟨union_subset (hx.2.trans (hXY.trans hYZ)) hy.1,
      hx.1.mono (subset_inter subset_union_left hx.2)⟩
  · rintro ⟨hs, hX⟩
    exact ⟨s ∩ X, mem_nePowerset_iff.2 ⟨hX, inter_subset_right⟩, s,
      mem_containing_iff.2 ⟨hs, hX.mono (inter_subset_inter (Subset.refl _) hXY)⟩,
      union_eq_right.2 inter_subset_left⟩

/-- Lexical Complementarity against a more specified sibling: the groups containing a
`Y`-atom but no `X`-atom, marked reference. -/
theorem mem_lexComp_containing_iff {X Y Z s : Finset α} :
    s ∈ lexComp (containing Y Z) (containing X Z) ↔
      s ⊆ Z ∧ (s ∩ Y).Nonempty ∧ ¬ (s ∩ X).Nonempty := by
  rw [mem_lexComp_iff, mem_containing_iff, mem_containing_iff]
  exact ⟨λ h => ⟨h.1.1, h.1.2, λ hX => h.2 ⟨h.1.1, hX⟩⟩,
    λ h => ⟨⟨h.1, h.2.1⟩, λ h' => h.2.2 h'.2⟩⟩

/-- Disjoint atom sets give incomparable denotations: neither is the more specified. -/
theorem containing_not_subset_of_disjoint {X Y Z : Finset α} (hd : Disjoint X Y)
    (hX : X.Nonempty) (hXZ : X ⊆ Z) :
    ¬ containing X Z ⊆ containing Y Z := by
  obtain ⟨x, hx⟩ := hX
  intro h
  obtain ⟨y, hy⟩ := (mem_containing_iff.1
    (h (mem_containing_iff.2 ⟨singleton_subset_iff.2 (hXZ hx), ⟨x, by simp [hx]⟩⟩))).2
  rw [mem_inter, mem_singleton] at hy
  exact disjoint_left.1 hd hx (hy.1 ▸ hy.2)

/-! ### Signed feature application -/

/-- Apply a signed feature (lattice `F`) to a collection `G`: `+F` is `oplus`, `−F`
is `ominus`. The `sign : Bool` is genuine bivalent feature polarity ([harbour-2016]
treats `±` as bivalent values), not predicate-shape data. -/
def act (sign : Bool) (F G : Finset (Finset α)) : Finset (Finset α) :=
  if sign then oplus F G else ominus F G

@[simp] theorem act_true (F G : Finset (Finset α)) : act true F G = oplus F G := rfl
@[simp] theorem act_false (F G : Finset (Finset α)) : act false F G = ominus F G := rfl

end Minimalist.Phi.Lattice
