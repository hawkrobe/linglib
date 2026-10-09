module

public import Linglib.Logic.Trivalent.Pointwise
public import Mathlib.Order.SetNotation

/-!
# Homogeneity

A trivalent proposition `W → Trivalent` is homogeneous, in Križ's sense, when its extension
gap is nonempty: true when the predicate holds throughout its specification points, false when it
fails throughout, and undefined in between. Instantiations differ in the specification points:
atoms of a plurality (`Homogeneity.Plural`), closest antecedent worlds
(`Conditional.selectionalCounterfactual`), overlapping pluralities (`Homogeneity.Collective`),
best modal worlds (`Studies/AghaJeretic2022`). Homogeneity removers such as *all*, *necessarily*
and *completely* denote the Beaver–Krahmer assertion operator `Trivalent.metaAssert`, applied
pointwise, which collapses
the gap into the negative extension. A family of propositions is `Homogeneous` at a world when
its members are all true there or all false there, which is where the supervaluation over them is
defined; presuppositional exhaustification presupposes this of its includable alternatives.

## Main declarations

* `isHomogeneous`: a trivalent proposition has a nonempty gap.
* `Homogeneous`: the members of a family of propositions agree at a world.
* `homogeneous_coe_iff`: on a finite family, agreement is definedness of the supervaluation.

## References

* [kriz-2016]
* [kriz-2015]
* [delpinal-bassi-sauerland-2024]
-/

@[expose] public section

namespace Homogeneity

variable {W : Type*}

/-- A proposition is homogeneous if its extension gap is nonempty. The gap
    is what enables non-maximal readings. -/
def isHomogeneous (p : W → Trivalent) : Prop := (Trivalent.gapExt p).Nonempty

/-- A single gap-world witnesses homogeneity. -/
theorem isHomogeneous_of_gap (p : (W → Trivalent)) (w : W) (h : p w = .indet) :
    isHomogeneous p :=
  ⟨w, h⟩

/-- Bivalence and homogeneity are complementary. -/
theorem isBivalent_iff_not_isHomogeneous (p : W → Trivalent) :
    Trivalent.IsBivalent p ↔ ¬isHomogeneous p := by
  rw [Trivalent.isBivalent_iff_gapExt_eq_empty, isHomogeneous,
    Set.not_nonempty_iff_eq_empty]

/-- A meta-asserted proposition is never homogeneous: gap removers yield
    bivalence. -/
theorem not_isHomogeneous_comp_metaAssert (p : W → Trivalent) :
    ¬isHomogeneous (Trivalent.metaAssert ∘ p) := by
  simp [isHomogeneous, Trivalent.gapExt_comp_metaAssert]

/-- The propositions of `S` are homogeneous at `w` when they are all true there or all false
there. -/
def Homogeneous (S : Set (Set W)) (w : W) : Prop :=
  (∀ α ∈ S, w ∈ α) ∨ ∀ α ∈ S, w ∉ α

section Homogeneous

variable {S : Set (Set W)} {φ : Set W} {w : W}

@[simp] theorem homogeneous_empty : Homogeneous (∅ : Set (Set W)) w :=
  .inl fun _ h ↦ h.elim

@[simp] theorem homogeneous_pair {p q : Set W} : Homogeneous {p, q} w ↔ (w ∈ p ↔ w ∈ q) := by
  grind [Homogeneous]

/-- On a finite family, homogeneity at `w` is definedness at `w` of the supervaluation of truth
over the family. -/
theorem homogeneous_coe_iff (s : Finset (Set W)) [DecidablePred fun α : Set W ↦ w ∈ α] :
    Homogeneous (s : Set (Set W)) w ↔ Trivalent.supervaluation s (w ∈ ·) ≠ .indet := by
  rw [Ne, Trivalent.supervaluation_eq_indet_iff]
  grind [Homogeneous]

/-- Under homogeneity, a proposition between the meet and the join of `S` is true where every
member of `S` is. -/
theorem Homogeneous.mem_iff (h : Homogeneous S w) (hl : ⋂₀ S ⊆ φ) (hu : φ ⊆ ⋃₀ S) :
    w ∈ φ ↔ ∀ α ∈ S, w ∈ α := by
  grind [Homogeneous]

/-- Under homogeneity, a proposition between the meet and the join of `S` is false where every
member of `S` is. -/
theorem Homogeneous.notMem_iff (h : Homogeneous S w) (hl : ⋂₀ S ⊆ φ) (hu : φ ⊆ ⋃₀ S) :
    w ∉ φ ↔ ∀ α ∈ S, w ∉ α := by
  grind [Homogeneous]

end Homogeneous

end Homogeneity
