import Linglib.Core.Logic.Trivalent

/-!
# Homogeneity

A trivalent proposition (`Trivalent.Prop3`) is *homogeneous* when its
extension gap is nonempty ([kriz-2016]): true when the predicate holds
throughout its specification points, false when it fails throughout, and
undefined in between. Instantiations differ in the specification-point
sort — atoms of a plurality (`Homogeneity.Plural`), closest antecedent
worlds (`Homogeneity.Conditional`), overlapping pluralities
(`Homogeneity.Collective`), best modal worlds (`Studies/AghaJeretic2022`).
Homogeneity removers (*all*, *necessarily*, *completely*) denote the
Beaver-Krahmer assertion operator `Prop3.metaAssert`, which collapses the
gap into the negative extension; the pragmatics of the gap lives in
`Homogeneity.Usable`.

## References

* [M. Križ, *Homogeneity, Non-Maximality, and All*][kriz-2016]
* [M. Križ, *Aspects of Homogeneity in the Semantics of Natural Language*][kriz-2015]
-/

namespace Semantics.Homogeneity

open Trivalent (Prop3)

variable {W : Type*}

/-- A proposition is homogeneous if its extension gap is nonempty. The gap
    is what enables non-maximal readings. -/
def isHomogeneous (p : Prop3 W) : Prop := p.gapExt.Nonempty

/-- A single gap-world witnesses homogeneity. -/
theorem isHomogeneous_of_gap (p : Prop3 W) (w : W) (h : p w = .indet) :
    isHomogeneous p :=
  ⟨w, h⟩

/-- Bivalence and homogeneity are complementary. -/
theorem isBivalent_iff_not_isHomogeneous (p : Prop3 W) :
    p.isBivalent ↔ ¬isHomogeneous p := by
  rw [Prop3.isBivalent_iff_gapExt_eq_empty, isHomogeneous,
    Set.not_nonempty_iff_eq_empty]

/-- A meta-asserted proposition is never homogeneous: gap removers yield
    bivalence. -/
theorem not_isHomogeneous_metaAssert (p : Prop3 W) :
    ¬isHomogeneous p.metaAssert := by
  simp [isHomogeneous, Prop3.gapExt_metaAssert]

end Semantics.Homogeneity
