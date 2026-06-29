/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Segmental.Defs

/-!
# Basic theory of segments

This file develops the theory of the segments defined in
`Phonology/Segmental/Defs.lean`. Natural-class membership is just the bundle order
— a pattern `p` matches `s` exactly when `p ≤ s` ([shieber-1986]; [carpenter-1992])
— so the results here are about the feature-change operations and the injectivity
of the Parker sonority ranking.

## Main results

* `Segment.setFeature_hasValue` &c. — the feature-change operations act as specified.
* `Sonority.Class.parkerRank_injective` — the Parker scale ranks classes distinctly.
-/

namespace Phonology

namespace Segment

variable (s : Segment)

/-! ### Feature changes -/

/-- Applying the empty change list is the identity. -/
@[simp] theorem applyChanges_ofSpecs_nil : s.applyChanges (Segment.ofSpecs []) = s := by
  funext f; simp [Segment.applyChanges, Segment.ofSpecs, Features.Bundle.merge]

/-- Applying the same change twice equals applying it once. -/
@[simp] theorem applyChanges_idem (change : Segment) :
    (s.applyChanges change).applyChanges change = s.applyChanges change := by
  funext f
  simp only [Segment.applyChanges, Features.Bundle.merge]
  cases change f <;> rfl

/-! ### Effect on the modified feature -/

@[simp] theorem unsetFeature_unspecified (f : Feature) : (s.unsetFeature f).Unspecified f :=
  Function.update_self _ _ _

@[simp] theorem setFeature_hasValue (f : Feature) (v : Bool) : (s.setFeature f v).HasValue f v :=
  Function.update_self _ _ _

theorem fillFeature_hasValue_of_unspecified {f : Feature} (h : s.Unspecified f) (v : Bool) :
    (s.fillFeature f v).HasValue f v := by
  simp only [Segment.fillFeature, Segment.HasValue, Features.Bundle.merge,
    Features.Bundle.single, show s f = none from h, Function.update_self]

theorem fillFeature_apply_of_specified {f : Feature} {w : Bool} (h : s.HasValue f w) (v : Bool) :
    (s.fillFeature f v) f = some w := by
  simp only [Segment.fillFeature, Features.Bundle.merge, show s f = some w from h]

theorem fillFromContext_apply_self_of_unspecified {f : Feature} (h : s.Unspecified f) (ctx : Segment) :
    (s.fillFromContext f ctx) f = ctx f := by
  simp only [Segment.fillFromContext, Features.Bundle.merge,
    show s f = none from h, Function.update_self]

theorem fillFromContext_apply_self_of_specified {f : Feature} {w : Bool} (h : s.HasValue f w)
    (ctx : Segment) : (s.fillFromContext f ctx) f = some w := by
  simp only [Segment.fillFromContext, Features.Bundle.merge, show s f = some w from h]

/-! ### Value preserved on other features -/

@[simp] theorem unsetFeature_apply_of_ne {f g : Feature} (h : f ≠ g) : (s.unsetFeature f) g = s g :=
  Function.update_of_ne (Ne.symm h) _ _

@[simp] theorem setFeature_apply_of_ne {f g : Feature} (h : f ≠ g) (v : Bool) :
    (s.setFeature f v) g = s g :=
  Function.update_of_ne (Ne.symm h) _ _

@[simp] theorem fillFeature_apply_of_ne {f g : Feature} (h : f ≠ g) (v : Bool) :
    (s.fillFeature f v) g = s g := by
  simp only [Segment.fillFeature, Features.Bundle.merge, Features.Bundle.single,
    Function.update_of_ne (Ne.symm h)]
  cases s g <;> rfl

@[simp] theorem fillFromContext_apply_of_ne {f g : Feature} (h : f ≠ g) (ctx : Segment) :
    (s.fillFromContext f ctx) g = s g := by
  simp only [Segment.fillFromContext, Features.Bundle.merge, Function.update_of_ne (Ne.symm h)]
  cases s g <;> rfl

end Segment

/-! ### Sonority -/

namespace Sonority.Class

/-- The eight Parker classes receive distinct ranks: `parkerRank` is injective
    ([parker-2002]). The ranking is Parker's reversible default, so this is the
    faithful invariant — no fixed order on `Sonority.Class` is implied. -/
theorem parkerRank_injective : Function.Injective parkerRank := by
  intro a b h
  cases a <;> cases b <;> simp_all [parkerRank]

end Sonority.Class

end Phonology
