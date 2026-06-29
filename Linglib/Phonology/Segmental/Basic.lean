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

/-! ### Effect on the modified feature -/

@[simp] theorem setFeature_hasValue (f : Feature) (v : Bool) : (s.setFeature f v).HasValue f v :=
  Function.update_self _ _ _

theorem fillFromContext_apply_self_of_unspecified {f : Feature} (h : s.Unspecified f) (ctx : Segment) :
    (s.fillFromContext f ctx) f = ctx f := by
  simp only [Segment.fillFromContext, Features.Bundle.merge,
    show s f = none from h, Function.update_self]

theorem fillFromContext_apply_self_of_specified {f : Feature} {w : Bool} (h : s.HasValue f w)
    (ctx : Segment) : (s.fillFromContext f ctx) f = some w := by
  simp only [Segment.fillFromContext, Features.Bundle.merge, show s f = some w from h]

/-! ### Value preserved on other features -/

@[simp] theorem setFeature_apply_of_ne {f g : Feature} (h : f ≠ g) (v : Bool) :
    (s.setFeature f v) g = s g :=
  Function.update_of_ne (Ne.symm h) _ _

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
