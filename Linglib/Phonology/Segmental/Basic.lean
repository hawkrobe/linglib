/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Segmental.Defs

/-!
# Segments: basic theory

The theory of segments over the definitions in `Phonology/Segmental/Defs.lean`:
that natural-class membership coincides with the bundle subsumption order, the
behaviour of the feature-change operations, and the totality of the Parker
sonority ranking.

[hayes-2009] [chomsky-halle-1968] [clements-1990] [parker-2002] [shieber-1986]
[carpenter-1992]
-/

namespace Phonology

/-! ### Specification -/

/-- Specification is the bundle notion of carrying more than the unspecified
    bottom. -/
theorem Segment.specified_iff_specifies (s : Segment) (f : Feature) :
    s.Specified f ↔ BundleLike.Specifies s f := by
  simp only [Segment.Specified, BundleLike.Specifies, BundleLike.val,
    ne_eq, Option.isSome_iff_ne_none]
  rfl

/-! ### Natural-class membership is subsumption -/

/-- Matching a natural-class pattern is subsumption: `s` matches `p` exactly when
    `p` refines to `s` ([shieber-1986]; [carpenter-1992]). -/
theorem Segment.matchesPattern_iff_le {s p : Segment} :
    s.matchesPattern p = true ↔ p ≤ s := by
  simp only [Segment.matchesPattern, List.all_eq_true, decide_eq_true_eq, Pi.le_def]
  exact ⟨fun h f => h f (allFeatures_complete f), fun h f _ => h f⟩

@[simp] theorem Segment.matchesPattern_iff_le' {s p : Segment} :
    s.MatchesPattern p ↔ p ≤ s := matchesPattern_iff_le

/-- Every segment matches itself as a pattern (reflexivity of subsumption). -/
@[simp] theorem Segment.matchesPattern_self (s : Segment) :
    s.matchesPattern s = true :=
  matchesPattern_iff_le.mpr le_rfl

/-! ### Feature changes -/

/-- Applying the empty change list is the identity. -/
@[simp] theorem Segment.applyChanges_ofSpecs_nil (s : Segment) :
    s.applyChanges (Segment.ofSpecs []) = s := by
  funext f; simp [Segment.applyChanges, Segment.ofSpecs, Features.Bundle.merge]

/-- Applying the same change twice equals applying it once. -/
@[simp] theorem Segment.applyChanges_idem (s change : Segment) :
    (s.applyChanges change).applyChanges change = s.applyChanges change := by
  funext f
  simp only [Segment.applyChanges, Features.Bundle.merge]
  cases change f <;> rfl

namespace Segment

/-! ### Underspecification -/

/-- Specification and unspecification are mutually exclusive and exhaustive. -/
theorem specified_iff_not_unspecified (s : Segment) (f : Feature) :
    s.Specified f ↔ ¬ s.Unspecified f := by
  unfold Specified Unspecified
  cases s f <;> simp

/-! ### Effect on the modified feature -/

@[simp] theorem unsetFeature_unspecified (s : Segment) (f : Feature) :
    (s.unsetFeature f).Unspecified f :=
  Function.update_self _ _ _

@[simp] theorem setFeature_hasValue (s : Segment) (f : Feature) (v : Bool) :
    (s.setFeature f v).HasValue f v :=
  Function.update_self _ _ _

theorem fillFeature_hasValue_of_unspecified
    (s : Segment) {f : Feature} (h : s.Unspecified f) (v : Bool) :
    (s.fillFeature f v).HasValue f v := by
  simp only [Segment.fillFeature, Segment.HasValue, Features.Bundle.merge,
    Features.Bundle.single, show s f = none from h, Function.update_self]

theorem fillFeature_apply_of_specified
    (s : Segment) {f : Feature} {w : Bool} (h : s.HasValue f w) (v : Bool) :
    (s.fillFeature f v) f = some w := by
  simp only [Segment.fillFeature, Features.Bundle.merge,
    show s f = some w from h]

theorem fillFromContext_apply_self_of_unspecified
    (s : Segment) {f : Feature} (h : s.Unspecified f) (ctx : Segment) :
    (s.fillFromContext f ctx) f = ctx f := by
  simp only [Segment.fillFromContext, Features.Bundle.merge,
    show s f = none from h, Function.update_self]

theorem fillFromContext_apply_self_of_specified
    (s : Segment) {f : Feature} {w : Bool} (h : s.HasValue f w) (ctx : Segment) :
    (s.fillFromContext f ctx) f = some w := by
  simp only [Segment.fillFromContext, Features.Bundle.merge,
    show s f = some w from h]

/-! ### Value preserved on other features -/

@[simp] theorem unsetFeature_apply_of_ne
    (s : Segment) {f g : Feature} (h : f ≠ g) :
    (s.unsetFeature f) g = s g :=
  Function.update_of_ne (Ne.symm h) _ _

@[simp] theorem setFeature_apply_of_ne
    (s : Segment) {f g : Feature} (h : f ≠ g) (v : Bool) :
    (s.setFeature f v) g = s g :=
  Function.update_of_ne (Ne.symm h) _ _

@[simp] theorem fillFeature_apply_of_ne
    (s : Segment) {f g : Feature} (h : f ≠ g) (v : Bool) :
    (s.fillFeature f v) g = s g := by
  simp only [Segment.fillFeature, Features.Bundle.merge, Features.Bundle.single,
    Function.update_of_ne (Ne.symm h)]
  cases s g <;> rfl

@[simp] theorem fillFromContext_apply_of_ne
    (s : Segment) {f g : Feature} (h : f ≠ g) (ctx : Segment) :
    (s.fillFromContext f ctx) g = s g := by
  simp only [Segment.fillFromContext, Features.Bundle.merge,
    Function.update_of_ne (Ne.symm h)]
  cases s g <;> rfl

end Segment

/-! ### Sonority -/

/-- Parker sonority is strictly monotone: the ranking is a total order. -/
theorem parker_strictly_monotone (a b : SonorityClass) (h : a ≠ b) :
    SonorityClass.parkerSonority a < SonorityClass.parkerSonority b ∨
    SonorityClass.parkerSonority a > SonorityClass.parkerSonority b := by
  cases a <;> cases b <;> simp_all [SonorityClass.parkerSonority]

end Phonology
