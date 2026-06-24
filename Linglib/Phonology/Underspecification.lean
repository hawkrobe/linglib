/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Features
import Linglib.Phonology.FeatureBundle

/-!
# Underspecification of Features on Segments
[keating-1988] [inkelas-orgun-1995] [steriade-1995]

A segment is **underspecified** for a feature `f` when its specification
function returns `none` at `f`. This file lifts the underspecification
operations defined generically in `FeatureBundle.lean` to the segment
level, and provides the `Prop` predicates and `Decidable` instances that
consumers work with.

Three-valued (`+ / − / ∅`) feature specifications are standard in
[keating-1988] (which argues some segments stay unspecified into
phonetic interpretation, surfacing via gradient interpolation rather
than categorical rule-application), [inkelas-orgun-1995] (Turkish
voicing as the canonical equipollent case), and [steriade-1995]
(cross-linguistic survey of when feature values are left blank at
underlying representation). The Latin coda /l/ analysis in
[sen-2015] Ch 2 is a worked example: geminate /ll/ is [+high, −back],
coda /l/ is [+high, +back], onset /l/ is [+high, Ø back]; on Sen's
account onset /l/'s surface backness inherits the value of the following
vowel.

## Main definitions

* `Segment.Unspecified` — feature `f` has no value on `s`.
* `Segment.unsetFeature` — remove the specification of `f` (lift of
  `FeatureBundle.delete`).
* `Segment.setFeature` — override `f` with a new value (lift of
  `FeatureBundle.set`).
* `Segment.fillFeature` — assign `v` to `f` only if `s` is currently
  unspecified for `f`; preserves existing values (default-fill semantics).
* `Segment.fillFromContext` — categorical feature spreading from
  context: an unspecified-for-`f` segment takes its `f`-value from a
  contextual segment, leaving already-specified targets untouched.

## Implementation notes

`FeatureVal := Option Bool` from `Features.lean` already encodes
the ternary `+ / − / ∅` distinction; this file does not introduce a
separate `Ternary` enum. The same `Option`-valued partial-function shape
is the generic `FeatureBundle F V` algebra in `FeatureBundle.lean`, so
the operations here are thin segment-level lifts of bundle operations.

`fillFeature` uses the bundle's `merge` (which preserves the
left-operand's specified values) rather than its `set` (which overrides),
because default-fill rules in lexical phonology [kiparsky-1982]
[archangeli-1988] are conditioned on the target being currently
underspecified. `setFeature` provides the override variant for use by
SPE-style structural-change rules.

## TODO

* `fillFromContextTier` — tier-level version that propagates an `f`-value
  leftward or rightward across a sequence of segments, skipping
  already-specified bearers.
* `Underspecified.spreadFiller` — characterise when an underspecified
  segment surfaces with the same `f`-value on both sides (interpolation)
  vs a categorical filled value (rule application).
-/

namespace Phonology

open Phonology

namespace Segment

/-! ### Underspecification predicate -/

/-- A segment is **unspecified** for feature `f` iff its spec returns `none`. -/
def Unspecified (s : Segment) (f : Feature) : Prop := s.spec f = none

instance (s : Segment) (f : Feature) : Decidable (s.Unspecified f) :=
  inferInstanceAs (Decidable (_ = none))

/-- Specification and unspecification are mutually exclusive and exhaustive. -/
theorem specified_iff_not_unspecified (s : Segment) (f : Feature) :
    s.Specified f ↔ ¬ s.Unspecified f := by
  unfold Specified Unspecified
  cases s.spec f <;> simp

/-! ### Operations -/

/-- Remove the specification of feature `f` from `s` (lift of
    `FeatureBundle.delete`). The result is unspecified for `f` and agrees
    with `s` on every other feature. -/
def unsetFeature (s : Segment) (f : Feature) : Segment :=
  ⟨FeatureBundle.delete f s.spec⟩

/-- Set feature `f` to value `v`, overriding any existing specification
    (lift of `FeatureBundle.set`). For default-fill semantics that only
    assigns when `f` is currently unspecified, use `fillFeature`. -/
def setFeature (s : Segment) (f : Feature) (v : Bool) : Segment :=
  ⟨FeatureBundle.set f v s.spec⟩

/-- Fill feature `f` with value `v` only if `s` is currently unspecified
    for `f`; existing specifications are preserved. This implements the
    default-fill semantics of feature-filling rules in lexical phonology
    [kiparsky-1982] [archangeli-1988]. -/
def fillFeature (s : Segment) (f : Feature) (v : Bool) : Segment :=
  ⟨FeatureBundle.merge s.spec (FeatureBundle.single f v)⟩

/-- Categorical feature spreading from context: the target `s`, when
    unspecified for `f`, takes the `f`-value of `ctx`; already-specified
    targets and features other than `f` are untouched. When `ctx` is
    itself unspecified for `f`, the target stays unspecified.

    This is a [keating-1988] *context rule*: the target acquires a categorical
    feature value from its neighbour and that value blocks further
    interactions. It is **distinct from** her gradient phonetic interpolation
    (her unspecified /h/ example), in which an unspecified segment stays
    unspecified and the phonetics builds a continuous trajectory through it;
    gradient phonetic interpolation is out of scope at this categorical-featural
    substrate. -/
def fillFromContext (s : Segment) (f : Feature) (ctx : Segment) : Segment :=
  ⟨FeatureBundle.merge s.spec
    (Function.update (FeatureBundle.empty : FeatureBundle Feature Bool)
       f (ctx.spec f))⟩

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
  show (s.spec f).orElse (fun _ => FeatureBundle.single f v f) = some v
  rw [show s.spec f = none from h]
  exact Function.update_self _ _ _

theorem fillFeature_spec_of_specified
    (s : Segment) {f : Feature} {w : Bool} (h : s.HasValue f w) (v : Bool) :
    (s.fillFeature f v).spec f = some w := by
  show (s.spec f).orElse (fun _ => FeatureBundle.single f v f) = some w
  rw [show s.spec f = some w from h]
  rfl

theorem fillFromContext_spec_self_of_unspecified
    (s : Segment) {f : Feature} (h : s.Unspecified f) (ctx : Segment) :
    (s.fillFromContext f ctx).spec f = ctx.spec f := by
  show (s.spec f).orElse
    (fun _ => Function.update (FeatureBundle.empty : FeatureBundle Feature Bool)
                f (ctx.spec f) f) = ctx.spec f
  rw [show s.spec f = none from h]
  exact Function.update_self _ _ _

theorem fillFromContext_spec_self_of_specified
    (s : Segment) {f : Feature} {w : Bool} (h : s.HasValue f w) (ctx : Segment) :
    (s.fillFromContext f ctx).spec f = some w := by
  show (s.spec f).orElse
    (fun _ => Function.update (FeatureBundle.empty : FeatureBundle Feature Bool)
                f (ctx.spec f) f) = some w
  rw [show s.spec f = some w from h]
  rfl

/-! ### Spec preserved on other features -/

@[simp] theorem unsetFeature_spec_of_ne
    (s : Segment) {f g : Feature} (h : f ≠ g) :
    (s.unsetFeature f).spec g = s.spec g :=
  Function.update_of_ne (Ne.symm h) _ _

@[simp] theorem setFeature_spec_of_ne
    (s : Segment) {f g : Feature} (h : f ≠ g) (v : Bool) :
    (s.setFeature f v).spec g = s.spec g :=
  Function.update_of_ne (Ne.symm h) _ _

@[simp] theorem fillFeature_spec_of_ne
    (s : Segment) {f g : Feature} (h : f ≠ g) (v : Bool) :
    (s.fillFeature f v).spec g = s.spec g := by
  have hg : FeatureBundle.single f v g = none := by
    show Function.update (FeatureBundle.empty : FeatureBundle Feature Bool)
           f (some v) g = none
    rw [Function.update_of_ne (Ne.symm h)]; rfl
  show (s.spec g).orElse (fun _ => FeatureBundle.single f v g) = s.spec g
  rw [hg]
  cases s.spec g <;> rfl

@[simp] theorem fillFromContext_spec_of_ne
    (s : Segment) {f g : Feature} (h : f ≠ g) (ctx : Segment) :
    (s.fillFromContext f ctx).spec g = s.spec g := by
  have hg : Function.update (FeatureBundle.empty : FeatureBundle Feature Bool)
              f (ctx.spec f) g = none := by
    rw [Function.update_of_ne (Ne.symm h)]; rfl
  show (s.spec g).orElse
    (fun _ => Function.update (FeatureBundle.empty : FeatureBundle Feature Bool)
                f (ctx.spec f) g) = s.spec g
  rw [hg]
  cases s.spec g <;> rfl

end Segment

end Phonology
