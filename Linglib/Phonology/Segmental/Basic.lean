/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Segmental.Defs

/-!
# Basic theory of segments

This file develops the theory of the segments defined in
`Phonology/Segmental/Defs.lean`. Natural-class membership is the bundle order: a
specification matches a segment exactly when it lies below it in the subsumption order
of Shieber and Carpenter, so having a value is lying above the bundle specifying that
value alone, matching a specification list is having each listed value, and each
conjunctive natural class is the segments above its specification. The remaining
results concern the feature-change operations, the features on which sonority depends, the
sonority rise between two classes, and the Parker sonority ranking.

## Main results

* `Segment.hasValue_iff_single_le`: having a value is lying above the single-feature
  bundle.
* `Segment.ofSpecs_le_iff`: a specification list lies below a segment iff the segment has
  every listed value.
* `Segment.isVowel_iff_le`: a natural class is the segments above its specification, and
  likewise for consonants, stops, fricatives, nasals and glides.
* `Segment.setFeature_hasValue`: the feature-change operations act as specified.
* `IsDistinctive`: a feature set on which no two segments of an inventory agree, with
  `Segment.restrict_eq_restrict_iff` relating restriction to agreement on the set.
* `Sonority.ofSegment_congr`: sonority depends on a segment only through the major-class
  features and continuancy, so it is blind to place and laryngeal features.
* `Sonority.rise_pos`, `Sonority.rise_eq_zero`, `Sonority.rise_neg`: the sign of the
  sonority rise separates rises, plateaus and falls.
* `Sonority.Class.parkerRank_injective`: the Parker scale ranks classes distinctly.
* `Sonority.Class.toSonority_ofSegment`: the Parker classification coarsens to the
  six-level one.

## References

* [shieber-1986]
* [carpenter-1992]
* [parker-2002]
-/

@[expose] public section

namespace Phonology

namespace Segment

variable (s : Segment)

/-! ### Natural classes are the bundle order -/

/-- Having a value is lying above the bundle that specifies that value alone. -/
theorem hasValue_iff_single_le (f : Feature) (v : Bool) :
    s.HasValue f v ↔ Bundle.single f v ≤ s :=
  Bundle.single_le_iff.symm

@[simp] theorem ofSpecs_apply (specs : List (Feature × Bool)) (f : Feature) :
    ofSpecs specs f = specs.lookup f := rfl

/-- A specification list lies below a segment exactly when the segment has every value the
list looks up. -/
theorem ofSpecs_le_iff (specs : List (Feature × Bool)) :
    ofSpecs specs ≤ s ↔ ∀ f v, specs.lookup f = some v → s.HasValue f v :=
  Bundle.ofList_le_iff

/-- With distinct features, a specification list lies below a segment exactly when the
segment has each listed value. -/
theorem ofSpecs_le_iff_forall_mem {specs : List (Feature × Bool)}
    (h : (specs.map Prod.fst).Nodup) :
    ofSpecs specs ≤ s ↔ ∀ p ∈ specs, s.HasValue p.1 p.2 :=
  Bundle.ofList_le_iff_forall_mem h

/-- The vowels are the segments above `[+syllabic]`. -/
theorem isVowel_iff_le : s.IsVowel ↔ ofSpecs [(.syllabic, true)] ≤ s := by
  rw [ofSpecs_le_iff_forall_mem s (by decide)]; simp [IsVowel]

/-- The consonants are the segments above `[+consonantal]`. -/
theorem isConsonant_iff_le : s.IsConsonant ↔ ofSpecs [(.consonantal, true)] ≤ s := by
  rw [ofSpecs_le_iff_forall_mem s (by decide)]; simp [IsConsonant]

/-- The obstruents are the segments above `[+cons, −son]`. -/
theorem isObstruent_iff_le :
    s.IsObstruent ↔ ofSpecs [(.consonantal, true), (.sonorant, false)] ≤ s := by
  rw [ofSpecs_le_iff_forall_mem s (by decide)]; simp [IsObstruent]

/-- The stops are the segments above `[+cons, −son, −cont]`. -/
theorem isStop_iff_le :
    s.IsStop ↔
      ofSpecs [(.consonantal, true), (.sonorant, false), (.continuant, false)] ≤ s := by
  rw [ofSpecs_le_iff_forall_mem s (by decide)]; simp [IsStop]

/-- The fricatives are the segments above `[+cons, −son, +cont]`. -/
theorem isFricative_iff_le :
    s.IsFricative ↔
      ofSpecs [(.consonantal, true), (.sonorant, false), (.continuant, true)] ≤ s := by
  rw [ofSpecs_le_iff_forall_mem s (by decide)]; simp [IsFricative]

/-- The nasals are the segments above `[+nasal]`. -/
theorem isNasal_iff_le : s.IsNasal ↔ ofSpecs [(.nasal, true)] ≤ s := by
  rw [ofSpecs_le_iff_forall_mem s (by decide)]; simp [IsNasal]

/-- The glides are the segments above `[−cons, −syll, +approx]`. -/
theorem isGlide_iff_le :
    s.IsGlide ↔
      ofSpecs [(.consonantal, false), (.syllabic, false), (.approximant, true)] ≤ s := by
  rw [ofSpecs_le_iff_forall_mem s (by decide)]; simp [IsGlide]

/-! ### Effect on the modified feature -/

@[simp] theorem setFeature_hasValue (f : Feature) (v : Bool) : (s.setFeature f v).HasValue f v :=
  Function.update_self _ _ _

theorem fillFromContext_apply_self_of_unspecified {f : Feature} (h : s.Unspecified f)
    (ctx : Segment) :
    (s.fillFromContext f ctx) f = ctx f := by
  simp only [Segment.fillFromContext, Bundle.merge,
    show s f = none from h, Function.update_self]

theorem fillFromContext_apply_self_of_specified {f : Feature} {w : Bool} (h : s.HasValue f w)
    (ctx : Segment) : (s.fillFromContext f ctx) f = some w := by
  simp only [Segment.fillFromContext, Bundle.merge, show s f = some w from h]

/-! ### Value preserved on other features -/

@[simp] theorem setFeature_apply_of_ne {f g : Feature} (h : f ≠ g) (v : Bool) :
    (s.setFeature f v) g = s g :=
  Function.update_of_ne (Ne.symm h) _ _

@[simp] theorem fillFromContext_apply_of_ne {f g : Feature} (h : f ≠ g) (ctx : Segment) :
    (s.fillFromContext f ctx) g = s g := by
  simp only [Segment.fillFromContext, Bundle.merge, Function.update_of_ne (Ne.symm h)]
  cases s g <;> rfl

end Segment

/-! ### Distinctive feature sets -/

section Distinctive

variable {C D : Finset Feature} {I J : Finset Segment}

/-- Two segments have the same restriction to a feature set iff they agree on it. -/
theorem Segment.restrict_eq_restrict_iff {s s' : Segment} :
    Bundle.restrict C s = Bundle.restrict C s' ↔ Set.EqOn s s' ↑C :=
  Bundle.restrict_eq_restrict_iff C

/-- A feature set is distinctive for an inventory when no two segments of the inventory agree
on it. -/
def IsDistinctive (C : Finset Feature) (I : Finset Segment) : Prop :=
  Set.InjOn (Bundle.restrict C) (I : Set Segment)

instance : Decidable (IsDistinctive C I) :=
  decidable_of_iff (∀ s ∈ I, ∀ s' ∈ I, Bundle.restrict C s = Bundle.restrict C s' → s = s')
    ⟨fun h _ hs _ hs' ↦ h _ hs _ hs', fun h _ hs _ hs' ↦ h hs hs'⟩

/-- A larger feature set is still distinctive. -/
theorem IsDistinctive.mono (h : IsDistinctive C I) (hCD : C ⊆ D) : IsDistinctive D I :=
  fun s hs s' hs' he ↦ h hs hs' <| by
    have := congrArg (Bundle.restrict C) he
    rwa [Bundle.restrict_restrict, Bundle.restrict_restrict,
      Finset.inter_eq_right.2 hCD] at this

/-- A distinctive feature set is distinctive for every smaller inventory. -/
theorem IsDistinctive.subset (h : IsDistinctive C I) (hJI : J ⊆ I) : IsDistinctive C J :=
  Set.InjOn.mono (Finset.coe_subset.2 hJI) h

end Distinctive

/-! ### Sonority -/

namespace Sonority

theorem rank_strictMono : StrictMono rank := fun _ _ h ↦ h

/-- The features `ofSegment` reads are the major-class features and continuancy. Place and
laryngeal features are absent. -/
def features : Finset Feature := {.sonorant, .continuant, .approximant, .consonantal, .syllabic}

/-- Sonority depends on a segment only through `Sonority.features`. -/
theorem ofSegment_congr {s s' : Segment} (h : ∀ f ∈ features, s f = s' f) :
    ofSegment s = ofSegment s' := by
  simp only [ofSegment, Segment.HasValue, h _ (by decide : Feature.sonorant ∈ features),
    h _ (by decide : Feature.continuant ∈ features),
    h _ (by decide : Feature.approximant ∈ features),
    h _ (by decide : Feature.consonantal ∈ features),
    h _ (by decide : Feature.syllabic ∈ features)]

/-- Setting a feature that sonority does not read leaves sonority unchanged. -/
theorem ofSegment_setFeature {f : Feature} (hf : f ∉ features) (s : Segment) (v : Bool) :
    ofSegment (s.setFeature f v) = ofSegment s :=
  ofSegment_congr fun g hg ↦ Segment.setFeature_apply_of_ne (s := s) (by rintro rfl; exact hf hg) v

/-- The sonority rise from `a` to `b` is positive when sonority rises, zero on a plateau,
and negative when it falls. -/
def rise (a b : Sonority) : ℤ := b.rank - a.rank

@[simp] theorem rise_self (a : Sonority) : rise a a = 0 := by simp only [rise]; omega

theorem neg_rise (a b : Sonority) : -rise a b = rise b a := by simp only [rise]; omega

theorem rise_add_rise (a b c : Sonority) : rise a b + rise b c = rise a c := by
  simp only [rise]; omega

@[simp] theorem rise_pos {a b : Sonority} : 0 < rise a b ↔ a < b := by
  change 0 < (b.rank : ℤ) - a.rank ↔ a.rank < b.rank; omega

@[simp] theorem rise_neg {a b : Sonority} : rise a b < 0 ↔ b < a := by
  change (b.rank : ℤ) - a.rank < 0 ↔ b.rank < a.rank; omega

@[simp] theorem rise_eq_zero {a b : Sonority} : rise a b = 0 ↔ a = b :=
  ⟨fun h ↦ rank_strictMono.injective (by simp only [rise] at h; omega),
    by rintro rfl; exact rise_self _⟩

end Sonority

namespace Sonority.Class

/-- The eight Parker classes receive distinct ranks ([parker-2002]). The ranking is Parker's
    reversible default, so injectivity is the faithful invariant, and no fixed order on
    `Sonority.Class` is implied. -/
theorem parkerRank_injective : Function.Injective parkerRank := by
  intro a b h
  cases a <;> cases b <;> simp_all [parkerRank]

/-- Classifying on the Parker scale and collapsing the voicing split is the six-level
    classification. -/
theorem toSonority_ofSegment (s : Segment) : (ofSegment s).toSonority = Sonority.ofSegment s := by
  unfold ofSegment Sonority.ofSegment
  split_ifs <;> rfl

end Sonority.Class

end Phonology
