module

public import Linglib.Semantics.Degree.Quantifier
public import Linglib.Semantics.Presupposition.Defs

/-!
# The presuppositional superlative

*x is the μ-est of C* presupposes that `x` is a member of the comparison class and asserts that
it measures above every other member. Von Fintel gives the superlative morpheme this entry, with
the class a predicate like *girl in her class*, so that the presupposition rather than the
assertion fails when the class shrinks below `x`; at a world it is Heim's absolute superlative
`Degree.absoluteSuperlative`. The assertion is the set-standard comparative of `x` over the other
members' degrees, so its anti-additivity in the class comes from Hoeksema's anti-additivity of
the set comparative.

## Main definitions

* `Degree.superlative`: the superlative as a partial proposition.

## Main results

* `Degree.superlative_assertion`: the assertion is the set-standard comparative over the other
  members of the class.
* `Degree.isAntiAdditive_superlative_assertion`: the assertion is anti-additive in the class.
* `Degree.holds_superlative_iff`: at a world the superlative holds exactly when `x` is the
  absolute superlative of the class there.

## Implementation notes

The comparison class is given at each world, `C : W → Set α`, the transpose of von Fintel's
world-dependent predicate. The degree measure `μ` does not vary with the world; von Fintel's
`ιd P(x)(d)` measures at the world of evaluation.

## References

* [von-fintel-1999]
* [heim-1999]
* [hoeksema-1983]
-/

@[expose] public section

namespace Degree

open Presupposition Set

variable {α D W : Type*}

section Preorder

variable [Preorder D]

/-- *x is the μ-est of C* presupposes that `x` is in the comparison class and asserts that it
measures above every other member of the class ([von-fintel-1999]'s (79)). -/
def superlative (μ : α → D) (C : W → Set α) (x : α) : PartialProp W where
  presup w := x ∈ C w
  assertion w := ∀ y ∈ C w, y ≠ x → μ y < μ x

variable {μ : α → D} {C : W → Set α} {x : α} {w : W}

@[simp] theorem superlative_presup : (superlative μ C x).presup w ↔ x ∈ C w := Iff.rfl

/-- The assertion is the set-standard comparative of `x` against the degrees of the other
members of the class. -/
theorem superlative_assertion :
    (superlative μ C x).assertion w ↔ x ∈ μ ⁻¹' strictUpperBounds (μ '' (C w \ {x})) := by
  simp only [superlative, mem_gtOverSet_iff_subset_Iio, subset_def, mem_Iio, forall_mem_image,
    mem_sdiff, mem_singleton_iff, and_imp]

/-- The assertion is anti-additive in the comparison class, by the anti-additivity of the
set-standard comparative ([hoeksema-1983]). -/
theorem isAntiAdditive_superlative_assertion (μ : α → D) (x : α) :
    NaturalLogic.IsAntiAdditive fun C : W → Set α ↦ (superlative μ C x).assertion :=
  fun C C' ↦ funext fun w ↦ propext <| by
    simp only [Pi.inf_apply, inf_Prop_eq, superlative_assertion, Pi.sup_apply, sup_eq_union,
      union_sdiff_distrib, image_union]
    have h := gtOverSet_isAntiAdditive μ (μ '' (C w \ {x})) (μ '' (C' w \ {x}))
    beta_reduce at h
    rw [show μ '' (C w \ {x}) ∪ μ '' (C' w \ {x}) = _ ⊔ _ from rfl, h]
    exact Iff.rfl

end Preorder

/-- At a world the superlative holds exactly when `x` is the absolute superlative of the class
there ([heim-1999]). -/
theorem holds_superlative_iff [LinearOrder D] {μ : α → D} {C : W → Set α} {x : α} {w : W} :
    (superlative μ C x).holds w ↔ absoluteSuperlative μ (C w) x :=
  Iff.rfl

end Degree
