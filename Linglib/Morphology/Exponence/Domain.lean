module

public import Linglib.Morphology.Exponence.Elsewhere
public import Mathlib.Data.Finset.Disjoint
public import Mathlib.Data.Fintype.Defs

/-!
# Domain rules

This file defines domain rules, rules of exponence that apply exactly at the contexts of a
finite domain, ordered by domain inclusion so that the rule with the narrower domain is the more
specific. O'Donnell's finitely supported rules, whose domain is the finite set of forms a rule
generates, and Stump's rules of paradigm linkage, whose domain is a set of content cells, are
domain rules.

## Main definitions

* `Exponence.DomainRule`: a finite domain with an exponent, with its `Exponence.Rule` instance
  and the specificity preorder of domain inclusion.

## Main results

* `DomainRule.le_iff`, `DomainRule.lt_iff`: specificity is domain inclusion.
* `DomainRule.factorsThrough_applies_iff`: a rule's applicability factors through a map exactly
  when its domain is a union of the map's fibers.
* `DomainRule.comparable_of_nested`: rules whose overlapping domains are nested have comparable
  Elsewhere winners.

## References

* [odonnell-2015]
* [stump-2006]
-/

@[expose] public section

namespace Morphology.Exponence

/-- A domain rule carries an exponent and applies exactly at the contexts of a finite
domain. -/
structure DomainRule (Ctx E : Type*) where
  /-- The domain is the finite set of contexts the rule applies at. -/
  dom : Finset Ctx
  /-- The exponent is what the rule assigns. -/
  exponent : E
  deriving DecidableEq

namespace DomainRule

variable {Ctx E : Type*} {r s : DomainRule Ctx E} {c : Ctx}

instance : Rule (DomainRule Ctx E) Ctx E := ⟨DomainRule.exponent, fun r c ↦ c ∈ r.dom⟩

/-- Domain rules are ordered by the specificity preorder, so that a rule whose domain is
included in another's is the more specific. -/
instance : Preorder (DomainRule Ctx E) := toPreorder

@[simp] theorem applies_iff : Applies r c ↔ c ∈ r.dom := Iff.rfl

@[simp] theorem rule_exponent : Rule.exponent r = r.exponent := rfl

theorem le_iff : r ≤ s ↔ r.dom ⊆ s.dom := Finset.coe_subset

theorem lt_iff : r < s ↔ r.dom ⊂ s.dom := Finset.coe_ssubset

/-- A domain rule's applicability factors through `A` exactly when its domain is a union of
fibers of `A`. -/
theorem factorsThrough_applies_iff {V : Type*} {A : Ctx → V} :
    (Applies r).FactorsThrough A ↔ ∀ c c', A c = A c' → (c ∈ r.dom ↔ c' ∈ r.dom) :=
  ⟨fun h _ _ hA ↦ Iff.of_eq (h hA), fun h _ _ hA ↦ propext (h _ _ hA)⟩

/-- Rules whose overlapping domains are nested have comparable Elsewhere winners. -/
theorem comparable_of_nested {v : List (DomainRule Ctx E)}
    (h : ∀ r ∈ v, ∀ s ∈ v, ¬ Disjoint r.dom s.dom → r ≤ s ∨ s ≤ r) ⦃r s : DomainRule Ctx E⦄
    (hr : IsElsewhereWinner v c r) (hs : IsElsewhereWinner v c s) : s ≤ r ∨ r ≤ s :=
  h s hs.prop.1 r hr.prop.1 (Finset.not_disjoint_iff.mpr ⟨c, hs.prop.2, hr.prop.2⟩)

variable [DecidableEq Ctx]

instance : DecidableRel (Applies : DomainRule Ctx E → Ctx → Prop) :=
  fun r c ↦ inferInstanceAs (Decidable (c ∈ r.dom))

instance : DecidableRel (· < · : DomainRule Ctx E → DomainRule Ctx E → Prop) :=
  fun r s ↦ inferInstanceAs (Decidable (r.dom ⊂ s.dom))

instance [Fintype Ctx] {V : Type*} [DecidableEq V] (r : DomainRule Ctx E) (A : Ctx → V) :
    Decidable ((Applies r).FactorsThrough A) :=
  decidable_of_iff _ factorsThrough_applies_iff.symm

end DomainRule

end Morphology.Exponence
