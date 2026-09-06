/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.Trivalent
import Mathlib.Data.Set.Basic

/-!
# Trivalent propositions

`Prop3 W` is a proposition valued in `Trivalent`: at each world it is true,
false, or undefined. Its worlds split into the positive extension, the
negative extension, and the extension gap; `Prop3.metaAssert` — the
Beaver-Krahmer 𝒜 operator lifted pointwise — collapses the gap into the
negative extension. As a `Pi` type, `Prop3 W` inherits its lattice
structure pointwise (`⊓`/`⊔` via `Pi.instLattice`).

## References

[beaver-krahmer-2001] [kriz-2016]
-/

namespace Trivalent

/-- Three-valued propositions: functions from worlds to `Trivalent`. -/
abbrev Prop3 (W : Type*) := W → Trivalent

namespace Prop3

variable {W : Type*}

/-! `Prop3 W := W → Trivalent` is a `Pi` type: `Lattice (W → Trivalent)` auto-derives from
`Pi.instLattice`, so `(p ⊔ q) w = p w ⊔ q w` and `(p ⊓ q) w = p w ⊓ q w` come for
free from `Pi.sup_apply`/`Pi.inf_apply` — use `⊔`/`⊓` directly rather than bespoke
wrappers. The only Trivalent-specific operation needing a pointwise lift is
`metaAssert`: there is no `Pi` analogue of a unary collapsing operator. -/

/-- Pointwise meta-assertion (Beaver-Krahmer 𝒜 operator). -/
def metaAssert (p : Prop3 W) : Prop3 W := λ w => Trivalent.metaAssert (p w)

@[simp] theorem metaAssert_apply (p : Prop3 W) (w : W) :
    Prop3.metaAssert p w = Trivalent.metaAssert (p w) := rfl

/-! ### Extensions -/

/-- Positive extension: worlds where the proposition is true. -/
def posExt (p : Prop3 W) : Set W := {w | p w = .true}

/-- Negative extension: worlds where the proposition is false. -/
def negExt (p : Prop3 W) : Set W := {w | p w = .false}

/-- Extension gap: worlds where the proposition is neither true nor false. -/
def gapExt (p : Prop3 W) : Set W := {w | p w = .indet}

@[simp] theorem mem_posExt {p : Prop3 W} {w : W} :
    w ∈ p.posExt ↔ p w = .true := Iff.rfl

@[simp] theorem mem_negExt {p : Prop3 W} {w : W} :
    w ∈ p.negExt ↔ p w = .false := Iff.rfl

@[simp] theorem mem_gapExt {p : Prop3 W} {w : W} :
    w ∈ p.gapExt ↔ p w = .indet := Iff.rfl

/-- The three extensions cover the world space. -/
theorem posExt_union_negExt_union_gapExt (p : Prop3 W) :
    p.posExt ∪ p.negExt ∪ p.gapExt = Set.univ := by
  ext w
  simp only [Set.mem_union, mem_posExt, mem_negExt, mem_gapExt, Set.mem_univ,
    iff_true]
  cases p w <;> simp

/-- The positive and negative extensions are disjoint. -/
theorem disjoint_posExt_negExt (p : Prop3 W) :
    Disjoint p.posExt p.negExt := by
  rw [Set.disjoint_left]
  intro w hw hw'
  rw [mem_posExt] at hw
  rw [mem_negExt, hw] at hw'
  cases hw'

/-- A proposition is bivalent if it takes no `.indet` value. -/
def isBivalent (p : Prop3 W) : Prop :=
  ∀ w, p w = .true ∨ p w = .false

theorem isBivalent_iff_gapExt_eq_empty (p : Prop3 W) :
    p.isBivalent ↔ p.gapExt = ∅ := by
  simp only [isBivalent, Set.eq_empty_iff_forall_notMem, mem_gapExt]
  exact forall_congr' fun w => by cases p w <;> simp

theorem isBivalent_iff_forall_ne_indet (p : Prop3 W) : p.isBivalent ↔ ∀ w, p w ≠ .indet :=
  forall_congr' λ w => by cases p w <;> simp

theorem isBivalent.ne_indet {p : Prop3 W} (h : p.isBivalent) (w : W) : p w ≠ .indet :=
  (isBivalent_iff_forall_ne_indet p).1 h w

/-! ### Extensions under meta-assertion -/

@[simp] theorem posExt_metaAssert (p : Prop3 W) :
    p.metaAssert.posExt = p.posExt := by
  ext w; simp only [mem_posExt, metaAssert_apply]
  cases p w <;> simp

@[simp] theorem negExt_metaAssert (p : Prop3 W) :
    p.metaAssert.negExt = p.negExt ∪ p.gapExt := by
  ext w
  simp only [mem_negExt, Set.mem_union, mem_gapExt, metaAssert_apply]
  cases p w <;> simp

@[simp] theorem gapExt_metaAssert (p : Prop3 W) :
    p.metaAssert.gapExt = ∅ := by
  ext w
  simp only [mem_gapExt, metaAssert_apply, Set.mem_empty_iff_false, iff_false]
  cases p w <;> simp

/-- Meta-assertion produces a bivalent proposition. -/
theorem isBivalent_metaAssert (p : Prop3 W) : p.metaAssert.isBivalent := by
  intro w; simp only [metaAssert_apply]; cases p w <;> simp

/-! ### Quantifiers

The universal quantifier of [haug-2014], adopted by [coppock-beaver-2015] and
[cooper-2023]: undefined only when every instance is, false when some instance is, and
true otherwise, so that a quantified presupposition projects existentially. The
existential is its dual. -/

open Classical in
/-- Haug's universal quantifier over a trivalent predicate. -/
noncomputable def forall' (p : Prop3 W) : Trivalent :=
  if ∀ w, p w = .indet then .indet else if ∃ w, p w = .false then .false else .true

/-- The existential quantifier, the dual of `forall'`. -/
noncomputable def exists' (p : Prop3 W) : Trivalent := neg (forall' (λ w => neg (p w)))

@[simp] theorem forall'_eq_indet_iff (p : Prop3 W) : forall' p = .indet ↔ ∀ w, p w = .indet := by
  unfold forall'; split_ifs <;> simp_all

@[simp] theorem forall'_eq_false_iff (p : Prop3 W) : forall' p = .false ↔ ∃ w, p w = .false := by
  unfold forall'; split_ifs <;> simp_all

@[simp] theorem forall'_eq_true_iff (p : Prop3 W) :
    forall' p = .true ↔ (∃ w, p w ≠ .indet) ∧ ∀ w, p w ≠ .false := by
  unfold forall'; split_ifs <;> simp_all

@[simp] theorem exists'_eq_indet_iff (p : Prop3 W) : exists' p = .indet ↔ ∀ w, p w = .indet := by
  simp only [exists', neg_eq_indet_iff, forall'_eq_indet_iff]

@[simp] theorem exists'_eq_true_iff (p : Prop3 W) : exists' p = .true ↔ ∃ w, p w = .true := by
  simp only [exists', neg_eq_true_iff, forall'_eq_false_iff, neg_eq_false_iff]

@[simp] theorem exists'_eq_false_iff (p : Prop3 W) :
    exists' p = .false ↔ (∃ w, p w ≠ .indet) ∧ ∀ w, p w ≠ .true := by
  simp only [exists', neg_eq_false_iff, forall'_eq_true_iff, ne_eq, neg_eq_indet_iff]

/-- An existentially quantified presupposition is true or undefined, never false. -/
theorem exists'_presuppose_ne_false (p : Prop3 W) :
    exists' (λ w => presuppose (p w)) ≠ .false := by
  simp

/-- Quantifier Projection ([coppock-beaver-2015]'s appendix): over bivalent `φ` and `ψ`, a
presupposition under the existential projects as an existentially quantified
presupposition. -/
theorem exists'_meetWeak_presuppose {φ ψ : Prop3 W} (hφ : φ.isBivalent) (hψ : ψ.isBivalent) :
    exists' (λ w => meetWeak (presuppose (φ w)) (ψ w)) =
      meetWeak (exists' (λ w => presuppose (φ w))) (exists' (λ w => meetWeak (φ w) (ψ w))) := by
  refine eq_of_indet_iff_of_true_iff ?_ ?_
  · simp only [exists'_eq_indet_iff, meetWeak_eq_indet_iff, presuppose_eq_indet_iff, hφ.ne_indet,
      hψ.ne_indet, or_false]
    exact ⟨Or.inl, λ h => h.elim id λ h w => (h w).elim⟩
  · simp only [exists'_eq_true_iff, meetWeak_eq_true_iff, presuppose_eq_true_iff]
    exact ⟨λ ⟨w, h⟩ => ⟨⟨w, h.1⟩, w, h⟩, λ h => h.2⟩

end Prop3

end Trivalent
