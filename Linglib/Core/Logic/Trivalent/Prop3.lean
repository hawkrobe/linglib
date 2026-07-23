/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Logic.Trivalent.Basic
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

end Prop3

end Trivalent
