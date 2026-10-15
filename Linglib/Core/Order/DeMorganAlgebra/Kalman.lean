/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.DeMorganAlgebra.Basic
public import Mathlib.Order.Hom.BoundedLattice
public import Mathlib.Order.LatticeIntervals

/-!
# Kalman's construction

Over a distributive lattice `L` with a least element, the pairs `(a, b)` whose coordinates are
disjoint, `a ⊓ b = ⊥`, form a Kleene lattice `Kalman L` under the operations
`(a, b) ⊓ (c, d) = (a ⊓ c, b ⊔ d)` and the swap `(a, b)ᶜ = (b, a)`, ordered as `L × Lᵒᵈ`
([kalman-1958] §3, where the pairs are written `P(O)`). The Kleene law needs only the least
element, and `Kalman L` is bounded when `L` is. Reading `a` as evidence for and `b` as evidence
against a proposition, these are the pairs of the product bilattice `L ⊙ L` whose evidence never
overlaps; `Bilattice.Product` defines `L ⊙ L` as `L × Lᵒᵈ`, so the carrier here is definitionally
its subtype of disjoint pairs.

A bounded lattice homomorphism `f` induces a homomorphism `(a, b) ↦ (f a, f b)` commuting with
the involution (`Kalman.map`), the construction on morphisms of the functor from bounded
distributive lattices to Kleene algebras of [cignoli-1986], as presented by
[jansana-san-martin-2017].

## Main definitions

* `Kalman L`: the disjoint pairs of `L × Lᵒᵈ`, with its `InvolutiveCompl` and `IsKleene`
  instances.
* `Kalman.map`: the construction on bounded lattice homomorphisms.

## TODO

* Kalman's general `P(a)`: for any element `a` of a distributive lattice, the pairs with
  `x ⊓ y ≤ a ≤ x ⊔ y` form a normal i-lattice with center `(a, a)`; this file is the case `a = ⊥`.
* Kalman's Theorem 6: the normal extensions of `L` are the i-sublattices of `Kalman L` containing
  the pairs `(⊥, y)` and `(x, ⊥)`.

## References

* [cignoli-1986]
* [jansana-san-martin-2017]
* [kalman-1958]
-/

@[expose] public section

open Function OrderDual

/-- **Kalman's construction** ([kalman-1958] §3): the pairs of `L × Lᵒᵈ` whose coordinates are
disjoint. -/
def Kalman (L : Type*) [PartialOrder L] [OrderBot L] : Type _ :=
  {x : L × Lᵒᵈ // Disjoint x.1 (ofDual x.2)}

namespace Kalman

section PartialOrder

variable {L : Type*} [PartialOrder L] [OrderBot L]

/-- The coercion `Kalman L → L × Lᵒᵈ`. -/
@[coe] def val : Kalman L → L × Lᵒᵈ := Subtype.val

instance : CoeOut (Kalman L) (L × Lᵒᵈ) := ⟨val⟩

theorem coe_injective : Injective ((↑) : Kalman L → L × Lᵒᵈ) := Subtype.coe_injective

@[simp, norm_cast] theorem coe_inj {x y : Kalman L} : (x : L × Lᵒᵈ) = y ↔ x = y :=
  Subtype.coe_inj

/-- The Kalman pair `(a, b)`. -/
def mk (a b : L) (h : Disjoint a b) : Kalman L := ⟨(a, toDual b), h⟩

/-- The first coordinate, the evidence for. -/
def pro (x : Kalman L) : L := (x : L × Lᵒᵈ).1

/-- The second coordinate, the evidence against. -/
def con (x : Kalman L) : L := ofDual (x : L × Lᵒᵈ).2

theorem disjoint_pro_con (x : Kalman L) : Disjoint x.pro x.con := x.2

@[simp] theorem pro_mk (a b : L) (h : Disjoint a b) : (mk a b h).pro = a := rfl
@[simp] theorem con_mk (a b : L) (h : Disjoint a b) : (mk a b h).con = b := rfl

@[ext] theorem ext {x y : Kalman L} (h₁ : x.pro = y.pro) (h₂ : x.con = y.con) : x = y :=
  coe_injective (Prod.ext h₁ (congrArg toDual h₂))

/-! ### The order and the involution -/

instance : PartialOrder (Kalman L) := PartialOrder.lift _ coe_injective

@[simp, norm_cast] theorem coe_le_coe {x y : Kalman L} : (x : L × Lᵒᵈ) ≤ y ↔ x ≤ y := Iff.rfl

@[simp, norm_cast] theorem coe_lt_coe {x y : Kalman L} : (x : L × Lᵒᵈ) < y ↔ x < y := Iff.rfl

/-- The order on the coordinates: more for, less against. -/
theorem le_def {x y : Kalman L} : x ≤ y ↔ x.pro ≤ y.pro ∧ y.con ≤ x.con := Iff.rfl

@[simp] theorem mk_le_mk {a₁ b₁ a₂ b₂ : L} {h₁ : Disjoint a₁ b₁} {h₂ : Disjoint a₂ b₂} :
    mk a₁ b₁ h₁ ≤ mk a₂ b₂ h₂ ↔ a₁ ≤ a₂ ∧ b₂ ≤ b₁ := Iff.rfl

/-- The involution swaps the coordinates. -/
instance : InvolutiveCompl (Kalman L) where
  compl x := mk x.con x.pro x.disjoint_pro_con.symm
  compl_compl _ := rfl
  compl_le_compl h := ⟨h.2, h.1⟩

@[simp] theorem pro_compl (x : Kalman L) : xᶜ.pro = x.con := rfl
@[simp] theorem con_compl (x : Kalman L) : xᶜ.con = x.pro := rfl
@[simp] theorem mk_compl (a b : L) (h : Disjoint a b) : (mk a b h)ᶜ = mk b a h.symm := rfl

end PartialOrder

/-! ### The Kleene lattice -/

section DistribLattice

variable {L : Type*} [DistribLattice L] [OrderBot L]

instance : Max (Kalman L) :=
  ⟨fun x y ↦ ⟨(x : L × Lᵒᵈ) ⊔ (y : L × Lᵒᵈ),
    (x.disjoint_pro_con.inf_right _).sup_left (y.disjoint_pro_con.inf_right' _)⟩⟩

instance : Min (Kalman L) :=
  ⟨fun x y ↦ ⟨(x : L × Lᵒᵈ) ⊓ (y : L × Lᵒᵈ),
    (x.disjoint_pro_con.inf_left _).sup_right (y.disjoint_pro_con.inf_left' _)⟩⟩

@[simp, norm_cast] theorem coe_sup (x y : Kalman L) :
    ((x ⊔ y : Kalman L) : L × Lᵒᵈ) = (x : L × Lᵒᵈ) ⊔ (y : L × Lᵒᵈ) := rfl
@[simp, norm_cast] theorem coe_inf (x y : Kalman L) :
    ((x ⊓ y : Kalman L) : L × Lᵒᵈ) = (x : L × Lᵒᵈ) ⊓ (y : L × Lᵒᵈ) := rfl

@[simp] theorem pro_sup (x y : Kalman L) : (x ⊔ y).pro = x.pro ⊔ y.pro := rfl
@[simp] theorem con_sup (x y : Kalman L) : (x ⊔ y).con = x.con ⊓ y.con := rfl
@[simp] theorem pro_inf (x y : Kalman L) : (x ⊓ y).pro = x.pro ⊓ y.pro := rfl
@[simp] theorem con_inf (x y : Kalman L) : (x ⊓ y).con = x.con ⊔ y.con := rfl

instance : DistribLattice (Kalman L) :=
  coe_injective.distribLattice _ Iff.rfl Iff.rfl coe_sup coe_inf

/-- The disjoint pairs satisfy the Kleene law ([kalman-1958] §3: the pairs `P(O)` form a normal
i-lattice). A contradiction `x ⊓ xᶜ` has first coordinate `⊥` and an excluded middle `y ⊔ yᶜ`
second coordinate `⊥`, so the first lies below the second. -/
instance : IsKleene (Kalman L) :=
  ⟨fun x y ↦ ⟨x.disjoint_pro_con.le_bot.trans bot_le,
    y.disjoint_pro_con.symm.le_bot.trans bot_le⟩⟩

end DistribLattice

section Bounded

variable {L : Type*} [DistribLattice L] [BoundedOrder L]

instance : Top (Kalman L) := ⟨mk ⊤ ⊥ disjoint_bot_right⟩
instance : Bot (Kalman L) := ⟨mk ⊥ ⊤ disjoint_bot_left⟩

@[simp] theorem pro_top : (⊤ : Kalman L).pro = ⊤ := rfl
@[simp] theorem con_top : (⊤ : Kalman L).con = ⊥ := rfl
@[simp] theorem pro_bot : (⊥ : Kalman L).pro = ⊥ := rfl
@[simp] theorem con_bot : (⊥ : Kalman L).con = ⊤ := rfl

@[simp, norm_cast] theorem coe_top : ((⊤ : Kalman L) : L × Lᵒᵈ) = ⊤ := rfl
@[simp, norm_cast] theorem coe_bot : ((⊥ : Kalman L) : L × Lᵒᵈ) = ⊥ := rfl

instance : BoundedOrder (Kalman L) :=
  BoundedOrder.lift ((↑) : Kalman L → L × Lᵒᵈ) (fun _ _ ↦ id) coe_top coe_bot

/-! ### Functoriality -/

variable {M : Type*} [DistribLattice M] [BoundedOrder M]

/-- **Kalman's construction on morphisms** ([cignoli-1986], as presented by
[jansana-san-martin-2017]): a bounded lattice homomorphism applied to both coordinates. -/
def map (f : BoundedLatticeHom L M) : BoundedLatticeHom (Kalman L) (Kalman M) where
  toFun x := mk (f x.pro) (f x.con) (x.disjoint_pro_con.map f)
  map_sup' x y := ext (map_sup f x.pro y.pro) (map_inf f x.con y.con)
  map_inf' x y := ext (map_inf f x.pro y.pro) (map_sup f x.con y.con)
  map_top' := ext (map_top f) (map_bot f)
  map_bot' := ext (map_bot f) (map_top f)

variable (f : BoundedLatticeHom L M) (x : Kalman L)

@[simp] theorem pro_map : (map f x).pro = f x.pro := rfl
@[simp] theorem con_map : (map f x).con = f x.con := rfl

/-- `map f` commutes with the involution. -/
@[simp] theorem map_compl : map f xᶜ = (map f x)ᶜ := rfl

end Bounded

end Kalman
