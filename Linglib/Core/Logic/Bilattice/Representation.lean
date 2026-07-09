import Mathlib.Order.Hom.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.Disjoint

/-!
# Representation of distributive bilattices
[avron-1996]

Constructive direction (`Core.Logic.Bilattice.Product`): the Ginsberg–Fitting
product `L ⊙ R` is an interlaced bilattice. This file proves the **converse /
representation theorem** for the *distributive* case ([avron-1996] Thm 4.3
generalizes its knowledge-order conclusion to all interlaced bilattices — see
`Core.Logic.Bilattice.Interlaced`).

Presented *knowledge-first*: a distributive bilattice is a bounded distributive
lattice `B` — the **knowledge** lattice `(≤_k, ⊗ = ⊓, ⊕ = ⊔, ⊥, ⊤)` — together
with the two **truth bounds** `t, f`, which are *complementary* (`IsCompl t f`:
`t ⊗ f = ⊥`, `t ⊕ f = ⊤`). The truth order is recovered from the decomposition.

The representation: `B` decomposes as the product `(Iic t) ⊙ (Iic f)` of
the two principal ideals, via `x ↦ (x ⊗ t, x ⊗ f)` with inverse `(a, b) ↦ a ⊕ b`
([avron-1996] Cor 3.8(1), Thm 4.3). The factors `Iic t = {x | ⊥ ≤_t x}` and
`Iic f = {x | x ≤_t ⊥}` are [avron-1996]'s `L_B`, `R_B`.

## Main results

* `Bilattice.decomposeOfIsCompl` — the knowledge-order isomorphism
  `B ≃o Iic t × Iic f` (the general interlaced version is `Bilattice.decompose`)
* `Bilattice.tLE` / `tLE_iff_decomposeOfIsCompl` — the recovered truth order is
  the twisted order on the factors (first factor up, second factor down): the
  bilattice representation (cf. `Bilattice.Product.mk_le_mk`)
-/

variable {B : Type*}

namespace Bilattice

section Decompose

variable [DistribLattice B] [BoundedOrder B] {t f : B}

/-- The knowledge-order decomposition of a distributive bilattice: `x ↦ (x ⊓ t,
x ⊓ f)` is an order isomorphism `B ≃o Iic t × Iic f` ([avron-1996] Thm 4.3,
distributive case), with inverse `(a, b) ↦ a ⊔ b`. -/
def decomposeOfIsCompl (h : IsCompl t f) : B ≃o (Set.Iic t × Set.Iic f) where
  toFun x := (⟨x ⊓ t, inf_le_right⟩, ⟨x ⊓ f, inf_le_right⟩)
  invFun p := p.1.1 ⊔ p.2.1
  left_inv x := by
    show x ⊓ t ⊔ x ⊓ f = x
    rw [← inf_sup_left, h.sup_eq_top, inf_top_eq]
  right_inv p := by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := p
    have hat : a ⊓ t = a := inf_eq_left.mpr ha
    have hbf : b ⊓ f = b := inf_eq_left.mpr hb
    have hbt : b ⊓ t = ⊥ := le_bot_iff.mp <|
      le_trans (inf_le_inf_right t hb) (by rw [inf_comm]; exact h.inf_eq_bot.le)
    have haf : a ⊓ f = ⊥ := le_bot_iff.mp <|
      le_trans (inf_le_inf_right f ha) h.inf_eq_bot.le
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show (a ⊔ b) ⊓ t = a
      rw [inf_sup_right, hat, hbt, sup_bot_eq]
    · show (a ⊔ b) ⊓ f = b
      rw [inf_sup_right, haf, hbf, bot_sup_eq]
  map_rel_iff' {x y} := by
    constructor
    · rintro ⟨h1, h2⟩
      calc x = x ⊓ t ⊔ x ⊓ f := by rw [← inf_sup_left, h.sup_eq_top, inf_top_eq]
        _ ≤ y ⊓ t ⊔ y ⊓ f := sup_le_sup h1 h2
        _ = y := by rw [← inf_sup_left, h.sup_eq_top, inf_top_eq]
    · intro hxy
      exact ⟨inf_le_inf_right t hxy, inf_le_inf_right f hxy⟩

theorem decomposeOfIsCompl_apply (h : IsCompl t f) (x : B) :
    decomposeOfIsCompl h x = (⟨x ⊓ t, inf_le_right⟩, ⟨x ⊓ f, inf_le_right⟩) := rfl

theorem decomposeOfIsCompl_symm_apply (h : IsCompl t f) (p : Set.Iic t × Set.Iic f) :
    (decomposeOfIsCompl h).symm p = p.1.1 ⊔ p.2.1 := rfl

end Decompose

section Truth

variable [DistribLattice B] [BoundedOrder B] (t f : B)

/-- The recovered **truth order** on a distributive bilattice: `x ≤_t y` iff `x`
has less evidence-for-truth (`⊓ t`) and more evidence-for-falsity (`⊓ f`)
([avron-1996] Def 2.4(ii)). -/
def tLE (x y : B) : Prop := x ⊓ t ≤ y ⊓ t ∧ y ⊓ f ≤ x ⊓ f

/-- The recovered truth order *is* the twisted order on the decomposition
factors (`Iic t` up, `Iic f` down): this exhibits `B` as the product
`(Iic t) ⊙ (Iic f)`, i.e. the bilattice representation. -/
theorem tLE_iff_decomposeOfIsCompl {t f : B} (h : IsCompl t f) (x y : B) :
    tLE t f x y ↔
      (decomposeOfIsCompl h x).1 ≤ (decomposeOfIsCompl h y).1 ∧
        (decomposeOfIsCompl h y).2 ≤ (decomposeOfIsCompl h x).2 :=
  Iff.rfl

end Truth

end Bilattice
