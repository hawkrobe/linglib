import Linglib.Core.Order.Probability.Defs
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Data.Set.Image
import Mathlib.Logic.Equiv.Set

/-!
# Qualitative probability orders: basic API

Consequences of the axioms on any Boolean algebra (disjoint common context
cancels; disjoint comparisons merge), and the transport operations on
set-carriers: pullback along an injection (`comap`) and along an equivalence
(`transport`).

## Main statements

* `QualitativeProbability.sup_le_sup_iff_right`, `sup_le_sup_right`,
  `sup_le_sup`.
* `QualitativeProbability.comap`, `transport`, `elim0`.
-/

namespace ComparativeProbability

namespace QualitativeProbability

variable {α : Type*} [BooleanAlgebra α] (sys : QualitativeProbability α)

/-! #### Consequences of the axioms -/

/-- Disjoint common context cancels: `a ⊔ c ≼ b ⊔ c ↔ a ≼ b` for `c` disjoint
    from both. -/
theorem sup_le_sup_iff_right {a b c : α} (hca : Disjoint c a) (hcb : Disjoint c b) :
    sys.le (a ⊔ c) (b ⊔ c) ↔ sys.le a b := by
  rw [sys.additive a b, sys.additive (a ⊔ c) (b ⊔ c), sup_comm b c, ← sdiff_sdiff_left,
    sup_sdiff_right_self, sdiff_eq_left.mpr hca.symm, sup_comm a c, ← sdiff_sdiff_left,
    sup_sdiff_left_self, sdiff_eq_left.mpr hcb.symm]

theorem sup_le_sup_right {a b c : α} (h : sys.le a b) (hca : Disjoint c a)
    (hcb : Disjoint c b) : sys.le (a ⊔ c) (b ⊔ c) :=
  (sys.sup_le_sup_iff_right hca hcb).mpr h

/-- Two comparisons with disjoint left parts and disjoint right parts merge
    into their joins, even with cross overlaps: add context to each side,
    transit through `b₁ ⊔ a₂`, then restore the pivot `a₂ ⊓ b₁` by additivity. -/
theorem sup_le_sup {a₁ b₁ a₂ b₂ : α} (h₁ : sys.le a₁ b₁) (h₂ : sys.le a₂ b₂)
    (ha : Disjoint a₁ a₂) (hb : Disjoint b₁ b₂) : sys.le (a₁ ⊔ a₂) (b₁ ⊔ b₂) := by
  have e₁ : (a₂ ⊔ a₁ \ b₂) ⊔ a₁ ⊓ b₂ = a₁ ⊔ a₂ := by
    rw [sup_assoc, sup_comm (a₁ \ b₂), sup_inf_sdiff, sup_comm]
  have e₂ : (b₁ ⊔ b₂ \ a₁) ⊔ a₁ ⊓ b₂ = b₁ ⊔ b₂ := by
    rw [sup_assoc, inf_comm a₁, sup_comm (b₂ \ a₁), sup_inf_sdiff]
  rw [← e₁, ← e₂]
  refine sys.sup_le_sup_right (sys.trans (b := b₂ ⊔ a₁) ?_ ?_)
    ((ha.mono_left inf_le_left).sup_right (disjoint_sdiff_self_right.mono_left inf_le_right))
    ((hb.symm.mono_left inf_le_right).sup_right (disjoint_sdiff_self_right.mono_left inf_le_left))
  · have h := sys.sup_le_sup_right h₂ (ha.mono_left sdiff_le) disjoint_sdiff_self_left
    rwa [sup_sdiff_self_right] at h
  · have h := sys.sup_le_sup_right h₁ disjoint_sdiff_self_left (hb.symm.mono_left sdiff_le)
    rwa [sup_sdiff_self_right, sup_comm a₁ b₂] at h


end QualitativeProbability

/-! ### Transport on set carriers -/

/-- Pull back a qualitative probability order along an injection: `α`-sets
    compare via their images. Non-triviality requires a witness and must be
    supplied. -/
def QualitativeProbability.comap {α W : Type*} (f : α → W) (hf : Function.Injective f)
    (sys : QualitativeProbability (Set W)) (hnt : ¬sys.le (Set.range f) ∅) :
    QualitativeProbability (Set α) where
  le A B := sys.le (f '' A) (f '' B)
  mono' _ _ hAB := sys.mono (Set.image_mono hAB)
  nonTrivial := by
    show ¬sys.le (f '' Set.univ) (f '' ∅)
    rwa [Set.image_empty, Set.image_univ]
  total _ _ := sys.total _ _
  trans' _ _ _ h1 h2 := sys.trans h1 h2
  additive A B := by
    show sys.le (f '' A) (f '' B) ↔ sys.le (f '' (A \ B)) (f '' (B \ A))
    rw [Set.image_sdiff hf, Set.image_sdiff hf]; exact sys.additive _ _

/-- Transport a qualitative probability order along an equivalence of carriers. -/
def QualitativeProbability.transport {W α : Type*} (e : W ≃ α)
    (sys : QualitativeProbability (Set W)) : QualitativeProbability (Set α) :=
  sys.comap e.symm e.symm.injective
    (by rw [Equiv.range_eq_univ, ← Set.top_eq_univ, ← Set.bot_eq_empty]; exact sys.nonTrivial)

/-- There is no qualitative probability order on an empty carrier: `∅ = Ω`
    contradicts non-triviality. Mirrors `Fin.elim0`. -/
def QualitativeProbability.elim0 {C : Sort*} (sys : QualitativeProbability (Set (Fin 0))) :
    C := by
  have : (∅ : Set (Fin 0)) = Set.univ := by ext x; exact Fin.elim0 x
  have h : sys.le ⊤ ⊥ := by
    rw [Set.top_eq_univ, Set.bot_eq_empty, ← this]; exact sys.refl ∅
  exact absurd h sys.nonTrivial


end ComparativeProbability
