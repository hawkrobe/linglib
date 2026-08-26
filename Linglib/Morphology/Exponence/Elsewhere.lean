import Linglib.Morphology.Exponence.Basic
import Mathlib.Order.Antisymmetrization
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Set.Finite.Basic

/-!
# The Elsewhere Condition

This file defines Elsewhere winners — `≤`-minimal applicable rules of
exponence under the specificity preorder ([kiparsky-1973]) — and the
prediction relation they induce.

## Main definitions

* `IsElsewhereWinner`: a `≤`-minimal applicable rule of a vocabulary at a
  context.
* `Coherent`: equivalent rules carry the same exponent.
* `Realizes`: some Elsewhere winner carries the given exponent.
* `Realizes.of_realizes`: no ABA pattern across nested contexts.
-/

namespace Morphology.Exponence

variable {Ctx E : Type*} {R : Type*} [Rule R Ctx E] [Preorder R]
variable {v : List R} {c : Ctx} {r s : R} {φ : E}

/-! ### Elsewhere winners -/

/-- Two comparable minimal elements of the same predicate are equivalent.
[UPSTREAM] candidate for `Mathlib/Order/Minimal.lean`. -/
theorem _root_.Minimal.antisymmRel {α : Type*} [Preorder α] {P : α → Prop} {x y : α}
    (hx : Minimal P x) (hy : Minimal P y) (h : y ≤ x ∨ x ≤ y) :
    AntisymmRel (· ≤ ·) x y :=
  h.elim (fun h => ⟨hx.le_of_le hy.1 h, h⟩) (fun h => ⟨h, hy.le_of_le hx.1 h⟩)

/-- A `≤`-minimal applicable rule of `v` at `c`. -/
abbrev IsElsewhereWinner (v : List R) (c : Ctx) (r : R) : Prop :=
  Minimal (fun s => s ∈ v ∧ Applies s c) r

/-- A vocabulary is coherent if equivalent rules carry the same exponent. -/
def Coherent (v : List R) : Prop :=
  ∀ r ∈ v, ∀ s ∈ v, AntisymmRel (· ≤ ·) r s →
    exponent r = exponent s

/-- Comparable winners of a coherent vocabulary carry the same exponent. -/
theorem IsElsewhereWinner.exponent_eq
    (hv : Coherent v) (hr : IsElsewhereWinner v c r)
    (hs : IsElsewhereWinner v c s) (h : s ≤ r ∨ r ≤ s) :
    exponent r = exponent s :=
  hv r hr.1.1 s hs.1.1 (hr.antisymmRel hs h)

/-- A vocabulary with an applicable rule has an Elsewhere winner. -/
theorem exists_isElsewhereWinner
    (h : ∃ r ∈ v, Applies r c) : ∃ r, IsElsewhereWinner v c r :=
  (v.finite_toSet.subset fun _ hr => hr.1).exists_minimal h

/-! ### The prediction relation -/

/-- `φ` is realized at `c` when some Elsewhere winner carries it. -/
def Realizes (v : List R) (c : Ctx) (φ : E) : Prop :=
  ∃ r, IsElsewhereWinner v c r ∧ exponent r = φ

/-- Over a coherent vocabulary with comparable winners, the prediction is unique. -/
theorem Realizes.eq {ψ : E} (hv : Coherent v)
    (hcmp : ∀ ⦃r s⦄, IsElsewhereWinner v c r → IsElsewhereWinner v c s → s ≤ r ∨ r ≤ s)
    (hφ : Realizes v c φ) (hψ : Realizes v c ψ) : φ = ψ := by
  obtain ⟨r, hr, rfl⟩ := hφ
  obtain ⟨s, hs, rfl⟩ := hψ
  exact hr.exponent_eq hv hs (hcmp hr hs)

/-! ### Containment -/

/-- A winner at a context that applies at a smaller context, in the sense that everything
applicable there is applicable at the larger, is a winner at the smaller. -/
theorem IsElsewhereWinner.of_applies {c' : Ctx} (h : ∀ s : R, Applies s c' → Applies s c)
    (hr : IsElsewhereWinner v c r) (hc' : Applies r c') : IsElsewhereWinner v c' r :=
  hr.mono (fun s hs => ⟨hs.1, h s hs.2⟩) ⟨hr.1.1, hc'⟩

/-- No ABA across nested contexts: with one item per exponent, an exponent realized at the
smallest and the largest of three nested contexts is realized at the middle one. -/
theorem Realizes.of_realizes {c₁ c₂ : Ctx} (hinj : (v.map exponent).Nodup)
    (h₁ : ∀ s : R, Applies s c₁ → Applies s c₂) (h₂ : ∀ s : R, Applies s c₂ → Applies s c)
    (hr₁ : Realizes v c₁ φ) (hr : Realizes v c φ) : Realizes v c₂ φ := by
  obtain ⟨t, ht, rfl⟩ := hr
  obtain ⟨u, hu, hut⟩ := hr₁
  have e := List.inj_on_of_nodup_map hinj hu.1.1 ht.1.1 hut
  subst e
  exact ⟨_, ht.of_applies h₂ (h₁ _ hu.1.2), rfl⟩

end Morphology.Exponence
