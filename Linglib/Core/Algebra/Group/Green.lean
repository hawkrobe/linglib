/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.Divisibility.Basic

/-!
# Green's relations

Green's equivalences on a monoid, defined through the divisibility (principal-ideal)
preorders:

* `Green.RRel` (`𝓡`) — mutual divisibility, i.e. equal principal right ideals `aM = bM`;
* `Green.LRel` (`𝓛`) — mutual left-divisibility, i.e. equal principal left ideals `Ma = Mb`;
* `Green.JRel` (`𝓙`) — equal principal two-sided ideals `MaM = MbM`;
* `Green.HRel` (`𝓗 = 𝓡 ⊓ 𝓛`).

`𝓡` is *mutual divisibility* — mathlib's `Dvd` — so its equivalence and the
left-congruence property come straight from the divisibility API; `𝓛` is the
left-handed dual.

These relations underlie the structure theory of finite semigroups — the minimal
ideal (kernel), completely simple semigroups, and the algebraic characterisation of
the subregular language hierarchy. [howie-1995] §2.1, [pin-mfa] Ch. V §1.

`[UPSTREAM]`: mathlib provides `Dvd`/`Associated` but no Green's relations.

## Implementation notes

Stated for a `Monoid` (so principal ideals are `aM` rather than `aM¹`), which is the
setting of the syntactic monoid. `𝓓 = 𝓡 ∘ 𝓛 = 𝓛 ∘ 𝓡` and `𝓓 = 𝓙` for finite
(periodic) monoids are the next increment.
-/

namespace Green

variable {M : Type*} [Monoid M] {a b c : M}

/-- Green's `𝓡`: `a` and `b` divide each other — equal principal right ideals `aM = bM`. -/
def RRel (a b : M) : Prop := a ∣ b ∧ b ∣ a

/-- Green's `𝓛`: `a` and `b` are mutually left-divisible — equal principal left ideals. -/
def LRel (a b : M) : Prop := (∃ c, b = c * a) ∧ (∃ c, a = c * b)

/-- Green's `𝓙`: equal principal two-sided ideals `MaM = MbM`. -/
def JRel (a b : M) : Prop := (∃ x y, b = x * a * y) ∧ (∃ x y, a = x * b * y)

/-- Green's `𝓗`, the intersection `𝓡 ⊓ 𝓛`. -/
def HRel (a b : M) : Prop := RRel a b ∧ LRel a b

/-- `𝓡` is mutual divisibility. -/
theorem rRel_iff_dvd : RRel a b ↔ a ∣ b ∧ b ∣ a := Iff.rfl

theorem hRel_iff : HRel a b ↔ RRel a b ∧ LRel a b := Iff.rfl

/-! ### Equivalences -/

theorem rRel_equivalence : Equivalence (RRel : M → M → Prop) where
  refl a := ⟨dvd_refl a, dvd_refl a⟩
  symm h := ⟨h.2, h.1⟩
  trans h₁ h₂ := ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

theorem lRel_equivalence : Equivalence (LRel : M → M → Prop) where
  refl a := ⟨⟨1, (one_mul a).symm⟩, ⟨1, (one_mul a).symm⟩⟩
  symm h := ⟨h.2, h.1⟩
  trans := by
    rintro a b d ⟨⟨p, hp⟩, q, hq⟩ ⟨⟨r, hr⟩, s, hs⟩
    exact ⟨⟨r * p, by rw [hr, hp, mul_assoc]⟩, ⟨q * s, by rw [hq, hs, mul_assoc]⟩⟩

theorem jRel_equivalence : Equivalence (JRel : M → M → Prop) where
  refl a := ⟨⟨1, 1, by simp⟩, ⟨1, 1, by simp⟩⟩
  symm h := ⟨h.2, h.1⟩
  trans := by
    rintro a b d ⟨⟨x, y, hb⟩, x', y', ha⟩ ⟨⟨u, v, hd⟩, u', v', hb'⟩
    refine ⟨⟨u * x, y * v, ?_⟩, ⟨x' * u', v' * y', ?_⟩⟩
    · rw [hd, hb]; simp only [mul_assoc]
    · rw [ha, hb']; simp only [mul_assoc]

theorem hRel_equivalence : Equivalence (HRel : M → M → Prop) where
  refl a := ⟨rRel_equivalence.refl a, lRel_equivalence.refl a⟩
  symm h := ⟨rRel_equivalence.symm h.1, lRel_equivalence.symm h.2⟩
  trans h₁ h₂ := ⟨rRel_equivalence.trans h₁.1 h₂.1, lRel_equivalence.trans h₁.2 h₂.2⟩

/-! ### Congruence and inclusion -/

/-- `𝓡` is a left congruence. -/
theorem RRel.mul_left (h : RRel a b) (c : M) : RRel (c * a) (c * b) :=
  ⟨mul_dvd_mul_left c h.1, mul_dvd_mul_left c h.2⟩

/-- `𝓛` is a right congruence. -/
theorem LRel.mul_right (h : LRel a b) (c : M) : LRel (a * c) (b * c) := by
  obtain ⟨⟨p, hp⟩, q, hq⟩ := h
  exact ⟨⟨p, by rw [hp, mul_assoc]⟩, ⟨q, by rw [hq, mul_assoc]⟩⟩

/-- `𝓡 ⊆ 𝓙`. -/
theorem RRel.jRel (h : RRel a b) : JRel a b := by
  obtain ⟨⟨c, hc⟩, d, hd⟩ := h
  exact ⟨⟨1, c, by rw [hc, one_mul]⟩, ⟨1, d, by rw [hd, one_mul]⟩⟩

/-- `𝓛 ⊆ 𝓙`. -/
theorem LRel.jRel (h : LRel a b) : JRel a b := by
  obtain ⟨⟨c, hc⟩, d, hd⟩ := h
  exact ⟨⟨c, 1, by rw [hc, mul_one]⟩, ⟨d, 1, by rw [hd, mul_one]⟩⟩

/-- `𝓗 ⊆ 𝓡`. -/
theorem HRel.rRel (h : HRel a b) : RRel a b := h.1

/-- `𝓗 ⊆ 𝓛`. -/
theorem HRel.lRel (h : HRel a b) : LRel a b := h.2

end Green
