/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.NormalForm

/-!
# The association hull

`AR.hull m` closes each node of melody tier `m` to the interval hull of its links on every
other tier: a melody node links to a position iff that position lies between two of its
links. Applied after OCP fusion, the hull of the fused H's links is the plateau of
[hyman-katamba-2010]'s plateauing rule (`Phonology/Tone/Plateauing`). The hull of a melody
with several nodes can violate the No-Crossing Constraint, since two interleaved hulls cross;
the rule applies to the fused representation, whose melody is a single node.

## Main results

* `AR.link_hull_left`: a melody node links to the positions between two of its links.
* `AR.link_subset_hull`: the hull extends the link relation.
* `AR.link_hull_convex`: each melody node's links form an interval.

## References

* [hyman-katamba-2010]
-/

@[expose] public section

namespace Autosegmental

section CoordinateHull

variable {ι : Type*} [Finite ι] {τ : ι → Type*}
variable (m : ι) (X : TieredAR ι τ) [Finite X.obj.V]

/-- The hull closes each tier-`m` node's association set to its interval hull on each
other tier. -/
noncomputable def AR.hull :
    TieredAR ι τ :=
  AR.ofData (fun i => X.tierWord i)
    (fun i j p q =>
      (i = m ∧ ∃ q₁ q₂, X.link i j p q₁ ∧ X.link i j p q₂ ∧ q₁ ≤ q ∧ q ≤ q₂) ∨
        (i ≠ m ∧ j ≠ m ∧ X.link i j p q))

instance : Finite (X.hull m).obj.V :=
  inferInstanceAs (Finite ((_ : ι) × Fin _))

@[simp] theorem AR.tierWord_hull (i : ι) :
    (X.hull m).tierWord i = X.tierWord i :=
  AR.tierWord_ofData i

@[simp] theorem AR.tierLength_hull (i : ι) : (X.hull m).tierLength i = X.tierLength i := by
  rw [← AR.length_tierWord, AR.tierWord_hull, AR.length_tierWord]

/-- In the hull, melody node `p` links to `q` iff `q` lies between two of `p`'s links. -/
theorem AR.link_hull_left {j : ι} (hj : m ≠ j) {p q : ℕ}
    (hq : q < X.tierLength j) :
    (X.hull m).link m j p q ↔
      ∃ q₁ q₂, X.link m j p q₁ ∧ X.link m j p q₂ ∧ q₁ ≤ q ∧ q ≤ q₂ := by
  unfold AR.hull
  rw [AR.link_ofData]
  constructor
  · rintro ⟨-, -, -, (⟨-, hfl⟩ | ⟨hne, -, -⟩) | (⟨rfl, -⟩ | ⟨-, hne, -⟩)⟩
    · exact hfl
    · exact absurd rfl hne
    · exact absurd rfl hj
    · exact absurd rfl hne
  · rintro ⟨q₁, q₂, h₁, h₂, hle₁, hle₂⟩
    obtain ⟨hp, -, -⟩ := id h₁
    refine ⟨hj, ?_, ?_, Or.inl (Or.inl ⟨rfl, q₁, q₂, h₁, h₂, hle₁, hle₂⟩)⟩
    · simpa using hp
    · simpa [AR.length_tierWord] using hq

/-- Links not involving the melody tier pass through the hull unchanged. -/
theorem AR.link_hull_of_ne {i j : ι} (hi : i ≠ m) (hj : j ≠ m) (p q : ℕ) :
    (X.hull m).link i j p q ↔ X.link i j p q := by
  unfold AR.hull
  rw [AR.link_ofData]
  constructor
  · rintro ⟨-, -, -, (⟨rfl, -⟩ | ⟨-, -, hl⟩) | (⟨rfl, -⟩ | ⟨-, -, hl⟩)⟩
    · exact absurd rfl hi
    · exact hl
    · exact absurd rfl hj
    · exact X.link_symm hl
  · intro hl
    obtain ⟨hp, hq, -⟩ := id hl
    refine ⟨?_, by simpa using hp, by simpa using hq,
      Or.inl (Or.inr ⟨hi, hj, hl⟩)⟩
    rintro rfl
    exact X.not_link_self_tier i p q hl

/-- Melody links flank themselves: the hull extends the link relation. -/
theorem AR.link_subset_hull {i j : ι} {p q : ℕ} (h : X.link i j p q) :
    (X.hull m).link i j p q := by
  obtain ⟨hp, hq, -⟩ := id h
  rcases eq_or_ne m i with rfl | hi
  · rcases eq_or_ne m j with rfl | hj
    · exact absurd h (X.not_link_self_tier m p q)
    · exact (X.link_hull_left m hj hq).mpr ⟨q, q, h, h, le_rfl, le_rfl⟩
  · rcases eq_or_ne m j with rfl | hj
    · exact (X.hull m).link_symm ((X.link_hull_left m hi hp).mpr
        ⟨p, p, X.link_symm h, X.link_symm h, le_rfl, le_rfl⟩)
    · exact (X.link_hull_of_ne m (Ne.symm hi) (Ne.symm hj) p q).mpr h

/-- Each melody node's hull links form an interval. -/
theorem AR.link_hull_convex {j : ι} (hj : m ≠ j) {p q₁ q q₂ : ℕ}
    (hq : q < X.tierLength j)
    (h₁ : (X.hull m).link m j p q₁) (h₂ : (X.hull m).link m j p q₂)
    (hle₁ : q₁ ≤ q) (hle₂ : q ≤ q₂) : (X.hull m).link m j p q := by
  have hlen : (X.hull m).tierLength j = X.tierLength j := by
    rw [← AR.length_tierWord, AR.tierWord_hull,
      AR.length_tierWord]
  obtain ⟨-, hb₁, -⟩ := id h₁
  obtain ⟨-, hb₂, -⟩ := id h₂
  rw [hlen] at hb₁ hb₂
  obtain ⟨a₁, -, ha₁, -, hle₃, -⟩ := (X.link_hull_left m hj hb₁).mp h₁
  obtain ⟨-, a₂, -, ha₂, -, hle₄⟩ := (X.link_hull_left m hj hb₂).mp h₂
  exact (X.link_hull_left m hj hq).mpr ⟨a₁, a₂, ha₁, ha₂, by omega, by omega⟩

end CoordinateHull

end Autosegmental
