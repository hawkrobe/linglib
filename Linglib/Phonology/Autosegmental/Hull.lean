/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.AR
import Linglib.Phonology.Autosegmental.NormalForm

/-!
# The association hull

`Graph.hull` closes each upper node's association set to its interval hull on the lower
tier: `(k, j)` is a hull link iff `j` lies between two of `k`'s links. This is the
representational content of tonal spreading-to-a-span: [hyman-katamba-2010]'s plateauing
rule, applied after OCP-fusion, is exactly the hull of the fused H's associations
(`Phonology/Tone/Plateauing`).

Hull-closure of a multi-node melody can violate the no-crossing constraint (two
interleaved hulls cross); the phonological operation applies to the fused
representation, where the melody is a single node and the hull is planar.

## Main results

* `mem_links_hull` — hull membership as flanking (`Graph` form with explicit bounds;
  side-condition-free `AR.mem_links_hull` for well-formed representations).
* `links_subset_hull` — the hull extends the link set.
* `hull_convex` — per-node convexity: the defining property of the hull.
* `AR.hull` — the operation on well-formed representations.
-/

namespace Autosegmental

variable {α β : Type*}

namespace Graph

/-- Close each upper node's association set to its interval hull on the lower tier. -/
def hull (r : Graph α β) : Graph α β where
  upper := r.upper
  lower := r.lower
  links := (Finset.range r.upper.len ×ˢ Finset.range r.lower.len).filter fun p =>
    (∃ q ∈ r.links, q.1 = p.1 ∧ q.2 ≤ p.2) ∧ ∃ q ∈ r.links, q.1 = p.1 ∧ p.2 ≤ q.2

@[simp] theorem hull_upper (r : Graph α β) : r.hull.upper = r.upper := rfl

@[simp] theorem hull_lower (r : Graph α β) : r.hull.lower = r.lower := rfl

/-- Hull membership, on an in-bounds graph: `j` lies between two of `k`'s links. -/
theorem mem_links_hull {r : Graph α β} (hr : r.InBounds) {k j : ℕ} :
    (k, j) ∈ r.hull.links
      ↔ ∃ j₁ j₂, (k, j₁) ∈ r.links ∧ (k, j₂) ∈ r.links ∧ j₁ ≤ j ∧ j ≤ j₂ := by
  simp only [hull, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨-, ⟨⟨k₁, j₁⟩, h₁, rfl, hle₁⟩, ⟨k₂, j₂⟩, h₂, hk₂, hle₂⟩
    subst hk₂
    exact ⟨j₁, j₂, h₁, h₂, hle₁, hle₂⟩
  · rintro ⟨j₁, j₂, h₁, h₂, hle₁, hle₂⟩
    exact ⟨⟨(hr _ h₁).1, lt_of_le_of_lt hle₂ (hr _ h₂).2⟩,
      ⟨(k, j₁), h₁, rfl, hle₁⟩, ⟨(k, j₂), h₂, rfl, hle₂⟩⟩

/-- The hull stays in bounds. -/
theorem InBounds.hull {r : Graph α β} (hr : r.InBounds) : r.hull.InBounds := fun p hp => by
  simpa [Finset.mem_product] using (Finset.mem_filter.mp hp).1

/-- Links flank themselves: the hull extends the link set. -/
theorem links_subset_hull {r : Graph α β} (hr : r.InBounds) : r.links ⊆ r.hull.links :=
  fun ⟨k, j⟩ hp => (mem_links_hull hr).mpr ⟨j, j, hp, hp, le_rfl, le_rfl⟩

/-- Per-node convexity: the defining property of the hull. -/
theorem hull_convex {r : Graph α β} (hr : r.InBounds) {k j₁ j j₂ : ℕ}
    (h₁ : (k, j₁) ∈ r.hull.links) (h₂ : (k, j₂) ∈ r.hull.links) (hle₁ : j₁ ≤ j)
    (hle₂ : j ≤ j₂) : (k, j) ∈ r.hull.links := by
  obtain ⟨a₁, -, ha₁, -, hle₃, -⟩ := (mem_links_hull hr).mp h₁
  obtain ⟨-, a₂, -, ha₂, -, hle₄⟩ := (mem_links_hull hr).mp h₂
  exact (mem_links_hull hr).mpr ⟨a₁, a₂, ha₁, ha₂, by omega, by omega⟩

end Graph

/-- The hull on well-formed representations. -/
def AR.hull (A : AR α β) : AR α β where
  toGraph := A.toGraph.hull
  inBounds := A.inBounds.hull

@[simp] theorem AR.hull_upper (A : AR α β) : A.hull.upper = A.upper := rfl

@[simp] theorem AR.hull_lower (A : AR α β) : A.hull.lower = A.lower := rfl

/-- Hull membership on a well-formed representation: no side condition — the
representation carries its own bounds. -/
theorem AR.mem_links_hull {A : AR α β} {k j : ℕ} :
    (k, j) ∈ A.hull.links
      ↔ ∃ j₁ j₂, (k, j₁) ∈ A.links ∧ (k, j₂) ∈ A.links ∧ j₁ ≤ j ∧ j ≤ j₂ :=
  Graph.mem_links_hull A.inBounds

/-! ### The hull in coordinates

The interval closure on the graph foundation: tier-`m` nodes' links close to
their hulls on each other tier; links not involving `m` pass through. -/

section CoordinateHull

variable {ι : Type*} [Finite ι] {τ : ι → Type*}
variable (m : ι) (X : Representation (Sigma.fst : ((i : ι) × τ i) → ι)) [Finite X.obj.V]

/-- Close each tier-`m` node's association set to its interval hull on each
    other tier. -/
noncomputable def Representation.hull :
    Representation (Sigma.fst : ((i : ι) × τ i) → ι) :=
  Representation.ofData (fun i => X.tierWord i)
    (fun i j p q =>
      (i = m ∧ ∃ q₁ q₂, X.link i j p q₁ ∧ X.link i j p q₂ ∧ q₁ ≤ q ∧ q ≤ q₂) ∨
        (i ≠ m ∧ j ≠ m ∧ X.link i j p q))

instance : Finite (X.hull m).obj.V :=
  inferInstanceAs (Finite ((_ : ι) × Fin _))

@[simp] theorem Representation.tierWord_hull (i : ι) :
    (X.hull m).tierWord i = X.tierWord i :=
  Representation.tierWord_ofData i

/-- Hull membership at the melody tier: `q` lies between two of `p`'s links. -/
theorem Representation.link_hull_left {j : ι} (hj : m ≠ j) {p q : ℕ}
    (hq : q < X.tierLength j) :
    (X.hull m).link m j p q ↔
      ∃ q₁ q₂, X.link m j p q₁ ∧ X.link m j p q₂ ∧ q₁ ≤ q ∧ q ≤ q₂ := by
  unfold Representation.hull
  rw [Representation.link_ofData]
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
    · simpa [Representation.length_tierWord] using hq

/-- Links not involving the melody tier pass through the hull unchanged. -/
theorem Representation.link_hull_of_ne {i j : ι} (hi : i ≠ m) (hj : j ≠ m) (p q : ℕ) :
    (X.hull m).link i j p q ↔ X.link i j p q := by
  unfold Representation.hull
  rw [Representation.link_ofData]
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
theorem Representation.link_subset_hull {i j : ι} {p q : ℕ} (h : X.link i j p q) :
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

/-- Per-node convexity at the melody tier: the defining property of the hull. -/
theorem Representation.link_hull_convex {j : ι} (hj : m ≠ j) {p q₁ q q₂ : ℕ}
    (hq : q < X.tierLength j)
    (h₁ : (X.hull m).link m j p q₁) (h₂ : (X.hull m).link m j p q₂)
    (hle₁ : q₁ ≤ q) (hle₂ : q ≤ q₂) : (X.hull m).link m j p q := by
  have hlen : (X.hull m).tierLength j = X.tierLength j := by
    rw [← Representation.length_tierWord, Representation.tierWord_hull,
      Representation.length_tierWord]
  obtain ⟨-, hb₁, -⟩ := id h₁
  obtain ⟨-, hb₂, -⟩ := id h₂
  rw [hlen] at hb₁ hb₂
  obtain ⟨a₁, -, ha₁, -, hle₃, -⟩ := (X.link_hull_left m hj hb₁).mp h₁
  obtain ⟨-, a₂, -, ha₂, -, hle₄⟩ := (X.link_hull_left m hj hb₂).mp h₂
  exact (X.link_hull_left m hj hq).mpr ⟨a₁, a₂, ha₁, ha₂, by omega, by omega⟩

end CoordinateHull

end Autosegmental
