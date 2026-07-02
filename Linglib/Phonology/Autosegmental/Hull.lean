/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.AR

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

* `mem_hull_links` — hull membership as flanking, for in-bounds graphs.
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
theorem mem_hull_links {r : Graph α β} (hr : r.InBounds) {k j : ℕ} :
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
  fun ⟨k, j⟩ hp => (mem_hull_links hr).mpr ⟨j, j, hp, hp, le_rfl, le_rfl⟩

/-- Per-node convexity: the defining property of the hull. -/
theorem hull_convex {r : Graph α β} (hr : r.InBounds) {k j₁ j j₂ : ℕ}
    (h₁ : (k, j₁) ∈ r.hull.links) (h₂ : (k, j₂) ∈ r.hull.links) (hle₁ : j₁ ≤ j)
    (hle₂ : j ≤ j₂) : (k, j) ∈ r.hull.links := by
  obtain ⟨a₁, -, ha₁, -, hle₃, -⟩ := (mem_hull_links hr).mp h₁
  obtain ⟨-, a₂, -, ha₂, -, hle₄⟩ := (mem_hull_links hr).mp h₂
  exact (mem_hull_links hr).mpr ⟨a₁, a₂, ha₁, ha₂, by omega, by omega⟩

/-- Surfacing through the hull: a same-node flanking pair with the right label. -/
theorem surfacesWith_hull {r : Graph α β} (hr : r.InBounds) {a : α} {j : ℕ} :
    r.hull.SurfacesWith a j
      ↔ ∃ i j₁ j₂, (i, j₁) ∈ r.links ∧ (i, j₂) ∈ r.links ∧ j₁ ≤ j ∧ j ≤ j₂
          ∧ r.upper.get? i = some a := by
  constructor
  · rintro ⟨i, hlink, hlabel⟩
    obtain ⟨j₁, j₂, h₁, h₂, hle₁, hle₂⟩ := (mem_hull_links hr).mp hlink
    exact ⟨i, j₁, j₂, h₁, h₂, hle₁, hle₂, hlabel⟩
  · rintro ⟨i, j₁, j₂, h₁, h₂, hle₁, hle₂, hlabel⟩
    exact ⟨i, (mem_hull_links hr).mpr ⟨j₁, j₂, h₁, h₂, hle₁, hle₂⟩, hlabel⟩

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
  Graph.mem_hull_links A.inBounds

end Autosegmental
