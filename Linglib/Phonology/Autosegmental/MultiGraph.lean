/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Pi
import Linglib.Core.CategoryTheory.Monoidal.LabeledTuple
import Linglib.Phonology.Autosegmental.NonCrossing

/-!
# Multi-tier autosegmental graphs

`MultiGraph τ` is the autosegmental representation at **general tier arity**:
`n` heterogeneously-typed ordered **tiers** (`tiers i : LabeledTuple (τ i)`, with
`τ : Fin n → Type u`) plus, for every ordered tier-pair `(i, j)`, a `Finset (ℕ × ℕ)`
of association **links** (`links i j`; empty ⇒ the pair does not associate). This is
[jardine-2017]'s autosegmental phonological graph at arbitrary arity, and the home
of [lionnet-2022]'s register-tier tone geometry (subtonal-feature tiers + a mora
tier around a Tonal Root Node hub).

The classical **bipartite** `Graph α β` (`Graph.lean`) is the `n = 2` case. It is a
*separate first-class structure* (so it keeps `extends`/`.toGraph`/anonymous-
constructor ergonomics and independent universes); the two are related by the
**monoidal inclusion functor** rather than a defeq view — see `Inclusion.lean`.

## Design (three-reviewer mathlib panel, 2026-06-24)

* **Heterogeneous tiers** `τ : Fin n → Type u` — per-tier static typing, fiberwise.
* **Links per ordered tier-pair** `(i j) → Finset (ℕ × ℕ)` — keeps `concat`'s shift
  fiberwise; the associating topology is `{(i,j) | links i j ≠ ∅}`.
* **Planarity stays binary, per pair** (`IsPlanar := ∀ i j, IsNonCrossing (links i j)`):
  the existing `MonovaryOn`-based NCC reused pointwise — no N-ary planarity theory.
-/

namespace Autosegmental

universe u

/-- A **multi-tier autosegmental graph**: `n` heterogeneously-typed ordered tiers
    plus a `Finset (ℕ × ℕ)` of association links on each ordered tier-pair. -/
@[ext]
structure MultiGraph {n : ℕ} (τ : Fin n → Type u) where
  /-- The `n` heterogeneously-typed ordered tiers. -/
  tiers : (i : Fin n) → LabeledTuple (τ i)
  /-- Association links per ordered tier-pair; empty ⇒ the pair does not associate. -/
  links : (i j : Fin n) → Finset (ℕ × ℕ)

namespace MultiGraph

variable {n : ℕ} {τ : Fin n → Type u}

instance [∀ i, DecidableEq (τ i)] : DecidableEq (MultiGraph τ) := fun _ _ =>
  decidable_of_iff _ MultiGraph.ext_iff.symm

/-! ### Well-formedness predicates -/

/-- **Planarity**: every tier-pair's link set is non-crossing — the binary
    `MonovaryOn` NCC applied pointwise per pair (no N-ary generalization). -/
def IsPlanar (G : MultiGraph τ) : Prop := ∀ i j, IsNonCrossing (G.links i j)

instance (G : MultiGraph τ) : Decidable G.IsPlanar :=
  inferInstanceAs (Decidable (∀ _ _, _))

/-- **In-bounds**: every link's endpoints fall within the respective tier lengths. -/
def InBounds (G : MultiGraph τ) : Prop :=
  ∀ i j, ∀ p ∈ G.links i j, p.1 < (G.tiers i).len ∧ p.2 < (G.tiers j).len

instance (G : MultiGraph τ) : Decidable G.InBounds :=
  inferInstanceAs (Decidable (∀ _ _, _))

/-! ### The empty graph -/

/-- The empty multigraph: every tier empty, no links. -/
def empty : MultiGraph τ where
  tiers _ := LabeledTuple.empty
  links _ _ := ∅

@[simp] theorem empty_tiers (i : Fin n) : (empty : MultiGraph τ).tiers i = LabeledTuple.empty := rfl
@[simp] theorem empty_links (i j : Fin n) : (empty : MultiGraph τ).links i j = ∅ := rfl

theorem isPlanar_empty : (empty : MultiGraph τ).IsPlanar := by
  intro i j; simp [empty, isNonCrossing_empty]

theorem inBounds_empty : (empty : MultiGraph τ).InBounds := by
  intro i j p hp; simp at hp

/-! ### Shift algebra -/

/-- Shift a link by `(δ₁, δ₂)`. -/
def shiftLink (δ₁ δ₂ : ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (p.1 + δ₁, p.2 + δ₂)

@[simp] theorem shiftLink_apply (δ₁ δ₂ : ℕ) (p : ℕ × ℕ) :
    shiftLink δ₁ δ₂ p = (p.1 + δ₁, p.2 + δ₂) := rfl

@[simp] theorem shiftLink_zero : shiftLink 0 0 = (id : ℕ × ℕ → ℕ × ℕ) := by funext p; simp

theorem shiftLink_comp (a₁ a₂ b₁ b₂ : ℕ) :
    shiftLink a₁ a₂ ∘ shiftLink b₁ b₂ = shiftLink (a₁ + b₁) (a₂ + b₂) := by
  funext p; simp only [Function.comp_apply, shiftLink_apply, Prod.mk.injEq]; omega

/-- Shifting a link set preserves non-crossing (via `isNonCrossing_image`). -/
theorem isNonCrossing_image_shiftLink (s : Finset (ℕ × ℕ)) (δ₁ δ₂ : ℕ) :
    IsNonCrossing (s.image (shiftLink δ₁ δ₂)) ↔ IsNonCrossing s := by
  grind [isNonCrossing_image, IsNonCrossing, MonovaryOn, shiftLink]

/-! ### Concatenation ([jardine-heinz-2015], fiberwise coproduct) -/

/-- Concatenation: tier-wise `LabeledTuple.concat`, and per-pair link union with
    `B`'s links shifted past `A`'s tier lengths on each coordinate. -/
def concat (A B : MultiGraph τ) : MultiGraph τ where
  tiers i := (A.tiers i).concat (B.tiers i)
  links i j := A.links i j ∪ (B.links i j).image (shiftLink (A.tiers i).len (A.tiers j).len)

@[simp] theorem concat_tiers (A B : MultiGraph τ) (i : Fin n) :
    (A.concat B).tiers i = (A.tiers i).concat (B.tiers i) := rfl

@[simp] theorem concat_links (A B : MultiGraph τ) (i j : Fin n) :
    (A.concat B).links i j =
      A.links i j ∪ (B.links i j).image (shiftLink (A.tiers i).len (A.tiers j).len) := rfl

/-! #### Monoid laws -/

theorem empty_concat (A : MultiGraph τ) : empty.concat A = A := by
  refine MultiGraph.ext ?_ ?_
  · funext i; simpa using LabeledTuple.empty_concat (A.tiers i)
  · funext i j; simp [concat_links, empty, shiftLink_zero]

theorem concat_empty (A : MultiGraph τ) : A.concat empty = A := by
  refine MultiGraph.ext ?_ ?_
  · funext i; simpa using LabeledTuple.concat_empty (A.tiers i)
  · funext i j; simp [concat_links, empty]

theorem concat_assoc (A B C : MultiGraph τ) :
    (A.concat B).concat C = A.concat (B.concat C) := by
  refine MultiGraph.ext ?_ ?_
  · funext i; simp only [concat_tiers, LabeledTuple.concat_assoc]
  · funext i j
    simp only [concat_links, concat_tiers, LabeledTuple.concat_len, Finset.image_union,
      Finset.image_image, shiftLink_comp]
    rw [Finset.union_assoc]

instance : Monoid (MultiGraph τ) where
  mul := concat
  one := empty
  mul_assoc := concat_assoc
  one_mul := empty_concat
  mul_one := concat_empty

/-! #### Predicate preservation -/

/-- Concatenation preserves planarity, given `A.InBounds`. -/
theorem isPlanar_concat {A B : MultiGraph τ} (hAib : A.InBounds)
    (hA : A.IsPlanar) (hB : B.IsPlanar) : (A.concat B).IsPlanar := by
  intro i j
  have hAij := hA i j; have hBij := hB i j; have hAibij := hAib i j
  grind [IsPlanar, IsNonCrossing, InBounds, MonovaryOn, concat_links, Finset.coe_union,
    monovaryOn_union, isNonCrossing_image_shiftLink, shiftLink]

/-- Concatenation preserves in-bounds. -/
theorem inBounds_concat {A B : MultiGraph τ}
    (hA : A.InBounds) (hB : B.InBounds) : (A.concat B).InBounds := by
  intro i j p hp
  simp only [concat_links, Finset.mem_union, Finset.mem_image, concat_tiers,
    LabeledTuple.concat_len] at hp ⊢
  obtain hp | ⟨q, hq, rfl⟩ := hp
  · have := hA i j p hp; omega
  · have := hB i j q hq; simp only [shiftLink]; omega

end MultiGraph

end Autosegmental
