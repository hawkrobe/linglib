/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.Group.Defs
import Linglib.Phonology.Autosegmental.NonCrossing

/-!
# Autosegmental graph (the AR object)

A `Autosegmental.Graph α β` is a finite ordered bipartite labeled relation
between two tiers: an `upper` list of `α`s, a `lower` list of `β`s, and a
`Finset` of association lines (index pairs). It is the standard *autosegmental
representation* (AR) of [goldsmith-1976] and the computational-phonology
tradition ([jardine-2017], [chandlee-jardine-2019], [burness-mcmullin-2020]).

Well-formedness splits into separable `Prop`s (the post-1986 view): `IsPlanar`
(Goldsmith's no-crossing constraint) is [pulleyblank-1986]'s sole *structural*
requirement, while saturation (`IsSaturated*`, [goldsmith-1979]'s original WFC)
is language-particular — so floating elements ([bird-1966], [laoide-kemp-2026])
are well-formed.

## Main definitions

* `Graph α β` — the bipartite structure; `empty`, `ofTiers` builders.
* `IsPlanar` — Pulleyblank-WFC: no association lines cross.
* `IsLinked*`/`IsFloating*` — index predicates (`IsFloating*` add in-bounds).
* `IsSaturated*`/`IsGoldsmithWFC` — saturation and Goldsmith's original WFC.
* `insertLink`/`eraseLink` — atomic link operations.
* `concat` — [jardine-heinz-2015] concatenation (disjoint union, index-shifted).

## Main results

`concat` satisfies the monoid laws with `empty` as unit (`concat_assoc`,
`empty_concat`, `concat_empty`; [jardine-heinz-2015] Thms 1, 3) and preserves
planarity and in-bounds (`isPlanar_concat`/`inBounds_concat`, Thm 4). The
`Monoid` typeclass instance lives one layer up, on the in-bounds object `AR α β`
(`AR.lean`), whose planar full monoidal subcategory is `WellFormedAR`
(`WellFormedAR.lean`); the raw `Graph` exports only the named laws, since
multiplicative notation on a bare graph carries no phonological meaning.
Concatenation is the autosegmentally meaningful join; relational composition
through a shared tier is not (it breaks planarity).

## Implementation notes

`links : Finset (ℕ × ℕ)` uses raw natural-number indexing (matching the
`MonovaryOn`-based `NonCrossing` substrate); in-bounds is a `Prop` (`InBounds`),
not a structural invariant, and well-formedness conditions are separate `Prop`s
rather than bundled invariants. A `Finset` permits multi-edges natively
(spreading, geminates, contour tones). The label-merging variant of `concat`
(unbounded spreading), multi-tier feature geometry, and the OT
underlying/surface split are paper-specific and live in consumers, not here.
-/

namespace Autosegmental

/-- A bipartite autosegmental representation: two ordered tiers and a finite
    set of association lines (index pairs) between them. -/
@[ext]
structure Graph (α β : Type*) where
  /-- The upper tier (e.g., tonal tier, melodic tier, root). -/
  upper : List α
  /-- The lower tier (e.g., segmental backbone, skeleton, template). -/
  lower : List β
  /-- Association lines as a finite set of index pairs
      `(upper-index, lower-index)`. -/
  links : Finset (ℕ × ℕ)
  deriving DecidableEq

namespace Graph

variable {α β : Type*} (r : Graph α β)

/-! ### Construction -/

/-- The empty bipartite representation with no tiers and no links. -/
def empty : Graph α β := ⟨[], [], ∅⟩

/-- Tiers with no links — the underlying form before any docking. -/
def ofTiers (upper : List α) (lower : List β) : Graph α β :=
  ⟨upper, lower, ∅⟩

/-! ### Planarity (no-crossing) -/

/-- **Planar** (no-crossing): the link set satisfies [goldsmith-1976]'s NCC. -/
def IsPlanar : Prop := IsNonCrossing r.links

/-! ### Index predicates -/

/-- Upper index `i` is **linked** to some lower position (no in-bounds check). -/
def IsLinkedUpper (i : ℕ) : Prop :=
  ∃ p ∈ r.links, p.fst = i

/-- Lower index `j` is **linked** to some upper position (no in-bounds check). -/
def IsLinkedLower (j : ℕ) : Prop :=
  ∃ p ∈ r.links, p.snd = j

/-- Upper index `i` is **floating**: in-bounds but unlinked. -/
def IsFloatingUpper (i : ℕ) : Prop :=
  i < r.upper.length ∧ ¬ r.IsLinkedUpper i

/-- Lower index `j` is **floating**: in-bounds but unlinked (*segmentally empty*). -/
def IsFloatingLower (j : ℕ) : Prop :=
  j < r.lower.length ∧ ¬ r.IsLinkedLower j

/-! ### Decidability of index predicates -/

instance (i : ℕ) : Decidable (r.IsLinkedUpper i) :=
  inferInstanceAs (Decidable (∃ p ∈ r.links, p.fst = i))

instance (j : ℕ) : Decidable (r.IsLinkedLower j) :=
  inferInstanceAs (Decidable (∃ p ∈ r.links, p.snd = j))

instance (i : ℕ) : Decidable (r.IsFloatingUpper i) :=
  inferInstanceAs (Decidable (i < r.upper.length ∧ ¬ r.IsLinkedUpper i))

instance (j : ℕ) : Decidable (r.IsFloatingLower j) :=
  inferInstanceAs (Decidable (j < r.lower.length ∧ ¬ r.IsLinkedLower j))

/-! ### Saturation and Goldsmith's WFC -/

/-- **Saturated**: every in-bounds upper index is linked. -/
def IsSaturatedUpper : Prop :=
  ∀ i, i < r.upper.length → r.IsLinkedUpper i

/-- **Saturated**: every in-bounds lower index is linked. -/
def IsSaturatedLower : Prop :=
  ∀ j, j < r.lower.length → r.IsLinkedLower j

/-- [goldsmith-1979]'s original WFC: planar *and* both tiers saturated.
    Post-[pulleyblank-1986], only `IsPlanar` is structural. -/
def IsGoldsmithWFC : Prop :=
  r.IsPlanar ∧ r.IsSaturatedUpper ∧ r.IsSaturatedLower

instance : Decidable r.IsSaturatedUpper :=
  Nat.decidableBallLT _ _

instance : Decidable r.IsSaturatedLower :=
  Nat.decidableBallLT _ _

/-! ### Link-set operations -/

/-- Insert the association line `(i, j)`. -/
def insertLink (i j : ℕ) : Graph α β :=
  { r with links := insert (i, j) r.links }

/-- Erase the association line `(i, j)`. -/
def eraseLink (i j : ℕ) : Graph α β :=
  { r with links := r.links.erase (i, j) }

/-! ### Basic properties -/

@[simp] theorem upper_insertLink (i j : ℕ) :
    (r.insertLink i j).upper = r.upper := rfl

@[simp] theorem lower_insertLink (i j : ℕ) :
    (r.insertLink i j).lower = r.lower := rfl

@[simp] theorem links_insertLink (i j : ℕ) :
    (r.insertLink i j).links = insert (i, j) r.links := rfl

@[simp] theorem upper_eraseLink (i j : ℕ) :
    (r.eraseLink i j).upper = r.upper := rfl

@[simp] theorem lower_eraseLink (i j : ℕ) :
    (r.eraseLink i j).lower = r.lower := rfl

@[simp] theorem links_eraseLink (i j : ℕ) :
    (r.eraseLink i j).links = r.links.erase (i, j) := rfl

/-- `insertLink` preserves planarity if the new link crosses nothing. -/
theorem isPlanar_insertLink {i j : ℕ}
    (hP : r.IsPlanar) (hNX : ¬ IndexCrosses r.links i j) :
    (r.insertLink i j).IsPlanar :=
  IsNonCrossing.insert_of_not_indexCrosses hP hNX

/-- `eraseLink` preserves planarity (a subset of a no-crossing set). -/
theorem isPlanar_eraseLink (i j : ℕ)
    (hP : r.IsPlanar) : (r.eraseLink i j).IsPlanar :=
  IsNonCrossing.subset (Finset.erase_subset _ _) hP

/-- The empty representation is planar (vacuously). -/
theorem isPlanar_empty : (empty : Graph α β).IsPlanar := by
  simp [IsPlanar, empty]

/-- `ofTiers` produces a planar representation (no links to cross). -/
theorem isPlanar_ofTiers (upper : List α) (lower : List β) :
    (ofTiers upper lower).IsPlanar := by
  simp [IsPlanar, ofTiers]

/-! ### In-bounds predicate -/

/-- Every link's indices fall within the tier lengths. -/
def InBounds : Prop :=
  ∀ p ∈ r.links, p.fst < r.upper.length ∧ p.snd < r.lower.length

instance : Decidable r.InBounds := by
  unfold InBounds; infer_instance

theorem inBounds_empty : (empty : Graph α β).InBounds := by
  simp [InBounds, empty]

theorem inBounds_ofTiers (upper : List α) (lower : List β) :
    (ofTiers upper lower).InBounds := by
  simp [InBounds, ofTiers]

/-! ### Concatenation ([jardine-heinz-2015]) -/

/-- Shift a link by `(δᵤ, δₗ)`. -/
def shiftLink (δᵤ δₗ : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  (p.1 + δᵤ, p.2 + δₗ)

/-! #### Shift algebra -/

@[simp] theorem shiftLink_apply (δᵤ δₗ : ℕ) (p : ℕ × ℕ) :
    shiftLink δᵤ δₗ p = (p.1 + δᵤ, p.2 + δₗ) := rfl

@[simp] theorem shiftLink_zero : shiftLink 0 0 = (id : ℕ × ℕ → ℕ × ℕ) := by
  funext p; simp

theorem shiftLink_comp (a₁ a₂ b₁ b₂ : ℕ) :
    shiftLink a₁ a₂ ∘ shiftLink b₁ b₂ = shiftLink (a₁ + b₁) (a₂ + b₂) := by
  funext p
  simp only [Function.comp_apply, shiftLink_apply, Prod.mk.injEq]
  omega

/-! #### Concatenation -/

/-- [jardine-heinz-2015] concatenation: tier-concatenation plus
    index-shifted link-set union. -/
def concat (A B : Graph α β) : Graph α β where
  upper := A.upper ++ B.upper
  lower := A.lower ++ B.lower
  links := A.links ∪ B.links.image (shiftLink A.upper.length A.lower.length)

@[simp] theorem upper_concat (A B : Graph α β) :
    (A.concat B).upper = A.upper ++ B.upper := rfl

@[simp] theorem lower_concat (A B : Graph α β) :
    (A.concat B).lower = A.lower ++ B.lower := rfl

@[simp] theorem links_concat (A B : Graph α β) :
    (A.concat B).links =
      A.links ∪ B.links.image (shiftLink A.upper.length A.lower.length) := rfl

/-! #### Monoid laws ([jardine-heinz-2015] Theorems 1, 3) -/

/-- `empty` is a left identity for `concat`. -/
theorem empty_concat (A : Graph α β) : empty.concat A = A := by
  ext <;> simp [empty, shiftLink_zero]

/-- `empty` is a right identity for `concat`. -/
theorem concat_empty (A : Graph α β) : A.concat empty = A := by
  ext <;> simp [empty]

/-- `concat` is associative. -/
theorem concat_assoc (A B C : Graph α β) :
    (A.concat B).concat C = A.concat (B.concat C) := by
  ext
  · simp [List.append_assoc]
  · simp [List.append_assoc]
  · simp only [links_concat, upper_concat, lower_concat, List.length_append,
               Finset.image_union, Finset.image_image, shiftLink_comp]
    rw [Finset.union_assoc]

/-! #### Planarity preservation ([jardine-heinz-2015] Theorem 4) -/

/-- Shifting a link set preserves non-crossing: `shiftLink` is a coordinatewise
    order-embedding, so by `monovaryOn_image` it preserves monovariance. -/
theorem isNonCrossing_image_shiftLink (s : Finset (ℕ × ℕ)) (δᵤ δₗ : ℕ) :
    IsNonCrossing (s.image (shiftLink δᵤ δₗ)) ↔ IsNonCrossing s := by
  grind [IsNonCrossing, Finset.coe_image, monovaryOn_image, MonovaryOn, shiftLink]

/-- Concatenation preserves planarity, given `A.InBounds`: `A.links` and the
    shifted `B.links` are each non-crossing (`monovaryOn_union` +
    `isNonCrossing_image_shiftLink`), and `A` sits entirely before `B`. -/
theorem isPlanar_concat {A B : Graph α β} (hAib : A.InBounds) (hA : A.IsPlanar) (hB : B.IsPlanar) :
    (A.concat B).IsPlanar := by
  grind [IsPlanar, IsNonCrossing, InBounds, MonovaryOn, links_concat, Finset.coe_union,
    monovaryOn_union, isNonCrossing_image_shiftLink, shiftLink]

/-- Concatenation preserves in-bounds. -/
theorem inBounds_concat {A B : Graph α β}
    (hA : A.InBounds) (hB : B.InBounds) : (A.concat B).InBounds := by
  rintro p hp
  simp only [links_concat, Finset.mem_union, Finset.mem_image, upper_concat, lower_concat,
    List.length_append] at hp ⊢
  obtain hp | ⟨q, hq, rfl⟩ := hp
  · have := hA p hp; omega
  · have := hB q hq; simp only [shiftLink]; omega

end Graph

end Autosegmental
