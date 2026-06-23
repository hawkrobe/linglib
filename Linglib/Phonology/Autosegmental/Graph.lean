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

`concat` forms a `Monoid` with `empty` as unit ([jardine-heinz-2015] Thms 1, 3)
and preserves planarity and in-bounds (`isPlanar_concat`/`inBounds_concat`,
Thm 4). The well-formed ARs form the analogous monoidal category — see `AR.lean`,
which also reserves the bundled symbol `AR α β`. Concatenation is the
autosegmentally meaningful join; relational composition through a shared tier is
not (it breaks planarity).

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

/-- A bipartite autosegmental representation: two ordered tiers and a
    finite set of association lines between them. Generic over both
    tier-element types. -/
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

/-- A bipartite representation with the given tiers and no links —
    the canonical *underlying* form before any docking has applied. -/
def ofTiers (upper : List α) (lower : List β) : Graph α β :=
  ⟨upper, lower, ∅⟩

/-! ### Planarity (no-crossing) -/

/-- The bipartite representation is **planar** (no-crossing) iff its
    link set satisfies [goldsmith-1976]'s NCC. Lifted from
    `NonCrossing.IsNonCrossing` so mathlib's `MonovaryOn` lemma library
    applies directly. -/
def IsPlanar : Prop := IsNonCrossing r.links

/-! ### Index predicates -/

/-- The upper-tier element at index `i` is **linked** to some lower-tier
    position. No in-bounds check. -/
def IsLinkedUpper (i : ℕ) : Prop :=
  ∃ p ∈ r.links, p.fst = i

/-- The lower-tier element at index `j` is **linked** to some upper-tier
    position. No in-bounds check. -/
def IsLinkedLower (j : ℕ) : Prop :=
  ∃ p ∈ r.links, p.snd = j

/-- The upper-tier element at index `i` is **floating**: in-bounds but
    not linked to any lower position. -/
def IsFloatingUpper (i : ℕ) : Prop :=
  i < r.upper.length ∧ ¬ r.IsLinkedUpper i

/-- The lower-tier element at index `j` is **floating**: in-bounds but
    not linked to any upper position. The paper calls a lower slot
    with this property *segmentally empty*. -/
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

/-! ### Saturation and Goldsmith's WFC

[goldsmith-1979] bundled saturation with non-crossing
into a single Well-Formedness Condition; [pulleyblank-1986]
weakened WFC to non-crossing alone, with saturation devolved to
language-particular association conventions. The post-1986 view is
the modern default — it admits floating elements
([bird-1966], [laoide-kemp-2026]) as structurally
well-formed.
-/

/-- The upper tier is **saturated**: every in-bounds upper-tier index
    is linked to some lower-tier position. -/
def IsSaturatedUpper : Prop :=
  ∀ i, i < r.upper.length → r.IsLinkedUpper i

/-- The lower tier is **saturated**: every in-bounds lower-tier index
    is linked to some upper-tier position. -/
def IsSaturatedLower : Prop :=
  ∀ j, j < r.lower.length → r.IsLinkedLower j

/-- [goldsmith-1979]'s original Well-Formedness Condition: both
    tiers fully saturated *and* no association lines cross. Modern
    usage (post-[pulleyblank-1986]) treats only `IsPlanar` as
    structurally required and demotes saturation to language-particular
    association conventions. -/
def IsGoldsmithWFC : Prop :=
  r.IsPlanar ∧ r.IsSaturatedUpper ∧ r.IsSaturatedLower

instance : Decidable r.IsSaturatedUpper :=
  Nat.decidableBallLT _ _

instance : Decidable r.IsSaturatedLower :=
  Nat.decidableBallLT _ _

/-! ### Link-set operations -/

/-- Insert the association line `(i, j)`. Does not check planarity; use
    `isPlanar_insertLink` to preserve it. Naming mirrors
    `Floating.lean`'s `insertLink`. -/
def insertLink (i j : ℕ) : Graph α β :=
  { r with links := insert (i, j) r.links }

/-- Erase the association line `(i, j)`. Naming mirrors
    `Floating.lean`'s `deleteLink`. -/
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

/-- `insertLink` preserves planarity iff the inserted link does not
    cross any existing link. Lifts
    `IsNonCrossing.insert_of_not_indexCrosses`. -/
theorem isPlanar_insertLink {i j : ℕ}
    (hP : r.IsPlanar) (hNX : ¬ IndexCrosses r.links i j) :
    (r.insertLink i j).IsPlanar :=
  IsNonCrossing.insert_of_not_indexCrosses hP hNX

/-- `eraseLink` preserves planarity: removing a link from a no-crossing
    set leaves a no-crossing subset. -/
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

/-- A `Graph` is **in bounds** if every link's indices fall within
    the bounds of its tiers. The substrate does not enforce this
    structurally (`links : Finset (ℕ × ℕ)` permits any indices);
    `InBounds` is required as a hypothesis for theorems that depend on
    it (e.g. `isPlanar_concat`, where the cross-case of A-link vs
    shifted B-link needs to know A's links don't reach past A's
    length). Real ARs always satisfy this — the substrate just doesn't
    bake it in. -/
def InBounds : Prop :=
  ∀ p ∈ r.links, p.fst < r.upper.length ∧ p.snd < r.lower.length

instance : Decidable r.InBounds := by
  unfold InBounds; infer_instance

theorem inBounds_empty : (empty : Graph α β).InBounds := by
  simp [InBounds, empty]

theorem inBounds_ofTiers (upper : List α) (lower : List β) :
    (ofTiers upper lower).InBounds := by
  simp [InBounds, ofTiers]

/-! ### Concatenation (Jardine-Heinz 2015 §5)

The autosegmentally-meaningful join operation. Concatenates the two
tiers and the link sets, with B's link indices shifted past A's tier
lengths. Preserves planarity. Forms a monoid with `empty` as identity.

This is the *disjoint-union* concatenation — no label-based merging.
The merging variant of [jardine-heinz-2015] (which derives
spreading by merging adjacent identical melody-tier nodes) is a
paper-specific quotient on top of this primitive.
-/

/-- Shift a link `(i, j)` by `(δᵤ, δₗ)` upper- and lower-tier positions.
    Not marked `@[simp]` (would over-unfold); explicit `simp [shiftLink]`
    invocations in proofs. -/
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

/-- **The monoid of autosegmental representations** ([jardine-heinz-2015]
    Theorems 1, 3): graphs form a `Monoid` under concatenation, with `empty`
    as the unit. `A * B = A.concat B`, `1 = empty`; the monoid laws are
    `empty_concat`/`concat_empty`/`concat_assoc`. -/
instance instMonoid : Monoid (Graph α β) where
  mul := concat
  one := empty
  mul_assoc := concat_assoc
  one_mul := empty_concat
  mul_one := concat_empty

@[simp] theorem mul_eq_concat (A B : Graph α β) : A * B = A.concat B := rfl

@[simp] theorem one_eq_empty : (1 : Graph α β) = empty := rfl

/-! #### Planarity preservation ([jardine-heinz-2015] Theorem 4) -/

/-- Concatenation preserves planarity, given `A` is in-bounds. The
    cross-case (an `A`-link vs a shifted `B`-link) needs `A.InBounds`
    to bound `A`'s lower-tier indices below `A.lower.length`, which is
    not structural on `Graph`. -/
theorem isPlanar_concat (A B : Graph α β)
    (hAib : A.InBounds) (hA : A.IsPlanar) (hB : B.IsPlanar) :
    (A.concat B).IsPlanar := by
  rw [IsPlanar, isNonCrossing_iff] at hA hB ⊢
  intro l₁ hl₁ l₂ hl₂ hlt
  rw [links_concat, Finset.mem_union] at hl₁ hl₂
  rcases hl₁ with hl₁ | hl₁
  · rcases hl₂ with hl₂ | hl₂
    · -- Both from A.
      exact hA l₁ hl₁ l₂ hl₂ hlt
    · -- l₁ from A, l₂ from shifted B.
      rw [Finset.mem_image] at hl₂
      obtain ⟨b₂, _, rfl⟩ := hl₂
      have := hAib l₁ hl₁
      simp only [shiftLink] at *
      omega
  · rw [Finset.mem_image] at hl₁
    obtain ⟨b₁, hb₁, rfl⟩ := hl₁
    rcases hl₂ with hl₂ | hl₂
    · -- l₁ from shifted B, l₂ from A. Vacuous under hAib:
      -- hlt says (b₁.fst + A.upper.length) < l₂.fst, but hAib says
      -- l₂.fst < A.upper.length, contradiction.
      have := hAib l₂ hl₂
      simp only [shiftLink] at hlt
      omega
    · -- Both from shifted B.
      rw [Finset.mem_image] at hl₂
      obtain ⟨b₂, hb₂, rfl⟩ := hl₂
      simp only [shiftLink] at hlt ⊢
      have hltB : b₁.fst < b₂.fst := by omega
      have := hB b₁ hb₁ b₂ hb₂ hltB
      omega

/-- Concatenation preserves in-bounds: links from `A` stay in `A`'s
    tier range (which is a prefix of `(A.concat B)`'s range), and
    shifted links from `B` land in the suffix `B`'s range adds. -/
theorem inBounds_concat {A B : Graph α β}
    (hA : A.InBounds) (hB : B.InBounds) : (A.concat B).InBounds := by
  intro p hp
  rw [links_concat, Finset.mem_union] at hp
  simp only [upper_concat, lower_concat, List.length_append]
  rcases hp with hp | hp
  · have := hA p hp
    refine ⟨?_, ?_⟩ <;> omega
  · rw [Finset.mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have := hB q hq
    simp only [shiftLink]
    refine ⟨?_, ?_⟩ <;> omega

end Graph

end Autosegmental
