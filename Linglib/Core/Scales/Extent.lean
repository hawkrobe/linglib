import Linglib.Core.Scales.Scale

/-!
# Extent Functions
@cite{kennedy-1999}

Given a measure function μ : Entity → D on a linearly ordered set,
the **extent functions** partition the scale into degrees the entity
"has" and degrees it "lacks":

- **posExt**(μ, x) = {d | d ≤ μ(x)} — the principal downset (positive extent)
- **negExt**(μ, x) = {d | μ(x) < d} — the strict upper set (negative extent)

These two sets are disjoint and exhaustive (they partition D).

**Note on boundary convention**: @cite{kennedy-1999} defines
POSδ(a) = {p ∈ Sδ | p ≤ d(a)} and NEGδ(a) = {p ∈ Sδ | d(a) ≤ p},
with the boundary point d(a) in BOTH sets (a cover, not a partition).
We use the strict inequality for negExt, placing d(a) in posExt only.
This gives a true partition without affecting any linguistic claims —
the key theorems (monotonicity, cross-polar anomaly, antonymy biconditional)
hold under either convention.

Three degree-semantic frameworks independently arrived at the positive
extent under different names:

| Framework    | Name                  | Motivation             |
|--------------|-----------------------|------------------------|
| Kennedy      | degree set / pos-ext  | antonymy, cross-polar  |
| Heim         | than-clause denotation| comparative composition|
| Schwarzschild| positive interval     | differential measures  |

This module defines the common algebraic core that all three use.
-/

namespace Core.Scale

variable {Entity D : Type*}

-- ════════════════════════════════════════════════════
-- § 1. Extent Functions
-- ════════════════════════════════════════════════════

/-- Positive extent: the set of degrees entity x "has" on scale μ.
    posExt(μ, x) = {d | d ≤ μ(x)}.
    This is the principal downset (initial segment) of μ(x). -/
def posExt [Preorder D] (μ : Entity → D) (x : Entity) : Set D :=
  { d | d ≤ μ x }

/-- Negative extent: the set of degrees entity x "lacks" on scale μ.
    negExt(μ, x) = {d | μ(x) < d}.
    This is the strict upper set above μ(x).
    Negative adjectives (short, light) access the negative extent
    of the *same* underlying measure function as their positive
    counterpart. -/
def negExt [Preorder D] (μ : Entity → D) (x : Entity) : Set D :=
  { d | μ x < d }

-- ════════════════════════════════════════════════════
-- § 2. Partition Theorems
-- ════════════════════════════════════════════════════

/-- Extents are disjoint: no degree is both "had" and "lacked". -/
theorem extent_disjoint [LinearOrder D] (μ : Entity → D) (x : Entity) :
    posExt μ x ∩ negExt μ x = ∅ := by
  ext d
  simp only [Set.mem_inter_iff, posExt, negExt, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, iff_false, not_and]
  exact fun h => not_lt.mpr h

/-- Extents exhaust the scale: every degree is either had or lacked. -/
theorem extent_exhaustive [LinearOrder D] (μ : Entity → D) (x : Entity) :
    posExt μ x ∪ negExt μ x = Set.univ := by
  ext d
  simp only [Set.mem_union, posExt, negExt, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact le_or_gt d (μ x)

/-- Positive extent is downward closed. -/
theorem posExt_downward_closed [Preorder D] (μ : Entity → D) (x : Entity)
    {d₁ d₂ : D} (h₁ : d₁ ≤ d₂) (h₂ : d₂ ∈ posExt μ x) :
    d₁ ∈ posExt μ x :=
  le_trans h₁ h₂

/-- Negative extent is upward closed (strict). -/
theorem negExt_upward_closed [Preorder D] (μ : Entity → D) (x : Entity)
    {d₁ d₂ : D} (h₁ : d₁ < d₂) (h₂ : d₁ ∈ negExt μ x) :
    d₂ ∈ negExt μ x :=
  lt_trans h₂ h₁

-- ════════════════════════════════════════════════════
-- § 3. Monotonicity
-- ════════════════════════════════════════════════════

/-- Higher degree ↔ larger positive extent. -/
theorem posExt_subset_iff [LinearOrder D] (μ : Entity → D) (a b : Entity) :
    posExt μ a ⊆ posExt μ b ↔ μ a ≤ μ b := by
  simp only [posExt, Set.subset_def, Set.mem_setOf_eq]
  constructor
  · intro h; exact h _ (le_refl _)
  · intro h d hd; exact le_trans hd h

/-- Strict extent inclusion ↔ strict degree ordering. -/
theorem posExt_ssubset_iff [LinearOrder D] (μ : Entity → D) (a b : Entity) :
    posExt μ a ⊂ posExt μ b ↔ μ a < μ b := by
  rw [Set.ssubset_def]
  constructor
  · intro ⟨hsub, hnsub⟩
    exact lt_of_le_of_ne ((posExt_subset_iff μ a b).mp hsub)
      (fun h => hnsub ((posExt_subset_iff μ b a).mpr (le_of_eq h.symm)))
  · intro h
    exact ⟨(posExt_subset_iff μ a b).mpr (le_of_lt h),
           fun hsub => absurd h (not_lt.mpr ((posExt_subset_iff μ b a).mp hsub))⟩

-- ════════════════════════════════════════════════════
-- § 4. Negative Extent Monotonicity
-- ════════════════════════════════════════════════════

/-- Higher degree ↔ SMALLER negative extent (reverse monotonicity). -/
theorem negExt_subset_iff [LinearOrder D] (μ : Entity → D) (a b : Entity) :
    negExt μ a ⊆ negExt μ b ↔ μ b ≤ μ a := by
  simp only [negExt, Set.subset_def, Set.mem_setOf_eq]
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    exact absurd (h _ hlt) (lt_irrefl _)
  · intro h d hd; exact lt_of_le_of_lt h hd

/-- Strict negative extent inclusion ↔ strict degree ordering (reversed). -/
theorem negExt_ssubset_iff [LinearOrder D] (μ : Entity → D) (a b : Entity) :
    negExt μ a ⊂ negExt μ b ↔ μ b < μ a := by
  rw [Set.ssubset_def]
  constructor
  · intro ⟨hsub, hnsub⟩
    exact lt_of_le_of_ne ((negExt_subset_iff μ a b).mp hsub)
      (fun h => hnsub ((negExt_subset_iff μ b a).mpr (le_of_eq h.symm)))
  · intro h
    exact ⟨(negExt_subset_iff μ a b).mpr (le_of_lt h),
           fun hsub => absurd h (not_lt.mpr ((negExt_subset_iff μ b a).mp hsub))⟩

-- ════════════════════════════════════════════════════
-- § 5. Antonymy Biconditional
-- ════════════════════════════════════════════════════

/-- **Antonymy biconditional** (@cite{kennedy-1999}):
    "A is taller than B" iff "B is shorter than A".

    posExt(a) ⊃ posExt(b)  ↔  negExt(b) ⊃ negExt(a)

    This is the central theorem of @cite{kennedy-1999} Ch. 3: the
    equivalence of positive and negative comparative sentences is
    DERIVED from the complementarity of positive and negative extents,
    rather than stipulated as a lexical property of antonym pairs. -/
theorem antonymy_biconditional [LinearOrder D] (μ : Entity → D) (a b : Entity) :
    posExt μ b ⊂ posExt μ a ↔ negExt μ a ⊂ negExt μ b := by
  rw [posExt_ssubset_iff, negExt_ssubset_iff]

/-- Weak antonymy biconditional (subset version):
    posExt(b) ⊆ posExt(a) ↔ negExt(a) ⊆ negExt(b). -/
theorem antonymy_biconditional_weak [LinearOrder D] (μ : Entity → D) (a b : Entity) :
    posExt μ b ⊆ posExt μ a ↔ negExt μ a ⊆ negExt μ b := by
  rw [posExt_subset_iff, negExt_subset_iff]

-- ════════════════════════════════════════════════════
-- § 6. Cross-Extent Comparison
-- ════════════════════════════════════════════════════

/-- Cross-extent inclusion: posExt of one entity ⊆ negExt of another.
    This is the semantic content of a cross-polar equative like
    "Kim is as tall as Lee is short". -/
def crossExtentInclusion [Preorder D] (μ : Entity → D) (a b : Entity) : Prop :=
  posExt μ a ⊆ negExt μ b

/-- Cross-extent inclusion is always false on any linear order.
    This is the algebraic core of the **cross-polar anomaly**:
    you cannot coherently compare a positive extent with a negative
    extent because they occupy complementary parts of the scale. -/
theorem crossExtent_always_false [LinearOrder D]
    (μ : Entity → D) (a b : Entity) :
    ¬ crossExtentInclusion μ a b := by
  intro h
  rcases le_total (μ a) (μ b) with hab | hba
  · -- μ a ≤ μ b: then μ a ∈ posExt, so μ a ∈ negExt μ b, i.e. μ b < μ a — contradicts μ a ≤ μ b
    exact absurd (h (le_refl (μ a))) (not_lt.mpr hab)
  · -- μ b ≤ μ a: then μ b ∈ posExt μ a, so μ b ∈ negExt μ b, i.e. μ b < μ b — impossible
    exact absurd (h hba) (lt_irrefl _)

end Core.Scale
