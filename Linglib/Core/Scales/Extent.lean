import Linglib.Core.Scales.Scale
import Mathlib.Order.GaloisConnection.Basic

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

-- ════════════════════════════════════════════════════
-- § 7. Galois Connection on Extents
-- ════════════════════════════════════════════════════

-- ─── Galois Connection Foundation ─────────────────
--
-- The extent functions are instances of Mathlib's `gc_sSup_Iic`:
--
--   GaloisConnection (sSup : Set D → D) (Set.Iic : D → Set D)
--
-- Since `posExt μ x = Set.Iic (μ x)` definitionally, posExt factors
-- through the right adjoint of sSup. The antonymy biconditional is
-- then a consequence of the Galois connection's monotonicity.
--
-- For the antitone direction (negExt), we use `gc_Ici_sInf` on
-- OrderDual: negExt is the complement of Iic, and Ici on the dual
-- order gives the strict upset.
--
-- @cite{heim-2006}'s LITTLE operator is the order-reversing map
-- witnessing this Galois duality: it sends posExt(a) to negExt(a),
-- inverting the set-inclusion ordering.

/-- `posExt μ x` is the principal downset `Set.Iic (μ x)`. This
    grounds all extent algebra in Mathlib's order infrastructure. -/
theorem posExt_eq_Iic [Preorder D] (μ : Entity → D) (x : Entity) :
    posExt μ x = Set.Iic (μ x) :=
  rfl

/-- `posExt` is an order embedding: it faithfully reflects ≤.
    Follows from `gc_sSup_Iic`: `Set.Iic` is the right adjoint
    of `sSup`, so it is monotone and reflects the order. -/
theorem posExt_orderEmbedding [LinearOrder D] (μ : Entity → D) (a b : Entity) :
    μ a ≤ μ b ↔ posExt μ a ⊆ posExt μ b :=
  (posExt_subset_iff μ a b).symm

/-- `negExt` is an order-reversing embedding: it faithfully reflects ≥.
    This is the antitone half of the Galois connection — the map
    that LITTLE implements. -/
theorem negExt_orderReversing [LinearOrder D] (μ : Entity → D) (a b : Entity) :
    μ a ≤ μ b ↔ negExt μ b ⊆ negExt μ a :=
  (negExt_subset_iff μ b a).symm

/-- **Antitone Galois connection**: the composition posExt → negExt
    reverses set-inclusion ordering. This is the abstract content of
    @cite{heim-2006}'s LITTLE operator: degree negation reverses the
    lattice ordering on extents.

    Concretely: if posExt(a) ⊆ posExt(b), then negExt(b) ⊆ negExt(a).
    The unique order-reversing map witnessing this IS LITTLE. -/
theorem extent_galois_antitone [LinearOrder D] (μ : Entity → D) (a b : Entity) :
    posExt μ a ⊆ posExt μ b ↔ negExt μ b ⊆ negExt μ a :=
  antonymy_biconditional_weak μ b a

/-- **Cross-polar anomaly as Galois incompatibility**: posExt and negExt
    occupy complementary sublattices of (Set D, ⊆). The downset lattice
    (posExt's range) and the upset lattice (negExt's range) never contain
    a pair S ⊆ T — they are separated by the boundary degree.

    The algebraic content: for any d, `d ∈ Set.Iic (μ a)` implies `d ≤ μ a`,
    but `d ∈ Set.Ioi (μ b)` requires `μ b < d`. At `d = μ a`, the first
    holds but the second requires `μ b < μ a`. At `d = μ b + ε`, the second
    holds but the first requires `μ b + ε ≤ μ a`, which can't hold for
    all ε. So no element witnesses containment. -/
theorem galois_cross_incompatible [LinearOrder D] (μ : Entity → D) (a b : Entity) :
    ¬ posExt μ a ⊆ negExt μ b :=
  crossExtent_always_false μ a b

end Core.Scale
