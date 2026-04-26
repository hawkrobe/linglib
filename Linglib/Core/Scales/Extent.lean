import Mathlib.Order.Interval.Set.LinearOrder

/-!
# Extent Functions
@cite{kennedy-1999} Ch. 3

Algebraic primitives for Kennedy's degree-semantic extent ontology,
named aliases over Mathlib's `Set.Iic`/`Set.Ioi`.

Given a measure function `μ : Entity → D`:

* `posExt μ x = Set.Iic (μ x)` — degrees `x` "has"
* `negExt μ x = Set.Ioi (μ x)` — degrees `x` "lacks"

Both are `abbrev`s; all of Mathlib's `Iic`/`Ioi` algebra applies
transparently — partition (`Set.Iic_disjoint_Ioi`, `Set.Iic_union_Ioi`),
downward/upward closure, the lattice complement (`Set.compl_Iic`).

## Boundary convention deviation from @cite{kennedy-1999}

@cite{kennedy-1999} eqs (30)–(31) define POSδ and NEGδ both with `≤`,
placing the boundary point in BOTH (a *cover*; eqs (52)–(53) state
their join-complementarity). We use strict `<` for `negExt` (`Ioi`),
giving a strict partition. Convention impact:

* `antonymy_biconditional` (Kennedy eq (54)) is convention-INDEPENDENT
  — depends only on linear-order monotonicity.
* `crossExtent_always_false` is convention-SPECIFIC. Under Kennedy's
  ≤/≤ convention, `posExt μ a ⊆ negExt μ b` holds whenever `μ b ≤ μ a`.

## Scope: lattice-algebraic, not sortal

@cite{kennedy-1999}'s own cross-polar anomaly argument (§3.1.7) is
**sortal**: positive and negative extents are different sorts, and
the comparative DEG operator is undefined on cross-sort arguments —
an interpretation failure, not a set-inclusion non-fact. This file
models both extents as `Set D` for the same `D`, losing the sortal
structure. `crossExtent_always_false` here is a convention-specific
algebraic *consequence* of Kennedy's analysis, not the analysis
itself. A faithful sortal formalization (typed `PosExt D` / `NegExt D`
with a partial DEG) is not provided here.
-/

namespace Core.Scale

variable {Entity D : Type*}

/-- Positive extent: degrees entity `x` "has" on scale `μ`.
    Definitionally `Set.Iic (μ x)`. -/
abbrev posExt [Preorder D] (μ : Entity → D) (x : Entity) : Set D :=
  Set.Iic (μ x)

/-- Negative extent: degrees entity `x` "lacks" on scale `μ`.
    Definitionally `Set.Ioi (μ x)`. See module docstring for the
    boundary deviation from @cite{kennedy-1999}. -/
abbrev negExt [Preorder D] (μ : Entity → D) (x : Entity) : Set D :=
  Set.Ioi (μ x)

/-- Higher degree ↔ larger positive extent. -/
theorem posExt_subset_iff [Preorder D] (μ : Entity → D) (a b : Entity) :
    posExt μ a ⊆ posExt μ b ↔ μ a ≤ μ b :=
  Set.Iic_subset_Iic

/-- Strict version of `posExt_subset_iff`. -/
theorem posExt_ssubset_iff [Preorder D] (μ : Entity → D) (a b : Entity) :
    posExt μ a ⊂ posExt μ b ↔ μ a < μ b :=
  Set.Iic_ssubset_Iic

/-- Higher degree ↔ SMALLER negative extent (reverse monotonicity). -/
theorem negExt_subset_iff [LinearOrder D] (μ : Entity → D) (a b : Entity) :
    negExt μ a ⊆ negExt μ b ↔ μ b ≤ μ a :=
  Set.Ioi_subset_Ioi_iff

/-- Strict version of `negExt_subset_iff`. -/
theorem negExt_ssubset_iff [LinearOrder D] (μ : Entity → D) (a b : Entity) :
    negExt μ a ⊂ negExt μ b ↔ μ b < μ a :=
  Set.Ioi_ssubset_Ioi_iff

/-- **Antonymy biconditional** (@cite{kennedy-1999} eq (54)).

    `posExt μ b ⊂ posExt μ a  ↔  negExt μ a ⊂ negExt μ b`

    "A is taller than B" iff "B is shorter than A". Kennedy's Ch. 3
    derives this from the join-complementarity of POS/NEG extents
    (eqs (52)–(53)); under our strict-partition convention it follows
    from monotonicity, which is the linear-order fact the two
    formulations share. The linguistic content — equivalence of polar
    comparatives is *derived* from extent algebra, not stipulated as
    a lexical antonymy property — survives the convention deviation. -/
theorem antonymy_biconditional [LinearOrder D] (μ : Entity → D) (a b : Entity) :
    posExt μ b ⊂ posExt μ a ↔ negExt μ a ⊂ negExt μ b := by
  rw [posExt_ssubset_iff, negExt_ssubset_iff]

/-- `posExt` and `negExt` are set-theoretic complements on a linear order
    (`Set.compl_Iic` under the abbrev). The lattice expression of
    @cite{kennedy-1999} eqs (52)–(53)'s join-complementarity. -/
theorem compl_posExt [LinearOrder D] (μ : Entity → D) (x : Entity) :
    (posExt μ x)ᶜ = negExt μ x :=
  Set.compl_Iic

/-- Order-reversing equivalence between `posExt`- and `negExt`-inclusions.
    The Galois-antitone framing is `compl_subset_compl` specialized at
    `Iic`/`Ioi` via `compl_posExt`. Linglib's
    `Theories.Semantics.Degree.Comparative.littlePred` defines
    @cite{heim-2006}'s LITTLE as predicate complement; LITTLE is *not*
    this map (it operates on type ⟨d,t⟩, not the powerset lattice),
    but the algebraic shadow of LITTLE *is* this antitone identity. -/
theorem extent_galois_antitone [LinearOrder D] (μ : Entity → D) (a b : Entity) :
    posExt μ a ⊆ posExt μ b ↔ negExt μ b ⊆ negExt μ a := by
  rw [posExt_subset_iff, negExt_subset_iff]

/-- The set-theoretic claim of "cross-polar inclusion": that the positive
    extent of one entity is included in the negative extent of another.
    This is the LF a cross-polar equative like "Kim is as tall as Lee
    is short" would assign. -/
abbrev crossExtentInclusion [Preorder D] (μ : Entity → D) (a b : Entity) : Prop :=
  posExt μ a ⊆ negExt μ b

/-- Convention-specific cross-polar non-inclusion: under the strict-
    partition convention used here, `crossExtentInclusion` is always
    false on a linear order. **Not** @cite{kennedy-1999}'s sortal
    cross-polar anomaly argument (§3.1.7); see module docstring. -/
theorem crossExtent_always_false [LinearOrder D]
    (μ : Entity → D) (a b : Entity) : ¬ crossExtentInclusion μ a b :=
  fun h => absurd (h (min_le_left (μ a) (μ b))) (not_lt.mpr (min_le_right _ _))

end Core.Scale
