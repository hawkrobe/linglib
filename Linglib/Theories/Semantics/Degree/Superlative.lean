import Linglib.Core.Scales.Extent
import Linglib.Theories.Semantics.Degree.Core
import Linglib.Theories.Semantics.Degree.Comparative

/-!
# Superlative Semantics
@cite{heim-1999} @cite{sharvit-stateva-2002} @cite{szabolcsi-1986}

Compositional semantics for the superlative morpheme `-est`/`most`.

## @cite{heim-1999}: Absolute vs. Relative

@cite{heim-1999} identifies two readings of superlatives:

- **Absolute**: "Kim climbed the highest mountain" = the mountain that
  is highest of all mountains.
  ⟦-est⟧ = λC.λG.λx. x ∈ C ∧ ∀y ∈ C, y ≠ x → G(x) > G(y)

- **Relative**: "KIM climbed the highest mountain" = the mountain that
  Kim climbed is higher than what anyone else climbed.
  Focus on "Kim" determines the comparison set.

The two readings arise from the scope of `-est` relative to other
operators: wide scope yields relative, narrow scope yields absolute.

-/

namespace Semantics.Degree.Superlative

-- ════════════════════════════════════════════════════
-- § 1. Absolute Superlative
-- ════════════════════════════════════════════════════

/-- Absolute superlative: x is the G-est entity in comparison class C.
    "The tallest mountain" = the mountain x in C such that for all
    y ≠ x in C, height(x) > height(y). -/
def absoluteSuperlative {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (C : Set Entity) (x : Entity) : Prop :=
  x ∈ C ∧ ∀ y ∈ C, y ≠ x → μ x > μ y

-- ════════════════════════════════════════════════════
-- § 2. Relative Superlative
-- ════════════════════════════════════════════════════

/-- Relative superlative: x has a higher degree than all focus
    alternatives. "KIM climbed the highest mountain" = Kim's mountain
    is higher than anyone else's.

    `f` maps each alternative (person) to the relevant entity
    (the mountain they climbed). Focus alternatives determine
    the comparison. -/
def relativeSuperlative {Alt Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (f : Alt → Entity) (focusedAlt : Alt)
    (alternatives : Set Alt) : Prop :=
  ∀ a ∈ alternatives, a ≠ focusedAlt → μ (f focusedAlt) > μ (f a)

-- ════════════════════════════════════════════════════
-- § 3. Uniqueness and Definiteness
-- ════════════════════════════════════════════════════

/-- The absolute superlative is unique (at most one entity satisfies it)
    when the ordering is strict. -/
theorem absolute_unique {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (C : Set Entity) (x y : Entity)
    (hx : absoluteSuperlative μ C x) (hy : absoluteSuperlative μ C y) :
    x = y := by
  by_contra hne
  have h1 := hx.2 y hy.1 (Ne.symm hne)
  have h2 := hy.2 x hx.1 hne
  exact absurd h1 (not_lt.mpr (le_of_lt h2))

-- ════════════════════════════════════════════════════
-- § 4. Order-Theoretic Foundation
-- ════════════════════════════════════════════════════

/-- The absolute superlative entails that `μ(x)` is the greatest
    element of the degree image `μ '' C`. Strict `>` for distinct
    entities implies `≥` for all.

    The converse fails: `IsGreatest` allows ties (`μ x = μ y`),
    while `absoluteSuperlative` requires strict dominance. -/
theorem absoluteSuperlative_isGreatest {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (C : Set Entity) (x : Entity)
    (h : absoluteSuperlative μ C x) :
    IsGreatest (μ '' C) (μ x) := by
  refine ⟨Set.mem_image_of_mem μ h.1, fun d hd => ?_⟩
  obtain ⟨y, hy, rfl⟩ := hd
  rcases eq_or_ne y x with rfl | hne
  · exact le_refl _
  · exact le_of_lt (h.2 y hy hne)

-- ════════════════════════════════════════════════════
-- § 5. Superlative as Universal Comparative
-- ════════════════════════════════════════════════════

/-- **Superlative = universal comparative** (@cite{heim-1999}):
    "x is the tallest in C" iff "x is taller than every other y in C".

    The superlative universally quantifies over the comparative:
    ⟦-est⟧ applies ⟦-er⟧ to every alternative in the comparison class.
    This semantic decomposition is the reflex of @cite{bobaljik-2012}'s
    morphosyntactic containment hypothesis (`[[[ADJ] CMPR] SPRL]`). -/
theorem superlative_iff_universal_comparative {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (C : Set Entity) (x : Entity) :
    absoluteSuperlative μ C x ↔
      x ∈ C ∧ ∀ y ∈ C, y ≠ x →
        Semantics.Degree.Comparative.comparativeSem μ x y .positive := by
  simp [absoluteSuperlative, Semantics.Degree.Comparative.comparativeSem]

end Semantics.Degree.Superlative
