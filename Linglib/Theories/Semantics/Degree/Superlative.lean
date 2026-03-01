import Linglib.Core.Scales.Scale
import Linglib.Theories.Semantics.Degree.Core

/-!
# Superlative Semantics
@cite{heim-1999} @cite{sharvit-stateva-2002} @cite{szabolcsi-1986}

Compositional semantics for the superlative morpheme `-est`/`most`.

## Heim (1999): Absolute vs. Relative

Heim (1999) identifies two readings of superlatives:

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

end Semantics.Degree.Superlative
