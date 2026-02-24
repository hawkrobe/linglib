import Linglib.Core.Scales.Scale
import Linglib.Theories.Semantics.Degree.Core

/-!
# Equative Semantics

Compositional semantics for equative constructions ("as tall as").

## At-Least vs. Exactly

The literal semantics of the equative is "at least as tall as" (≥).
The "exactly as tall as" reading arises via scalar implicature:
the speaker chose "as tall as" over the stronger "taller than",
implicating that "taller than" is false, yielding equality.

This parallels numeral strengthening: "three" literally means "at least
three" and is strengthened to "exactly three" by implicature.

## References

- Rett, J. (2020). Separate but equal: A typology of equative constructions.
- Kennedy, C. (2007). Vagueness and grammar.
- Schwarzschild, R. (2008). The semantics of comparatives.
-/

namespace Semantics.Degree.Equative

open Core.Scale

-- ════════════════════════════════════════════════════
-- § 1. Literal (At-Least) Semantics
-- ════════════════════════════════════════════════════

/-- Equative literal semantics: "A is as tall as B" iff μ(A) ≥ μ(B).
    This is the "at least as" reading. -/
def equativeLiteral {Entity D : Type*} [Preorder D]
    (μ : Entity → D) (a b : Entity) : Prop :=
  μ a ≥ μ b

-- ════════════════════════════════════════════════════
-- § 2. Strengthened (Exactly) Semantics
-- ════════════════════════════════════════════════════

/-- Equative strengthened semantics: "A is as tall as B" iff μ(A) = μ(B).
    This is the "exactly as" reading, derived by implicature. -/
def equativeStrengthened {Entity D : Type*} [Preorder D]
    (μ : Entity → D) (a b : Entity) : Prop :=
  μ a = μ b

/-- The strengthened reading entails the literal reading. -/
theorem strengthened_entails_literal {Entity D : Type*} [Preorder D]
    (μ : Entity → D) (a b : Entity) :
    equativeStrengthened μ a b → equativeLiteral μ a b := by
  intro h
  exact le_of_eq h.symm

-- ════════════════════════════════════════════════════
-- § 3. Negated Equative
-- ════════════════════════════════════════════════════

/-- Negated equative: "A is not as tall as B" iff μ(A) < μ(B).
    Negation of the at-least semantics yields strict less-than. -/
def negatedEquative {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a b : Entity) : Prop :=
  μ a < μ b

/-- Negated equative is the negation of the literal equative. -/
theorem negated_iff_not_literal {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a b : Entity) :
    negatedEquative μ a b ↔ ¬ equativeLiteral μ a b := by
  simp [negatedEquative, equativeLiteral, not_le]

end Semantics.Degree.Equative
