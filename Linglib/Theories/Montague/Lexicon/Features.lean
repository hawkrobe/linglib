/-
# Montague Semantics: Feature Predicates

Feature types for reference game domains following Montague's type theory.

## Semantic Analysis

In reference games (Frank & Goodman 2012), utterances like "blue" or "square"
are predicates over objects. In Montague's type system:

- Objects are entities (type `e`)
- Features are predicates (type `e → t`)
- ⟦blue⟧ = λx. color(x) = blue
- ⟦square⟧ = λx. shape(x) = square

## Architecture

This module provides the feature vocabulary (Color, Shape, Feature).
The reference game entity type and meaning functions are in `Fragments/ReferenceGames`.

## References

- Frank, M. C. & Goodman, N. D. (2012). Predicting pragmatic reasoning in
  language games. Science 336(6084): 998.
- Montague, R. (1973). The Proper Treatment of Quantification in Ordinary English.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum

namespace Montague.Lexicon.Features

-- ============================================================================
-- Feature Types (Color, Shape)
-- ============================================================================

/-- Colors for reference game objects -/
inductive Color where
  | blue | green | red | yellow | purple | orange
  deriving Repr, DecidableEq, BEq, Inhabited

instance : Fintype Color where
  elems := {.blue, .green, .red, .yellow, .purple, .orange}
  complete := fun c => by cases c <;> decide

instance : ToString Color where
  toString
    | .blue => "blue"
    | .green => "green"
    | .red => "red"
    | .yellow => "yellow"
    | .purple => "purple"
    | .orange => "orange"

/-- Shapes for reference game objects -/
inductive Shape where
  | square | circle | triangle | star
  deriving Repr, DecidableEq, BEq, Inhabited

instance : Fintype Shape where
  elems := {.square, .circle, .triangle, .star}
  complete := fun s => by cases s <;> decide

instance : ToString Shape where
  toString
    | .square => "square"
    | .circle => "circle"
    | .triangle => "triangle"
    | .star => "star"

-- ============================================================================
-- Entity Interfaces
-- ============================================================================

/-- Typeclass for entities that have a color attribute -/
class HasColor (E : Type) where
  color : E → Color

/-- Typeclass for entities that have a shape attribute -/
class HasShape (E : Type) where
  shape : E → Shape

-- ============================================================================
-- Feature Predicates
-- ============================================================================

/--
A feature is either a color or a shape predicate.

In Montague's terms, features have type `e → t` (predicates over entities).
-/
inductive Feature where
  | color (c : Color)
  | shape (s : Shape)
  deriving Repr, DecidableEq, BEq

instance : Inhabited Feature := ⟨.color .blue⟩

/-- Feature is finite (Color + Shape) -/
instance : Fintype Feature :=
  Fintype.ofEquiv (Color ⊕ Shape) {
    toFun := fun | .inl c => .color c | .inr s => .shape s
    invFun := fun | .color c => .inl c | .shape s => .inr s
    left_inv := fun | .inl _ => rfl | .inr _ => rfl
    right_inv := fun | .color _ => rfl | .shape _ => rfl
  }

-- ============================================================================
-- Feature Meaning (Generic)
-- ============================================================================

/--
The Montague meaning of a feature predicate.

This is generic over any entity type with color and shape attributes.
Each feature denotes a characteristic function from entities to truth values:

- ⟦color c⟧ = λx. color(x) = c
- ⟦shape s⟧ = λx. shape(x) = s
-/
def featureMeaning {E : Type} [HasColor E] [HasShape E] : Feature → E → Bool
  | .color c, obj => HasColor.color obj == c
  | .shape s, obj => HasShape.shape obj == s

/-- Apply a feature predicate to an entity -/
def Feature.appliesTo {E : Type} [HasColor E] [HasShape E] (f : Feature) (obj : E) : Bool :=
  featureMeaning f obj

-- ============================================================================
-- Feature Lexicon
-- ============================================================================

/-- Lookup a feature by name -/
def featureLexicon : String → Option Feature
  | "blue" => some (.color .blue)
  | "green" => some (.color .green)
  | "red" => some (.color .red)
  | "yellow" => some (.color .yellow)
  | "purple" => some (.color .purple)
  | "orange" => some (.color .orange)
  | "square" => some (.shape .square)
  | "circle" => some (.shape .circle)
  | "triangle" => some (.shape .triangle)
  | "star" => some (.shape .star)
  | _ => none

end Montague.Lexicon.Features
