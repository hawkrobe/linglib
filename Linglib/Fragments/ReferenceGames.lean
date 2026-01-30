/-
# Reference Game Fragments

Building blocks for RSA reference games.

## Grounding in Montague Semantics

Feature predicates are type `e → t` in Montague's type system:
- Objects are entities (type `e`) defined as Color × Shape pairs
- Features are predicates: ⟦blue⟧ = λx. color(x) = blue

## Components

- `Color`, `Shape`, `Feature`: Re-exported from Montague.Lexicon.Features
- `Object`: Color × Shape pairs (reference game entities)
- `featureMeaning`: The Montague `e → t` meaning function
- `TypedContext`: A set of objects with their available features

## Usage

```lean
import Linglib.Fragments.ReferenceGames

def myContext := ReferenceGame.fromPairs
  [(.blue, .square), (.blue, .circle), (.green, .square)]

#eval ReferenceGame.l1 myContext (.shape .square)
```

## References

- Frank, M. C. & Goodman, N. D. (2012). Predicting pragmatic reasoning in
  language games. Science 336(6084): 998.
- Montague, R. (1973). The Proper Treatment of Quantification.
-/

import Linglib.Theories.RSA.Core.Basic
import Linglib.Theories.RSA.Core.Eval
import Linglib.Theories.Montague.Lexicon.Features
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Prod

namespace ReferenceGame

open Montague.Lexicon.Features

-- ============================================================================
-- Re-export Montague Feature Infrastructure
-- ============================================================================

-- Types from Montague.Lexicon.Features
abbrev Color := Montague.Lexicon.Features.Color
abbrev Shape := Montague.Lexicon.Features.Shape
abbrev Feature := Montague.Lexicon.Features.Feature

-- ============================================================================
-- Reference Game Entity Type
-- ============================================================================

/--
An object is a color-shape pair.

This is the entity type `e` for reference games. Objects are characterized
by their color and shape attributes.
-/
structure Object where
  color : Color
  shape : Shape
  deriving Repr, DecidableEq, BEq

instance : Inhabited Object := ⟨⟨.blue, .square⟩⟩

/-- Object is finite (Color × Shape) -/
instance : Fintype Object :=
  Fintype.ofEquiv (Color × Shape) {
    toFun := fun (c, s) => ⟨c, s⟩
    invFun := fun e => (e.color, e.shape)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }

-- ============================================================================
-- HasColor / HasShape Instances
-- ============================================================================

instance : Montague.Lexicon.Features.HasColor Object where
  color := Object.color

instance : Montague.Lexicon.Features.HasShape Object where
  shape := Object.shape

-- ============================================================================
-- Feature Meaning (via Montague generic)
-- ============================================================================

/-- Re-export featureMeaning specialized to Object -/
abbrev featureMeaning : Feature → Object → Bool :=
  Montague.Lexicon.Features.featureMeaning

/-- Re-export appliesTo specialized to Object -/
abbrev Feature.appliesTo (f : Feature) (obj : Object) : Bool :=
  Montague.Lexicon.Features.Feature.appliesTo f obj

-- ============================================================================
-- Theorems: Compositional Meaning
-- ============================================================================

/-- Blue applies to blue objects -/
theorem blue_applies_to_blue :
    Feature.appliesTo (.color .blue) ⟨.blue, .square⟩ = true := by native_decide

/-- Blue doesn't apply to green objects -/
theorem blue_not_green :
    Feature.appliesTo (.color .blue) ⟨.green, .square⟩ = false := by native_decide

/-- Square applies to square objects -/
theorem square_applies_to_square :
    Feature.appliesTo (.shape .square) ⟨.blue, .square⟩ = true := by native_decide

/-- Features are characteristic functions -/
theorem feature_is_characteristic (f : Feature) (obj : Object) :
    Feature.appliesTo f obj = true ↔
    (match f with
     | .color c => obj.color == c
     | .shape s => obj.shape == s) := by
  cases f <;> simp [Feature.appliesTo, Montague.Lexicon.Features.Feature.appliesTo,
                    Montague.Lexicon.Features.featureMeaning,
                    Montague.Lexicon.Features.HasColor.color,
                    Montague.Lexicon.Features.HasShape.shape]

-- ============================================================================
-- Generic Reference Game Context (String-based, for flexibility)
-- ============================================================================

/--
A reference game context: objects with their properties.

This is the minimal data needed to build an RSA scenario for a reference game.
-/
structure Context where
  /-- Object names -/
  objects : List String
  /-- Property/feature names -/
  properties : List String
  /-- Which properties each object has -/
  hasProperty : String → String → Bool

/-- Build a context from a list of (object, properties) pairs -/
def context (pairs : List (String × List String)) (_h : pairs ≠ [] := by decide) : Context :=
  let objects := pairs.map (·.1)
  let allProps := pairs.flatMap (·.2) |>.eraseDups
  let hasProperty obj prop := pairs.any fun (o, ps) => o == obj && ps.contains prop
  { objects := objects
  , properties := allProps
  , hasProperty := hasProperty
  }

/-- Literal semantics: utterance (property name) applies to object -/
def Context.satisfies (ctx : Context) (obj : String) (utt : String) : Bool :=
  ctx.hasProperty obj utt

/-- Run L1 for a context using RSA.Eval -/
def Context.runL1 (ctx : Context) (utt : String) : List (String × ℚ) :=
  RSA.Eval.basicL1 ctx.properties ctx.objects
    (fun u w => boolToRat (ctx.satisfies w u)) (fun _ => 1) 1 (fun _ => 0) utt

/--
A typed reference game context with Color × Shape objects.
-/
structure TypedContext where
  /-- Objects in the context -/
  objects : List Object
  /-- Available feature utterances -/
  features : List Feature

/-- Build typed context from objects, inferring available features -/
def TypedContext.fromObjects (objs : List Object) : TypedContext :=
  let colors := objs.map (·.color) |>.eraseDups
  let shapes := objs.map (·.shape) |>.eraseDups
  let features := colors.map Feature.color ++ shapes.map Feature.shape
  { objects := objs
  , features := features
  }

/-- Run L1 for a typed context using RSA.Eval -/
def TypedContext.runL1 (ctx : TypedContext) (feat : Feature) : List (Object × ℚ) :=
  RSA.Eval.basicL1 ctx.features ctx.objects
    (fun f o => boolToRat (f.appliesTo o)) (fun _ => 1) 1 (fun _ => 0) feat

/-- Run S1 for a typed context using RSA.Eval -/
def TypedContext.runS1 (ctx : TypedContext) (obj : Object) : List (Feature × ℚ) :=
  RSA.Eval.basicS1 ctx.features ctx.objects
    (fun f o => boolToRat (f.appliesTo o)) (fun _ => 1) 1 (fun _ => 0) obj

/-- Run L0 for a typed context using RSA.Eval -/
def TypedContext.runL0 (ctx : TypedContext) (feat : Feature) : List (Object × ℚ) :=
  RSA.Eval.basicL0 ctx.features ctx.objects
    (fun f o => boolToRat (f.appliesTo o)) (fun _ => 1) feat

-- ============================================================================
-- Convenience: Quick Context Builders
-- ============================================================================

/-- Build context with just colors (single shape) -/
def colorsOnly (colors : List Color) (shape : Shape := .square) : TypedContext :=
  TypedContext.fromObjects (colors.map fun c => ⟨c, shape⟩)

/-- Build context with just shapes (single color) -/
def shapesOnly (shapes : List Shape) (color : Color := .blue) : TypedContext :=
  TypedContext.fromObjects (shapes.map fun s => ⟨color, s⟩)

/-- Build context from color-shape pairs -/
def fromPairs (pairs : List (Color × Shape)) : TypedContext :=
  TypedContext.fromObjects (pairs.map fun (c, s) => ⟨c, s⟩)

-- ============================================================================
-- RSA Computations (Convenience wrappers)
-- ============================================================================

/-- L0 distribution for a feature in a typed context -/
def l0 (ctx : TypedContext) (f : Feature) : List (Object × ℚ) :=
  ctx.runL0 f

/-- S1 distribution for an object in a typed context -/
def s1 (ctx : TypedContext) (obj : Object) : List (Feature × ℚ) :=
  ctx.runS1 obj

/-- L1 distribution for a feature in a typed context -/
def l1 (ctx : TypedContext) (f : Feature) : List (Object × ℚ) :=
  ctx.runL1 f

-- ============================================================================
-- Example Usage
-- ============================================================================

-- Build a simple context
private def exampleCtx : TypedContext :=
  fromPairs [(.blue, .square), (.blue, .circle), (.green, .square)]

#eval l1 exampleCtx (.shape .square)
-- blue_square > green_square (pragmatic inference)

#eval s1 exampleCtx ⟨.green, .square⟩
-- green preferred (uniquely identifies)

-- ============================================================================
-- Grounding Verification
-- ============================================================================

/-- The RSA.Eval meaning function uses the compositional semantics -/
theorem rsa_eval_uses_compositional_semantics (f : Feature) (obj : Object) :
    boolToRat (f.appliesTo obj) = if f.appliesTo obj then 1 else 0 := rfl

end ReferenceGame
