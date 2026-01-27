/-
# Reference Game Fragments

Building blocks for RSA reference games.

## Components

- `Color`, `Shape`: Standard property types
- `Object`: Color × Shape pairs
- `Feature`: Feature utterances (colors and shapes)
- `TypedContext`: A set of objects with their available features
- `fromPairs`: Build context from (Color × Shape) list

## Usage

```lean
-- In your paper replication file:
import Linglib.Fragments.ReferenceGames

def myContext := ReferenceGame.fromPairs
  [(.blue, .square), (.blue, .circle), (.green, .square)]

#eval ReferenceGame.l1 myContext (.shape .square)
```

## References

- Frank, M. C. & Goodman, N. D. (2012). Predicting pragmatic reasoning in
  language games. Science 336(6084): 998.
-/

import Linglib.Theories.RSA.Core
import Mathlib.Data.Rat.Defs

namespace ReferenceGame

-- ============================================================================
-- Generic Reference Game Context
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

/-- Build RSAScenario from context -/
def Context.toScenario (ctx : Context) : RSAScenario :=
  RSAScenario.basicBool ctx.properties ctx.objects ctx.satisfies

-- ============================================================================
-- Standard Reference Game: Objects with Color × Shape
-- ============================================================================

/-- Colors for reference games -/
inductive Color where
  | blue | green | red | yellow | purple | orange
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Shapes for reference games -/
inductive Shape where
  | square | circle | triangle | star
  deriving Repr, DecidableEq, BEq, Inhabited

/-- An object is a color-shape pair -/
structure Object where
  color : Color
  shape : Shape
  deriving Repr, DecidableEq, BEq

instance : Inhabited Object := ⟨⟨.blue, .square⟩⟩

/-- Feature utterances (colors and shapes) -/
inductive Feature where
  | color (c : Color)
  | shape (s : Shape)
  deriving Repr, DecidableEq, BEq

/-- Does a feature apply to an object? -/
def Feature.appliesTo : Feature → Object → Bool
  | .color c, obj => obj.color == c
  | .shape s, obj => obj.shape == s

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

/-- Build RSAScenario from typed context -/
def TypedContext.toScenario (ctx : TypedContext) : RSAScenario :=
  RSAScenario.basicBool ctx.features ctx.objects (fun obj feat => feat.appliesTo obj)

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
  RSA.L0 ctx.toScenario f ()

/-- S1 distribution for an object in a typed context -/
def s1 (ctx : TypedContext) (obj : Object) : List (Feature × ℚ) :=
  RSA.S1 ctx.toScenario obj () ()

/-- L1 distribution for a feature in a typed context -/
def l1 (ctx : TypedContext) (f : Feature) : List (Object × ℚ) :=
  RSA.L1_world ctx.toScenario f

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

end ReferenceGame
