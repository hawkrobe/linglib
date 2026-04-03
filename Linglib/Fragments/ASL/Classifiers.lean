import Linglib.Theories.Semantics.Iconic.Basic

/-!
# ASL Classifier Predicates
@cite{schlenker-lamberton-2024} @cite{schlenker-lamberton-lamberton-2026}

Lexical entries for ASL classifier predicates used in the elicited paradigms
of @cite{schlenker-lamberton-lamberton-2026}. Each classifier has a handshape
that iconically represents a class of objects, and its position/movement in
signing space is interpreted relative to a viewpoint.

## Classifiers

| Gloss | Handshape | Object class |
|-------|-----------|-------------|
| TREE-cl | 1-hand (upright index finger) | trees |
| POLE-cl | 1-hand (upright index finger) | poles, posts |
| PERSON-cl | index finger (upright) | people |
| VEHICLE-cl | 3-hand (thumb + index + middle) | vehicles, cars |
| WALL-cl | open hand (upright, flat) | walls, flat surfaces |
| RECTANGLE-cl | two-handed rectangle | rectangular objects |
| CORNER-cl | two-handed L-shape | corners |
-/

namespace Fragments.ASL

open Semantics.Iconic

-- ════════════════════════════════════════════════════════════════
-- § Signing Space
-- ════════════════════════════════════════════════════════════════

/-- Abstract signing space. The position type for ASL classifier
    predicates. Concrete spatial geometry (Cartesian coordinates,
    scaling factors) is left for future extension. -/
opaque SigningSpace : Type := Unit

/-- An entity type for ASL classifier constructions. -/
inductive Entity where
  | ann       -- character in the elicited paradigms
  | tree      -- a tree
  | pole      -- a pole / post
  | house     -- a house
  | vehicle   -- a car / vehicle
  | wall      -- a wall
  | corner    -- a corner
  | rectangle -- a rectangular object
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════════
-- § Lexical Predicates
-- ════════════════════════════════════════════════════════════════

/-- Logical predicate: is the entity a tree? -/
def isTree : Entity → Bool
  | .tree => true
  | _ => false

/-- Logical predicate: is the entity a pole? -/
def isPole : Entity → Bool
  | .pole => true
  | _ => false

/-- Logical predicate: is the entity a person? -/
def isPerson : Entity → Bool
  | .ann => true
  | _ => false

/-- Logical predicate: is the entity a vehicle? -/
def isVehicle : Entity → Bool
  | .vehicle => true
  | _ => false

/-- Logical predicate: is the entity a wall or flat surface? -/
def isWall : Entity → Bool
  | .wall => true
  | _ => false

/-- Logical predicate: is the entity a rectangular object? -/
def isRectangle : Entity → Bool
  | .rectangle => true
  | _ => false

/-- Logical predicate: is the entity a corner? -/
def isCorner : Entity → Bool
  | .corner => true
  | _ => false

-- ════════════════════════════════════════════════════════════════
-- § Classifier Entries
-- ════════════════════════════════════════════════════════════════

-- Projection functions are opaque — we only need their type signatures.
-- The geometric details (3D projection from viewpoint to signing space)
-- are left abstract.
variable (proj : Entity → StaticViewpoint SigningSpace → Bool)

/-- TREE-cl: 1-handshape classifier for trees.
    Viewpoint variable π₀ (free by default). -/
def treeCl : ClassifierPred Entity SigningSpace where
  logical := isTree
  projects := proj
  viewpointVar := .free 0
  label := "TREE-cl"

/-- POLE-cl: 1-handshape classifier for poles.
    Viewpoint variable π₀ (free by default). -/
def poleCl : ClassifierPred Entity SigningSpace where
  logical := isPole
  projects := proj
  viewpointVar := .free 0
  label := "POLE-cl"

/-- PERSON-cl: index finger classifier for people.
    Viewpoint variable π₀ (free by default). -/
def personCl : ClassifierPred Entity SigningSpace where
  logical := isPerson
  projects := proj
  viewpointVar := .free 0
  label := "PERSON-cl"

/-- VEHICLE-cl: 3-handshape classifier for vehicles.
    Viewpoint variable π₀ (free by default). -/
def vehicleCl : ClassifierPred Entity SigningSpace where
  logical := isVehicle
  projects := proj
  viewpointVar := .free 0
  label := "VEHICLE-cl"

/-- WALL-cl: open hand classifier for walls / flat surfaces. -/
def wallCl : ClassifierPred Entity SigningSpace where
  logical := isWall
  projects := proj
  viewpointVar := .free 0
  label := "WALL-cl"

/-- RECTANGLE-cl: two-handed classifier for rectangular objects. -/
def rectangleCl : ClassifierPred Entity SigningSpace where
  logical := isRectangle
  projects := proj
  viewpointVar := .free 0
  label := "RECTANGLE-cl"

/-- CORNER-cl: two-handed L-shape classifier for corners. -/
def cornerCl : ClassifierPred Entity SigningSpace where
  logical := isCorner
  projects := proj
  viewpointVar := .free 0
  label := "CORNER-cl"

-- ════════════════════════════════════════════════════════════════
-- § Viewpoint Variable Agreement
-- ════════════════════════════════════════════════════════════════

/-- All default classifiers use free viewpoint variables. -/
theorem treeCl_free : (treeCl proj).viewpointVar = .free 0 := rfl
theorem poleCl_free : (poleCl proj).viewpointVar = .free 0 := rfl
theorem personCl_free : (personCl proj).viewpointVar = .free 0 := rfl
theorem vehicleCl_free : (vehicleCl proj).viewpointVar = .free 0 := rfl

end Fragments.ASL
