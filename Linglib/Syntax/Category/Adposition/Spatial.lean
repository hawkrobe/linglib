module

public import Linglib.Syntax.Category.Adposition.Basic
public import Linglib.Semantics.Events.PathDir

/-!
# Spatial adpositions

A theory refines a spatial `Adposition` by decomposing its relation into an axial part, a
localization, a direction and a boundedness, as Svenonius does in the cartographic sequence. The
direction is `Spatial.PathDir`, Pantcheva's Place, Goal, Source and Route, and the localization
is `Spatial.Localization`, the vocabulary spatial cases decompose into as well. The axial parts
are what case morphology lacks, a flat paradigm rather than a ranked containment, and
boundedness is Zwarts's separate axis, *to* against *towards*.

## Main declarations

* `Adposition.AxPart`: the axial parts (front, back, top, …).
* `Adposition.SpatialReading`: the cartographic decomposition.
* `Adposition.SpatialReading.denote`: the paths a spatial reading denotes relative to a region.

## References

* [svenonius-2010]
* [svenonius-2006]
* [pantcheva-2011]
* [zwarts-2005]
-/

@[expose] public section

namespace Adposition

/-- The axial parts are the regions a spatial adposition projects onto the Ground's axes, as
*behind* projects `back` and *under* `bottom`. -/
inductive AxPart where
  | front
  | back
  | top
  | bottom
  | side
  | interior
  | exterior
  deriving DecidableEq, Repr, Fintype

/-- A spatial reading decomposes a spatial adposition's relation into an axial part, a
localization, a direction and a boundedness. -/
structure SpatialReading where
  /-- The axial part of an axial adposition such as *behind*; `none` for *in*, *to*,
  *from*. -/
  axPart : Option AxPart := none
  /-- The localization, interior, surface or exterior. -/
  localization : Option Spatial.Localization := none
  /-- The direction, Place, Goal, Source or Route. -/
  direction : Spatial.PathDir
  /-- The reading is bounded, telic *to*, rather than unbounded, atelic *towards*. -/
  bounded : Bool := false
  deriving Repr, DecidableEq

/-- A spatial reading denotes, relative to a region, the paths its direction denotes. -/
def SpatialReading.denote {Loc : Type*} (r : SpatialReading) (R : Set Loc) :
    Set (Spatial.Path Loc) :=
  r.direction.denote R

/-! ### Readings -/

/-- The reading of *behind* is axial (back) and stative. -/
def behind : SpatialReading :=
  { axPart := some .back, direction := .place }

/-- The reading of *under* is axial (bottom) and stative. -/
def under : SpatialReading :=
  { axPart := some .bottom, direction := .place }

/-- The reading of *into* is a bounded interior goal with no axial part. -/
def into : SpatialReading :=
  { localization := some .interior, direction := .goal, bounded := true }

/-- The axial parts case morphology lacks are genuinely present here. -/
example : behind.axPart = some .back := by decide
/-- A simple directional reading denotes what its direction denotes. -/
example (R : Set ℕ) : into.denote R = Spatial.PathDir.goal.denote R := rfl

end Adposition
