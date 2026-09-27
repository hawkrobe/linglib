module

public import Linglib.Syntax.Category.Adposition.Basic
public import Linglib.Semantics.Events.PathDir

/-!
# Spatial adpositions: the cartographic refinement

The refinement a theory supplies for `Adposition` with `relation = .spatial`: the decomposition
of the spatial relation into axial part, localization, direction and boundedness
([svenonius-2010]). This is the spatial slice of the universal functional sequence; a temporal
or grammatical adposition has none of it, which is why it refines a relation rather than
defining the category.

The direction is `Spatial.PathDir`, [pantcheva-2011]'s Place ⊂ Goal ⊂ Source ⊂ Route, and the
localization is `Spatial.Localization`, the vocabulary spatial cases decompose into as well, so
that a spatial adposition and a spatial case with the same direction denote the same paths
(`Spatial.PathDir.denote`). The new piece is `AxPart`, the object-geometry axial parts
([svenonius-2006]) that case morphology lacks; unlike the directions, the axial parts are a
flat paradigm, not a ranked containment. Boundedness is [zwarts-2005]'s separate axis, *to*
against *towards*.

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

/-- Axial parts ([svenonius-2006]): the object-geometry regions a spatial
    adposition projects onto the Ground's axes. *behind* = `back`, *under* =
    `bottom`, *on top of* = `top`, *in front of* = `front`, *beside* = `side`,
    *inside* = `interior`, *outside* = `exterior`. A flat paradigm (the axes are
    not nested), distinct from the ranked `Spatial.PathDir`/`Spatial.Localization`. -/
inductive AxPart where
  | front
  | back
  | top
  | bottom
  | side
  | interior
  | exterior
  deriving DecidableEq, Repr, Fintype

/-- The cartographic decomposition of a spatial adposition's `relation`
    ([svenonius-2010]): an axial part, a localization (`Spatial.Localization`), a direction
    (`Spatial.PathDir`, [pantcheva-2011]), and a
    boundedness ([zwarts-2005], the *separate* algebraic axis — `to` vs
    `towards`). Theories own the slices; this is the shared vocabulary that a
    `relation = .spatial` adposition is refined into. -/
structure SpatialReading where
  /-- The axial part, if the P is axial/complex (*behind*); `none` for the simple
      directional/locative Ps (*in*/*to*/*from*). -/
  axPart : Option AxPart := none
  /-- The localization, interior, surface or exterior. -/
  localization : Option Spatial.Localization := none
  /-- The direction, Place, Goal, Source or Route. -/
  direction : Spatial.PathDir
  /-- Boundedness ([zwarts-2005]): bounded (telic *to*) vs unbounded (atelic
      *towards*) — orthogonal to direction. -/
  bounded : Bool := false
  deriving Repr, DecidableEq

/-- The paths a spatial reading denotes relative to a region, those its direction denotes: a
spatial adposition and a spatial case with the same direction share one meaning, two
exponences. -/
def SpatialReading.denote {Loc : Type*} (r : SpatialReading) (R : Set Loc) :
    Set (Spatial.Path Loc) :=
  r.direction.denote R

/-! ### Smoke tests — the differentia and the reuse -/

/-- *behind*: an axial preposition (back), stative, no direction change. -/
def behind : SpatialReading :=
  { axPart := some .back, direction := .place }

/-- *under*: axial (bottom), stative. -/
def under : SpatialReading :=
  { axPart := some .bottom, direction := .place }

/-- *into*: interior goal, bounded — no axial part (a simple directional P). -/
def into : SpatialReading :=
  { localization := some .interior, direction := .goal, bounded := true }

/-- The axial parts case morphology lacks are genuinely present here. -/
example : behind.axPart = some .back := by decide
/-- A simple directional reading denotes what its direction denotes. -/
example (R : Set ℕ) : into.denote R = Spatial.PathDir.goal.denote R := rfl

end Adposition
