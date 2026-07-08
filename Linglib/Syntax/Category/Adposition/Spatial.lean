import Linglib.Syntax.Category.Adposition.Basic
import Linglib.Syntax.Case.Order

/-!
# Spatial adpositions: the cartographic refinement
[svenonius-2010] [svenonius-2006] [pantcheva-2011] [zwarts-2005]

The refinement a *theory* supplies for `Adposition` with `relation = .spatial`:
the Cinque-Rizzi/Svenonius decomposition of the spatial relation into
**axial part × region × direction × boundedness**. This is the spatial slice
of the universal functional sequence ([svenonius-2010]); a temporal or
grammatical adposition has none of it, which is why it refines a relation
rather than defining the category.

The decomposition **reuses the Case spatial substrate**: direction is
`Case.PathDir` (Pantcheva's Place ⊂ Goal ⊂ Source ⊂ Route) and region is
`Case.Region` — an adposition and a spatial case spell out the *same* content
([cinque, this volume]: spatial P, adverb, particle, and case all spell out
portions of one configuration). The genuinely new piece is `AxPart`, the
object-geometry axial parts ([svenonius-2006]) that case morphology lacks — and
unlike `PathDir`/`Region`, the axial parts are a **flat paradigm**, not a ranked
containment, so `AxPart` does not instantiate the `partialOrderOfRank` gadget.

## Main declarations

* `Adposition.AxPart` — Svenonius axial parts (front/back/top/…), the differentia
* `Adposition.SpatialReading` — the cartographic decomposition (the plug-in type)
* `Adposition.SpatialReading.toCase` is left to per-language Studies
-/

namespace Adposition

/-- Axial parts ([svenonius-2006]): the object-geometry regions a spatial
    adposition projects onto the Ground's axes. *behind* = `back`, *under* =
    `bottom`, *on top of* = `top`, *in front of* = `front`, *beside* = `side`,
    *inside* = `interior`, *outside* = `exterior`. A flat paradigm (the axes are
    not nested), distinct from the ranked `Case.PathDir`/`Case.Region`. -/
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
    ([svenonius-2010]): an axial part (Svenonius), a stative region (reused
    `Case.Region`), a direction (reused `Case.PathDir`, Pantcheva), and a
    boundedness ([zwarts-2005], the *separate* algebraic axis — `to` vs
    `towards`). Theories own the slices; this is the shared vocabulary that a
    `relation = .spatial` adposition is refined into. -/
structure SpatialReading where
  /-- The axial part, if the P is axial/complex (*behind*); `none` for the simple
      directional/locative Ps (*in*/*to*/*from*). -/
  axPart : Option AxPart := none
  /-- The stative region (interior/surface/exterior), reused from `Case`. -/
  region : Option Case.Region := none
  /-- The direction (Place/Goal/Source/Route), reused from `Case` (Pantcheva). -/
  direction : Case.PathDir
  /-- Boundedness ([zwarts-2005]): bounded (telic *to*) vs unbounded (atelic
      *towards*) — orthogonal to direction. -/
  bounded : Bool := false
  deriving Repr, DecidableEq

/-- The directional denotation of a spatial reading is the reused
    `Case.PathDir.denote` — a spatial adposition and a spatial case with the
    same direction share one meaning, two exponences. -/
def SpatialReading.denote (r : SpatialReading) : Case.PathProfile :=
  r.direction.denote

/-! ### Smoke tests — the differentia and the reuse -/

/-- *behind*: an axial preposition (back), stative, no direction change. -/
def behind : SpatialReading :=
  { axPart := some .back, direction := .place }

/-- *under*: axial (bottom), stative. -/
def under : SpatialReading :=
  { axPart := some .bottom, direction := .place }

/-- *into*: interior goal, bounded — no axial part (a simple directional P). -/
def into : SpatialReading :=
  { region := some .interior, direction := .goal, bounded := true }

/-- The axial parts case morphology lacks are genuinely present here. -/
example : behind.axPart = some .back := by decide
/-- A simple directional reading reuses `PathDir.denote` (the Case substrate). -/
example : into.denote = Case.PathDir.goal.denote := by rfl

end Adposition
