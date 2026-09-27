module

public import Linglib.Syntax.Case.Basic
public import Linglib.Semantics.Events.PathDir

/-!
# Spatial cases

The spatial cases decompose into a localization and a direction ([pantcheva-2011]): the
interior, surface and exterior series of Finnish, Hungarian and Daghestanian local cases each
cross a localization with Place, Goal and Source. `Case.toCase` builds a case from the two,
and `Case.spatialDecomp` recovers them where both are determinable.

## Main definitions

* `Case.dirOf`, `Case.localizationOf`: the direction and the localization a spatial case
  expresses, if any.
* `Case.toCase`, `Case.spatialDecomp`: a spatial case from its localization and direction, and
  back.

## Main results

* `Case.spatialDecomp_toCase`: the decomposition round-trips on the localization-specific cells.

## References

* [pantcheva-2011]
-/

@[expose] public section

namespace Case

open Spatial (PathDir Localization)

/-- The path direction a spatial case expresses, if any. Robust across
    the inventory — direction is determinable even on the cells where
    localization is conflated (`localizationOf` is the partial companion). The
    spatial case cells decompose as `Localization × PathDir`. -/
def dirOf : Case → Option PathDir
  | .loc | .ine | .ade | .sup => some .place
  | .ill | .all | .sub => some .goal
  | .ela | .abl | .del => some .source
  | .perl => some .route
  | _ => none

/-- Build a spatial case from its `Localization × PathDir` decomposition — the
    constructor direction spatial-case fragments consume. The 3 × 3
    localization-specific cells; `route` is localization-neutral in these
    inventories (`none`). -/
def toCase : Localization → PathDir → Option Case
  | .interior, .place => some .ine
  | .interior, .goal => some .ill
  | .interior, .source => some .ela
  | .surface, .place => some .sup
  | .surface, .goal => some .sub
  | .surface, .source => some .del
  | .exterior, .place => some .ade
  | .exterior, .goal => some .all
  | .exterior, .source => some .abl
  | _, .route => none

/-- The localization a case expresses, under the spatial reading. The
    exterior series is `ade`/`all`/`abl` (Finnish's external local
    cases). **Conflation caveat**: `all`/`abl` double as the *general*
    allative/ablative (Latin-type, localization-neutral); the spatial
    decomposition reads them as exterior-goal/source, the use the
    analytical split `Syntax/Case/Basic.lean` anticipates separating.
    `loc` is the genuinely localization-neutral general locative (`none`). -/
def localizationOf : Case → Option Localization
  | .ine | .ela | .ill => some .interior
  | .sup | .del | .sub => some .surface
  | .ade | .all | .abl => some .exterior
  | _ => none

/-- Analyze a spatial case into `Localization × PathDir`, where both are
    determinable (lossy on localization-conflated cells; the faithful inverse
    of `toCase` on the 3 × 3 localization-specific cells). -/
def spatialDecomp (c : Case) : Option (Localization × PathDir) :=
  match localizationOf c, dirOf c with
  | some r, some d => some (r, d)
  | _, _ => none

/-- `toCase` and `spatialDecomp` are inverse on the localization-specific
    cells — the decomposition round-trips where localization is not conflated.
    (`route` is localization-neutral, hence `none` on both sides.) -/
theorem spatialDecomp_toCase (r : Localization) (d : PathDir) :
    (toCase r d).bind spatialDecomp =
      (toCase r d).map (fun _ => (r, d)) := by
  cases r <;> cases d <;> decide

end Case
