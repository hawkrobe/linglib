module

public import Linglib.Syntax.Case.Basic
public import Linglib.Semantics.Events.PathDir

/-!
# Spatial cases

A spatial case combines a localization with a direction, as Pantcheva decomposes them: the
interior, surface and exterior series of Finnish, Hungarian and Daghestanian local cases each
cross a localization with Place, Goal and Source. The general locative, allative, ablative and
perlative express a direction with no localization. Blake's types of case (Table 2.7) place
the spatial cases among the semantic cases, apart from the grammatical ones.

## Main definitions

* `Case.dirOf`, `Case.localizationOf`: the direction and the localization a spatial case
  expresses, if any.
* `Case.toCase`, `Case.spatialDecomp`: a spatial case from its localization and direction, and
  back.
* `Case.ofDir`: the localization-neutral case of a direction.
* `Case.Kind`, `Case.kind`: grammatical, spatial and other semantic cases.

## Main results

* `Case.spatialDecomp_toCase`: the decomposition round-trips on the localization-specific cells.
* `Case.dirOf_ofDir`: the localization-neutral case of a direction expresses it.
* `Case.kind_eq_spatial_iff`: the spatial cases are those with a direction, and the
  terminative.

## Implementation notes

Blake names the nominative, accusative, ergative, genitive and dative as grammatical cases;
`Case.kind` adds the absolutive, the oblique, the partitive and the vocative to them, and the
terminative to the spatial cases.

## References

* [pantcheva-2011]
* [blake-2001]
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

/-- The localization a case expresses, under the spatial reading. The exterior series is
    `ade`, `all` and `abl`, Finnish's external local cases; `all` and `abl` also serve as the
    general allative and ablative, with no localization, a use this decomposition does not
    separate. The general locative `loc` has no localization. -/
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

/-- `ofDir d` is the case that expresses `d` with no localization, the general locative,
allative, ablative or perlative. -/
def ofDir : PathDir → Case
  | .place => .loc
  | .goal => .all
  | .source => .abl
  | .route => .perl

@[simp] theorem dirOf_ofDir (d : PathDir) : (ofDir d).dirOf = some d := by
  cases d <;> rfl

theorem ofDir_injective : Function.Injective ofDir := by
  intro d d' h
  simpa using congrArg dirOf h

/-! ### Types of case -/

/-- A case is grammatical, encoding a syntactic relation, or semantic, and a semantic case is
spatial when it encodes location, source, destination or path. -/
inductive Kind where
  /-- A grammatical case is a core case, the genitive or the dative. -/
  | grammatical
  /-- A spatial case encodes location, source, destination or path, alone or with another
  notion. -/
  | spatial
  /-- A semantic case that is not spatial, such as the instrumental and the comitative. -/
  | semantic
  deriving DecidableEq, Repr, Fintype

/-- The type of a case value. -/
def kind : Case → Kind
  | .nom | .acc | .gen | .dat | .erg | .abs | .obl | .part | .voc => .grammatical
  | .loc | .ine | .ade | .sup | .ill | .all | .sub | .ela | .abl | .del | .perl | .ter =>
    .spatial
  | .inst | .com | .ben | .abess | .caus | .tem | .ess | .transl => .semantic

theorem kind_eq_spatial_iff (c : Case) : c.kind = .spatial ↔ c.dirOf.isSome ∨ c = .ter := by
  cases c <;> decide

theorem kind_eq_spatial_of_dirOf_isSome {c : Case} (h : c.dirOf.isSome) : c.kind = .spatial :=
  (kind_eq_spatial_iff c).2 (.inl h)

end Case
