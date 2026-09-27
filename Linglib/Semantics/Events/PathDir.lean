module

public import Linglib.Semantics.Events.Path
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.Disjoint
public import Mathlib.Tactic.DeriveFintype

/-!
# Path directions

The directions a path can take relative to a place, in [pantcheva-2011]'s containment order
Place ⊂ Goal ⊂ Source ⊂ Route: a Source path structurally contains a Goal path, reflected where
the Source marker contains the Goal marker (Imbabura Quechua Goal *-man* ⊂ Source *-man-da*).
A direction denotes the paths that take it relative to a region, [zwarts-2005]'s paths
classified by where they start, pass and end: a Place path stays in the region, a Goal path
ends in it having started outside, a Source path does the reverse, and a Route path passes
through it, starting and ending outside. [pantcheva-2011]'s phase profiles are these
conditions, and Source being the reversal of Goal is a theorem about paths
(`PathDir.mem_denote_source_iff`), so that no path is both a Goal and a Source path
(`PathDir.disjoint_denote_goal_source`), the contradiction behind the *A&¬A constraint on
syncretism. Orthogonal to the direction is the localization a spatial expression picks out
within the reference object: interior, surface or exterior.

## Main definitions

* `Spatial.PathDir`: Place, Goal, Source and Route, with the containment rank and shells.
* `Spatial.PathDir.denote`: the paths that take a direction relative to a region.
* `Spatial.PathDir.reverse`: the direction of a reversed path.
* `Spatial.Localization`: interior, surface or exterior.

## Main results

* `Spatial.PathDir.lt_iff_shells_ssubset`: the containment order is strict inclusion of shell
  stacks.
* `Spatial.PathDir.reverse_mem_denote_iff`: reversing a path reverses its direction, so a
  Source path is a reversed Goal path (`Spatial.PathDir.mem_denote_source_iff`).
* `Spatial.PathDir.disjoint_denote_goal_source`: no path is both a Goal and a Source path.

## References

* [pantcheva-2011]
* [zwarts-2005]
-/

@[expose] public section

namespace Spatial

/-! ### Directions and their containment -/

/-- The path-direction heads, in containment order Place ⊂ Goal ⊂ Source ⊂ Route
([pantcheva-2011]). -/
inductive PathDir where
  /-- Place: static location, the locative base. -/
  | place
  /-- Goal: motion *to*, built on Place. -/
  | goal
  /-- Source: motion *from*, built on Goal. -/
  | source
  /-- Route: motion *via* or *through*, built on Source. -/
  | route
  deriving DecidableEq, Repr, Fintype

/-- Containment rank: how many path heads the direction nests. -/
def PathDir.rank : PathDir → Fin 4
  | .place => 0
  | .goal => 1
  | .source => 2
  | .route => 3

/-- The shell stack of a direction: the downward-closed set of path heads its structure
contains, [pantcheva-2011]'s nested [Route [Source [Goal [Place]]]]. -/
def PathDir.shells (d : PathDir) : Finset (Fin 4) := Finset.Iic d.rank

/-- The containment order is the shadow of the decomposition: strict rank is strict inclusion
of shell stacks. -/
theorem PathDir.lt_iff_shells_ssubset (d₁ d₂ : PathDir) :
    d₁.rank < d₂.rank ↔ d₁.shells ⊂ d₂.shells := by
  simp [PathDir.shells]

/-! ### Denotation -/

variable {Loc : Type*}

/-- The paths that take direction `d` relative to the region `R`: a Place path stays in it, a
Goal path ends in it having started outside, a Source path starts in it and ends outside, and a
Route path passes through it, starting and ending outside. -/
def PathDir.denote (d : PathDir) (R : Set Loc) : Set (Path Loc) :=
  match d with
  | .place => {p | ∀ x ∈ p.points, x ∈ R}
  | .goal => {p | p.source ∉ R ∧ p.goal ∈ R}
  | .source => {p | p.source ∈ R ∧ p.goal ∉ R}
  | .route => {p | p.source ∉ R ∧ p.goal ∉ R ∧ ∃ x ∈ p.points, x ∈ R}

/-- The direction of a path traversed the other way: Goal and Source swap, and Place and Route
are their own reverses. -/
def PathDir.reverse : PathDir → PathDir
  | .goal => .source
  | .source => .goal
  | d => d

/-- Reversing a path reverses its direction. -/
theorem PathDir.reverse_mem_denote_iff (d : PathDir) {R : Set Loc} {p : Path Loc} :
    p.reverse ∈ d.denote R ↔ p ∈ d.reverse.denote R := by
  cases d <;> simp [denote, PathDir.reverse, and_comm, and_left_comm]

/-- A Source path is a Goal path traversed the other way. -/
theorem PathDir.mem_denote_source_iff {R : Set Loc} {p : Path Loc} :
    p ∈ source.denote R ↔ p.reverse ∈ goal.denote R :=
  (goal.reverse_mem_denote_iff).symm

/-- No path is both a Goal and a Source path: one marker for both would denote a path and its
reverse at once. -/
theorem PathDir.disjoint_denote_goal_source (R : Set Loc) :
    Disjoint (goal.denote R) (source.denote R) :=
  Set.disjoint_left.2 fun _ hg hs ↦ hg.1 hs.1

/-! ### Localization -/

/-- The part of the reference object a spatial expression localizes in, orthogonal to the
direction. -/
inductive Localization where
  /-- Interior: in, into, out of. -/
  | interior
  /-- Surface: on, onto, off. -/
  | surface
  /-- Exterior: at, to, from. -/
  | exterior
  deriving DecidableEq, Repr, Fintype

end Spatial
