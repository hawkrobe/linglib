import Linglib.Core.Order.Boundedness
import Mathlib.Data.List.Infix

/-!
# Spatial paths

Directed trajectories between locations, as finite location sequences — the
spatial analog of temporal intervals, carrying [zwarts-2005]'s Appendix A path
algebra in discrete form: partial concatenation (defined only head-to-tail),
the subpath order, and endpoint-sharing adjacency ([krifka-1998]). Zwarts's
own paths are continuous constant-speed curves `[0,1] → ℝ³` — mathlib's
topological `_root_.Path`, whose `trans` reparametrizes, so the algebra would
need the arc-length quotient there; the paper endorses the constructive
sequence-of-places route as equally compatible with the algebra, and it keeps
every operation computable.

## Main declarations

* `Path`: a directed trajectory — `source` plus later `steps`, with endpoint
  `Path.goal`; `Path.const` is the constant path, the identity of
  concatenation and least in the subpath order.
* `Path.IsConcat`: concatenation as in [zwarts-2005]'s (67) — `r` is `p + q`,
  defined only when `p` ends where `q` starts; associative, neither
  commutative nor idempotent.
* `Path.Subpath`: the subpath order of (68) — `p ≤ q` iff `r + p + r′ = q`
  for some `r`, `r′`; equivalently infix-hood of point sequences
  (`Path.subpath_iff_infix`), whence a scoped `PartialOrder`
  (`open scoped Spatial.Path`).
* `Path.adjacent`: endpoint-sharing spatial adjacency ([krifka-1998]), the
  spatial half of the movement relations in `Studies/Krifka1998.lean`.
* `PathShape`: [zwarts-2005]'s boundedness classification of directional PPs,
  with `PathShape.toBoundedness` into `Core.Order.Boundedness`.
-/

namespace Spatial

/-- A directed trajectory through space, as the finite sequence of visited
    locations. The spatial analog of a temporal `NonemptyInterval`. -/
structure Path (Loc : Type*) where
  /-- The starting location p(0). -/
  source : Loc
  /-- The later locations, ending at p(1); empty for a constant path. -/
  steps : List Loc
  deriving DecidableEq, Repr

namespace Path

variable {Loc : Type*}

/-- The endpoint p(1). -/
def goal (p : Path Loc) : Loc := p.steps.getLastD p.source

/-- The full point sequence p(0) … p(1). -/
def points (p : Path Loc) : List Loc := p.source :: p.steps

/-- The constant path at a location. -/
def const (l : Loc) : Path Loc := ⟨l, []⟩

@[simp] theorem goal_const (l : Loc) : (const l).goal = l := rfl

theorem points_ne_nil (p : Path Loc) : p.points ≠ [] := List.cons_ne_nil _ _

theorem points_injective : Function.Injective (points : Path Loc → List Loc) := by
  rintro ⟨s, l⟩ ⟨s', l'⟩ h
  simpa [points] using h

private theorem getLastD_append {α : Type*} (l₁ l₂ : List α) (d : α) :
    (l₁ ++ l₂).getLastD d = l₂.getLastD (l₁.getLastD d) := by
  simp only [List.getLastD_eq_getLast?, List.getLast?_append]
  cases l₂.getLast? <;> simp

/-! ### Concatenation and subpaths -/

/-- `r` is the concatenation `p + q`, defined only when `p` ends where `q`
    starts. Associative, neither commutative nor idempotent. -/
def IsConcat (p q r : Path Loc) : Prop :=
  p.goal = q.source ∧ r = ⟨p.source, p.steps ++ q.steps⟩

theorem IsConcat.source_eq {p q r : Path Loc} (h : IsConcat p q r) :
    r.source = p.source := by rw [h.2]

theorem IsConcat.goal_eq {p q r : Path Loc} (h : IsConcat p q r) :
    r.goal = q.goal := by
  obtain ⟨h1, rfl⟩ := h
  show (p.steps ++ q.steps).getLastD p.source = q.goal
  rw [getLastD_append]
  show q.steps.getLastD p.goal = q.goal
  rw [h1]; rfl

theorem IsConcat.points_eq {p q r : Path Loc} (h : IsConcat p q r) :
    r.points = p.points ++ q.steps := by
  rw [h.2]; simp [points]

/-- A constant path concatenates with itself to itself. -/
theorem isConcat_const (l : Loc) : IsConcat (const l) (const l) (const l) :=
  ⟨rfl, rfl⟩

/-- `p` is a subpath of `q` if concatenating some `r`, `r′` around `p`
    yields `q`. -/
def Subpath (p q : Path Loc) : Prop :=
  ∃ r r' m, IsConcat r p m ∧ IsConcat m r' q

/-- Subpath-hood is infix-hood of point sequences. -/
theorem subpath_iff_infix {p q : Path Loc} :
    Subpath p q ↔ p.points <:+: q.points := by
  constructor
  · rintro ⟨r, r', m, hrp, hmq⟩
    refine ⟨r.points.dropLast, r'.steps, ?_⟩
    have hgoal : r.points.getLast r.points_ne_nil = p.source := by
      have : r.points.getLast r.points_ne_nil = r.goal := by
        cases h : r.steps <;>
          simp [points, goal, h, List.getLast_cons,
            List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast]
      rw [this, hrp.1]
    calc r.points.dropLast ++ p.points ++ r'.steps
        = (r.points.dropLast ++ [p.source]) ++ p.steps ++ r'.steps := by
          simp [points]
      _ = r.points ++ p.steps ++ r'.steps := by
          rw [← hgoal, List.dropLast_append_getLast]
      _ = q.points := by rw [hmq.points_eq, hrp.points_eq]
  · rintro ⟨A, B, hAB⟩
    match A with
    | [] =>
      obtain ⟨hs, hst⟩ : q.source = p.source ∧ q.steps = p.steps ++ B := by
        simpa [points, List.cons.injEq] using hAB.symm
      exact ⟨const p.source, ⟨p.goal, B⟩, p,
        ⟨rfl, by cases p; rfl⟩, ⟨rfl, by cases q; simp_all [points]⟩⟩
    | a :: A' =>
      obtain ⟨hs, hst⟩ : q.source = a ∧ q.steps = A' ++ (p.source :: p.steps) ++ B := by
        simpa [points, List.cons.injEq, List.append_assoc] using hAB.symm
      refine ⟨⟨a, A' ++ [p.source]⟩, ⟨p.goal, B⟩,
        ⟨a, (A' ++ [p.source]) ++ p.steps⟩,
        ⟨by simp [goal], rfl⟩, ⟨?_, ?_⟩⟩
      · show ((A' ++ [p.source]) ++ p.steps).getLastD a = p.goal
        rw [getLastD_append, getLastD_append]
        rfl
      · cases q
        simp_all [points, List.append_assoc]

/-- The subpath order, as a **scoped** instance: path sets are also studied
    under a rival total lattice sum ([krifka-1998]'s part structures,
    hypothesized as `SemilatticeSup (Path Loc)` in `Spatial/Trace.lean`).
    Activate with `open scoped Spatial.Path`. -/
scoped instance instSubpathOrder : PartialOrder (Path Loc) where
  le := Subpath
  le_refl p := subpath_iff_infix.mpr (List.infix_refl _)
  le_trans _ _ _ hab hbc := subpath_iff_infix.mpr
    ((subpath_iff_infix.mp hab).trans (subpath_iff_infix.mp hbc))
  le_antisymm _ _ hab hba := points_injective
    (List.infix_antisymm (subpath_iff_infix.mp hab) (subpath_iff_infix.mp hba))

/-- Constant paths are least in the subpath order. -/
theorem const_source_le (p : Path Loc) : const p.source ≤ p :=
  subpath_iff_infix.mpr ⟨[], p.steps, rfl⟩

/-! ### Adjacency -/

/-- Two paths are adjacent if one's goal is the other's source —
    [krifka-1998]'s spatial adjacency `∞_H`, the spatial half of the
    movement relations in `Studies/Krifka1998.lean`. -/
def adjacent (p1 p2 : Path Loc) : Prop :=
  p1.goal = p2.source ∨ p2.goal = p1.source

/-- Path adjacency is symmetric. -/
theorem adjacent_comm {p1 p2 : Path Loc} :
    p1.adjacent p2 ↔ p2.adjacent p1 :=
  or_comm

/-- A path is adjacent to itself iff it is a loop. -/
@[simp]
theorem adjacent_self {p : Path Loc} :
    p.adjacent p ↔ p.goal = p.source :=
  or_self_iff

/-- Concatenable paths are adjacent. -/
theorem IsConcat.adjacent {p q r : Path Loc} (h : IsConcat p q r) :
    p.adjacent q :=
  Or.inl h.1

end Path

/-! ### Path shape -/

/-- Directional PP boundedness classification.
    [zwarts-2005]: the boundedness of a directional PP determines
    whether the VP it creates is telic or atelic.

    - `bounded`: goal-oriented ("to the store", "into the room")
    - `unbounded`: direction-oriented ("towards the store", "along the road")
    - `source`: origin-oriented ("from the store", "out of the room")

    This classifies the *set of paths* denoted by a PP, not individual
    paths, by closure under path concatenation: "towards X" denotes a
    cumulative set (concatenating two towards-X paths gives another),
    while "to X" strictly read denotes a set with no concatenable pairs
    at all. [zwarts-2005] shows bounded PPs are *not* quantized — a to-X
    path has proper to-X subpaths — so boundedness is non-cumulativity,
    not `Mereology.QUA`; see `Studies/Zwarts2005.lean`. -/
inductive PathShape where
  | bounded
  | unbounded
  | source
  deriving DecidableEq, Repr

/-- Path shape to scale boundedness: bounded/source paths correspond
    to closed scales, unbounded paths to open scales. -/
def PathShape.toBoundedness : PathShape → Core.Order.Boundedness
  | .bounded => .closed
  | .source => .closed
  | .unbounded => .open_

instance : Core.Order.LicensingPipeline PathShape where
  toBoundedness := PathShape.toBoundedness

end Spatial
