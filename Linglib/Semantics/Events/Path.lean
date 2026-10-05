module

public import Mathlib.Data.List.Infix
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic.DeriveFintype

/-!
# Spatial paths

A path is a finite sequence of locations, the spatial counterpart of a temporal interval. Zwarts
gives paths an algebra: concatenation, defined only when one path ends where the next starts, the
subpath order, and Krifka's adjacency of paths that share an endpoint. Zwarts's own paths are
continuous curves, mathlib's topological `_root_.Path`, but he allows sequences of places as
compatible with the algebra, and they keep every operation computable.

Relative to a region, the points of a path fall into runs inside and outside it, and Pantcheva
classifies paths by those runs: a cofinal path (*to*) runs outside then inside, a coinitial one
(*from*) the reverse, a transitive one (*past*) outside, inside and outside again. A delimited
path keeps one point of its inside run (*up to*, *starting from*) and a non-transitional one
none of its transition (*towards*, *away from*, *along*). Pantcheva builds these from the heads
Place, Goal, Source and Route, each containing the last, and a source path is a reversed goal
path.

## Main definitions

* `Spatial.Path`: a directed trajectory, a source with later steps, ending at `Path.goal`.
* `Spatial.Path.IsConcat`, `Subpath`, `adjacent`, `reverse`: the path algebra.
* `Spatial.Path.Direction`: Place, Goal, Source and Route, in containment order.
* `Spatial.Path.IsCofinal`, `IsCoinitial`, `IsTransitive`, `IsTerminative`, `IsEgressive`,
  `IsProlative`, `IsApproximative`, `IsRecessive`: the shapes of a path relative to a region.
* `Spatial.Path.Shape`, `Shape.direction`, `Shape.transition`, `HasShape`: the eight shapes.
* `Spatial.Localization`: interior, surface or exterior.

## Main results

* `Spatial.Path.Direction.lt_iff_shells_ssubset`: the containment order is strict inclusion of
  head stacks.
* `Spatial.Path.Shape.exists_direction_transition_iff`: a direction and a transition combine
  into a shape exactly when the direction is a path and a route is not delimited.
* `Spatial.Path.hasShape_reverse`: reversing a path reverses its shape.
* `Spatial.Path.IsCofinal.not_isCoinitial`: no path is both cofinal and coinitial.

## References

* [zwarts-2005]
* [krifka-1998]
* [pantcheva-2011]
-/

@[expose] public section

namespace Spatial

/-- A path is a directed trajectory through space, given by the finite sequence of locations it
visits. -/
structure Path (Loc : Type*) where
  /-- The location the path starts from. -/
  source : Loc
  /-- The later locations, which are empty for a constant path. -/
  steps : List Loc
  deriving DecidableEq, Repr

namespace Path

variable {Loc : Type*}

/-- The goal of a path is its last location. -/
def goal (p : Path Loc) : Loc := p.steps.getLastD p.source

/-- The points of a path are its locations from source to goal. -/
def points (p : Path Loc) : List Loc := p.source :: p.steps

/-- The constant path at `l` visits only `l`. -/
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

/-- `IsConcat p q r` says that `r` is the concatenation `p + q`, defined only when `p` ends where
`q` starts. -/
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

/-- `p` is a subpath of `q` when concatenating some paths around `p` yields `q`. -/
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

/-- The subpath order is a scoped instance, since paths are also studied under a rival total
lattice sum (the `SemilatticeSup (Path Loc)` of `Studies/GoldbergJackendoff2004.lean`).
Activate it with `open scoped Spatial.Path`. -/
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

/-- Two paths are adjacent when the goal of one is the source of the other, Krifka's spatial
adjacency. -/
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

/-! ### Reversal -/

/-- The reverse of a path traverses it from its goal to its source. -/
def reverse (p : Path Loc) : Path Loc := ⟨p.goal, p.points.reverse.tail⟩

@[simp] theorem source_reverse (p : Path Loc) : p.reverse.source = p.goal := rfl

@[simp] theorem points_reverse (p : Path Loc) : p.reverse.points = p.points.reverse := by
  obtain ⟨s, l⟩ := p
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l x _ => simp [reverse, points, goal]

@[simp] theorem goal_reverse (p : Path Loc) : p.reverse.goal = p.source := by
  have h : p.reverse.points.getLast (points_ne_nil _) = p.reverse.goal := by
    obtain ⟨s, l⟩ := p.reverse
    cases l using List.reverseRecOn <;> simp [points, goal]
  rw [← h]
  simp only [points_reverse, List.getLast_reverse]
  rfl

@[simp] theorem reverse_reverse (p : Path Loc) : p.reverse.reverse = p :=
  points_injective (by simp)

/-! ### Phases relative to a region

The points of a path lie inside or outside a region, and the runs they form classify the path.
A source shape is the reverse of the corresponding goal shape. -/

section Phases

variable {α : Type*} (R : Set Loc) (p : Path Loc)

/-- A cofinal path lies outside `R` and then inside it, as a path *to* `R` does. -/
def IsCofinal : Prop :=
  ∃ l₁ l₂, p.points = l₁ ++ l₂ ∧ l₁ ≠ [] ∧ l₂ ≠ [] ∧ (∀ x ∈ l₁, x ∉ R) ∧ ∀ x ∈ l₂, x ∈ R

/-- A coinitial path lies inside `R` and then outside it, the reverse of a cofinal path. -/
def IsCoinitial : Prop := p.reverse.IsCofinal R

/-- A transitive path lies outside `R`, inside it, and outside it again, as a path *past* `R`
does. -/
def IsTransitive : Prop :=
  ∃ l₁ l₂ l₃, p.points = l₁ ++ l₂ ++ l₃ ∧ l₁ ≠ [] ∧ l₂ ≠ [] ∧ l₃ ≠ [] ∧
    (∀ x ∈ l₁, x ∉ R) ∧ (∀ x ∈ l₂, x ∈ R) ∧ ∀ x ∈ l₃, x ∉ R

/-- A terminative path lies outside `R` up to its goal, which is in `R`, as a path *up to* `R`
does. -/
def IsTerminative : Prop :=
  ∃ l x, p.points = l ++ [x] ∧ l ≠ [] ∧ (∀ y ∈ l, y ∉ R) ∧ x ∈ R

/-- An egressive path starts in `R` and lies outside it after its source, the reverse of a
terminative path. -/
def IsEgressive : Prop := p.reverse.IsTerminative R

/-- A prolative path lies inside `R` throughout, as a path *along* `R` does. -/
def IsProlative : Prop := ∀ x ∈ p.points, x ∈ R

/-- An approximative path lies outside `R` and comes nearer to it at each point by the distance
`d`, as a path *towards* `R` does. -/
def IsApproximative [Preorder α] (d : Loc → α) : Prop :=
  (∀ x ∈ p.points, x ∉ R) ∧ p.points.IsChain fun a b ↦ d b < d a

/-- A recessive path is the reverse of an approximative one, as a path *away from* `R` is. -/
def IsRecessive [Preorder α] (d : Loc → α) : Prop := p.reverse.IsApproximative R d

variable {R p}

@[simp] theorem isCoinitial_reverse : p.reverse.IsCoinitial R ↔ p.IsCofinal R := by
  simp [IsCoinitial]

@[simp] theorem isCofinal_reverse : p.reverse.IsCofinal R ↔ p.IsCoinitial R := Iff.rfl

@[simp] theorem isEgressive_reverse : p.reverse.IsEgressive R ↔ p.IsTerminative R := by
  simp [IsEgressive]

@[simp] theorem isTerminative_reverse : p.reverse.IsTerminative R ↔ p.IsEgressive R := Iff.rfl

@[simp] theorem isRecessive_reverse [Preorder α] {d : Loc → α} :
    p.reverse.IsRecessive R d ↔ p.IsApproximative R d := by
  simp [IsRecessive]

@[simp] theorem isApproximative_reverse [Preorder α] {d : Loc → α} :
    p.reverse.IsApproximative R d ↔ p.IsRecessive R d := Iff.rfl

@[simp] theorem isProlative_reverse : p.reverse.IsProlative R ↔ p.IsProlative R := by
  simp [IsProlative]

theorem IsTransitive.reverse (h : p.IsTransitive R) : p.reverse.IsTransitive R := by
  obtain ⟨l₁, l₂, l₃, hp, h₁, h₂, h₃, hR₁, hR₂, hR₃⟩ := h
  exact ⟨l₃.reverse, l₂.reverse, l₁.reverse, by simp [hp], by simpa, by simpa, by simpa,
    by simpa using hR₃, by simpa using hR₂, by simpa using hR₁⟩

@[simp] theorem isTransitive_reverse : p.reverse.IsTransitive R ↔ p.IsTransitive R :=
  ⟨fun h ↦ by simpa using h.reverse, IsTransitive.reverse⟩

/-- A terminative path is cofinal. -/
theorem IsTerminative.isCofinal (h : p.IsTerminative R) : p.IsCofinal R := by
  obtain ⟨l, x, hp, hl, hR, hx⟩ := h
  exact ⟨l, [x], hp, hl, by simp, hR, by simpa⟩

/-- An egressive path is coinitial. -/
theorem IsEgressive.isCoinitial (h : p.IsEgressive R) : p.IsCoinitial R :=
  IsTerminative.isCofinal h

private theorem head_mem_of_points_eq {l₁ l₂ : List Loc} (hp : p.points = l₁ ++ l₂)
    (h : l₁ ≠ []) : p.source ∈ l₁ := by
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil h
  have : p.source = a := by simpa [points] using congrArg List.head? hp
  simp [this]

private theorem goal_mem_of_points_eq {l₁ l₂ : List Loc} (hp : p.points = l₁ ++ l₂)
    (h : l₂ ≠ []) : p.goal ∈ l₂ := by
  have := head_mem_of_points_eq (p := p.reverse) (l₁ := l₂.reverse) (l₂ := l₁.reverse)
    (by simp [hp]) (by simpa)
  simpa using this

theorem IsCofinal.source_not_mem (h : p.IsCofinal R) : p.source ∉ R := by
  obtain ⟨l₁, l₂, hp, h₁, -, hR₁, -⟩ := h
  exact hR₁ _ (head_mem_of_points_eq hp h₁)

theorem IsCofinal.goal_mem (h : p.IsCofinal R) : p.goal ∈ R := by
  obtain ⟨l₁, l₂, hp, -, h₂, -, hR₂⟩ := h
  exact hR₂ _ (goal_mem_of_points_eq hp h₂)

theorem IsCoinitial.source_mem (h : p.IsCoinitial R) : p.source ∈ R := by
  simpa using IsCofinal.goal_mem h

theorem IsCoinitial.goal_not_mem (h : p.IsCoinitial R) : p.goal ∉ R := by
  simpa using IsCofinal.source_not_mem h

theorem IsTransitive.source_not_mem (h : p.IsTransitive R) : p.source ∉ R := by
  obtain ⟨l₁, l₂, l₃, hp, h₁, -, -, hR₁, -⟩ := h
  exact hR₁ _ (head_mem_of_points_eq (l₂ := l₂ ++ l₃) (by simp [hp]) h₁)

theorem IsTransitive.goal_not_mem (h : p.IsTransitive R) : p.goal ∉ R := by
  obtain ⟨l₁, l₂, l₃, hp, -, -, h₃, -, -, hR₃⟩ := h
  exact hR₃ _ (goal_mem_of_points_eq hp h₃)

theorem IsTransitive.exists_mem (h : p.IsTransitive R) : ∃ x ∈ p.points, x ∈ R := by
  obtain ⟨l₁, l₂, l₃, hp, -, h₂, -, -, hR₂, -⟩ := h
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil l₂ h₂
  exact ⟨x, by simp [hp, hx], hR₂ x hx⟩

/-- No path is both cofinal and coinitial. -/
theorem IsCofinal.not_isCoinitial (h : p.IsCofinal R) : ¬ p.IsCoinitial R :=
  fun h' ↦ h'.goal_not_mem h.goal_mem

end Phases

/-! ### Directions -/

/-- The direction heads of a path, in containment order, Goal built on Place, Source on Goal,
and Route on Source. -/
inductive Direction where
  /-- Place is static location, the base of the others. -/
  | place
  /-- Goal is motion *to*. -/
  | goal
  /-- Source is motion *from*. -/
  | source
  /-- Route is motion *via* or *past*. -/
  | route
  deriving DecidableEq, Repr, Fintype

namespace Direction

/-- The number of heads below a direction. -/
def rank : Direction → Fin 4
  | place => 0
  | goal => 1
  | source => 2
  | route => 3

/-- The heads a direction contains, a downward-closed stack. -/
def shells (d : Direction) : Finset (Fin 4) := Finset.Iic d.rank

/-- Strict rank is strict inclusion of head stacks. -/
theorem lt_iff_shells_ssubset (d₁ d₂ : Direction) :
    d₁.rank < d₂.rank ↔ d₁.shells ⊂ d₂.shells := by
  simp [shells]

/-- The direction of a path traversed the other way swaps Goal and Source and keeps Place and
Route. -/
def reverse : Direction → Direction
  | goal => source
  | source => goal
  | d => d

@[simp] theorem reverse_reverse (d : Direction) : d.reverse.reverse = d := by cases d <;> rfl

end Direction

/-! ### Shapes -/

/-- How a path relates its run inside the region to its run outside. -/
inductive Transition where
  /-- The path changes its relation to the region, as *to* does. -/
  | transitional
  /-- The path changes it at one point, which bounds the motion, as *up to* does. -/
  | delimited
  /-- The path does not change it, as *towards* does. -/
  | nonTransitional
  deriving DecidableEq, Repr, Fintype

/-- The eight shapes of a path relative to a region. -/
inductive Shape where
  /-- A cofinal path runs outside, then inside, as *to* does. -/
  | cofinal
  /-- A coinitial path runs inside, then outside, as *from* does. -/
  | coinitial
  /-- A transitive path runs outside, inside and outside, as *past* does. -/
  | transitive
  /-- A terminative path runs outside up to its goal, which is inside, as *up to* does. -/
  | terminative
  /-- An egressive path starts inside and runs outside, as *starting from* does. -/
  | egressive
  /-- An approximative path runs outside, nearer at each point, as *towards* does. -/
  | approximative
  /-- A recessive path runs outside, farther at each point, as *away from* does. -/
  | recessive
  /-- A prolative path runs inside throughout, as *along* does. -/
  | prolative
  deriving DecidableEq, Repr, Fintype

namespace Shape

/-- The direction of a shape. -/
def direction : Shape → Direction
  | cofinal | terminative | approximative => .goal
  | coinitial | egressive | recessive => .source
  | transitive | prolative => .route

/-- The transition of a shape. -/
def transition : Shape → Transition
  | cofinal | coinitial | transitive => .transitional
  | terminative | egressive => .delimited
  | approximative | recessive | prolative => .nonTransitional

/-- A shape is its direction and its transition. -/
theorem direction_transition_injective :
    Function.Injective fun s : Shape ↦ (s.direction, s.transition) := by
  intro a b h
  cases a <;> cases b <;> simp_all [direction, transition]

/-- A direction and a transition make a shape exactly when the direction is not Place and a
Route is not delimited. -/
theorem exists_direction_transition_iff (d : Direction) (t : Transition) :
    (∃ s : Shape, s.direction = d ∧ s.transition = t) ↔
      d ≠ .place ∧ (d = .route → t ≠ .delimited) := by
  cases d <;> cases t <;> decide

/-- The shape of a path traversed the other way. -/
def reverse : Shape → Shape
  | cofinal => coinitial
  | coinitial => cofinal
  | terminative => egressive
  | egressive => terminative
  | approximative => recessive
  | recessive => approximative
  | s => s

@[simp] theorem reverse_reverse (s : Shape) : s.reverse.reverse = s := by cases s <;> rfl

@[simp] theorem direction_reverse (s : Shape) : s.reverse.direction = s.direction.reverse := by
  cases s <;> rfl

@[simp] theorem transition_reverse (s : Shape) : s.reverse.transition = s.transition := by
  cases s <;> rfl

/-- A shape is bounded when it has a transition, which makes the motion telic. -/
def IsBounded (s : Shape) : Prop := s.transition ≠ .nonTransitional

instance : DecidablePred IsBounded := fun s ↦ inferInstanceAs (Decidable (s.transition ≠ _))

end Shape

/-- `p.HasShape d R s` says that `p` has shape `s` relative to the region `R`, the distance `d`
measuring nearness to it. -/
def HasShape {α : Type*} [Preorder α] (d : Loc → α) (R : Set Loc) (p : Path Loc) :
    Shape → Prop
  | .cofinal => p.IsCofinal R
  | .coinitial => p.IsCoinitial R
  | .transitive => p.IsTransitive R
  | .terminative => p.IsTerminative R
  | .egressive => p.IsEgressive R
  | .approximative => p.IsApproximative R d
  | .recessive => p.IsRecessive R d
  | .prolative => p.IsProlative R

/-- Reversing a path reverses its shape. -/
theorem hasShape_reverse {α : Type*} [Preorder α] {d : Loc → α} {R : Set Loc} {p : Path Loc}
    {s : Shape} : p.reverse.HasShape d R s ↔ p.HasShape d R s.reverse := by
  cases s <;> simp [HasShape, Shape.reverse]

end Path

/-! ### Localization -/

/-- The part of the reference object a spatial expression localizes in, orthogonal to the
direction. -/
inductive Localization where
  /-- The interior, as of *in*, *into* and *out of*. -/
  | interior
  /-- The surface, as of *on*, *onto* and *off*. -/
  | surface
  /-- The exterior, as of *at*, *to* and *from*. -/
  | exterior
  deriving DecidableEq, Repr, Fintype

end Spatial
