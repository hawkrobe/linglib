import Mathlib.Data.Set.Function
import Mathlib.Data.Setoid.Basic

/-!
# Possibilities

A *possibility* is a world paired with an assignment of discourse
referents — the point type of dynamic semantics. Based information
states over possibilities live in `State.lean`, the unbased register-form
states in `InfoState.lean`, and the generic level-0 CCP algebra in
`ContextChange.lean`.

## Main definitions

- `Possibility W V M`: the point object.
- `Possibility.agreeSetoid X`: possibilities up to agreement on `X` — the
  state space at granularity `X` (`Collapse.lean`, `State.fiberEquiv`).

## References

- [kamp-vangenabith-reyle-2011], Def. 22
- [heim-1982]
-/

namespace DynamicSemantics

/-! ### The point object -/

/-- A possibility: a world paired with an assignment of discourse referents
to individuals — the point type of dynamic semantics. -/
@[ext] structure Possibility (W V M : Type*) where
  /-- The world coordinate. -/
  world : W
  /-- The assignment of discourse referents. -/
  assignment : V → M

namespace Possibility

variable {W V M : Type*}

/-- Possibilities up to agreement on `X`: equal worlds, assignments agreeing
on `X`. Quotienting by this setoid is the state space at granularity `X` —
the collapse of `Collapse.lean`, and the target of `State.fiberEquiv`. -/
def agreeSetoid (X : Set V) : Setoid (Possibility W V M) where
  r p q := p.world = q.world ∧ Set.EqOn p.assignment q.assignment X
  iseqv :=
    ⟨fun _ => ⟨rfl, Set.eqOn_refl _ _⟩, fun h => ⟨h.1.symm, h.2.symm⟩,
      fun h h' => ⟨h.1.trans h'.1, h.2.trans h'.2⟩⟩

/-- Coarser bases identify more possibilities. -/
theorem agreeSetoid_anti : Antitone (agreeSetoid : Set V → Setoid (Possibility W V M)) :=
  fun _ _ hXY _ _ h => ⟨h.1, h.2.mono hXY⟩

/-- Extend the assignment at a single referent, via `Function.update`. -/
def extend [DecidableEq V] (p : Possibility W V M) (x : V) (e : M) :
    Possibility W V M :=
  { p with assignment := Function.update p.assignment x e }

@[simp] theorem extend_at [DecidableEq V] (p : Possibility W V M) (x : V) (e : M) :
    (p.extend x e).assignment x = e := by simp [extend]

@[simp] theorem extend_other [DecidableEq V] (p : Possibility W V M) (x y : V)
    (e : M) (h : y ≠ x) : (p.extend x e).assignment y = p.assignment y := by
  simp [extend, h]

@[simp] theorem extend_world [DecidableEq V] (p : Possibility W V M) (x : V) (e : M) :
    (p.extend x e).world = p.world := rfl

end Possibility

end DynamicSemantics
