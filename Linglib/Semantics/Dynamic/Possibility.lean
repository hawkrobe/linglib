import Mathlib.Data.Set.Function
import Mathlib.Data.Setoid.Basic

/-!
# Possibilities

A *possibility* is a world paired with an assignment of discourse
referents — the point type of dynamic semantics. Indexed information
states over possibilities live in `State.lean`; unindexed states are plain
sets of possibilities, with the generic level-0 CCP algebra in
`Update.lean`.

*Possibility* is the update-semantics tradition's word:
[groenendijk-stokhof-veltman-1996]'s possibilities are triples carrying a
referent system ([vermeulen-1995]) we do not; [elliott-sudo-2025]'s are
world–assignment pairs like ours. [kamp-vangenabith-reyle-2011] leaves the
pairs of its Def. 22 unnamed, and the monadic tradition calls the same
points *indices* ([charlow-2025-staged-updates]).

## Main definitions

- `Possibility W V M`: the point object.
- `Possibility.agreeSetoid X`: possibilities up to agreement on `X` — the
  state space at granularity `X` (`Collapse.lean`, `State.fiberEquiv`).

## References

- [groenendijk-stokhof-veltman-1996], [elliott-sudo-2025]
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

/-- The projection of a possibility to granularity `A`: its world together
with its assignment of the `A`-referents — the pointwise face of
`Category.lean`'s `environments`. -/
def proj (A : Set V) (p : Possibility W V M) : W × (A → M) :=
  (p.world, A.restrict p.assignment)

/-- Possibilities up to agreement on `X`: equal worlds, assignments agreeing
on `X`. Quotienting by this setoid is the state space at granularity `X` —
the collapse of `Collapse.lean`, and the target of `State.fiberEquiv`. -/
def agreeSetoid (X : Set V) : Setoid (Possibility W V M) where
  r p q := p.world = q.world ∧ Set.EqOn p.assignment q.assignment X
  iseqv :=
    ⟨fun _ => ⟨rfl, Set.eqOn_refl _ _⟩, fun h => ⟨h.1.symm, h.2.symm⟩,
      fun h h' => ⟨h.1.trans h'.1, h.2.trans h'.2⟩⟩

/-- Projections agree exactly on agreement classes: `proj A` is the
effective quotient map for `agreeSetoid A`. -/
theorem proj_eq_proj_iff {A : Set V} {p q : Possibility W V M} :
    proj A p = proj A q ↔ agreeSetoid A p q :=
  Prod.ext_iff.trans (and_congr Iff.rfl Set.restrict_eq_restrict_iff)

/-- Coarser bases identify more possibilities. -/
theorem agreeSetoid_anti : Antitone (agreeSetoid : Set V → Setoid (Possibility W V M)) :=
  fun _ _ hXY _ _ h => ⟨h.1, h.2.mono hXY⟩

open scoped Classical in
/-- The state space at granularity `X`, classified: a possibility up to
agreement on `X` is a world together with an assignment of the
`X`-referents. -/
noncomputable def agreeQuotientEquiv (X : Set V) [Nonempty M] :
    Quotient (agreeSetoid (W := W) (M := M) X) ≃ W × (X → M) where
  toFun := Quotient.lift (proj X) fun _ _ h => proj_eq_proj_iff.mpr h
  invFun wf :=
    Quotient.mk _
      ⟨wf.1, fun v => if h : v ∈ X then wf.2 ⟨v, h⟩ else Classical.arbitrary M⟩
  left_inv := by
    rintro ⟨p⟩
    exact Quotient.sound ⟨rfl, fun v hv => dif_pos hv⟩
  right_inv wf := Prod.ext rfl (funext fun x => dif_pos x.2)

@[simp] theorem agreeQuotientEquiv_mk (X : Set V) [Nonempty M]
    (p : Possibility W V M) :
    agreeQuotientEquiv X (Quotient.mk _ p) = (p.world, X.restrict p.assignment) :=
  rfl

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
