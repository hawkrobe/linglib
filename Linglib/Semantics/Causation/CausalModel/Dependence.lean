module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Linglib.Semantics.Causation.CausalModel.Development

/-!
# Causal sufficiency and causal necessity

This file defines the two relations of causal dependence that Nadathur and Lauer draw on for the
meanings of periphrastic causatives, over the strict development of an observation
(`CausalModel.CausallyEntails`). A fact is causally sufficient for another relative to a
background when the background does not settle the effect but, with the cause added, does
(`CausalModel.CausallySufficient`, Nadathur and Lauer's Definition 23). A fact is causally
necessary for another when the background settles neither, some settlement of the exogenous
variables together with the cause settles the effect, and every settlement of the exogenous
variables that settles the effect also settles the cause (`CausalModel.CausallyNecessary`,
Nadathur's Definition 10b).

## Main definitions

* `CausalModel.CausallySufficient`: Nadathur and Lauer's causal sufficiency
* `CausalModel.IsExogenousSettlement`: an extension of an observation at exogenous variables
* `CausalModel.CausallyNecessary`: Nadathur's causal necessity

## Implementation notes

Necessity quantifies over settlements of the exogenous variables, the variables with no parents,
not over every consistent extension of the background: on the literal quantification, settling an
inner variable can reach the effect around the cause and falsify the verdicts of Nadathur's worked
examples, which consider only background settlements. In a finite model each relation is decided
through the computed strict development (`CausalModel.causallyEntails_iff_develop`), the
quantified settlements ranging over the finitely many partial assignments.

## References

* [nadathur-lauer-2020]
* [nadathur-2023-implicatives]
-/

@[expose] public section

namespace CausalModel

variable {U V : Type*} {α : V → Type*} (M : CausalModel U V α) [M.IsAcyclic] [DecidableEq V]

/-- `M.CausallySufficient s c x e y` says that `c = x` is causally sufficient for `e = y` relative
to the background `s`: the background does not settle the effect, and the background together with
the cause does. -/
def CausallySufficient (s : ∀ v, Flat (α v)) (c : V) (x : α c) (e : V) (y : α e) : Prop :=
  ¬ M.CausallyEntails s e y ∧ M.CausallyEntails (Function.update s c ↑x) e y

/-- `s'` extends the observation `s` at exogenous variables only, those with no parents. -/
def IsExogenousSettlement (s s' : ∀ v, Flat (α v)) : Prop :=
  s ≤ s' ∧ ∀ v, s v = ⊥ → s' v ≠ ⊥ → ∀ w, ¬ M.graph.Adj w v

/-- `M.CausallyNecessary s c x e y` says that `c = x` is causally necessary for `e = y` relative to
the background `s`. The background settles neither fact; some exogenous settlement of the
background with the cause added, leaving the effect open, settles the effect; and every exogenous
settlement of the background leaving the effect open that settles the effect settles the cause. -/
def CausallyNecessary (s : ∀ v, Flat (α v)) (c : V) (x : α c) (e : V) (y : α e) : Prop :=
  (¬ M.CausallyEntails s c x ∧ ¬ M.CausallyEntails s e y) ∧
  (∃ s', M.IsExogenousSettlement (Function.update s c ↑x) s' ∧ s' e = ⊥ ∧
    M.CausallyEntails s' e y) ∧
  ∀ s', M.IsExogenousSettlement s s' → s' e = ⊥ → M.CausallyEntails s' e y →
    M.CausallyEntails s' c x

variable {M}

/-- A causally sufficient cause settles the effect in every context where the background and the
cause are observed. -/
theorem CausallySufficient.solve_eq [∀ v, Nonempty (α v)] {s : ∀ v, Flat (α v)} {c e : V}
    {x : α c} {y : α e} (h : M.CausallySufficient s c x e y) {u : U}
    (hu : u ∈ M.contexts (Function.update s c ↑x)) : M.solve ⊥ u e = y :=
  h.2.solve_eq hu

section Decidable

variable [Fintype U] [Inhabited U] [∀ v, Inhabited (α v)] [∀ v, DecidableEq (α v)] [Fintype V]
  [DecidableRel M.graph.Adj]

instance (s : ∀ v, Flat (α v)) (c : V) (x : α c) (e : V) (y : α e) :
    Decidable (M.CausallySufficient s c x e y) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (s s' : ∀ v, Flat (α v)) : Decidable (M.IsExogenousSettlement s s') :=
  inferInstanceAs (Decidable (_ ∧ _))

variable [∀ v, Fintype (α v)]

/-- Partial assignments over finitely many variables of finite types are finitely many. Not an
instance: a `Fintype` instance on `Flat` would change how `decide` evaluates flat-valued
functions, so necessity installs this one locally. -/
@[reducible] def fintypePartialAssignment : Fintype (∀ v, Flat (α v)) :=
  inferInstanceAs (Fintype (∀ v, Option (α v)))

instance (s : ∀ v, Flat (α v)) (c : V) (x : α c) (e : V) (y : α e) :
    Decidable (M.CausallyNecessary s c x e y) :=
  letI := fintypePartialAssignment (α := α)
  haveI : DecidablePred fun s' ↦ M.IsExogenousSettlement (Function.update s c ↑x) s' ∧
      s' e = ⊥ ∧ M.CausallyEntails s' e y := fun _ ↦ inferInstance
  haveI : DecidablePred fun s' ↦ M.IsExogenousSettlement s s' → s' e = ⊥ →
      M.CausallyEntails s' e y → M.CausallyEntails s' c x := fun _ ↦ inferInstance
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end Decidable

end CausalModel
