module

public import Linglib.Semantics.Causation.CausalModel.Basic

/-!
# Developing an observation through a causal model

An observation `s : ∀ v, Flat (α v)` settles some variables and leaves the context unknown. Two
local procedures propagate what it settles through the equations, each deciding a variable from
what has been decided about its parents alone.

* In the strict development of Schulz and of Nadathur, a variable is settled once all its parents
  are, and its equation then gives the same value in every context (`CausalModel.CausallyEntails`).
* In the Kleene development used by Baglini and Bar-Asher Siegal, a variable is forced to a value
  when every completion of what is known about its parents gives that value in every context,
  so a turned handle on an unlocked door forces the door open while other inputs are unknown
  (`CausalModel.Forced`).

Both are fixed points of maps that compute each variable from its parents
(`WellFounded.fixedPoint`). The strict development settles less than the Kleene one
(`CausalModel.Forced.of_causallyEntails`), and the Kleene one is sound: what it forces holds in
the actual world of every context in which the observation holds
(`CausalModel.Forced.solve_eq`).

## Main definitions

* `CausalModel.Forced`: the Kleene development of an observation
* `CausalModel.CausallyEntails`: the strict development of an observation

## Main results

* `CausalModel.forced_iff`, `CausalModel.causallyEntails_iff`: the defining equations
* `CausalModel.Forced.of_causallyEntails`: the strict development settles less
* `CausalModel.Forced.solve_eq`, `CausalModel.CausallyEntails.solve_eq`: soundness

## Implementation notes

Uncertainty about exogenous variables is uncertainty about the context, so a variable whose
equation reads the context is settled only when the equation gives the same value in every
context. A model whose root variables read the context therefore leaves them unsettled unless the
observation settles them, as the strict development of Schulz leaves undetermined background
variables. Both developments are families of predicates `∀ v, α v → Prop`, which spares choosing
the value a variable is settled to.

Soundness has no converse. With `b := ¬ a` and `v := a ∧ b`, `v` is false in every context, but
neither development settles it while `a` is unknown, since each looks only at what is settled
about `v`'s parents.

## References

* [schulz-2011]
* [nadathur-2023-implicatives]
* [baglini-bar-asher-siegal-2025]
* [bar-asher-siegal-2026]
-/

@[expose] public section

namespace CausalModel

variable {U V : Type*} {α : V → Type*} (M : CausalModel U V α)

/-- `M.forcedStep s P` is one round of Kleene development from the observation `s`, given what
`P` has settled. A variable is settled to `x` when `s` settles it so, or when `s` leaves it open
and its equation gives `x` in every context and on every assignment agreeing with what `P`
settles about its parents. -/
def forcedStep (s : ∀ v, Flat (α v)) (P : ∀ v, α v → Prop) : ∀ v, α v → Prop := fun v x ↦
  s v = ↑x ∨ s v = ⊥ ∧
    ∀ u y, (∀ w, M.graph.Adj w v → ∀ z, P w z → y w = z) → M.eqn v u y = x

/-- `M.entailsStep s P` is one round of strict development from the observation `s`. It is
`forcedStep`, except that a variable `s` leaves open is settled only once all its parents are. -/
def entailsStep (s : ∀ v, Flat (α v)) (P : ∀ v, α v → Prop) : ∀ v, α v → Prop := fun v x ↦
  s v = ↑x ∨ s v = ⊥ ∧ (∀ w, M.graph.Adj w v → ∃ z, P w z) ∧
    ∀ u y, (∀ w, M.graph.Adj w v → ∀ z, P w z → y w = z) → M.eqn v u y = x

variable {M}

theorem dependsOn_forcedStep (s : ∀ v, Flat (α v)) (v : V) :
    DependsOn (M.forcedStep s · v) {w | M.graph.Adj w v} := fun P Q h ↦ by
  funext x
  refine propext (or_congr_right (and_congr_right fun _ ↦ forall₂_congr fun u y ↦
    imp_congr_left (forall₂_congr fun w hw ↦ ?_)))
  rw [h w hw]

theorem dependsOn_entailsStep (s : ∀ v, Flat (α v)) (v : V) :
    DependsOn (M.entailsStep s · v) {w | M.graph.Adj w v} := fun P Q h ↦ by
  funext x
  refine propext (or_congr_right (and_congr_right fun _ ↦ and_congr
    (forall₂_congr fun w hw ↦ by rw [h w hw]) (forall₂_congr fun u y ↦
      imp_congr_left (forall₂_congr fun w hw ↦ ?_))))
  rw [h w hw]

/-- A strict round settles no more than a Kleene round given more. -/
theorem entailsStep_le_forcedStep (s : ∀ v, Flat (α v)) {P Q : ∀ v, α v → Prop} (h : P ≤ Q) :
    M.entailsStep s P ≤ M.forcedStep s Q := by
  rintro v x (hx | ⟨hs, -, hx⟩)
  · exact .inl hx
  · exact .inr ⟨hs, fun u y hy ↦ hx u y fun w hw z hz ↦ hy w hw z (h w z hz)⟩

variable (M) [hM : M.IsAcyclic]

/-- `M.Forced s v x` says that the Kleene development of the observation `s` forces `v` to `x`. -/
def Forced (s : ∀ v, Flat (α v)) (v : V) (x : α v) : Prop :=
  hM.fixedPoint (M.forcedStep s) v x

/-- `M.CausallyEntails s v x` says that the strict development of `s` settles `v` to `x`. -/
def CausallyEntails (s : ∀ v, Flat (α v)) (v : V) (x : α v) : Prop :=
  hM.fixedPoint (M.entailsStep s) v x

variable {M} {s : ∀ v, Flat (α v)} {v : V} {x : α v}

theorem forced_iff : M.Forced s v x ↔ s v = ↑x ∨ s v = ⊥ ∧
    ∀ u y, (∀ w, M.graph.Adj w v → ∀ z, M.Forced s w z → y w = z) → M.eqn v u y = x :=
  Iff.of_eq (congrFun (WellFounded.fixedPoint_apply (dependsOn_forcedStep s) v) x)

theorem causallyEntails_iff : M.CausallyEntails s v x ↔ s v = ↑x ∨ s v = ⊥ ∧
    (∀ w, M.graph.Adj w v → ∃ z, M.CausallyEntails s w z) ∧
    ∀ u y, (∀ w, M.graph.Adj w v → ∀ z, M.CausallyEntails s w z → y w = z) →
      M.eqn v u y = x :=
  Iff.of_eq (congrFun (WellFounded.fixedPoint_apply (dependsOn_entailsStep s) v) x)

/-- The strict development settles less than the Kleene one. -/
theorem Forced.of_causallyEntails (h : M.CausallyEntails s v x) : M.Forced s v x :=
  WellFounded.fixedPoint_le_fixedPoint (dependsOn_entailsStep s) (dependsOn_forcedStep s)
    (fun _ _ ↦ entailsStep_le_forcedStep s) v x h

/-- In a finite model, the Kleene development is reached by iterating its rounds once per
variable. -/
theorem forced_iff_iterate_card [Fintype V] :
    M.Forced s v x ↔ (M.forcedStep s)^[Fintype.card V] ⊥ v x :=
  Iff.of_eq (congrFun (congrFun (WellFounded.fixedPoint_eq_iterate_card
    (dependsOn_forcedStep s) ⊥) v) x)

/-- In a finite model, the strict development is reached by iterating its rounds once per
variable. -/
theorem causallyEntails_iff_iterate_card [Fintype V] :
    M.CausallyEntails s v x ↔ (M.entailsStep s)^[Fintype.card V] ⊥ v x :=
  Iff.of_eq (congrFun (congrFun (WellFounded.fixedPoint_eq_iterate_card
    (dependsOn_entailsStep s) ⊥) v) x)

variable [∀ v, Nonempty (α v)]

/-- The Kleene development is sound. What it forces holds in the actual world of every context
in which the observation holds. -/
theorem Forced.solve_eq (h : M.Forced s v x) {u : U} (hu : u ∈ M.contexts s) :
    M.solve ⊥ u v = x := by
  induction v using hM.induction with
  | _ v ih =>
    rcases forced_iff.1 h with hs | ⟨-, h⟩
    · exact mem_contexts.1 hu v x hs
    · rw [solve_of_eq_bot rfl u]
      exact h u _ fun w hw _ hz ↦ ih w hw hz

/-- Soundness of the strict development. -/
theorem CausallyEntails.solve_eq (h : M.CausallyEntails s v x) {u : U}
    (hu : u ∈ M.contexts s) : M.solve ⊥ u v = x :=
  (Forced.of_causallyEntails h).solve_eq hu

end CausalModel
