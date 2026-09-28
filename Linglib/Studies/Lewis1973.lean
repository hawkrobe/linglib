module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Causation.CausalModel.Basic
public import Linglib.Core.Relation.ReflTransGen
public import Linglib.Semantics.Reference.Context.Index
public import Mathlib.Logic.Relation

/-!
# Lewis (1973): Causation

This file formalizes the counterfactual analysis of causation of [lewis-1973-causation] on
deterministic Boolean structural equation models. An event depends causally on another when,
had the cause not occurred, the effect would not have occurred (`lewisButFor`,
`lewisDependence`), and causation is the ancestral of causal dependence, a chain of
stepwise dependences (`lewisCausation`, via `Relation.TransGen`). Four scenarios exercise the
analysis: a single cause, a chain, in which the distal cause is a cause through two steps
(`Chain.chain_causation`), the common-cause case of the barometer and the storm, where
neither effect depends on the other (`Epiphenomena.barometer_not_causes_storm`), and
symmetric overdetermination, where neither of two sufficient causes passes the but-for test
(`Overdetermination.overdetermination_no_dependence_a`), the limitation the paper concedes.

## Implementation notes

The actual world is a context of a causal model, and the counterfactual is an intervention
setting the cause to `false` in that context (`CausalModel.solve`), so the analysis is the but-for
test of the model rather than a similarity ordering over worlds; the two agree on these
deterministic scenarios. The paper's treatment of preemption is not represented.

## References

* [lewis-1973-causation]
-/

@[expose] public section

namespace Lewis1973

open Reference CausalModel Relation

section Dependence

variable {U W : Type*} [DecidableEq W] (M : CausalModel U W fun _ ↦ Bool) [M.IsAcyclic] (u : U)

/-- The but-for counterfactual holds when, had the cause not occurred, the effect would not have
occurred, the counterfactual being an intervention setting the cause to `false` in the actual
context `u`. -/
def lewisButFor (cause effect : W) : Prop :=
  M.solve (Function.update ⊥ cause ↑false) u effect ≠ true

/-- The effect depends causally on the cause (p. 562) when both occur and the effect would not
have occurred without the cause. -/
def lewisDependence (cause effect : W) : Prop :=
  M.solve ⊥ u cause = true ∧ M.solve ⊥ u effect = true ∧ lewisButFor M u cause effect

noncomputable instance [Fintype W] (cause effect : W) :
    Decidable (lewisButFor M u cause effect) :=
  inferInstanceAs (Decidable (_ ≠ _))

noncomputable instance [Fintype W] (cause effect : W) :
    Decidable (lewisDependence M u cause effect) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Causation is the ancestral of causal dependence (p. 563). -/
def lewisCausation (cause effect : W) : Prop :=
  Relation.TransGen (lewisDependence M u) cause effect

variable {M u}

/-- Causal dependence is causation through a chain of one step. -/
theorem dependence_implies_causation {cause effect : W} (h : lewisDependence M u cause effect) :
    lewisCausation M u cause effect :=
  Relation.TransGen.single h

/-- An effect does not depend on an event from which no directed path reaches it, since
intervening on the event leaves the effect as it was. -/
theorem not_lewisDependence_of_not_reflTransGen {cause effect : W}
    (h : ¬ ReflTransGen M.graph.Adj cause effect) : ¬ lewisDependence M u cause effect :=
  fun ⟨_, he, hbf⟩ ↦ hbf (by rw [solve_update_of_not_reflTransGen h]; exact he)

end Dependence

namespace SimpleCause

inductive V | a | b
  deriving DecidableEq, Fintype, Repr

/-- `b` follows `a`. -/
abbrev graph : Digraph V := ⟨fun w v ↦ (w, v) ∈ ({(.a, .b)} : Finset (V × V))⟩

/-- The context settles whether `a` occurs, and `b` occurs when `a` does. -/
def sem : CausalModel Bool V fun _ ↦ Bool where
  graph := graph
  eqn | .a => fun u _ ↦ u | .b => fun _ x ↦ x .a

instance : sem.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (r := graph.Adj) (by decide)

/-- A single cause passes the but-for test. -/
theorem simple_butfor : lewisButFor sem true .a .b := by decide

/-- The effect depends on its single cause. -/
theorem simple_dependence : lewisDependence sem true .a .b := by decide

/-- A single cause is a cause. -/
theorem simple_causation : lewisCausation sem true .a .b :=
  dependence_implies_causation simple_dependence

end SimpleCause

namespace Chain

inductive V | a | b | c
  deriving DecidableEq, Fintype, Repr

/-- `b` follows `a`, and `c` follows `b`. -/
abbrev graph : Digraph V := ⟨fun w v ↦ (w, v) ∈ ({(.a, .b), (.b, .c)} : Finset (V × V))⟩

/-- The context settles whether `a` occurs, and the chain passes it on. -/
def sem : CausalModel Bool V fun _ ↦ Bool where
  graph := graph
  eqn | .a => fun u _ ↦ u | .b => fun _ x ↦ x .a | .c => fun _ x ↦ x .b

instance : sem.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (r := graph.Adj) (by decide)

/-- In a chain the distal cause passes the but-for test for the final effect. -/
theorem chain_direct_butfor : lewisButFor sem true .a .c := by decide

/-- The middle event depends on the first. -/
theorem chain_step_AB : lewisDependence sem true .a .b := by decide

/-- The final event depends on the middle one. -/
theorem chain_step_BC : lewisDependence sem true .b .c := by decide

/-- The first event causes the last through the chain. -/
theorem chain_causation : lewisCausation sem true .a .c :=
  Relation.TransGen.trans
    (Relation.TransGen.single chain_step_AB)
    (Relation.TransGen.single chain_step_BC)

end Chain

namespace Epiphenomena

/-! The barometer reading and the storm are both effects of atmospheric pressure
(pp. 561 and 564–565): the analysis makes the pressure the cause of each and neither effect a
cause of the other. -/

inductive V | pressure | barometer | storm
  deriving DecidableEq, Fintype, Repr

/-- The pressure bears on the barometer and on the storm. -/
abbrev graph : Digraph V :=
  ⟨fun w v ↦ (w, v) ∈ ({(.pressure, .barometer), (.pressure, .storm)} : Finset (V × V))⟩

/-- The context settles the pressure, and the barometer and the storm both follow it. -/
def sem : CausalModel Bool V fun _ ↦ Bool where
  graph := graph
  eqn
    | .pressure => fun u _ ↦ u
    | .barometer => fun _ x ↦ x .pressure
    | .storm => fun _ x ↦ x .pressure

instance : sem.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (r := graph.Adj) (by decide)

/-- Pressure causes the barometer reading. -/
theorem pressure_causes_barometer : lewisDependence sem true .pressure .barometer := by decide

/-- Pressure causes the storm. -/
theorem pressure_causes_storm : lewisDependence sem true .pressure .storm := by decide

/-- The barometer does not cause the storm. No path runs from the barometer to the storm, so
intervening on the barometer leaves the pressure, and so the storm, in place. -/
theorem barometer_not_causes_storm (u : Bool) : ¬ lewisDependence sem u .barometer .storm :=
  not_lewisDependence_of_not_reflTransGen
    (by decide : ¬ ReflTransGen graph.Adj .barometer .storm)

/-- The storm does not cause the barometer reading. -/
theorem storm_not_causes_barometer (u : Bool) : ¬ lewisDependence sem u .storm .barometer :=
  not_lewisDependence_of_not_reflTransGen
    (by decide : ¬ ReflTransGen graph.Adj .storm .barometer)

end Epiphenomena

namespace Overdetermination

/-! Symmetric overdetermination (fn. 12): with two sufficient causes both
present, neither is necessary, so neither passes the but-for test. -/

inductive V | a | b | e
  deriving DecidableEq, Fintype, Repr

/-- Both causes bear on the effect. -/
abbrev graph : Digraph V := ⟨fun w v ↦ (w, v) ∈ ({(.a, .e), (.b, .e)} : Finset (V × V))⟩

/-- The context settles the two causes, and the effect occurs when either does. -/
def sem : CausalModel (Bool × Bool) V fun _ ↦ Bool where
  graph := graph
  eqn | .a => fun u _ ↦ u.1 | .b => fun u _ ↦ u.2 | .e => fun _ x ↦ x .a || x .b

instance : sem.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (r := graph.Adj) (by decide)

/-- Neither overdetermining cause passes the but-for test, both being present. -/
theorem overdetermination_no_butfor_a : ¬ lewisButFor sem (true, true) .a .e := by decide

theorem overdetermination_no_butfor_b : ¬ lewisButFor sem (true, true) .b .e := by decide

/-- Neither overdetermining cause is one the effect depends on. -/
theorem overdetermination_no_dependence_a : ¬ lewisDependence sem (true, true) .a .e := by
  decide

theorem overdetermination_no_dependence_b : ¬ lewisDependence sem (true, true) .b .e := by
  decide

end Overdetermination

end Lewis1973
