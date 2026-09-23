module

public import Linglib.Semantics.Causation.SEM.Bool
public import Linglib.Semantics.Causation.SEM.Counterfactual
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

The counterfactual is an intervention on the deterministic development of the model
(`SEM.causallySufficient`), so the analysis is the but-for test of the substrate rather than a
similarity ordering over worlds; the two agree on these deterministic scenarios. The paper's
treatment of preemption is not represented.

## References

* [lewis-1973-causation]
-/

@[expose] public section

namespace Lewis1973

open Reference
open Causation Causation.Mechanism

section Dependence

variable {W : Type*} [DecidableEq W] (M : BoolSEM W) [M.graph.IsDAG]
  (bg : Valuation (fun _ : W ↦ Bool))

/-- The but-for counterfactual: had the cause not occurred, the effect would not have
occurred, as an intervention setting the cause to `false` in the deterministic development. -/
def lewisButFor (cause effect : W) : Prop :=
  ¬ SEM.causallySufficient M bg cause false effect true

/-- Causal dependence (p. 562): both events occur, and the effect would not have
occurred without the cause. -/
def lewisDependence (cause effect : W) : Prop :=
  (M.developDet bg).hasValue cause true ∧ (M.developDet bg).hasValue effect true ∧
    lewisButFor M bg cause effect

instance [Fintype W] (cause effect : W) : Decidable (lewisButFor M bg cause effect) :=
  inferInstanceAs (Decidable (¬ _))

instance [Fintype W] (cause effect : W) : Decidable (lewisDependence M bg cause effect) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Causation: the ancestral of causal dependence (p. 563). -/
def lewisCausation (cause effect : W) : Prop :=
  Relation.TransGen (lewisDependence M bg) cause effect

/-- Causal dependence is causation through a chain of one step. -/
theorem dependence_implies_causation {cause effect : W} (h : lewisDependence M bg cause effect) :
    lewisCausation M bg cause effect :=
  Relation.TransGen.single h

end Dependence

namespace SimpleCause

inductive V | a | b
  deriving DecidableEq, Fintype, Repr

def graph : CausalGraph V := ⟨fun | .a => ∅ | .b => {.a}⟩

def sem : BoolSEM V :=
  { graph := graph
    mech := fun v ↦ match v with
      | .a => const (G := graph) false
      | .b => fun ρ ↦ ρ ⟨.a, by simp [graph]⟩ }

instance : CausalGraph.IsDAG sem.graph := .of_irrefl (by decide)

def bg : Valuation (fun _ : V ↦ Bool) := Valuation.empty.extend .a true

/-- A single cause passes the but-for test. -/
theorem simple_butfor : lewisButFor sem bg .a .b := by
  decide

/-- The effect depends on its single cause. -/
theorem simple_dependence : lewisDependence sem bg .a .b := by
  decide

/-- A single cause is a cause. -/
theorem simple_causation : lewisCausation sem bg .a .b :=
  dependence_implies_causation _ _ simple_dependence

end SimpleCause

namespace Chain

inductive V | a | b | c
  deriving DecidableEq, Fintype, Repr

def graph : CausalGraph V := ⟨fun | .a => ∅ | .b => {.a} | .c => {.b}⟩

def sem : BoolSEM V :=
  { graph := graph
    mech := fun v ↦ match v with
      | .a => const (G := graph) false
      | .b => fun ρ ↦ ρ ⟨.a, by simp [graph]⟩
      | .c => fun ρ ↦ ρ ⟨.b, by simp [graph]⟩ }

instance : CausalGraph.IsDAG sem.graph := .of_irrefl (by decide)

def bg : Valuation (fun _ : V ↦ Bool) := Valuation.empty.extend .a true

/-- In a chain the distal cause passes the but-for test for the final effect. -/
theorem chain_direct_butfor : lewisButFor sem bg .a .c := by
  decide

/-- The middle event depends on the first. -/
theorem chain_step_AB : lewisDependence sem bg .a .b := by
  decide

/-- The final event depends on the middle one. -/
theorem chain_step_BC : lewisDependence sem bg .b .c := by
  decide

/-- The first event causes the last through the chain. -/
theorem chain_causation : lewisCausation sem bg .a .c :=
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

def graph : CausalGraph V :=
  ⟨fun | .pressure => ∅ | .barometer => {.pressure} | .storm => {.pressure}⟩

def sem : BoolSEM V :=
  { graph := graph
    mech := fun v ↦ match v with
      | .pressure => const (G := graph) false
      | .barometer => fun ρ ↦ ρ ⟨.pressure, by simp [graph]⟩
      | .storm => fun ρ ↦ ρ ⟨.pressure, by simp [graph]⟩ }

instance : CausalGraph.IsDAG sem.graph := .of_irrefl (by decide)

def bg : Valuation (fun _ : V ↦ Bool) := Valuation.empty.extend .pressure true

/-- Pressure causes the barometer reading. -/
theorem pressure_causes_barometer : lewisDependence sem bg .pressure .barometer := by
  decide

/-- Pressure causes the storm. -/
theorem pressure_causes_storm : lewisDependence sem bg .pressure .storm := by
  decide

/-- The barometer does not cause the storm: intervening on the barometer leaves the
pressure, and so the storm, in place. -/
theorem barometer_not_causes_storm :
    ¬ (lewisDependence sem bg .barometer .storm) := by
  decide

/-- The storm does not cause the barometer reading. -/
theorem storm_not_causes_barometer :
    ¬ (lewisDependence sem bg .storm .barometer) := by
  decide

end Epiphenomena

namespace Overdetermination

/-! Symmetric overdetermination (fn. 12): with two sufficient causes both
present, neither is necessary, so neither passes the but-for test. -/

inductive V | a | b | e
  deriving DecidableEq, Fintype, Repr

def graph : CausalGraph V := ⟨fun | .a => ∅ | .b => ∅ | .e => {.a, .b}⟩

def sem : BoolSEM V :=
  { graph := graph
    mech := fun v ↦ match v with
      | .a => const (G := graph) false
      | .b => const (G := graph) false
      | .e => fun ρ ↦
          ρ ⟨.a, by simp [graph]⟩ || ρ ⟨.b, by simp [graph]⟩ }

instance : CausalGraph.IsDAG sem.graph := .of_irrefl (by decide)

/-- Both causes present. -/
def bg : Valuation (fun _ : V ↦ Bool) :=
  Valuation.empty.extend .a true |>.extend .b true

/-- Neither overdetermining cause passes the but-for test. -/
theorem overdetermination_no_butfor_a : ¬ lewisButFor sem bg .a .e := by
  decide

theorem overdetermination_no_butfor_b : ¬ lewisButFor sem bg .b .e := by
  decide

/-- Neither overdetermining cause is one the effect depends on. -/
theorem overdetermination_no_dependence_a : ¬ lewisDependence sem bg .a .e := by
  decide

theorem overdetermination_no_dependence_b : ¬ lewisDependence sem bg .b .e := by
  decide

end Overdetermination

end Lewis1973
