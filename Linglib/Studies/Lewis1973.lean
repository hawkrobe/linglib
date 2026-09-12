import Linglib.Semantics.Causation.SEM.Bool
import Linglib.Semantics.Causation.SEM.Counterfactual
import Linglib.Semantics.Reference.Context.Index
import Mathlib.Logic.Relation

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
(`developDetOn`), so the analysis is the but-for test of the substrate rather than a
similarity ordering over worlds; the two agree on these deterministic scenarios. The paper's
treatment of preemption is not represented.

## TODO

The page locators and the footnote on overdetermination are transcribed from an earlier
version of this file and are marked `UNVERIFIED` pending a check against the paper.

## References

* [lewis-1973-causation]
-/

namespace Lewis1973

open Semantics.Context (Index)
open Causation Causation.Mechanism Causation.SEM

/-- The but-for counterfactual: had the cause not occurred, the effect would not have
occurred, as an intervention setting the cause to `false` in the deterministic development. -/
noncomputable def lewisButFor {W : Type*} [Fintype W] [DecidableEq W]
    (M : BoolSEM W) [SEM.IsDeterministic M]
    (vs : List W) (bg : Valuation (λ _ : W => Bool))
    (cause effect : W) : Prop :=
  ¬ (developDetOn M vs 1 (bg.extend cause false)).hasValue effect true

/-- Causal dependence (UNVERIFIED: p. 563): both events occur, and the effect would not have
occurred without the cause. -/
noncomputable def lewisDependence {W : Type*} [Fintype W] [DecidableEq W]
    (M : BoolSEM W) [SEM.IsDeterministic M]
    (vs : List W) (bg : Valuation (λ _ : W => Bool))
    (cause effect : W) : Prop :=
  (developDetOn M vs 1 bg).hasValue cause true ∧
  (developDetOn M vs 1 bg).hasValue effect true ∧
  lewisButFor M vs bg cause effect

/-- Causation: the ancestral of causal dependence (UNVERIFIED: p. 563). -/
def lewisCausation {W : Type*} [Fintype W] [DecidableEq W]
    (M : BoolSEM W) [SEM.IsDeterministic M]
    (vs : List W) (bg : Valuation (λ _ : W => Bool))
    (cause effect : W) : Prop :=
  Relation.TransGen (lewisDependence M vs bg) cause effect

/-- Causal dependence is causation through a chain of one step. -/
theorem dependence_implies_causation {W : Type*} [Fintype W] [DecidableEq W]
    (M : BoolSEM W) [SEM.IsDeterministic M]
    (vs : List W) (bg : Valuation _) (cause effect : W)
    (h : lewisDependence M vs bg cause effect) :
    lewisCausation M vs bg cause effect :=
  Relation.TransGen.single h

namespace SimpleCause

inductive V | a | b
  deriving DecidableEq, Fintype, Repr

def varList : List V := [.a, .b]

def graph : CausalGraph V := ⟨λ | .a => ∅ | .b => {.a}⟩

noncomputable def sem : BoolSEM V :=
  { graph := graph
    mech := λ v => match v with
      | .a => const (G := graph) false
      | .b => deterministic (λ ρ => ρ ⟨.a, by simp [graph]⟩) }

noncomputable instance : SEM.IsDeterministic sem where
  mech_det v := match v with
    | .a => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .b => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

def bg : Valuation (λ _ : V => Bool) := Valuation.empty.extend .a true

/-- A single cause passes the but-for test. -/
theorem simple_butfor : lewisButFor sem varList bg .a .b := by
  unfold lewisButFor; intro h
  exact Bool.false_ne_true (Option.some.inj h)

/-- The effect depends on its single cause. -/
theorem simple_dependence : lewisDependence sem varList bg .a .b :=
  ⟨by rfl, by rfl, simple_butfor⟩

/-- A single cause is a cause. -/
theorem simple_causation : lewisCausation sem varList bg .a .b :=
  dependence_implies_causation _ _ _ _ _ simple_dependence

end SimpleCause

namespace Chain

inductive V | a | b | c
  deriving DecidableEq, Fintype, Repr

def varList : List V := [.a, .b, .c]

def graph : CausalGraph V := ⟨λ | .a => ∅ | .b => {.a} | .c => {.b}⟩

noncomputable def sem : BoolSEM V :=
  { graph := graph
    mech := λ v => match v with
      | .a => const (G := graph) false
      | .b => deterministic (λ ρ => ρ ⟨.a, by simp [graph]⟩)
      | .c => deterministic (λ ρ => ρ ⟨.b, by simp [graph]⟩) }

noncomputable instance : SEM.IsDeterministic sem where
  mech_det v := match v with
    | .a => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .b | .c => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

def bg : Valuation (λ _ : V => Bool) := Valuation.empty.extend .a true

/-- In a chain the distal cause passes the but-for test for the final effect. -/
theorem chain_direct_butfor : lewisButFor sem varList bg .a .c := by
  unfold lewisButFor; intro h
  exact Bool.false_ne_true (Option.some.inj h)

/-- The middle event depends on the first. -/
theorem chain_step_AB : lewisDependence sem varList bg .a .b :=
  ⟨by rfl, by rfl, by unfold lewisButFor; intro h; exact Bool.false_ne_true (Option.some.inj h)⟩

/-- The final event depends on the middle one. -/
theorem chain_step_BC : lewisDependence sem varList bg .b .c := by
  refine ⟨by rfl, by rfl, ?_⟩
  unfold lewisButFor; intro h
  exact Bool.false_ne_true (Option.some.inj h)

/-- The first event causes the last through the chain. -/
theorem chain_causation : lewisCausation sem varList bg .a .c :=
  Relation.TransGen.trans
    (Relation.TransGen.single chain_step_AB)
    (Relation.TransGen.single chain_step_BC)

end Chain

namespace Epiphenomena

/-! The barometer reading and the storm are both effects of atmospheric pressure
(UNVERIFIED: p. 565): the analysis makes the pressure the cause of each and neither effect a
cause of the other. -/

inductive V | pressure | barometer | storm
  deriving DecidableEq, Fintype, Repr

def varList : List V := [.pressure, .barometer, .storm]

def graph : CausalGraph V :=
  ⟨λ | .pressure => ∅ | .barometer => {.pressure} | .storm => {.pressure}⟩

noncomputable def sem : BoolSEM V :=
  { graph := graph
    mech := λ v => match v with
      | .pressure => const (G := graph) false
      | .barometer => deterministic (λ ρ => ρ ⟨.pressure, by simp [graph]⟩)
      | .storm => deterministic (λ ρ => ρ ⟨.pressure, by simp [graph]⟩) }

noncomputable instance : SEM.IsDeterministic sem where
  mech_det v := match v with
    | .pressure => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .barometer | .storm => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

def bg : Valuation (λ _ : V => Bool) := Valuation.empty.extend .pressure true

/-- Pressure causes the barometer reading. -/
theorem pressure_causes_barometer : lewisDependence sem varList bg .pressure .barometer := by
  refine ⟨by rfl, by rfl, ?_⟩
  unfold lewisButFor; intro h
  exact Bool.false_ne_true (Option.some.inj h)

/-- Pressure causes the storm. -/
theorem pressure_causes_storm : lewisDependence sem varList bg .pressure .storm := by
  refine ⟨by rfl, by rfl, ?_⟩
  unfold lewisButFor; intro h
  exact Bool.false_ne_true (Option.some.inj h)

/-- The barometer does not cause the storm: intervening on the barometer leaves the
pressure, and so the storm, in place. -/
theorem barometer_not_causes_storm :
    ¬ (lewisDependence sem varList bg .barometer .storm) := by
  intro ⟨_, _, hButFor⟩
  apply hButFor
  rfl

/-- The storm does not cause the barometer reading. -/
theorem storm_not_causes_barometer :
    ¬ (lewisDependence sem varList bg .storm .barometer) := by
  intro ⟨_, _, hButFor⟩
  apply hButFor
  rfl

end Epiphenomena

namespace Overdetermination

/-! Symmetric overdetermination (UNVERIFIED: fn. 12): with two sufficient causes both
present, neither is necessary, so neither passes the but-for test. -/

inductive V | a | b | e
  deriving DecidableEq, Fintype, Repr

def varList : List V := [.a, .b, .e]

def graph : CausalGraph V := ⟨λ | .a => ∅ | .b => ∅ | .e => {.a, .b}⟩

noncomputable def sem : BoolSEM V :=
  { graph := graph
    mech := λ v => match v with
      | .a => const (G := graph) false
      | .b => const (G := graph) false
      | .e => deterministic (λ ρ =>
          ρ ⟨.a, by simp [graph]⟩ || ρ ⟨.b, by simp [graph]⟩) }

noncomputable instance : SEM.IsDeterministic sem where
  mech_det v := match v with
    | .a | .b => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .e => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

/-- Both causes present. -/
def bg : Valuation (λ _ : V => Bool) :=
  Valuation.empty.extend .a true |>.extend .b true

/-- Neither overdetermining cause passes the but-for test. -/
theorem overdetermination_no_butfor_a : ¬ lewisButFor sem varList bg .a .e := by
  unfold lewisButFor; push Not; rfl

theorem overdetermination_no_butfor_b : ¬ lewisButFor sem varList bg .b .e := by
  unfold lewisButFor; push Not; rfl

/-- Neither overdetermining cause is one the effect depends on. -/
theorem overdetermination_no_dependence_a : ¬ lewisDependence sem varList bg .a .e := by
  intro ⟨_, _, h⟩; exact overdetermination_no_butfor_a h

theorem overdetermination_no_dependence_b : ¬ lewisDependence sem varList bg .b .e := by
  intro ⟨_, _, h⟩; exact overdetermination_no_butfor_b h

end Overdetermination

end Lewis1973
