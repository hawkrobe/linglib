import Linglib.Core.Causal.V2.SEM.Bool
import Linglib.Core.Causal.V2.SEM.Counterfactual
import Linglib.Core.WorldTimeIndex
import Mathlib.Logic.Relation

/-!
# @cite{lewis-1973-causation}: Causation

@cite{lewis-1973-causation}

Formalization of Lewis's counterfactual analysis of causation against
the V2 SEM substrate.

## Three Key Concepts

1. **Causal dependence** (p. 563): e depends causally on c iff the
   counterfactual "if c had not occurred, e would not have occurred"
   holds — the but-for test.

2. **Causation** (p. 563): the transitive closure of causal dependence.
   c causes e iff there exists a causal chain from c to e where each
   consecutive pair is a causal dependence. Defined via mathlib's
   `Relation.TransGen`.

3. **Epiphenomena asymmetry** (p. 565): intervention-based counterfactuals
   correctly distinguish genuine causes from mere correlates. The
   barometer does not cause the storm, even though they are correlated
   via atmospheric pressure.

## Bridge to Linglib Infrastructure

Lewis's causal dependence corresponds to the simple but-for test in our
V2 SEM framework. For exogenous causes, `lewisButFor` is structurally
identical to `¬ BoolSEM.causallySufficient` with the alternative cause-value.

The key difference from @cite{nadathur-2024} Def 10b (`causallyNecessary`):
Lewis's but-for operates on the actual world via minimal intervention,
while Def 10b quantifies over consistent supersituations. For simple models
they agree; for complex models with alternative pathways, Def 10b is
strictly stronger. Bridge theorems comparing Lewis to Nadathur 2024 await
the Necessity hub migration to V2.

## Limitations

@cite{lewis-1973-causation} acknowledges two limitations:

- **Overdetermination** (fn. 12): symmetric overdetermination cases are
  excluded — neither overdetermining cause passes the but-for test.
- **Late preemption**: the transitive closure mechanism handles early
  preemption but struggles with late preemption.
-/

namespace Lewis1973

open Core (WorldTimeIndex)
open Core.Causal.V2 Core.Causal.V2.Mechanism Core.Causal.V2.SEM

-- ════════════════════════════════════════════════════
-- § 1. Lewis's Counterfactual Predicates (V2)
-- ════════════════════════════════════════════════════

/-- Lewis's but-for counterfactual: setting cause to `false` (the absent
    value) prevents the effect under `developDetOn`.

    "If c had not occurred, e would not have occurred." Polymorphic
    over the vertex type W so each scenario can use its own enum. -/
noncomputable def lewisButFor {W : Type*} [Fintype W] [DecidableEq W]
    (M : BoolSEM W) [SEM.IsDeterministic M]
    (vs : List W) (bg : Valuation (fun _ : W => Bool))
    (cause effect : W) : Prop :=
  ¬ (developDetOn M vs 1 (bg.extend cause false)).hasValue effect true

noncomputable instance {W : Type*} [Fintype W] [DecidableEq W]
    (M : BoolSEM W) [SEM.IsDeterministic M]
    (vs : List W) (bg : Valuation _) (cause effect : W) :
    Decidable (lewisButFor M vs bg cause effect) := Classical.dec _

/-- Lewis's causal dependence (@cite{lewis-1973-causation} p. 563).

    Three conjuncts: cause develops, effect develops, and without cause
    the effect does not developDet. -/
noncomputable def lewisDependence {W : Type*} [Fintype W] [DecidableEq W]
    (M : BoolSEM W) [SEM.IsDeterministic M]
    (vs : List W) (bg : Valuation (fun _ : W => Bool))
    (cause effect : W) : Prop :=
  (developDetOn M vs 1 bg).hasValue cause true ∧
  (developDetOn M vs 1 bg).hasValue effect true ∧
  lewisButFor M vs bg cause effect

noncomputable instance {W : Type*} [Fintype W] [DecidableEq W]
    (M : BoolSEM W) [SEM.IsDeterministic M]
    (vs : List W) (bg : Valuation _) (cause effect : W) :
    Decidable (lewisDependence M vs bg cause effect) := Classical.dec _

/-- Lewis's causation: transitive closure of causal dependence
    (@cite{lewis-1973-causation} p. 563), via `Relation.TransGen`. -/
def lewisCausation {W : Type*} [Fintype W] [DecidableEq W]
    (M : BoolSEM W) [SEM.IsDeterministic M]
    (vs : List W) (bg : Valuation (fun _ : W => Bool))
    (cause effect : W) : Prop :=
  Relation.TransGen (lewisDependence M vs bg) cause effect

/-- Causal dependence implies causation (one-step chain). -/
theorem dependence_implies_causation {W : Type*} [Fintype W] [DecidableEq W]
    (M : BoolSEM W) [SEM.IsDeterministic M]
    (vs : List W) (bg : Valuation _) (cause effect : W)
    (h : lewisDependence M vs bg cause effect) :
    lewisCausation M vs bg cause effect :=
  Relation.TransGen.single h

-- ════════════════════════════════════════════════════
-- § 2. Simple Cause: A → B
-- ════════════════════════════════════════════════════

namespace SimpleCause

inductive V | a | b
  deriving DecidableEq, Fintype, Repr

def varList : List V := [.a, .b]

def graph : CausalGraph V := ⟨fun | .a => ∅ | .b => {.a}⟩

noncomputable def sem : BoolSEM V :=
  { graph := graph
    mech := fun v => match v with
      | .a => const (G := graph) false
      | .b => deterministic (fun ρ => ρ ⟨.a, by simp [graph]⟩) }

noncomputable instance : SEM.IsDeterministic sem where
  mech_det v := match v with
    | .a => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .b => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

def bg : Valuation (fun _ : V => Bool) := Valuation.empty.extend .a true

/-- Lewis's but-for holds for a simple cause. -/
theorem simple_butfor : lewisButFor sem varList bg .a .b := by
  unfold lewisButFor; intro h
  exact Bool.false_ne_true (Option.some.inj h)

/-- Lewis's causal dependence holds for a simple cause. -/
theorem simple_dependence : lewisDependence sem varList bg .a .b :=
  ⟨by rfl, by rfl, simple_butfor⟩

/-- Lewis's causation holds (trivially, one-step chain). -/
theorem simple_causation : lewisCausation sem varList bg .a .b :=
  dependence_implies_causation _ _ _ _ _ simple_dependence

end SimpleCause

-- ════════════════════════════════════════════════════
-- § 3. Causal Chain: A → B → C
-- ════════════════════════════════════════════════════

namespace Chain

inductive V | a | b | c
  deriving DecidableEq, Fintype, Repr

def varList : List V := [.a, .b, .c]

def graph : CausalGraph V := ⟨fun | .a => ∅ | .b => {.a} | .c => {.b}⟩

noncomputable def sem : BoolSEM V :=
  { graph := graph
    mech := fun v => match v with
      | .a => const (G := graph) false
      | .b => deterministic (fun ρ => ρ ⟨.a, by simp [graph]⟩)
      | .c => deterministic (fun ρ => ρ ⟨.b, by simp [graph]⟩) }

noncomputable instance : SEM.IsDeterministic sem where
  mech_det v := match v with
    | .a => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .b | .c => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

def bg : Valuation (fun _ : V => Bool) := Valuation.empty.extend .a true

/-- In the chain A→B→C, removing A prevents C. -/
theorem chain_direct_butfor : lewisButFor sem varList bg .a .c := by
  unfold lewisButFor; intro h
  exact Bool.false_ne_true (Option.some.inj h)

/-- B depends on A. -/
theorem chain_step_AB : lewisDependence sem varList bg .a .b :=
  ⟨by rfl, by rfl, by unfold lewisButFor; intro h; exact Bool.false_ne_true (Option.some.inj h)⟩

/-- C depends on B. -/
theorem chain_step_BC : lewisDependence sem varList bg .b .c := by
  refine ⟨by rfl, by rfl, ?_⟩
  unfold lewisButFor; intro h
  exact Bool.false_ne_true (Option.some.inj h)

/-- Lewis's causation via the full chain A→B→C. -/
theorem chain_causation : lewisCausation sem varList bg .a .c :=
  Relation.TransGen.trans
    (Relation.TransGen.single chain_step_AB)
    (Relation.TransGen.single chain_step_BC)

end Chain

-- ════════════════════════════════════════════════════
-- § 4. Epiphenomena: Barometer and Storm
-- ════════════════════════════════════════════════════

namespace Epiphenomena

/-! @cite{lewis-1973-causation} p. 565: barometer reading (B) and storm (S)
    are both effects of atmospheric pressure (P). The counterfactual analysis
    correctly identifies P as the common cause and rejects spurious
    "barometer causes storm" inference. -/

inductive V | pressure | barometer | storm
  deriving DecidableEq, Fintype, Repr

def varList : List V := [.pressure, .barometer, .storm]

def graph : CausalGraph V :=
  ⟨fun | .pressure => ∅ | .barometer => {.pressure} | .storm => {.pressure}⟩

noncomputable def sem : BoolSEM V :=
  { graph := graph
    mech := fun v => match v with
      | .pressure => const (G := graph) false
      | .barometer => deterministic (fun ρ => ρ ⟨.pressure, by simp [graph]⟩)
      | .storm => deterministic (fun ρ => ρ ⟨.pressure, by simp [graph]⟩) }

noncomputable instance : SEM.IsDeterministic sem where
  mech_det v := match v with
    | .pressure => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .barometer | .storm => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

def bg : Valuation (fun _ : V => Bool) := Valuation.empty.extend .pressure true

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

/-- The barometer does NOT cause the storm.

    @cite{lewis-1973-causation} p. 565: intervention on the barometer
    (do(B=false)) cuts B's incoming law (P→B) but leaves P→S intact.
    P still causes S regardless of B. -/
theorem barometer_not_causes_storm :
    ¬ (lewisDependence sem varList bg .barometer .storm) := by
  intro ⟨_, _, hButFor⟩
  apply hButFor
  rfl

/-- The storm does NOT cause the barometer. -/
theorem storm_not_causes_barometer :
    ¬ (lewisDependence sem varList bg .storm .barometer) := by
  intro ⟨_, _, hButFor⟩
  apply hButFor
  rfl

end Epiphenomena

-- ════════════════════════════════════════════════════
-- § 5. Overdetermination
-- ════════════════════════════════════════════════════

namespace Overdetermination

/-! @cite{lewis-1973-causation} fn. 12: symmetric overdetermination cases
    are excluded — neither overdetermining factor passes the but-for test.

    Model: A ∨ B → E. With both present, neither is necessary. -/

inductive V | a | b | e
  deriving DecidableEq, Fintype, Repr

def varList : List V := [.a, .b, .e]

def graph : CausalGraph V := ⟨fun | .a => ∅ | .b => ∅ | .e => {.a, .b}⟩

noncomputable def sem : BoolSEM V :=
  { graph := graph
    mech := fun v => match v with
      | .a => const (G := graph) false
      | .b => const (G := graph) false
      | .e => deterministic (fun ρ =>
          ρ ⟨.a, by simp [graph]⟩ || ρ ⟨.b, by simp [graph]⟩) }

noncomputable instance : SEM.IsDeterministic sem where
  mech_det v := match v with
    | .a | .b => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .e => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

/-- Both causes present. -/
def bg : Valuation (fun _ : V => Bool) :=
  Valuation.empty.extend .a true |>.extend .b true

/-- Neither overdetermining cause passes the but-for test (B alive when A
    removed; A alive when B removed). -/
theorem overdetermination_no_butfor_a : ¬ lewisButFor sem varList bg .a .e := by
  unfold lewisButFor; push_neg; rfl

theorem overdetermination_no_butfor_b : ¬ lewisButFor sem varList bg .b .e := by
  unfold lewisButFor; push_neg; rfl

/-- Neither overdetermining cause is a Lewis causal dependent. -/
theorem overdetermination_no_dependence_a : ¬ lewisDependence sem varList bg .a .e := by
  intro ⟨_, _, h⟩; exact overdetermination_no_butfor_a h

theorem overdetermination_no_dependence_b : ¬ lewisDependence sem varList bg .b .e := by
  intro ⟨_, _, h⟩; exact overdetermination_no_butfor_b h

end Overdetermination

end Lewis1973
