import Linglib.Semantics.Causation.SEM.Bool
import Linglib.Semantics.Causation.SEM.Counterfactual
import Linglib.Semantics.Causation.CCSelection
import Linglib.Semantics.Aspect.SubeventStructure

/-!
# Progressive Aspect and Causal Structure
[nadathur-bar-asher-siegal-2024] [bar-asher-siegal-2026] [dowty-1979]

The progressive picks out type-level causal processes rather than
token-level completed events. This module formalizes the distinction
using V2 SEMs, following [nadathur-bar-asher-siegal-2024]'s
reframing of the imperfective paradox through causal models.

## Type-Level vs Token-Level

[bar-asher-siegal-2026]: SEM models distinguish two levels:
- **Type-level**: General causal structure (graph + mechanisms).
- **Token-level**: A specific causal trajectory completed in the actual world.

## The Imperfective Paradox

"Mary was opening the door" (progressive) vs "Mary opened the door"
(perfective). The progressive entails the process is underway but NOT
that it completed. "Mary was opening the door (when it got stuck)" is
coherent — type-level process in progress, token-level result never obtained.

## V2 substrate

`CausalProcess V` is polymorphic over the vertex type. `progressiveTrue`
checks type-level sufficiency (`BoolSEM.causallySufficient`);
`perfectiveTrue` adds token-level but-for completion
(`CCSelection.completesForEffect`).
-/

namespace Causation.Progressive

open Intensional (WorldTimeIndex)
open Causation Causation.Mechanism Causation.SEM

/-! ### Causal Process -/

/-- A causal process for telic predicates, parameterized over a vertex type `V`.

    Bundles a `BoolSEM V` (the type-level causal model), an explicit
    vertex list (proof-side only: feeds `developDetOn` computations in
    `decide`-based proofs), the initiating action vertex, the result
    vertex, and any enabling-condition valuation. -/
structure CausalProcess (V : Type*) [Fintype V] [DecidableEq V] where
  /-- The type-level causal model. -/
  M : BoolSEM V
  /-- Topologically-ordered vertex list. Proof-side only: not consumed
      by the semantic predicates, but useful for `developDetOn`-based
      `decide` proofs about concrete processes. -/
  vertexList : List V
  /-- The initiating action vertex. -/
  initiator : V
  /-- The result-state vertex. -/
  result : V
  /-- Background enabling conditions (default: empty). -/
  enablingConditions : Valuation (fun _ : V => Bool) := Valuation.empty

namespace CausalProcess

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Progressive vs Perfective Semantics -/

/-- Type-level sufficiency: the causal trajectory from initiator to
    result exists. The progressive asserts this — no commitment to the
    result actually obtaining in the actual world. -/
noncomputable def typeLevelHolds (proc : CausalProcess V)
    [CausalGraph.IsDAG proc.M.graph] [SEM.IsDeterministic proc.M] : Prop :=
  BoolSEM.causallySufficient proc.M proc.enablingConditions
    proc.initiator proc.result

noncomputable instance (proc : CausalProcess V)
    [CausalGraph.IsDAG proc.M.graph] [SEM.IsDeterministic proc.M] :
    Decidable proc.typeLevelHolds := Classical.dec _

/-- Progressive semantics: type-level process underway, completion open. -/
noncomputable def progressiveTrue (proc : CausalProcess V)
    [CausalGraph.IsDAG proc.M.graph] [SEM.IsDeterministic proc.M] : Prop :=
  proc.typeLevelHolds

noncomputable instance (proc : CausalProcess V)
    [CausalGraph.IsDAG proc.M.graph] [SEM.IsDeterministic proc.M] :
    Decidable proc.progressiveTrue := Classical.dec _

/-- But-for completion test (`CCSelection.completesForEffect`): cause
    being true → effect; cause being false → ¬ effect. -/
noncomputable def completesForEffect (proc : CausalProcess V)
    [CausalGraph.IsDAG proc.M.graph] [SEM.IsDeterministic proc.M] : Prop :=
  CCSelection.completesForEffect proc.M proc.enablingConditions
    proc.initiator true false proc.result true

noncomputable instance (proc : CausalProcess V)
    [CausalGraph.IsDAG proc.M.graph] [SEM.IsDeterministic proc.M] :
    Decidable proc.completesForEffect := Classical.dec _

/-- Perfective semantics: token-level causation completed.

    Holds when the causal chain ran to completion AND the initiator was
    necessary (removing it would prevent the result). This captures
    "Mary opened the door." -/
noncomputable def perfectiveTrue (proc : CausalProcess V)
    [CausalGraph.IsDAG proc.M.graph] [SEM.IsDeterministic proc.M] : Prop :=
  proc.completesForEffect

noncomputable instance (proc : CausalProcess V)
    [CausalGraph.IsDAG proc.M.graph] [SEM.IsDeterministic proc.M] :
    Decidable proc.perfectiveTrue := Classical.dec _

end CausalProcess

/-! ### Imperfective Paradox: maryOpening -/

/-! Example: "Mary was opening the door" / "Mary opened the door."
    Simple model: Mary's action → door opens. -/

/-- Vertex type for the door-opening example. -/
inductive MaryVar | action | doorOpen
  deriving DecidableEq, Fintype, Repr

def maryVarList : List MaryVar := [.action, .doorOpen]

/-- Door-opening graph: doorOpen ← action. -/
def maryGraph : CausalGraph MaryVar :=
  ⟨fun | .action => ∅ | .doorOpen => {.action}⟩

instance : CausalGraph.IsDAG maryGraph :=
  CausalGraph.IsDAG.of_depth maryGraph (fun | .action => 0 | .doorOpen => 1)
    (by intro u v h; revert h; cases u <;> cases v <;> decide)

/-- Door-opening SEM: doorOpen := action. -/
noncomputable def marySEM : BoolSEM MaryVar :=
  { graph := maryGraph
    mech := fun v => match v with
      | .action => const (G := maryGraph) false
      | .doorOpen => deterministic (fun ρ => ρ ⟨.action, by simp [maryGraph]⟩) }

noncomputable instance : SEM.IsDeterministic marySEM where
  mech_det v := match v with
    | .action => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .doorOpen => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

noncomputable def maryOpening : CausalProcess MaryVar :=
  { M := marySEM, vertexList := maryVarList,
    initiator := .action, result := .doorOpen }

noncomputable instance : SEM.IsDeterministic maryOpening.M :=
  inferInstanceAs (SEM.IsDeterministic marySEM)

instance : CausalGraph.IsDAG maryOpening.M.graph :=
  inferInstanceAs (CausalGraph.IsDAG maryGraph)

/-- The progressive is true: Mary's action is type-level sufficient. -/
theorem maryOpening_progressive : maryOpening.progressiveTrue := by
  unfold CausalProcess.progressiveTrue CausalProcess.typeLevelHolds
  exact SEM.developDet_hasValue_of_developDetOn_hasValue
    (vs := maryVarList) (n := 1) (by decide)

/-- The perfective is true: Mary's action completed the process. -/
theorem maryOpening_perfective : maryOpening.perfectiveTrue := by
  unfold CausalProcess.perfectiveTrue CausalProcess.completesForEffect
  exact CCSelection.completesForEffect_of_developDetOn maryVarList 1
    (by decide) (by decide)

/-- Perfective entails progressive (for the same process). -/
theorem perfective_entails_progressive {V : Type*} [Fintype V] [DecidableEq V]
    (proc : CausalProcess V)
    [CausalGraph.IsDAG proc.M.graph] [SEM.IsDeterministic proc.M]
    (h : proc.perfectiveTrue) :
    proc.progressiveTrue := h.1

/-! ### Imperfective Paradox: overdetermination witness -/

/-! Witness for `progressive ∧ ¬ perfective`: an overdetermination model
    where the type-level process exists but the actual outcome would
    obtain regardless of the initiator. -/

/-- 3-vertex overdetermination model: A and B both cause R (disjunctively).
    With B in the background, A is sufficient but not necessary. -/
inductive OdVar | a | b | r
  deriving DecidableEq, Fintype, Repr

def odVarList : List OdVar := [.a, .b, .r]

def odGraph : CausalGraph OdVar :=
  ⟨fun | .a => ∅ | .b => ∅ | .r => {.a, .b}⟩

instance : CausalGraph.IsDAG odGraph :=
  CausalGraph.IsDAG.of_depth odGraph (fun | .a => 0 | .b => 0 | .r => 1)
    (by intro u v h; revert h; cases u <;> cases v <;> decide)

/-- R := A ∨ B (disjunctive overdetermination). -/
noncomputable def odSEM : BoolSEM OdVar :=
  { graph := odGraph
    mech := fun v => match v with
      | .a => const (G := odGraph) false
      | .b => const (G := odGraph) false
      | .r => deterministic (fun ρ =>
          ρ ⟨.a, by simp [odGraph]⟩ || ρ ⟨.b, by simp [odGraph]⟩) }

noncomputable instance : SEM.IsDeterministic odSEM where
  mech_det v := match v with
    | .a | .b => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .r => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

noncomputable def overdetProc : CausalProcess OdVar :=
  { M := odSEM, vertexList := odVarList,
    initiator := .a, result := .r,
    enablingConditions := Valuation.empty.extend .b true }

noncomputable instance : SEM.IsDeterministic overdetProc.M :=
  inferInstanceAs (SEM.IsDeterministic odSEM)

instance : CausalGraph.IsDAG overdetProc.M.graph :=
  inferInstanceAs (CausalGraph.IsDAG odGraph)

/-- Progressive holds for the overdetermination witness. -/
theorem overdet_progressive : overdetProc.progressiveTrue := by
  unfold CausalProcess.progressiveTrue CausalProcess.typeLevelHolds
  exact SEM.developDet_hasValue_of_developDetOn_hasValue
    (vs := odVarList) (n := 1) (by decide)

/-- Perfective FAILS for the overdetermination witness — even with
    `initiator = false`, the backup B in `enablingConditions` produces
    the result, so the but-for half of `completesForEffect` fails. -/
theorem overdet_not_perfective : ¬ overdetProc.perfectiveTrue := by
  intro h
  exact h.2 (SEM.developDet_hasValue_of_developDetOn_hasValue
    (vs := odVarList) (n := 1) (by decide))

/-- **Imperfective paradox**: progressive does NOT entail perfective.
    Witnessed by the overdetermination scenario. -/
theorem progressive_not_entails_perfective :
    overdetProc.progressiveTrue ∧ ¬ overdetProc.perfectiveTrue :=
  ⟨overdet_progressive, overdet_not_perfective⟩

/-! ### Type-level = development under inertia (Dowty 1979) -/

/-- [dowty-1979]: the progressive is true iff the outcome holds in
    all inertia worlds (normal continuations). The causal model account
    refines this: "normal continuation" means "the SEM develops the
    initiator into the result" — i.e., type-level sufficiency. -/
theorem typeLevelHolds_is_develop {V : Type*} [Fintype V] [DecidableEq V]
    (proc : CausalProcess V)
    [CausalGraph.IsDAG proc.M.graph] [SEM.IsDeterministic proc.M] :
    proc.typeLevelHolds ↔
    (proc.M.developDet
      (proc.enablingConditions.extend proc.initiator true)).hasValue proc.result true :=
  Iff.rfl

/-! ### Bridge to Temporal Decomposition -/

/-- A causally grounded telic event: bridges `CausalProcess` (causal
    explanation) with `SubeventPhases` (temporal realization).

    [nadathur-bar-asher-siegal-2024]: telic predicates encode
    structured causal models. The activity phase corresponds to the
    initiating action; the result phase corresponds to the effect
    variable. The causal model explains WHY the activity leads to the
    result: the initiator is type-level sufficient. -/
structure CausallyGroundedEvent (V : Type*) [Fintype V] [DecidableEq V]
    (Time : Type*) [LinearOrder Time] where
  /-- The causal process underlying the event -/
  process : CausalProcess V
  /-- IsDAG instance for process.M.graph (carried explicitly). -/
  dagInst : CausalGraph.IsDAG process.M.graph
  /-- IsDeterministic instance for proc.M (carried explicitly). -/
  detInst : SEM.IsDeterministic process.M
  /-- The temporal phases: activity and result with ordering -/
  phases : Semantics.Aspect.SubeventStructure.SubeventPhases Time
  /-- The causal trajectory is viable: initiator is type-level sufficient. -/
  causallyViable : @CausalProcess.typeLevelHolds V _ _ process dagInst detInst

end Causation.Progressive
