import Linglib.Core.Causal.V2.SEM.Bool
import Linglib.Core.Causal.V2.SEM.Counterfactual
import Linglib.Theories.Semantics.Events.TemporalDecomposition

/-!
# Progressive Aspect and Causal Structure
@cite{nadathur-bar-asher-siegal-2024} @cite{bar-asher-siegal-2026} @cite{dowty-1979}

The progressive picks out type-level causal processes rather than
token-level completed events. This module formalizes the distinction
using V2 SEMs, following @cite{nadathur-bar-asher-siegal-2024}'s
reframing of the imperfective paradox through causal models.

## Type-Level vs Token-Level

@cite{bar-asher-siegal-2026}: SEM models distinguish two levels:
- **Type-level**: General causal structure (graph + mechanisms).
- **Token-level**: A specific causal trajectory completed in the actual world.

## The Imperfective Paradox

"Mary was opening the door" (progressive) vs "Mary opened the door"
(perfective). The progressive entails the process is underway but NOT
that it completed. "Mary was opening the door (when it got stuck)" is
coherent — type-level process in progress, token-level result never obtained.

## V2 substrate

`CausalProcess V` is polymorphic over the vertex type. `progressiveTrue`
checks type-level sufficiency (the cause develops to the result via
`developDetOn`). `perfectiveTrue` adds token-level completion via a local
`completesForEffect` (defined inline to avoid the CCSelection cascade
during the V2 migration period).
-/

namespace Semantics.Causation.Progressive

open Core (WorldTimeIndex)
open Core.Causal.V2 Core.Causal.V2.Mechanism Core.Causal.V2.SEM

-- ════════════════════════════════════════════════════
-- § 1. Causal Process (V2)
-- ════════════════════════════════════════════════════

/-- A causal process for telic predicates, parameterized over a vertex type `V`.

    Bundles a `BoolSEM V` (the type-level causal model), an explicit
    vertex list (for `developDetOn`-based kernel reduction), the initiating
    action vertex, the result vertex, and any enabling-condition valuation. -/
structure CausalProcess (V : Type*) [Fintype V] [DecidableEq V] where
  /-- The type-level causal model. -/
  M : BoolSEM V
  /-- Topologically-ordered vertex list for structural unfolding. -/
  vertexList : List V
  /-- The initiating action vertex. -/
  initiator : V
  /-- The result-state vertex. -/
  result : V
  /-- Background enabling conditions (default: empty). -/
  enablingConditions : Valuation (fun _ : V => Bool) := Valuation.empty

namespace CausalProcess

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ════════════════════════════════════════════════════
-- § 2. Progressive vs Perfective Semantics
-- ════════════════════════════════════════════════════

/-- Type-level sufficiency: the causal trajectory from initiator to
    result exists. The progressive asserts this — no commitment to the
    result actually obtaining in the actual world. -/
noncomputable def typeLevelHolds (proc : CausalProcess V)
    [SEM.IsDeterministic proc.M] : Prop :=
  (developDetOn proc.M proc.vertexList 1
    (proc.enablingConditions.extend proc.initiator true)).hasValue proc.result true

noncomputable instance (proc : CausalProcess V) [SEM.IsDeterministic proc.M] :
    Decidable proc.typeLevelHolds := Classical.dec _

/-- Progressive semantics: type-level process underway, completion open. -/
noncomputable def progressiveTrue (proc : CausalProcess V)
    [SEM.IsDeterministic proc.M] : Prop :=
  proc.typeLevelHolds

noncomputable instance (proc : CausalProcess V) [SEM.IsDeterministic proc.M] :
    Decidable proc.progressiveTrue := Classical.dec _

/-- Local but-for completion test (avoids CCSelection import during migration):
    cause being true → effect; cause being false → ¬ effect. -/
noncomputable def completesForEffect (proc : CausalProcess V)
    [SEM.IsDeterministic proc.M] : Prop :=
  (developDetOn proc.M proc.vertexList 1
    (proc.enablingConditions.extend proc.initiator true)).hasValue proc.result true ∧
  ¬ (developDetOn proc.M proc.vertexList 1
      (proc.enablingConditions.extend proc.initiator false)).hasValue proc.result true

noncomputable instance (proc : CausalProcess V) [SEM.IsDeterministic proc.M] :
    Decidable proc.completesForEffect := Classical.dec _

/-- Perfective semantics: token-level causation completed.

    Holds when the causal chain ran to completion AND the initiator was
    necessary (removing it would prevent the result). This captures
    "Mary opened the door." -/
noncomputable def perfectiveTrue (proc : CausalProcess V)
    [SEM.IsDeterministic proc.M] : Prop :=
  proc.completesForEffect

noncomputable instance (proc : CausalProcess V) [SEM.IsDeterministic proc.M] :
    Decidable proc.perfectiveTrue := Classical.dec _

end CausalProcess

-- ════════════════════════════════════════════════════
-- § 3. Imperfective Paradox: maryOpening
-- ════════════════════════════════════════════════════

/-! Example: "Mary was opening the door" / "Mary opened the door."
    Simple model: Mary's action → door opens. -/

/-- Vertex type for the door-opening example. -/
inductive MaryVar | action | doorOpen
  deriving DecidableEq, Fintype, Repr

def maryVarList : List MaryVar := [.action, .doorOpen]

/-- Door-opening graph: doorOpen ← action. -/
def maryGraph : CausalGraph MaryVar :=
  ⟨fun | .action => ∅ | .doorOpen => {.action}⟩

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

/-- The progressive is true: Mary's action is type-level sufficient. -/
theorem maryOpening_progressive : maryOpening.progressiveTrue := by
  unfold CausalProcess.progressiveTrue CausalProcess.typeLevelHolds
  rfl

/-- The perfective is true: Mary's action completed the process. -/
theorem maryOpening_perfective : maryOpening.perfectiveTrue := by
  refine ⟨?_, ?_⟩
  · rfl
  · intro h; exact Bool.false_ne_true (Option.some.inj h)

/-- Perfective entails progressive (for the same process). -/
theorem perfective_entails_progressive {V : Type*} [Fintype V] [DecidableEq V]
    (proc : CausalProcess V) [SEM.IsDeterministic proc.M]
    (h : proc.perfectiveTrue) :
    proc.progressiveTrue := h.1

-- ════════════════════════════════════════════════════
-- § 4. Imperfective Paradox: overdetermination witness
-- ════════════════════════════════════════════════════

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

/-- Progressive holds for the overdetermination witness. -/
theorem overdet_progressive : overdetProc.progressiveTrue := by
  unfold CausalProcess.progressiveTrue CausalProcess.typeLevelHolds
  rfl

/-- Perfective FAILS for the overdetermination witness — even with
    `initiator = false`, the backup B in `enablingConditions` produces
    the result. -/
theorem overdet_not_perfective : ¬ overdetProc.perfectiveTrue := by
  intro ⟨_, hNot⟩
  apply hNot
  rfl

/-- **Imperfective paradox**: progressive does NOT entail perfective.
    Witnessed by the overdetermination scenario. -/
theorem progressive_not_entails_perfective :
    overdetProc.progressiveTrue ∧ ¬ overdetProc.perfectiveTrue :=
  ⟨overdet_progressive, overdet_not_perfective⟩

-- ════════════════════════════════════════════════════
-- § 5. Type-level = development under inertia (Dowty 1979)
-- ════════════════════════════════════════════════════

/-- @cite{dowty-1979}: the progressive is true iff the outcome holds in
    all inertia worlds (normal continuations). The causal model account
    refines this: "normal continuation" means "the SEM develops the
    initiator into the result" — i.e., type-level sufficiency. -/
theorem typeLevelHolds_is_developOn {V : Type*} [Fintype V] [DecidableEq V]
    (proc : CausalProcess V) [SEM.IsDeterministic proc.M] :
    proc.typeLevelHolds ↔
    (developDetOn proc.M proc.vertexList 1
      (proc.enablingConditions.extend proc.initiator true)).hasValue proc.result true :=
  Iff.rfl

-- ════════════════════════════════════════════════════
-- § 6. Bridge to Temporal Decomposition
-- ════════════════════════════════════════════════════

/-- A causally grounded telic event: bridges `CausalProcess` (causal
    explanation) with `SubeventPhases` (temporal realization).

    @cite{nadathur-bar-asher-siegal-2024}: telic predicates encode
    structured causal models. The activity phase corresponds to the
    initiating action; the result phase corresponds to the effect
    variable. The causal model explains WHY the activity leads to the
    result: the initiator is type-level sufficient. -/
structure CausallyGroundedEvent (V : Type*) [Fintype V] [DecidableEq V]
    (Time : Type*) [LinearOrder Time] where
  /-- The causal process underlying the event -/
  process : CausalProcess V
  /-- IsDeterministic instance for proc.M (carried explicitly). -/
  detInst : SEM.IsDeterministic process.M
  /-- The temporal phases: activity and result with ordering -/
  phases : Semantics.Events.SubeventPhases Time
  /-- The causal trajectory is viable: initiator is type-level sufficient. -/
  causallyViable : @CausalProcess.typeLevelHolds V _ _ process detInst

end Semantics.Causation.Progressive
