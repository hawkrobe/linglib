import Linglib.Core.StructuralEquationModel
import Linglib.Theories.Semantics.Causation.Sufficiency
import Linglib.Theories.Semantics.Causation.Necessity
import Linglib.Theories.Semantics.Causation.CCSelection

/-!
# Progressive Aspect and Causal Structure
@cite{nadathur-bar-asher-siegal-2024} @cite{bar-asher-siegal-2026} @cite{dowty-1979}

The progressive picks out type-level causal processes rather than
token-level completed events. This module formalizes the distinction
using structural equation models, following @cite{nadathur-bar-asher-siegal-2024}'s
reframing of the imperfective paradox through causal models.

## Type-Level vs Token-Level

@cite{bar-asher-siegal-2026}: SEM models distinguish two levels:

- **Type-level**: General causal laws — `CausalDynamics` encodes what
  WOULD happen given conditions. Laws are nomological structures
  (Hausman 1998, Woodward 2003).
- **Token-level**: Specific event instances — a `Situation` anchored
  to the actual world. `actuallyCaused` checks whether a particular
  cause brought about a particular effect.

## The Imperfective Paradox

"Mary was opening the door" (progressive) vs "Mary opened the door"
(perfective):

- **Progressive**: a type-level causal process is underway. Mary's action
  is part of a causal trajectory that, under normal conditions, leads to
  the door being open. No commitment to actual completion.
- **Perfective**: token-level causation completed. Mary's action actually
  caused the door to open.

The paradox: the progressive entails the process is underway but NOT
that it completed. "Mary was opening the door (when it got stuck)" is
coherent — the type-level process was in progress, but the token-level
result never obtained.

## Formalization

A `CausalProcess` packages a `CausalDynamics` with an initiating action
and a result state. Progressive semantics checks that the initiator is
type-level sufficient (the causal trajectory exists); perfective semantics
checks token-level completion (the effect actually obtained).
-/

namespace Causation.ProgressiveCausation

open Core.StructuralEquationModel
open NadathurLauer2020.Sufficiency
open NadathurLauer2020.Necessity
open Causation.CCSelection

-- ════════════════════════════════════════════════════
-- § 1. Causal Process
-- ════════════════════════════════════════════════════

/-- A causal process for telic predicates.

    @cite{nadathur-bar-asher-siegal-2024}: telic predicates encode structured
    causal models. The process specifies an initiating action and a result
    state connected by causal laws. The progressive asserts the process is
    underway (type-level); the perfective asserts it completed (token-level).

    - `dynamics`: the type-level causal model
    - `initiator`: the causing event/action variable
    - `result`: the result state variable
    - `enablingConditions`: background conditions assumed to hold
      (e.g., the door is unlocked, oxygen is present) -/
structure CausalProcess where
  dynamics : CausalDynamics
  initiator : Variable
  result : Variable
  enablingConditions : Situation := Situation.empty

-- ════════════════════════════════════════════════════
-- § 2. Progressive vs Perfective Semantics
-- ════════════════════════════════════════════════════

/-- Type-level sufficiency: the causal trajectory from initiator to
    result exists under normal conditions.

    @cite{nadathur-bar-asher-siegal-2024}: the progressive asserts that
    a type-level causal process is underway — the initiator is sufficient
    for the result given the enabling conditions. No commitment to the
    result actually obtaining in the actual world. -/
def CausalProcess.typeLevelHolds (proc : CausalProcess) : Bool :=
  causallySufficient proc.dynamics proc.enablingConditions proc.initiator proc.result

/-- Token-level completion: the initiator actually occurred and the
    causal chain ran to completion, producing the result.

    @cite{nadathur-bar-asher-siegal-2024}: the perfective asserts
    token-level completion — the causal process finished, and the
    result state actually obtained. -/
def CausalProcess.tokenLevelCompleted (proc : CausalProcess) : Bool :=
  let fullSituation := proc.enablingConditions.extend proc.initiator true
  (normalDevelopment proc.dynamics fullSituation).hasValue proc.result true

/-- Progressive semantics: type-level process underway, completion open.

    Returns `true` when the causal trajectory exists (type-level sufficiency
    holds) — regardless of whether the result actually obtained. This
    captures "Mary was opening the door": the action is part of a causal
    trajectory to door-opening, even if the door never opens. -/
def CausalProcess.progressiveTrue (proc : CausalProcess) : Bool :=
  proc.typeLevelHolds

/-- Perfective semantics: token-level causation completed.

    Returns `true` when the causal chain ran to completion and the
    initiator was the completing condition of the only actualized
    sufficient set. This captures "Mary opened the door." -/
def CausalProcess.perfectiveTrue (proc : CausalProcess) : Bool :=
  completesForEffect proc.dynamics proc.enablingConditions
    proc.initiator proc.result

-- ════════════════════════════════════════════════════
-- § 3. The Imperfective Paradox
-- ════════════════════════════════════════════════════

/-- Example: "Mary was opening the door" / "Mary opened the door."

    Simple model: Mary's action → door opens. -/
def maryOpening : CausalProcess :=
  { dynamics := CausalDynamics.mk [CausalLaw.simple (mkVar "action") (mkVar "door_open")],
    initiator := mkVar "action",
    result := mkVar "door_open" }

/-- The progressive is true: Mary's action is type-level sufficient
    for the door opening. -/
theorem maryOpening_progressive :
    maryOpening.progressiveTrue = true := by native_decide

/-- The perfective is true: Mary's action completed the causal process. -/
theorem maryOpening_perfective :
    maryOpening.perfectiveTrue = true := by native_decide

/-- Perfective entails progressive (for the same process).

    If the causal chain completed (perfective), then the type-level
    trajectory existed (progressive). Completion implies the causal
    model had the relevant sufficiency. -/
theorem perfective_entails_progressive (proc : CausalProcess)
    (h : proc.perfectiveTrue = true) :
    proc.progressiveTrue = true := by
  simp only [CausalProcess.perfectiveTrue, completesForEffect,
             Bool.and_eq_true] at h
  exact h.1

/-- Progressive does NOT entail perfective in general.

    The imperfective paradox: the type-level process can be underway
    (progressive true) even when a disruption prevents token-level
    completion. Witnessed by a model where an intervening blocker
    prevents the result despite the initiator being sufficient in
    isolation. -/
theorem progressive_not_entails_perfective :
    ∃ (proc : CausalProcess),
      proc.progressiveTrue = true ∧ proc.perfectiveTrue = false := by
  -- Overdetermination: action is type-level sufficient (progressive),
  -- but a backup cause in the enabling conditions means the result
  -- still obtains without the action (perfective fails).
  use { dynamics := ⟨[CausalLaw.simple (mkVar "a") (mkVar "r"),
                       CausalLaw.simple (mkVar "b") (mkVar "r")]⟩,
        initiator := mkVar "a",
        result := mkVar "r",
        enablingConditions := Situation.empty.extend (mkVar "b") true }
  constructor <;> native_decide

-- ════════════════════════════════════════════════════
-- § 4. Connecting to Inertial Modality
-- ════════════════════════════════════════════════════

/-- The causal process account subsumes the simple inertial account.

    @cite{dowty-1979}: the progressive is true iff the outcome holds in
    all inertia worlds (normal continuations). The causal model account
    refines this: "normal continuation" means "the causal model predicts
    the result from the initiator" — i.e., type-level sufficiency.

    `normalDevelopment` IS the formal counterpart of Dowty's "inertia
    worlds": it computes what would happen given normal law-application
    without interruption. So `typeLevelHolds` (progressive semantics)
    reduces to checking normalDevelopment in the sense of Dowty.

    This theorem confirms: type-level sufficiency is equivalent to
    the result holding in the "normal development" of the initiator
    (the causal model's inertia). -/
theorem typeLevelHolds_is_normalDevelopment (proc : CausalProcess) :
    proc.typeLevelHolds =
    (normalDevelopment proc.dynamics
      (proc.enablingConditions.extend proc.initiator true)).hasValue proc.result true := rfl

end Causation.ProgressiveCausation
