import Linglib.Discourse.CommonGround

/-!
# Dialogue state: the cross-framework scoreboard interface
[krifka-2015] [stalnaker-1978] [ginzburg-2012] [farkas-bruce-2010]

The `Discourse/` layer hosts many competing models of the conversational
scoreboard (Stalnaker common ground, Roberts' scoreboard, Farkas-Bruce's
Table, Krifka's commitment spaces, Ginzburg's per-participant gameboards).
They already share one projection — `CommonGround.HasContextSet`, extracting
the accepted-information set `Set W`. This file adds the *dynamic* half of the
interface: a shared event vocabulary, a step relation, and a completion
predicate, together with the law that ties them to the context-set observable.

## The completed-trace agreement

`groundedContent` is the **reference semantics**: the public content an event
sequence grounds, modelled as a proposal stack (`assert` proposes, `accept`
grounds the top by intersection, `reject` drops it). A framework is a
`LawfulDialogueState` when its context-set observable coincides with
`groundedContent` at every *completed* trace. The payoff
(`completedTrace_agreement`) is then immediate: any two lawful frameworks
agree on the context set at any commonly-completed trace — they may differ
arbitrarily on the journey through intermediate states, but agree on the
observable destination.

## Two grounding disciplines

Admitting this (lazy, accept-grounds) law is **not** the same as the eager
per-event narrowing of `Discourse.SpeechAct.Assertable` (where `assert`
narrows the context set immediately). The two coincide only on *balanced*
traces (every `assert` followed by `accept`); eager frameworks (Stalnaker,
Krifka) assume `propose = accept` ("perfect communication"), so their
observable runs ahead of `groundedContent` on unbalanced traces. Lazy,
grounding-explicit frameworks (Farkas-Bruce, Ginzburg) are the natural
`LawfulDialogueState` instances. (Verified empirically in the design spike:
the eager `Assertable ⟹ LawfulDialogueState` implication is *false*.)

## Main definitions

* `DialogueEvent W` — the shared event vocabulary.
* `groundedContent` — the proposal-stack reference semantics.
* `DialogueStep` — `init` / `step` / `isCompleted`.
* `LawfulDialogueState` — the law-bearing bundle (`contextSet_completed`).
* `completedTrace_agreement` — the framework-invariance theorem.
-/

namespace Discourse

open CommonGround (ContextSet HasContextSet)

universe u
variable {W : Type u}

/-! ### The shared event vocabulary -/

/-- A cross-framework dialogue event. The assertion/grounding fragment
(`assert`/`accept`/`reject`) drives the context-set observable; question
events raise issues without changing grounded content. Question events
(`polarQuestion`, `whQuestion`) keep the vocabulary expressive enough for
QUD-driven frameworks without privileging one framework's move set, and a
framework whose `step` predates a given event simply leaves the state
unchanged on it. -/
inductive DialogueEvent (W : Type u) where
  /-- Speaker proposes the proposition `p` (enters the proposal stack). -/
  | assert (p : Set W)
  /-- Speaker raises the polar question whether `p`. -/
  | polarQuestion (p : Set W)
  /-- Speaker raises a wh-question. -/
  | whQuestion
  /-- Addressee accepts the most recent proposal (grounds it). -/
  | accept
  /-- Addressee rejects the most recent proposal (drops it ungrounded). -/
  | reject

/-! ### The reference semantics -/

/-- The grounding machine: a floor of accepted content plus a stack of
proposals awaiting uptake. -/
structure GroundingState (W : Type u) where
  /-- Accepted (grounded) content. -/
  floor : Set W
  /-- Proposals awaiting acceptance, most recent first. -/
  pending : List (Set W)

namespace GroundingState

/-- The empty grounding state: everything possible, nothing pending. -/
def init : GroundingState W := ⟨Set.univ, []⟩

/-- One step of the reference machine. `assert` proposes, `accept` grounds the
top proposal by intersection, `reject` drops it; questions do not change
grounded content. -/
def step (s : GroundingState W) : DialogueEvent W → GroundingState W
  | .assert p => ⟨s.floor, p :: s.pending⟩
  | .accept   => match s.pending with
                 | p :: rest => ⟨s.floor ∩ p, rest⟩
                 | []        => s
  | .reject   => match s.pending with
                 | _ :: rest => ⟨s.floor, rest⟩
                 | []        => s
  | _         => s

end GroundingState

/-- The content an event sequence grounds: the floor of the reference machine
after replaying the events from `init`. -/
def groundedContent (es : List (DialogueEvent W)) : ContextSet W :=
  (es.foldl GroundingState.step GroundingState.init).floor

/-! ### The interface -/

/-- A discourse-state type that steps on `DialogueEvent`s and knows when a
trace is complete (no open proposals / issues). -/
class DialogueStep (S : Type u) (W : outParam (Type u)) where
  /-- The initial state. -/
  init : S
  /-- One update step. -/
  step : S → DialogueEvent W → S
  /-- Whether the state is conversationally complete. -/
  isCompleted : S → Prop

/-- Replay an event sequence from the initial state. -/
def DialogueStep.run {S : Type u} [DialogueStep S W]
    (es : List (DialogueEvent W)) : S :=
  es.foldl DialogueStep.step DialogueStep.init

/-- A discourse state whose context-set observable matches `groundedContent`
at every completed trace. This is the lazy, grounding-explicit discipline:
the observable reflects only grounded content, never open proposals. -/
class LawfulDialogueState (S : Type u) (W : outParam (Type u))
    extends HasContextSet S W, DialogueStep S W where
  /-- At a completed trace, the context set is exactly the grounded content. -/
  contextSet_completed : ∀ es : List (DialogueEvent W),
    isCompleted (es.foldl step init) →
      HasContextSet.toContextSet (es.foldl step init) = groundedContent es

/-- **Completed-trace agreement.** Any two lawful frameworks agree on the
context-set observable at any trace they both complete — regardless of how
their intermediate states differ. -/
theorem completedTrace_agreement {S₁ S₂ : Type u}
    [LawfulDialogueState S₁ W] [LawfulDialogueState S₂ W]
    (es : List (DialogueEvent W))
    (h₁ : DialogueStep.isCompleted (DialogueStep.run es : S₁))
    (h₂ : DialogueStep.isCompleted (DialogueStep.run es : S₂)) :
    HasContextSet.toContextSet (DialogueStep.run es : S₁)
      = HasContextSet.toContextSet (DialogueStep.run es : S₂) := by
  simp only [DialogueStep.run] at h₁ h₂ ⊢
  rw [LawfulDialogueState.contextSet_completed (S := S₁) es h₁,
      LawfulDialogueState.contextSet_completed (S := S₂) es h₂]

/-! ### Canonical instance

The reference machine is itself a lawful dialogue state — its observable is
the floor, which is `groundedContent` by construction. This witnesses that the
interface is inhabited and that the law is satisfiable. -/

instance : HasContextSet (GroundingState W) W where
  toContextSet s := s.floor

instance : DialogueStep (GroundingState W) W where
  init := GroundingState.init
  step := GroundingState.step
  isCompleted s := s.pending = []

instance : LawfulDialogueState (GroundingState W) W where
  contextSet_completed _ _ := rfl

end Discourse
