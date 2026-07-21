import Linglib.Semantics.Presupposition.BeliefEmbedding

/-!
# KD45 Projection: The [heim-1992] Know/Believe Asymmetry

[heim-1992]

[heim-1992] observed that presupposition projection differs under
knowledge vs. belief predicates:

- "John **knows** Mary stopped smoking" → Mary **actually** smoked
- "John **believes** Mary stopped smoking" → Mary smoked **in John's beliefs**

The first projects the presupposition to the actual world; the second
only attributes it to the attitude holder. This asymmetry follows from
the modal frame conditions:

- **Knowledge (S5)**: reflexive — the actual world is knowledge-accessible
  from itself, so presuppositions must hold there.
- **Belief (KD45)**: serial but not reflexive — the actual world need not
  be belief-accessible, so presuppositions can hold only in the agent's
  belief worlds without being true.

This file constructs a concrete 2-world model demonstrating the asymmetry,
connecting `KnowledgeBeliefFrame` (from `EpistemicLogic.lean`) through
`localCtxOf` (from `BeliefEmbedding.lean`) to `presupSatisfied`
(from `Context.lean`).

The *other* half of [heim-1992] — comparative-belief desire
semantics for `want`/`wish`/`hope` — is at
`Studies/Heim1992.lean`. Both halves of the paper are
formalized; the substrate splits along the natural empirical boundary
(presupposition vs modality).

-/

namespace Heim1992

open Semantics.Presupposition (PartialProp)
open CommonGround (ContextSet)
open Core.Logic.Modal (IsSerial IsEuclidean IsS5Frame IsKD45Frame
  IsBeliefRefinementOf)
open Semantics.Presupposition.Context (presupSatisfied)
open Semantics.Presupposition.BeliefEmbedding

/-! ## World Model -/

/-- Two-world model for the [heim-1992] scenario.

    - `actual`: Mary never smoked (presupposition false)
    - `believed`: Mary used to smoke (presupposition true),
      accessible via John's beliefs -/
inductive AttWorld where
  | actual   -- p is false here (Mary never smoked)
  | believed -- p is true here (Mary smoked)
  deriving DecidableEq, Repr

/-- Single agent: John. -/
inductive Holder where
  | john
  deriving DecidableEq

/-! ## Frame Construction -/

/-- Knowledge accessibility (S5: reflexive).
    Both worlds access both worlds. -/
def knowsR : AttWorld → AttWorld → Prop
  | _, _ => True

/-- Belief accessibility (KD45: serial, not reflexive).
    From `actual`, only `believed` is accessible.
    From `believed`, only `believed` is accessible. -/
def believesR : AttWorld → AttWorld → Prop
  | _, .believed => True
  | _, .actual => False

/-- Bool-valued mirror of `believesR` for downstream code that needs
    decidable accessibility (e.g., `Grove2022.believe`). -/
def believesRBool : AttWorld → AttWorld → Bool
  | _, .believed => true
  | _, .actual => false

/-- Knowledge relation is reflexive. -/
instance knowsR_isRefl : Std.Refl knowsR := ⟨fun _ => trivial⟩

/-- Knowledge relation is euclidean (trivially: knowsR is the universal
    relation, so any pair of successors satisfies the goal). -/
instance knowsR_isEucl : IsEuclidean knowsR := ⟨fun _ _ _ _ _ => trivial⟩

/-- Belief relation is serial (every world accesses some world). -/
instance believesR_isSerial : IsSerial believesR :=
  ⟨fun w => ⟨.believed, by cases w <;> trivial⟩⟩

/-- Belief relation is NOT reflexive (`actual` does not access itself). -/
theorem believesR_not_isRefl : ¬ Std.Refl believesR := by
  intro h; exact (h.refl .actual : (False : Prop))

/-- Belief relation is transitive. -/
instance believesR_isTrans : IsTrans AttWorld believesR := by
  refine ⟨?_⟩
  intro w v u hwv hvu
  cases u with
  | believed => cases w <;> trivial
  | actual => exact hvu.elim

/-- Belief relation is Euclidean. -/
instance believesR_isEucl : IsEuclidean believesR := by
  refine ⟨?_⟩
  intro w v u hwv hwu
  cases u with
  | believed => cases v <;> trivial
  | actual => exact hwu.elim

/-- The agent-indexed knowledge relation. -/
@[reducible] def agentKnowsR : Holder → AttWorld → AttWorld → Prop
  | .john => knowsR

/-- The agent-indexed belief relation. -/
@[reducible] def agentBelievesR : Holder → AttWorld → AttWorld → Prop
  | .john => believesR

/-- John's knowledge is S5. -/
instance : IsS5Frame (agentKnowsR .john) where

/-- John's belief is KD45. -/
instance : IsKD45Frame (agentBelievesR .john) where

/-- Belief refines knowledge for John: R_B ⊆ R_K. -/
instance : IsBeliefRefinementOf (agentKnowsR .john) (agentBelievesR .john) :=
  ⟨fun _ _ _ => trivial⟩

/-! ## Presupposition -/

/-- "Mary used to smoke" — the presupposition of "stop smoking".
    True at `believed`, false at `actual`. -/
def presup : PartialProp AttWorld :=
  { presup := fun w => match w with
      | .believed => True
      | .actual => False
  , assertion := fun _ => True }

/-- Global context: both worlds are in the context set. -/
def globalCtx : ContextSet AttWorld := fun _ => True

/-! ## Local Contexts -/

/-- Knowledge local context. -/
def knowledgeLocal : BeliefLocalCtx AttWorld Holder :=
  localCtxOf agentKnowsR globalCtx .john

/-- Belief local context. -/
def beliefLocal : BeliefLocalCtx AttWorld Holder :=
  localCtxOf agentBelievesR globalCtx .john

/-! ## [heim-1992] Asymmetry Theorems -/

/-- S5 reflexivity forces presupposed content to be true at the actual world.

    Under knowledge embedding, if the presupposition is filtered (entailed
    by the knowledge local context) at `actual`, then the presupposition
    must hold at `actual` — because S5 reflexivity makes `actual` one of
    the knowledge-accessible worlds from `actual`. -/
theorem reflexivity_forces_actual_truth
    (h : ContextSet.entails (knowledgeLocal.atWorld .actual) presup.presup) :
    presup.presup .actual := by
  refine @h .actual ?_
  exact ⟨trivial, knowsR_isRefl.refl AttWorld.actual⟩

/-- KD45 non-reflexivity permits false presuppositions under belief embedding.

    The presupposition is filtered at `actual` (entailed by the belief local
    context) even though `presup actual` is false. This is because the only
    belief-accessible world from `actual` is `believed`, where the
    presupposition holds. -/
theorem non_reflexivity_permits_false_presup :
    ContextSet.entails (beliefLocal.atWorld .actual) presup.presup
    ∧ ¬presup.presup .actual := by
  constructor
  · intro w ⟨_, hbel⟩
    show presup.presup w
    cases w with
    | believed => trivial
    | actual =>
      exfalso
      have : agentBelievesR .john .actual .actual := hbel
      exact this
  · simp [presup]

/-- The [heim-1992] know/believe asymmetry.

    Under our concrete model where the presupposition is false at the
    actual world:
    1. The presupposition IS filtered under belief embedding (KD45) —
       John's belief worlds satisfy it.
    2. The presupposition is NOT filtered under knowledge embedding (S5) —
       reflexivity forces it to hold at `actual`, where it is false. -/
theorem heim_know_believe_asymmetry :
    -- Belief filters the presupposition
    ContextSet.entails (beliefLocal.atWorld .actual) presup.presup
    -- Knowledge does NOT filter the presupposition
    ∧ ¬ ContextSet.entails (knowledgeLocal.atWorld .actual) presup.presup := by
  constructor
  · -- Belief case: all belief-accessible worlds from actual satisfy presup
    exact non_reflexivity_permits_false_presup.1
  · -- Knowledge case: actual is knowledge-accessible from actual, but presup actual = false
    intro h
    have := reflexivity_forces_actual_truth h
    simp [presup] at this

end Heim1992
