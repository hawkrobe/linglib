import Linglib.Theories.Semantics.Presupposition.BeliefEmbedding

/-!
# KD45 Projection: The @cite{heim-1992} Know/Believe Asymmetry

@cite{heim-1992}

@cite{heim-1992} observed that presupposition projection differs under
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
connecting `KnowledgeBeliefFrame` (from `CommonGround.lean`) through
`doxOfAccessRel` (from `BeliefEmbedding.lean`) to `presupFiltered`
(from `LocalContext.lean`).

-/

namespace Phenomena.Presupposition.Bridge.KD45Projection

open Core.Presupposition (PrProp)
open Core.CommonGround (ContextSet)
open Core.CommonGround.MultiAgent (KnowledgeBeliefFrame)
open Core.ModalLogic (Refl Serial Eucl Trans)
open Semantics.Presupposition.LocalContext (presupFiltered)
open Semantics.Presupposition.BeliefEmbedding

/-! ## World Model -/

/-- Two-world model for the @cite{heim-1992} scenario.

    - `actual`: Mary never smoked (presupposition false)
    - `believed`: Mary used to smoke (presupposition true),
      accessible via John's beliefs -/
inductive AttWorld where
  | actual   -- p is false here (Mary never smoked)
  | believed -- p is true here (Mary smoked)
  deriving DecidableEq, BEq, Repr

/-- Single agent: John. -/
inductive Holder where
  | john
  deriving DecidableEq, BEq

/-! ## Frame Construction -/

/-- Knowledge accessibility (S5: reflexive).
    Both worlds access both worlds. -/
def knowsR : AttWorld → AttWorld → Bool
  | _, _ => true

/-- Belief accessibility (KD45: serial, not reflexive).
    From `actual`, only `believed` is accessible.
    From `believed`, only `believed` is accessible. -/
def believesR : AttWorld → AttWorld → Bool
  | _, .believed => true
  | _, .actual => false

/-- Knowledge relation is reflexive. -/
theorem knowsR_refl : Refl knowsR := fun _ => rfl

/-- Belief relation is serial (every world accesses some world). -/
theorem believesR_serial : Serial believesR :=
  fun w => ⟨.believed, by cases w <;> rfl⟩

/-- Belief relation is NOT reflexive (`actual` does not access itself). -/
theorem believesR_not_refl : ¬ Refl believesR := by
  intro h; have := h .actual; simp [believesR] at this

/-- Belief relation is transitive. -/
theorem believesR_trans : Trans believesR := by
  intro w v u hwv hvu
  cases u with
  | believed => cases w <;> rfl
  | actual => simp [believesR] at hvu

/-- Belief relation is Euclidean. -/
theorem believesR_eucl : Eucl believesR := by
  intro w v u hwv hwu
  cases u with
  | believed => cases v <;> rfl
  | actual => simp [believesR] at hwu

/-- R_B ⊆ R_K: belief-accessible worlds are knowledge-accessible. -/
theorem believes_sub_knows :
    ∀ (w v : AttWorld), believesR w v = true → knowsR w v = true :=
  fun _ _ _ => rfl

/-- The agent-indexed knowledge relation. -/
def agentKnowsR : Holder → AttWorld → AttWorld → Bool
  | .john => knowsR

/-- The agent-indexed belief relation. -/
def agentBelievesR : Holder → AttWorld → AttWorld → Bool
  | .john => believesR

/-- The knowledge-belief frame bundling S5 knowledge and KD45 belief. -/
def frame : KnowledgeBeliefFrame AttWorld Holder :=
  { knowsRel := agentKnowsR
  , believesRel := agentBelievesR
  , believes_sub_knows := fun i w v h => by cases i; exact believes_sub_knows w v h }

/-! ## Presupposition -/

/-- "Mary used to smoke" — the presupposition of "stop smoking".
    True at `believed`, false at `actual`. -/
def presup : PrProp AttWorld :=
  { presup := fun w => match w with
      | .believed => true
      | .actual => false
  , assertion := fun _ => true }

/-- Global context: both worlds are in the context set. -/
def globalCtx : ContextSet AttWorld := fun _ => True

/-! ## Local Contexts -/

/-- Knowledge local context constructed via the bridge. -/
def knowledgeLocal : BeliefLocalCtx AttWorld Holder :=
  knowledgeLocalCtxOfFrame frame globalCtx .john

/-- Belief local context constructed via the bridge. -/
def beliefLocal : BeliefLocalCtx AttWorld Holder :=
  beliefLocalCtxOfFrame frame globalCtx .john

/-! ## @cite{heim-1992} Asymmetry Theorems -/

/-- S5 reflexivity forces presupposed content to be true at the actual world.

    Under knowledge embedding, if the presupposition is filtered (entailed
    by the knowledge local context) at `actual`, then the presupposition
    must hold at `actual` — because S5 reflexivity makes `actual` one of
    the knowledge-accessible worlds from `actual`. -/
theorem reflexivity_forces_actual_truth
    (h : ContextSet.entails (knowledgeLocal.atWorld .actual) presup.presup) :
    presup.presup .actual = true := by
  apply h
  constructor
  · trivial
  · show doxOfAccessRel frame.knowsRel .john .actual .actual
    simp [doxOfAccessRel, frame, agentKnowsR, knowsR]

/-- KD45 non-reflexivity permits false presuppositions under belief embedding.

    The presupposition is filtered at `actual` (entailed by the belief local
    context) even though `presup actual = false`. This is because the only
    belief-accessible world from `actual` is `believed`, where the
    presupposition holds. -/
theorem non_reflexivity_permits_false_presup :
    ContextSet.entails (beliefLocal.atWorld .actual) presup.presup
    ∧ presup.presup .actual = false := by
  constructor
  · intro w ⟨_, hbel⟩
    show presup.presup w = true
    cases w with
    | believed => rfl
    | actual =>
      exfalso
      have : agentBelievesR .john .actual .actual = true := hbel
      simp [agentBelievesR, believesR] at this
  · rfl

/-- The @cite{heim-1992} know/believe asymmetry.

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

end Phenomena.Presupposition.Bridge.KD45Projection
