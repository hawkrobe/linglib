/-
# Belief Embedding and Local Contexts

Formalizes how presuppositions project under belief predicates, following
@cite{schlenker-2009} Section 3.1.2. This provides the machinery for deriving
Obligatory Local Effect (OLE) from @cite{tonhauser-beaver-roberts-simons-2013}.

## Insight

When a presupposition trigger appears under a belief predicate, the local
context is determined by the *attitude holder's* belief state, not the
global context. This explains OLE.

## The Schlenker Analysis

For "John believes that pp'" uttered in context C:
- The local context of pp' is: λw* λw(w* ∈ C and w ∈ DoxJ(w*))
- Where DoxJ(w*) = worlds compatible with John's beliefs at w*
- Presupposition p projects iff p is NOT entailed by this local context
- Result: p must be part of John's beliefs (attributed to attitude holder)

## Connection to @cite{tonhauser-beaver-roberts-simons-2013}

OLE = yes (Class A, Class C): Presupposition attributed to attitude holder
  - Predicted by computing local context from attitude holder's beliefs

OLE = no (Class B, Class D): Presupposition attributed to speaker
  - These triggers "reset" to speaker's context under embedding
  - E.g., expressives like "damn" always express speaker's attitude

## Examples

"John believes Mary stopped smoking"
  - Trigger: stop (Class C, OLE=yes)
  - Presupposition: Mary used to smoke
  - Local context: John's belief state
  - Result: John believes Mary used to smoke (attributed to John)

"John believes that damn cat is outside"
  - Trigger: damn (Class B, OLE=no)
  - Expressive content: speaker is annoyed at the cat
  - Does not shift to John's perspective
  - Result: Speaker is annoyed (attributed to speaker)

-/

import Linglib.Core.Semantics.PresuppositionContext
import Linglib.Theories.Semantics.Presupposition.LocalContext
import Linglib.Theories.Semantics.Modality.EpistemicLogic

namespace Semantics.Presupposition.BeliefEmbedding

open Core.Presupposition
open Core.Proposition
open Core.CommonGround
open Core.PresuppositionContext
open Semantics.Presupposition.LocalContext

variable {W : Type*} {Agent : Type*}


/--
Doxastic accessibility relation: the worlds compatible with what an agent
believes at a given world.

`Dox agent w` = the set of worlds compatible with what `agent` believes at `w`

This is the standard modal semantics for belief.
-/
def DoxasticAccessibility (W : Type*) (Agent : Type*) :=
  Agent → W → ContextSet W

/--
An agent's belief state at a world: the characteristic function of the
doxastically accessible worlds.
-/
def beliefState (Dox : DoxasticAccessibility W Agent) (agent : Agent) (w : W) : ContextSet W :=
  Dox agent w

/--
An agent believes a proposition at a world iff the proposition holds at all
doxastically accessible worlds.
-/
def believes (Dox : DoxasticAccessibility W Agent) (agent : Agent) (p : (W → Bool)) (w : W) : Prop :=
  ∀ w', Dox agent w w' → p w' = true


/--
The local context of an embedded clause under a belief predicate.

For "agent believes φ" evaluated in context C at world w*:
The local context at φ is the set of (w*, w) pairs where:
- w* is in the global context C
- w is compatible with what agent believes at w*

Following @cite{schlenker-2009} Section 3.1.2, this is a function from
"context of utterance" (w*) to context sets.
-/
structure BeliefLocalCtx (W : Type*) (Agent : Type*) where
  /-- The global context set -/
  globalCtx : ContextSet W
  /-- The doxastic accessibility relation -/
  dox : DoxasticAccessibility W Agent
  /-- The attitude holder -/
  agent : Agent

/--
Get the local context at a specific world of utterance.

This is Schlenker's λw* λw(w* ∈ C and w ∈ DoxJ(w*))
-/
def BeliefLocalCtx.atWorld (blc : BeliefLocalCtx W Agent) (w_star : W) : ContextSet W :=
  λ w => blc.globalCtx w_star ∧ blc.dox blc.agent w_star w

/--
A presupposition projects globally (to speaker) from under belief
iff it's not entailed by the belief local context at any global world.
-/
def presupProjectsFromBelief (blc : BeliefLocalCtx W Agent) (p : PrProp W) : Prop :=
  ∃ w_star, blc.globalCtx w_star ∧ ¬ ContextSet.entails (blc.atWorld w_star) p.presup

/--
A presupposition is attributed to the attitude holder iff it's entailed
by the local context at all global worlds.

This is the OLE=yes case: the presupposition becomes part of the
attitude holder's beliefs.
-/
def presupAttributedToHolder (blc : BeliefLocalCtx W Agent) (p : PrProp W) : Prop :=
  ∀ w_star, blc.globalCtx w_star → ContextSet.entails (blc.atWorld w_star) p.presup


/--
World type for the smoking example:
- Whether Mary used to smoke (in reality)
- Whether John believes Mary used to smoke
- Whether Mary currently smokes (in reality)
-/
inductive SmokingWorld where
  | maryUsedToSmoke_johnBelieves_maryQuit
  | maryUsedToSmoke_johnBelieves_marySmokes
  | maryNeverSmoked_johnBelieves_usedTo
  | maryNeverSmoked_johnDoesntBelieve
  deriving DecidableEq

/--
Agent type for the example.
-/
inductive SmokingAgent where
  | john
  deriving DecidableEq

/--
John's belief state at each world.
-/
def smokingDox : DoxasticAccessibility SmokingWorld SmokingAgent
  -- At world where Mary used to smoke and John believes it:
  -- John's beliefs are consistent with Mary having smoked
  | .john, .maryUsedToSmoke_johnBelieves_maryQuit =>
      λ w => match w with
        | .maryUsedToSmoke_johnBelieves_maryQuit => True
        | .maryUsedToSmoke_johnBelieves_marySmokes => True
        | _ => False
  -- At world where Mary used to smoke but John believes she still does:
  | .john, .maryUsedToSmoke_johnBelieves_marySmokes =>
      λ w => match w with
        | .maryUsedToSmoke_johnBelieves_maryQuit => True
        | .maryUsedToSmoke_johnBelieves_marySmokes => True
        | _ => False
  -- At world where Mary never smoked but John believes she used to:
  | .john, .maryNeverSmoked_johnBelieves_usedTo =>
      λ w => match w with
        | .maryUsedToSmoke_johnBelieves_maryQuit => True
        | .maryUsedToSmoke_johnBelieves_marySmokes => True
        | _ => False
  -- At world where Mary never smoked and John doesn't believe she did:
  | .john, .maryNeverSmoked_johnDoesntBelieve =>
      λ w => match w with
        | .maryNeverSmoked_johnDoesntBelieve => True
        | _ => False

/--
"Mary stopped smoking" — presupposes Mary used to smoke.
-/
def maryStoppedSmoking : PrProp SmokingWorld :=
  { presup := λ w => match w with
      | .maryUsedToSmoke_johnBelieves_maryQuit => true
      | .maryUsedToSmoke_johnBelieves_marySmokes => true
      | .maryNeverSmoked_johnBelieves_usedTo => true  -- John believes it
      | .maryNeverSmoked_johnDoesntBelieve => false
  , assertion := λ w => match w with
      | .maryUsedToSmoke_johnBelieves_maryQuit => true
      | .maryUsedToSmoke_johnBelieves_marySmokes => false
      | .maryNeverSmoked_johnBelieves_usedTo => true  -- In John's beliefs
      | .maryNeverSmoked_johnDoesntBelieve => false }

/--
Under belief embedding, the presupposition "Mary used to smoke"
is attributed to John (the attitude holder), not required of the global context.

At world `maryNeverSmoked_johnBelieves_usedTo`:
- Reality: Mary never smoked
- John's beliefs: Mary used to smoke
- Sentence "John believes Mary stopped smoking" is TRUE
- The presupposition holds in John's belief worlds, not in reality

This demonstrates OLE = yes for "stop" (Class C trigger).
-/
theorem stop_ole_attribution :
    let blc : BeliefLocalCtx SmokingWorld SmokingAgent :=
      { globalCtx := λ w => w = .maryNeverSmoked_johnBelieves_usedTo
      , dox := smokingDox
      , agent := .john }
    presupAttributedToHolder blc maryStoppedSmoking := by
  intro blc
  intro w_star hw_star
  intro w hw
  -- w is in John's belief state at w_star
  simp only [blc, BeliefLocalCtx.atWorld] at hw
  obtain ⟨hw_eq, hw_dox⟩ := hw
  subst hw_eq
  -- In John's belief state, Mary used to smoke
  simp only [smokingDox] at hw_dox
  -- w must be one of the worlds in John's belief state
  cases w with
  | maryUsedToSmoke_johnBelieves_maryQuit => rfl
  | maryUsedToSmoke_johnBelieves_marySmokes => rfl
  | maryNeverSmoked_johnBelieves_usedTo => simp at hw_dox
  | maryNeverSmoked_johnDoesntBelieve => simp at hw_dox


/--
For OLE=no triggers (Class B and D), the projective content is not computed
from the attitude holder's beliefs. Instead, it projects directly to the
speaker's context.

This is modeled by having the local context be the global context, not
the belief-restricted context.
-/
def speakerLocalCtx (c : ContextSet W) : LocalCtx W :=
  { worlds := c
  , position := 0
  , depth := 0 }

/--
For Class B triggers (expressives, appositives), content projects to speaker.

"John believes that damn cat is outside"
→ SPEAKER is annoyed at the cat (not John)

The expressive content is evaluated in the speaker's context, ignoring
the belief embedding.
-/
def expressiveProjectsToSpeaker (globalCtx : ContextSet W)
    (expressiverContent : (W → Bool)) : Prop :=
  -- The content must be entailed by the global (speaker's) context
  ContextSet.entails globalCtx expressiverContent


/--
Convert a belief local context to a standard local context.

This shows how the belief embedding fits into the general local context
framework from LocalContext.lean.
-/
def beliefToLocalCtx (blc : BeliefLocalCtx W Agent) (w_star : W)
    (_h : blc.globalCtx w_star) : LocalCtx W :=
  { worlds := blc.atWorld w_star
  , position := 1  -- We're inside the belief operator
  , depth := 1 }   -- Embedding depth = 1

/--
The presupposition filtering condition is the same: a presupposition is
filtered iff it's entailed by the local context.
-/
theorem belief_filtering_condition (blc : BeliefLocalCtx W Agent) (p : PrProp W)
    (w_star : W) (_h : blc.globalCtx w_star) :
    presupFiltered (beliefToLocalCtx blc w_star _h) p ↔
    ContextSet.entails (blc.atWorld w_star) p.presup := by
  simp [presupSatisfied, beliefToLocalCtx]

-- ════════════════════════════════════════════════════════════════
-- § Bool/Prop Bridge: CommonGround ↔ BeliefEmbedding
-- ════════════════════════════════════════════════════════════════

/-!
### Bridging Agent-Indexed Accessibility into `DoxasticAccessibility`
@cite{hintikka-1962}

`EpistemicLogic` uses Prop-valued `AgentAccessRel W E = E → W → W → Prop`.
`BeliefEmbedding` uses Prop-valued `DoxasticAccessibility W E = E → W → ContextSet W`
where `ContextSet W = W → Prop`.

Both represent the same concept (agent-indexed world accessibility). The
"bridge" is now a definitional reshuffle (currying `i w v ↦ Prop` either as
`E → W → W → Prop` or `E → W → (W → Prop)`).
-/

section BoolPropBridge

open Semantics.Modality.EpistemicLogic (KnowledgeBeliefFrame)
open Core.IntensionalLogic.RestrictedModality (AgentAccessRel)

variable {W E : Type*}

/-- Reinterpret an `AgentAccessRel` as a `DoxasticAccessibility`. Since both are
    `E → W → W → Prop` up to currying, this is essentially the identity. -/
def doxOfAccessRel (Rs : AgentAccessRel W E) : DoxasticAccessibility W E :=
  fun i w v => Rs i w v

/-- Construct a `BeliefLocalCtx` from a `KnowledgeBeliefFrame` using the
    belief relation. This connects the KD45 belief operator from
    `CommonGround.lean` to the local context machinery in this file. -/
def beliefLocalCtxOfFrame (frame : KnowledgeBeliefFrame W E)
    (ctx : ContextSet W) (i : E) : BeliefLocalCtx W E :=
  { globalCtx := ctx
  , dox := doxOfAccessRel frame.believesRel
  , agent := i }

/-- Construct a `BeliefLocalCtx` from a `KnowledgeBeliefFrame` using the
    knowledge relation. S5 knowledge is reflexive, so the local context
    includes the evaluation world itself. -/
def knowledgeLocalCtxOfFrame (frame : KnowledgeBeliefFrame W E)
    (ctx : ContextSet W) (i : E) : BeliefLocalCtx W E :=
  { globalCtx := ctx
  , dox := doxOfAccessRel frame.knowsRel
  , agent := i }

/-- Belief-accessible worlds are a subset of knowledge-accessible worlds.

    Since `R_B ⊆ R_K` (from `KnowledgeBeliefFrame.believes_sub_knows`),
    the belief local context at any world is contained in the knowledge
    local context. -/
theorem beliefLocal_sub_knowledgeLocal (frame : KnowledgeBeliefFrame W E)
    (ctx : ContextSet W) (i : E) (w_star : W) :
    ∀ w, (beliefLocalCtxOfFrame frame ctx i).atWorld w_star w →
         (knowledgeLocalCtxOfFrame frame ctx i).atWorld w_star w := by
  intro w ⟨hctx, hbel⟩
  exact ⟨hctx, frame.believes_sub_knows i w_star w hbel⟩

/-- If a presupposition is filtered under knowledge embedding (S5), it is
    also filtered under belief embedding (KD45).

    The belief local context is a subset of the knowledge local context
    (since R_B ⊆ R_K). If p holds at all knowledge-accessible worlds,
    it holds at all belief-accessible worlds a fortiori. -/
theorem knowledge_filtered_implies_belief_filtered
    (frame : KnowledgeBeliefFrame W E)
    (ctx : ContextSet W) (i : E) (p : PrProp W) (w_star : W) :
    ContextSet.entails ((knowledgeLocalCtxOfFrame frame ctx i).atWorld w_star) p.presup →
    ContextSet.entails ((beliefLocalCtxOfFrame frame ctx i).atWorld w_star) p.presup := by
  intro h_know w h_bel
  exact h_know w (beliefLocal_sub_knowledgeLocal frame ctx i w_star w h_bel)

end BoolPropBridge

-- ════════════════════════════════════════════════════════════════
-- § Opaque vs Transparent Projection
-- @cite{delpinal-bassi-sauerland-2024} §3.2
-- ════════════════════════════════════════════════════════════════

/-!
### Opaque vs Transparent Presupposition Projection

@cite{delpinal-bassi-sauerland-2024} §3.2 distinguish two projection modes for
presuppositions under attitude predicates:

- **Transparent**: presupposition evaluated in the global context (speaker's
  knowledge state). Implemented by `PrProp.negFactive`: the factive
  presupposes the complement holds in reality.

- **Opaque**: presupposition attributed to the attitude holder's belief state.
  This is `presupAttributedToHolder`: the presupposition holds at all
  doxastically accessible worlds.

Both modes yield free choice when applied to pex output, because both ensure
homogeneity is satisfied (in different contexts) along with the prejacent.
-/

section OpaqueTransparent

variable {W : Type*} {Agent : Type*}

/-- Transparent projection: presupposition projects to the speaker's (global)
    context, evaluated independently of the attitude holder's beliefs.
    Captures negative factives ("is unaware that"): the factive presupposes
    the complement *holds* in the actual world.

    @cite{delpinal-bassi-sauerland-2024} §3.2 -/
def transparentProjection (globalCtx : ContextSet W) (p : PrProp W) : Prop :=
  ContextSet.entails globalCtx p.presup

/-- `PrProp.negFactive` subsumes transparent projection: its presupposition
    (complement holds = presup ∧ assertion) entails transparent projection of
    the complement's presupposition.

    This grounds the `negFactive` combinator in the projection theory.
    @cite{heim-1992}, @cite{delpinal-bassi-sauerland-2024} §3.2 -/
theorem negFactive_entails_transparent (complement : PrProp W)
    (believes : Prop' W → Prop' W) (globalCtx : ContextSet W)
    (h : ContextSet.entails globalCtx (PrProp.negFactive complement believes).presup) :
    transparentProjection globalCtx complement := by
  intro w hw
  exact (h w hw).1

/-- Under S5 knowledge (reflexive accessibility), opaque projection implies
    transparent projection.

    Reflexive `dox` means the evaluation world is among its own accessible
    worlds. What holds at all accessible worlds holds at the evaluation world.
    @cite{hintikka-1962}: S5 knowledge is reflexive. -/
theorem opaque_implies_transparent_when_reflexive
    (blc : BeliefLocalCtx W Agent) (p : PrProp W)
    (hReflexive : ∀ w, blc.globalCtx w → blc.dox blc.agent w w)
    (hOpaque : presupAttributedToHolder blc p) :
    transparentProjection blc.globalCtx p := by
  intro w hw
  exact hOpaque w hw w ⟨hw, hReflexive w hw⟩

end OpaqueTransparent

end Semantics.Presupposition.BeliefEmbedding
