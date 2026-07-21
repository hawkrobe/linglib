import Linglib.Semantics.Presupposition.Context
import Linglib.Semantics.Modality.EpistemicLogic

/-!
# Belief Embedding and Local Contexts

How presuppositions project under belief predicates, following
[schlenker-2009] Section 3.1.2: for "agent believes φ" uttered in context C,
the local context of φ at utterance world w* is C(w*) ∩ Dox_agent(w*), so a
projecting presupposition must hold throughout the attitude holder's belief
state. This derives Obligatory Local Effect
([tonhauser-beaver-roberts-simons-2013]: OLE=yes triggers are attributed to
the attitude holder).

## Main declarations

* `BeliefLocalCtx`, `BeliefLocalCtx.atWorld` — Schlenker's
  λw* λw(w* ∈ C ∧ w ∈ Dox(w*)) local context.
* `presupAttributedToHolder` — the OLE=yes condition.
* `localCtxOf`, `knowledge_filtered_implies_belief_filtered` — composition
  with epistemic-logic frame conditions ([hintikka-1962]).
* `transparentProjection`, `opaque_implies_transparent_when_reflexive` —
  the opaque/transparent projection modes of
  [delpinal-bassi-sauerland-2024] §3.2.
-/

namespace Semantics.Presupposition.BeliefEmbedding

open Semantics.Presupposition
open CommonGround
open Semantics.Presupposition.Context
open Core.Logic.Modal (AgentAccessRel IsBeliefRefinementOf)

variable {W : Type*} {Agent : Type*}


/--
An agent's belief state at a world: the doxastically accessible worlds,
viewed as a context set. Doxastic accessibility is the agent-indexed
accessibility relation `Core.Logic.Modal.AgentAccessRel` ([hintikka-1962]):
`Dox agent w w'` means `w'` is compatible with what `agent` believes at `w`.
-/
def beliefState (Dox : AgentAccessRel W Agent) (agent : Agent) (w : W) : ContextSet W :=
  Dox agent w

/--
An agent believes a proposition at a world iff the proposition holds at all
doxastically accessible worlds.
-/
def believes (Dox : AgentAccessRel W Agent) (agent : Agent) (p : W → Prop) (w : W) : Prop :=
  ∀ w', Dox agent w w' → p w'


/--
The local context of an embedded clause under a belief predicate.

For "agent believes φ" evaluated in context C at world w*:
The local context at φ is the set of (w*, w) pairs where:
- w* is in the global context C
- w is compatible with what agent believes at w*

Following [schlenker-2009] Section 3.1.2, this is a function from
"context of utterance" (w*) to context sets.
-/
structure BeliefLocalCtx (W : Type*) (Agent : Type*) where
  /-- The global context set -/
  globalCtx : ContextSet W
  /-- The doxastic accessibility relation -/
  dox : AgentAccessRel W Agent
  /-- The attitude holder -/
  agent : Agent

/--
Get the local context at a specific world of utterance.

This is Schlenker's λw* λw(w* ∈ C and w ∈ DoxJ(w*))
-/
def BeliefLocalCtx.atWorld (blc : BeliefLocalCtx W Agent) (w_star : W) : ContextSet W :=
  λ w => blc.globalCtx w_star ∧ blc.dox blc.agent w_star w

/--
A presupposition is attributed to the attitude holder iff it's entailed
by the local context at all global worlds.

This is the OLE=yes case: the presupposition becomes part of the
attitude holder's beliefs.
-/
def presupAttributedToHolder (blc : BeliefLocalCtx W Agent) (p : PartialProp W) : Prop :=
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
def smokingDox : AgentAccessRel SmokingWorld SmokingAgent
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
def maryStoppedSmoking : PartialProp SmokingWorld :=
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
  intro blc w_star hw_star w hw
  -- w is in John's belief state at w_star
  simp only [blc] at hw
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


/-!
### Refinement Between Knowledge and Belief Embeddings
[hintikka-1962]

Doxastic accessibility is `Core.Logic.Modal.AgentAccessRel` directly, so
belief local contexts compose with the epistemic-logic frame conditions:
when belief pointwise refines knowledge (`IsBeliefRefinementOf`), filtering
under knowledge embedding implies filtering under belief embedding.
-/

section Refinement

variable {W E : Type*}

/-- Build a `BeliefLocalCtx` from an agent-indexed accessibility relation. -/
def localCtxOf (Rs : AgentAccessRel W E) (ctx : ContextSet W) (i : E) :
    BeliefLocalCtx W E :=
  { globalCtx := ctx
  , dox := Rs
  , agent := i }

/-- Belief-accessible worlds are a subset of knowledge-accessible worlds
    when belief refines knowledge pointwise. -/
theorem localCtx_sub_of_refinement (Rk Rb : AgentAccessRel W E)
    (ctx : ContextSet W) (i : E) [hRef : IsBeliefRefinementOf (Rk i) (Rb i)]
    (w_star : W) :
    ∀ w, (localCtxOf Rb ctx i).atWorld w_star w →
         (localCtxOf Rk ctx i).atWorld w_star w := by
  intro w ⟨hctx, hbel⟩
  exact ⟨hctx, hRef.sub w_star w hbel⟩

/-- If a presupposition is filtered under knowledge embedding, it is also
    filtered under any belief embedding that refines knowledge. -/
theorem knowledge_filtered_implies_belief_filtered
    (Rk Rb : AgentAccessRel W E) (ctx : ContextSet W) (i : E)
    [IsBeliefRefinementOf (Rk i) (Rb i)] (p : PartialProp W) (w_star : W) :
    ContextSet.entails ((localCtxOf Rk ctx i).atWorld w_star) p.presup →
    ContextSet.entails ((localCtxOf Rb ctx i).atWorld w_star) p.presup := by
  intro h_know w h_bel
  exact h_know (localCtx_sub_of_refinement Rk Rb ctx i w_star w h_bel)

end Refinement

/-!
### Opaque vs Transparent Presupposition Projection

[delpinal-bassi-sauerland-2024] §3.2 distinguish two projection modes for
presuppositions under attitude predicates:

- **Transparent**: presupposition evaluated in the global context (speaker's
  knowledge state). Implemented by `PartialProp.negFactive`: the factive
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

    [delpinal-bassi-sauerland-2024] §3.2 -/
def transparentProjection (globalCtx : ContextSet W) (p : PartialProp W) : Prop :=
  ContextSet.entails globalCtx p.presup

/-- `PartialProp.negFactive` subsumes transparent projection: its presupposition
    (complement holds = presup ∧ assertion) entails transparent projection of
    the complement's presupposition.

    This grounds the `negFactive` combinator in the projection theory.
    [heim-1992], [delpinal-bassi-sauerland-2024] §3.2 -/
theorem negFactive_entails_transparent (complement : PartialProp W)
    (believes : Set W → Set W) (globalCtx : ContextSet W)
    (h : ContextSet.entails globalCtx (PartialProp.negFactive complement believes).presup) :
    transparentProjection globalCtx complement := by
  intro w hw
  exact (h hw).1

/-- Under S5 knowledge (reflexive accessibility), opaque projection implies
    transparent projection.

    Reflexive `dox` means the evaluation world is among its own accessible
    worlds. What holds at all accessible worlds holds at the evaluation world.
    [hintikka-1962]: S5 knowledge is reflexive. -/
theorem opaque_implies_transparent_when_reflexive
    (blc : BeliefLocalCtx W Agent) (p : PartialProp W)
    (hReflexive : ∀ w, blc.globalCtx w → blc.dox blc.agent w w)
    (hOpaque : presupAttributedToHolder blc p) :
    transparentProjection blc.globalCtx p := by
  intro w hw
  exact hOpaque w hw ⟨hw, hReflexive w hw⟩

end OpaqueTransparent

end Semantics.Presupposition.BeliefEmbedding
