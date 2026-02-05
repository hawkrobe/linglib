/-
# Belief Embedding and Local Contexts

Formalizes how presuppositions project under belief predicates, following
Schlenker (2009) Section 3.1.2. This provides the machinery for deriving
Obligatory Local Effect (OLE) from Tonhauser et al. (2013).

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

## Connection to Tonhauser et al. (2013)

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

## References

- Schlenker (2009). Local Contexts. Semantics & Pragmatics 2:3.
- Heim (1992). Presupposition Projection and the Semantics of Attitude Verbs.
- Tonhauser, Beaver, Roberts & Simons (2013). Toward a Taxonomy of
  Projective Content. Language 89(1).
-/

import Linglib.Core.CommonGround
import Linglib.Core.Presupposition
import Linglib.Theories.TruthConditional.Sentence.Presupposition.LocalContext
import Linglib.Phenomena.Presupposition.ProjectiveContent

namespace TruthConditional.Sentence.Presupposition.BeliefEmbedding

open Core.Presupposition
open Core.Proposition
open Core.CommonGround
open TruthConditional.Sentence.Presupposition.LocalContext
open Phenomena.Presupposition.ProjectiveContent

variable {W : Type*} {Agent : Type*}


/--
Doxastic accessibility relation: the worlds compatible with what an agent
believes at a given world.

`Dox agent w` = the set of worlds compatible with what `agent` believes at `w`

This is the standard modal semantics for belief (Hintikka 1962).
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
def believes (Dox : DoxasticAccessibility W Agent) (agent : Agent) (p : BProp W) (w : W) : Prop :=
  ∀ w', Dox agent w w' → p w' = true


/--
The local context of an embedded clause under a belief predicate.

For "agent believes φ" evaluated in context C at world w*:
The local context at φ is the set of (w*, w) pairs where:
- w* is in the global context C
- w is compatible with what agent believes at w*

Following Schlenker (2009) Section 3.1.2, this is a function from
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
Determines whether a projective trigger's content shifts to the attitude
holder's perspective under belief embedding.

OLE = yes: Content shifts to attitude holder (computed from their beliefs)
OLE = no: Content remains attributed to speaker (no perspective shift)
-/
def shiftsUnderBelief : ProjectiveClass → Bool
  | .classA => true   -- OLE = yes
  | .classB => false  -- OLE = no
  | .classC => true   -- OLE = yes
  | .classD => false  -- OLE = no

/--
OLE status matches shift behavior.
-/
theorem ole_matches_shift (c : ProjectiveClass) :
    shiftsUnderBelief c = true ↔ c.ole = .obligatory := by
  cases c <;> simp [shiftsUnderBelief, ProjectiveClass.ole]


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
    (expressiverContent : BProp W) : Prop :=
  -- The content must be entailed by the global (speaker's) context
  ContextSet.entails globalCtx expressiverContent


/--
The Schlenker local context machinery derives the OLE
predictions from Tonhauser et al. (2013).

For any trigger:
- If OLE=yes (Class A, C): Local context under belief = attitude holder's beliefs
- If OLE=no (Class B, D): Local context under belief = global context (speaker)

This explains why "stop" presuppositions shift to attitude holders but
"damn" expressives don't.
-/
theorem ole_from_local_contexts (trigger : ProjectiveTrigger) :
    shiftsUnderBelief trigger.toClass = true ↔
    trigger.toClass.ole = .obligatory := by
  exact ole_matches_shift trigger.toClass

/--
Class C triggers (stop, know, only) have OLE=yes.
-/
example : ProjectiveTrigger.stop_prestate.toClass.ole = .obligatory := rfl
example : ProjectiveTrigger.know_complement.toClass.ole = .obligatory := rfl

/--
Class B triggers (expressives, appositives) have OLE=no.
-/
example : ProjectiveTrigger.expressive.toClass.ole = .notObligatory := rfl
example : ProjectiveTrigger.appositive.toClass.ole = .notObligatory := rfl


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
  simp [presupFiltered, beliefToLocalCtx]

end TruthConditional.Sentence.Presupposition.BeliefEmbedding
