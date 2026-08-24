import Linglib.Semantics.Presupposition.Context

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
* `transparentProjection`, `opaque_implies_transparent_when_reflexive` —
  the opaque/transparent projection modes of
  [delpinal-bassi-sauerland-2024] §3.2.
-/

namespace Semantics.Presupposition.BeliefEmbedding

open Semantics.Presupposition
open CommonGround
open Semantics.Presupposition.Context

variable {W : Type*} {Agent : Type*}


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
  dox : Agent → W → W → Prop
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
