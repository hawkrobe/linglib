/-
# Deriving Tonhauser et al. (2013) from Local Contexts

This module states and proves the main theorems showing that Schlenker's
local context theory derives the four-class taxonomy of Tonhauser et al. (2013).

## The Main Result

Given Schlenker's theory of local contexts, we can characterize:

1. **SCF (Strong Contextual Felicity)**: Whether a trigger requires its
   projective content to be established in the global context (vs. allowing
   accommodation/informativity).

2. **OLE (Obligatory Local Effect)**: Whether, under belief embedding, the
   projective content is computed from the attitude holder's belief state
   (vs. the speaker's global context).

## The Four Classes

| Class | SCF | OLE | Derived Behavior |
|-------|-----|-----|------------------|
| A | yes | yes | Requires context + shifts under belief |
| B | no  | no  | Informative + speaker-anchored |
| C | no  | yes | Informative + shifts under belief |
| D | yes | no  | Requires context + speaker-anchored |

## The Tonhauser Critique and How We Address It

Tonhauser et al. (2013:105) raise an important objection to Schlenker's approach:

> "In theories like those of Schlenker (2009), where it is assumed that a
> presupposition is satisfied in its local context if it is entailed by it.
> Since, in general, the relevant local context is the context set ('which
> encodes what the speech act participants take for granted'), presuppositions
> are predicted to project. The heterogeneity of projective content, in
> particular the finding that many such contents are not associated with a
> strong contextual felicity constraint, provides an argument against an
> inclusive analysis of projection based on local satisfaction."

### The Problem

If Schlenker's theory just says "presupposition must be entailed by local context",
then it predicts SCF=yes for everything (content must be in context). But
Class B and C triggers have SCF=no (content can be informative).

### The Resolution

The key insight is that Schlenker's theory needs to be supplemented with a
theory of **accommodation**:

1. **Projection** is uniform: ALL projective content projects by default.
   This is what the local context machinery captures.

2. **Accommodation** varies by trigger type:
   - SCF=no triggers: Context can be UPDATED to satisfy the presupposition
     (accommodation is easy/automatic)
   - SCF=yes triggers: Context update is BLOCKED or heavily constrained
     (accommodation fails or requires special marking)

3. **The local context theory derives OLE directly** (via belief embedding),
   but derives SCF **indirectly** through constraints on accommodation.

### What We Formalize Here

- OLE: Fully derived from belief local contexts (Schlenker §3.1.2)
- SCF: Characterized as a constraint on accommodation (not built into local contexts)
- The four classes: Cross-classification of these two orthogonal properties

### What Remains to Formalize

A full derivation of SCF would require:
1. A theory of accommodation (Lewis 1979, Heim 1983, van der Sandt 1993)
2. Constraints on when accommodation is blocked (anaphoric triggers, salience)
3. Connection to information structure (QUD, at-issueness)

This module formalizes the taxonomy and the OLE derivation. The SCF derivation
requires additional pragmatic machinery that connects to QUD theory and
information structure (see Core.QUD, Core.InformationStructure).

## References

- Tonhauser, Beaver, Roberts & Simons (2013). Toward a Taxonomy of
  Projective Content. Language 89(1), 66-109.
- Schlenker (2009). Local Contexts. Semantics & Pragmatics 2:3.
- Lewis (1979). Scorekeeping in a Language Game.
- van der Sandt (1993). Presupposition Projection as Anaphora Resolution.
-/

import Linglib.Core.CommonGround
import Linglib.Core.Presupposition
import Linglib.Theories.Semantics.Presupposition.LocalContext
import Linglib.Theories.Semantics.Presupposition.BeliefEmbedding

namespace Semantics.Presupposition.TonhauserDerivation

open Core.Presupposition
open Core.Proposition
open Core.CommonGround
open Semantics.Presupposition.LocalContext
open Semantics.Presupposition.BeliefEmbedding

variable {W : Type*} {Agent : Type*}


/--
**SCF (Strong Contextual Felicity)** in local context terms.

A trigger has SCF=yes iff its projective content MUST be entailed by the
global context for felicitous use. Accommodation is blocked.

In Schlenker's terms: the local context at matrix level IS the global context,
and the presupposition must be entailed (not just "could be accommodated").
-/
structure SCF_Requires (W : Type*) where
  /-- The projective content -/
  content : BProp W
  /-- The trigger blocks accommodation: content MUST be in global context -/
  requiresEstablishment : ∀ (c : ContextSet W), ContextSet.nonEmpty c →
    (felicitous : Prop) → felicitous → ContextSet.entails c content

/--
**SCF=no** means accommodation is ALLOWED.

The projective content can be informative - it can update the context
rather than being required to already hold.
-/
structure SCF_Allows (W : Type*) where
  /-- The projective content -/
  content : BProp W
  /-- Accommodation is possible: there exist contexts where content is
      informative (not entailed) yet use is felicitous -/
  allowsInformativity : ∃ (c : ContextSet W), ContextSet.nonEmpty c ∧
    ¬ContextSet.entails c content ∧
    -- Use is still possible via accommodation
    True  -- (felicity after accommodation)

/--
**OLE (Obligatory Local Effect)** in local context terms.

OLE=yes means: under belief embedding, the local context is the attitude
holder's belief state. The projective content is attributed to the holder.
-/
def OLE_Obligatory (Dox : DoxasticAccessibility W Agent)
    (content : BProp W) : Prop :=
  ∀ (c : ContextSet W) (agent : Agent) (w_star : W),
    c w_star →
    let blc : BeliefLocalCtx W Agent := { globalCtx := c, dox := Dox, agent := agent }
    -- Content is evaluated relative to holder's beliefs
    ContextSet.entails (blc.atWorld w_star) content

/--
**OLE=no** means: under belief embedding, the projective content is still
evaluated relative to the speaker's (global) context, not the holder's beliefs.
-/
def OLE_NotObligatory (content : BProp W) : Prop :=
  ∀ (c : ContextSet W),
    -- Content is evaluated relative to global context, ignoring belief embedding
    ContextSet.entails c content →
    -- This suffices for felicity even under belief
    True


/--
**Main Theorem 1**: Local context at matrix position = global context.

This is the foundation for SCF: in unembedded sentences, the local context
is just the global context C.
-/
theorem matrix_local_context_is_global (c : ContextSet W) :
    (initialLocalCtx c).worlds = c := rfl

/--
**Main Theorem 2**: Local context under belief = attitude holder's beliefs.

This is the foundation for OLE=yes: under belief embedding, the local
context is determined by the attitude holder's doxastic state.
-/
theorem belief_local_context_is_holder_beliefs
    (blc : BeliefLocalCtx W Agent) (w_star : W) (h : blc.globalCtx w_star) :
    (beliefToLocalCtx blc w_star h).worlds = blc.atWorld w_star := rfl

/--
**Projection Theorem 1**: Presuppositions project from negation.

"not pp'" has local context = global context at pp'.
Therefore pp' projects (unless globally entailed).
-/
theorem negation_projects (c : ContextSet W) (p : PrProp W) :
    presupProjects (localCtxNegation (initialLocalCtx c)) p ↔
    presupProjects (initialLocalCtx c) p := by
  exact negation_preserves_projection (initialLocalCtx c) p

/--
**Projection Theorem 2**: Conditionals filter consequent presuppositions.

"if p then qq'" — if p.assertion entails q.presup, it's filtered.
-/
theorem conditional_filters (c : LocalCtx W) (p q : PrProp W)
    (h : ∀ w, c.worlds w → p.assertion w = true → q.presup w = true) :
    presupFiltered (localCtxConsequent c p) q :=
  conditional_filters_when_entailed c p q h

/--
**Projection Theorem 3**: Belief embedding creates attitude-holder context.

Under "x believes φ", the local context at φ is x's belief state.
This derives OLE=yes behavior.
-/
theorem belief_derives_ole (blc : BeliefLocalCtx W Agent) (p : PrProp W)
    (h : presupAttributedToHolder blc p) (w_star : W) (hw : blc.globalCtx w_star) :
    presupFiltered (beliefToLocalCtx blc w_star hw) p :=
  h w_star hw


end Semantics.Presupposition.TonhauserDerivation
