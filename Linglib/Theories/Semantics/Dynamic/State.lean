/-
# Discourse State

Formalizes the discourse state model from @cite{farkas-bruce-2010} "On Reacting
to Assertions and Polar Questions", which provides a unified framework for
understanding how conversation advances through assertions and questions.

## Key Concepts

Farkas & Bruce decompose the discourse state into five components:

| Component | Description |
|-----------|-------------|
| dcS | Speaker's discourse commitments (not yet joint) |
| dcL | Listener's discourse commitments |
| cg | Common ground (joint commitments) |
| table | Stack of issues under discussion |
| ps | Projected set (derivable from cg + table) |

## Connection to RSA Models

Current RSA models for presupposition projection use the `BeliefState` slot
for different components of the discourse state:

- @cite{scontras-tonhauser-2025}: BeliefState = dcS (speaker's private assumptions)
- @cite{warstadt-2022} / @cite{qing-goodman-lassiter-2016}: BeliefState = cg (common ground)

This module provides explicit types for these components, making the
theoretical distinctions clear while maintaining computational compatibility
with existing RSA infrastructure.

-/

import Linglib.Core.Semantics.Proposition
import Linglib.Core.Semantics.CommonGround
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic

namespace Semantics.Dynamic.State

open Core.Proposition
open Core.CommonGround


/--
Conversational participants.

Following Farkas & Bruce, we model two discourse roles: speaker and listener.
These roles are relative to a given utterance (they can swap between turns).
-/
inductive Participant where
  | speaker
  | listener
  deriving DecidableEq, Repr, Inhabited

/--
Sentence forms (clause types) that determine discourse effects.

Following Farkas & Bruce:
- Declaratives default-commit the speaker to the content
- Interrogatives raise an issue without commitment
-/
inductive SentenceForm where
  | declarative
  | interrogative
  deriving DecidableEq, Repr, Inhabited


/--
An issue on the conversational table.

In Farkas & Bruce's model, the table is a stack of issues that need to be
resolved before the conversation can return to a stable state.

For polar questions, `alternatives` is [p, ¬p].
For wh-questions, `alternatives` is the set of possible answers.
-/
structure Issue (W : Type*) where
  /-- The form of the sentence that raised this issue -/
  form : SentenceForm
  /-- The proposition(s) at issue -/
  alternatives : List (Prop' W)
  /-- Who raised this issue -/
  source : Participant := .speaker


/--
Discourse State following @cite{farkas-bruce-2010}.

This structure captures the conversational state at a given point in time.
It's parameterized by the World type for type-safe propositions.

Note: We omit `ps` (projected set) because it's derivable from `cg` and `table`.
The projected set contains worlds compatible with cg and at least one complete
answer to each issue on the table.
-/
structure DiscourseState (W : Type*) where
  /-- Speaker's discourse commitments (what speaker takes for granted) -/
  dcS : List (Prop' W)
  /-- Listener's discourse commitments -/
  dcL : List (Prop' W)
  /-- Common ground (joint commitments) -/
  cg : List (Prop' W)
  /-- The table: stack of issues under discussion -/
  table : List (Issue W)

namespace DiscourseState

variable {W : Type*}


/--
Empty/initial discourse state.

At the start of a conversation, there are no commitments and no issues
on the table. This is a "stable" state in F&B's terminology.
-/
def empty : DiscourseState W := ⟨[], [], [], []⟩

/--
Convert common ground to a ContextSet (worlds where all cg props hold).

This bridges to the existing `Core.CommonGround` infrastructure.
-/
def toContextSet (ds : DiscourseState W) : ContextSet W :=
  λ w => ∀ p ∈ ds.cg, p w

/--
World compatibility: w is compatible with the discourse state if
w satisfies all common ground propositions.
-/
def compatible (ds : DiscourseState W) (w : W) : Prop :=
  ∀ p ∈ ds.cg, p w

/--
Check if the table is empty (stable state).

A discourse state is stable when the table is empty, meaning all
issues have been resolved and there's nothing pending.
-/
def isStable (ds : DiscourseState W) : Bool := ds.table.isEmpty

/--
Check if a world is compatible with speaker's commitments.

This is what @cite{scontras-tonhauser-2025} call "speakerCredence": the speaker only considers
worlds compatible with their private assumptions.
-/
def speakerCompatible (ds : DiscourseState W) (w : W) : Prop :=
  ∀ p ∈ ds.dcS, p w

/--
Check if a world is compatible with listener's commitments.
-/
def listenerCompatible (ds : DiscourseState W) (w : W) : Prop :=
  ∀ p ∈ ds.dcL, p w


/--
Add a proposition to the common ground.

This models acceptance of an assertion: the proposition moves from
a participant's discourse commitments to the joint common ground.
-/
def addToCG (ds : DiscourseState W) (p : Prop' W) : DiscourseState W :=
  { ds with cg := p :: ds.cg }

/--
Add a proposition to speaker's discourse commitments.

This models the speaker asserting a proposition, which commits
the speaker but doesn't yet affect the common ground.
-/
def addToDcS (ds : DiscourseState W) (p : Prop' W) : DiscourseState W :=
  { ds with dcS := p :: ds.dcS }

/--
Add a proposition to listener's discourse commitments.
-/
def addToDcL (ds : DiscourseState W) (p : Prop' W) : DiscourseState W :=
  { ds with dcL := p :: ds.dcL }

/--
Push an issue onto the table.

This models raising a question or making an assertion (which implicitly
raises the issue of whether the content should be accepted).
-/
def pushIssue (ds : DiscourseState W) (issue : Issue W) : DiscourseState W :=
  { ds with table := issue :: ds.table }

/--
Pop an issue from the table (when resolved).
-/
def popIssue (ds : DiscourseState W) : DiscourseState W :=
  { ds with table := ds.table.tail }


/--
Effect of a declarative assertion.

Following F&B: an assertion of p by the speaker:
1. Adds p to dcS (speaker's commitments)
2. Pushes the issue {p} onto the table

The listener can then respond by:
- Accepting (adds p to dcL and cg, pops table)
- Rejecting (adds ¬p to dcL, creating a conflict)
- Neither (leaving p "on the table")
-/
def assertDeclarative (ds : DiscourseState W) (p : Prop' W) : DiscourseState W :=
  let issue : Issue W := { form := .declarative, alternatives := [p], source := .speaker }
  ds.addToDcS p |>.pushIssue issue

/--
Effect of a polar question.

Following F&B: a polar question about p:
1. Pushes the issue {p, ¬p} onto the table
2. Does not add commitments (questions don't commit)
-/
def askPolarQuestion (ds : DiscourseState W) (p : Prop' W) : DiscourseState W :=
  let negP : Prop' W := Classical.pnot W p
  let issue : Issue W := { form := .interrogative, alternatives := [p, negP], source := .speaker }
  ds.pushIssue issue

/--
Accept the top issue on the table.

This models the listener accepting an assertion (adding to dcL and cg)
or answering a question (adding the chosen alternative to cg).
-/
def acceptTop (ds : DiscourseState W) : DiscourseState W :=
  match ds.table with
  | [] => ds
  | issue :: rest =>
    match issue.alternatives.head? with
    | none => { ds with table := rest }
    | some p =>
      { ds with
        cg := p :: ds.cg
        dcL := p :: ds.dcL
        table := rest }


/--
Convert the common ground component to a `CG` structure.
-/
def toCG (ds : DiscourseState W) : CG W :=
  { propositions := ds.cg }

/--
Create a discourse state from a `CG` structure.

Sets cg, dcS, and dcL all to the CG propositions (everyone agrees).
-/
def fromCG (cg : CG W) : DiscourseState W :=
  { dcS := cg.propositions
    dcL := cg.propositions
    cg := cg.propositions
    table := [] }


/-!
## Connection to RSA Presupposition Models
@cite{scontras-tonhauser-2025} @cite{warstadt-2022} @cite{qing-goodman-lassiter-2016}

RSA models for presupposition projection use different components of the
discourse state as the latent variable that L1 infers:

### @cite{scontras-tonhauser-2025}: Inferring dcS

The `BeliefState` type represents different possible values of dcS (what
the speaker privately assumes). L1 infers which dcS best explains the
speaker's utterance choice.

The speaker may assume things not yet in the common ground,
which is why S&T prefer "private assumptions" over "common ground."

### @cite{warstadt-2022} / @cite{qing-goodman-lassiter-2016}: Inferring cg

The `Context` type represents different possible values of cg (what's
jointly accepted). L1 infers which cg state the speaker is acting on.

Accommodation is updating one's model of the common ground.
-/

end DiscourseState

end Semantics.Dynamic.State
