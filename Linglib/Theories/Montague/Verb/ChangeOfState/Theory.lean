/-
# Change-of-State Predicate Semantics

CoS predicates (stop, start, continue) presuppose a prior state:
- "stop P" presupposes P was true, asserts P is now false
- "start P" presupposes P was false, asserts P is now true
- "continue P" presupposes P was true, asserts P is still true

All are Class C triggers (SCF=no, OLE=yes): informative, shifts under belief.

## Semantic Structure

Each CoS predicate has:
1. A **presupposition** about the prior state
2. An **assertion** about the result state

This maps directly to `PrProp` from `Core.Presupposition`:
- `presup`: the prior state condition
- `assertion`: the result state condition

## Examples

"Mary stopped smoking" at world w where she was smoking, now isn't:
  - presup(w) = w.priorSmokes = true    ✓
  - assertion(w) = ¬w.currentSmokes = ¬false = true  ✓

"Mary started smoking" at same world:
  - presup(w) = ¬w.priorSmokes = false   ✗ (presupposition failure)

## References

- Abusch, D. (2002). Lexical Alternatives as a Source of Pragmatic Presuppositions.
- Tonhauser, J., Beaver, D., Roberts, C., & Simons, M. (2013).
  Toward a Taxonomy of Projective Content.
- Simons, M. (2001). On the conversational basis of some presuppositions.
-/

import Linglib.Core.Presupposition

namespace Montague.Verb.ChangeOfState

open Core.Presupposition

-- Change-of-State Verb Classification

/--
Classification of change-of-state verbs by the direction of state change.

- **cessation**: Activity ceases (stop, quit, cease, finish)
  - Presupposes: P was happening
  - Asserts: P is no longer happening
  - Example: "stopped smoking" → was smoking, now isn't

- **inception**: Activity begins (start, begin, commence)
  - Presupposes: P was NOT happening
  - Asserts: P is now happening
  - Example: "started smoking" → wasn't smoking, now is

- **continuation**: Activity persists (continue, keep, remain)
  - Presupposes: P was happening
  - Asserts: P is still happening
  - Example: "continued smoking" → was smoking, still is
-/
inductive CoSType where
  | cessation    -- stop, quit, cease: P → ¬P
  | inception    -- start, begin: ¬P → P
  | continuation -- continue, keep: P → P
  deriving DecidableEq, Repr, BEq, Inhabited

-- Lexical Entry Structure

/--
A lexical entry for a change-of-state verb.

Bundles:
- Surface form ("stop", "start", etc.)
- Change type (cessation, inception, continuation)
- Whether the state change is reversible (default: true)

The activity predicate P is NOT part of the entry — it's supplied compositionally.
-/
structure CoSEntry where
  /-- Surface form -/
  form : String
  /-- Type of state change -/
  cosType : CoSType
  /-- Can the state change be undone? (stop → start → stop) -/
  reversible : Bool := true
  deriving Repr, BEq

-- Core Lexical Entries

/-- "stop" — cessation verb -/
def stop : CoSEntry := { form := "stop", cosType := .cessation }

/-- "quit" — cessation verb -/
def quit : CoSEntry := { form := "quit", cosType := .cessation }

/-- "cease" — cessation verb -/
def cease : CoSEntry := { form := "cease", cosType := .cessation }

/-- "finish" — cessation verb (often irreversible in context) -/
def finish : CoSEntry := { form := "finish", cosType := .cessation, reversible := false }

/-- "start" — inception verb -/
def start : CoSEntry := { form := "start", cosType := .inception }

/-- "begin" — inception verb -/
def begin_ : CoSEntry := { form := "begin", cosType := .inception }

/-- "commence" — inception verb -/
def commence : CoSEntry := { form := "commence", cosType := .inception }

/-- "continue" — continuation verb -/
def continue_ : CoSEntry := { form := "continue", cosType := .continuation }

/-- "keep" — continuation verb -/
def keep : CoSEntry := { form := "keep", cosType := .continuation }

/-- "remain" — continuation verb -/
def remain : CoSEntry := { form := "remain", cosType := .continuation }

-- Semantic Functions

variable {W : Type*}

/--
The presupposition triggered by a CoS type, given the activity predicate P.

- cessation: presupposes P (the activity was happening)
- inception: presupposes ¬P (the activity wasn't happening)
- continuation: presupposes P (the activity was happening)
-/
def priorStatePresup (t : CoSType) (P : W → Bool) : W → Bool :=
  match t with
  | .cessation => P           -- stop P presupposes P was true
  | .inception => fun w => !P w  -- start P presupposes P was false
  | .continuation => P        -- continue P presupposes P was true

/--
The assertion made by a CoS type, given the activity predicate P.

- cessation: asserts ¬P (the activity is no longer happening)
- inception: asserts P (the activity is now happening)
- continuation: asserts P (the activity is still happening)
-/
def resultStateAssertion (t : CoSType) (P : W → Bool) : W → Bool :=
  match t with
  | .cessation => fun w => !P w  -- stop P asserts P is now false
  | .inception => P              -- start P asserts P is now true
  | .continuation => P           -- continue P asserts P is still true

/--
Combined semantics of a CoS predicate as a presuppositional proposition.

Given an activity predicate P, returns a `PrProp` with:
- presupposition: the expected prior state
- assertion: the expected result state

This is the core semantic contribution: CoS predicates are presupposition
triggers that constrain both the prior and current states.
-/
def cosSemantics (t : CoSType) (P : W → Bool) : PrProp W :=
  { presup := priorStatePresup t P
  , assertion := resultStateAssertion t P }

/--
Semantics for a lexical entry applied to an activity predicate.
-/
def entrySemantics (e : CoSEntry) (P : W → Bool) : PrProp W :=
  cosSemantics e.cosType P

-- Key Theorems

/--
Negation preserves presupposition (hole property).

"Mary didn't stop smoking" has the same presupposition as "Mary stopped smoking":
both presuppose she was smoking.

This is a defining property of presupposition triggers and enables the
classic test: if the presupposition projects through negation, it's a
presupposition, not an entailment.
-/
theorem negation_preserves_presup (t : CoSType) (P : W → Bool) :
    (cosSemantics t P).presup =
    (PrProp.neg (cosSemantics t P)).presup := by
  simp only [PrProp.neg]

/--
Cessation and inception have complementary presuppositions.

- "stop P" presupposes P
- "start P" presupposes ¬P

These are exact complements: at any world, exactly one presupposition is satisfied.
-/
theorem cessation_inception_complementary (P : W → Bool) (w : W) :
    priorStatePresup .cessation P w = !priorStatePresup .inception P w := by
  simp only [priorStatePresup, Bool.not_not]

/--
Cessation and continuation have the same presupposition.

Both "stop P" and "continue P" presuppose that P was happening.
The difference is only in the assertion about the result state.
-/
theorem cessation_continuation_same_presup (P : W → Bool) :
    priorStatePresup .cessation P = priorStatePresup .continuation P := rfl

/--
For cessation, the assertion is the negation of the presupposition.

"stop P" presupposes P and asserts ¬P.
This captures the change: from P being true to P being false.
-/
theorem cessation_assertion_negates_presup (P : W → Bool) (w : W) :
    resultStateAssertion .cessation P w = !priorStatePresup .cessation P w := rfl

/--
For inception, the assertion is the negation of the presupposition.

"start P" presupposes ¬P and asserts P.
This captures the change: from P being false to P being true.
-/
theorem inception_assertion_negates_presup (P : W → Bool) (w : W) :
    resultStateAssertion .inception P w = !priorStatePresup .inception P w := by
  simp only [resultStateAssertion, priorStatePresup, Bool.not_not]

/--
For continuation, the assertion equals the presupposition.

"continue P" presupposes P and asserts P.
No change occurs; the predicate reports persistence.
-/
theorem continuation_assertion_equals_presup (P : W → Bool) :
    resultStateAssertion .continuation P = priorStatePresup .continuation P := rfl

-- Class C Property

/--
All CoS predicates shift under belief (Tonhauser et al. 2013: Class C).

The presupposition is attributed to the speaker by default, but shifts
to a belief holder in embedded contexts:

  "John believes Mary stopped smoking"
  → Presupposes that JOHN believes Mary was smoking (not the speaker)

This is captured by returning `true` for all entries.
-/
def shiftsUnderBelief (_e : CoSEntry) : Bool := true

/--
All CoS predicates have OLE (Optional Local Effect) = yes.

The presupposition can be locally satisfied in conditionals and disjunctions:

  "If Mary was smoking, she stopped"
  → No presupposition projects (locally satisfied by antecedent)

This is a defining characteristic of soft triggers.
-/
def hasOLE (_e : CoSEntry) : Bool := true

/--
All CoS predicates have SCF (Strong Contextual Felicity) = no.

The presupposition need not be established in prior discourse:

  A: "What's new with Mary?"
  B: "She stopped smoking."
  → Felicitous even though A didn't establish Mary smoked

This distinguishes soft triggers from hard triggers like "too".
-/
def hasSCF (_e : CoSEntry) : Bool := false

-- Summary

/-
## Summary: Change-of-State Predicate Semantics

### Key Types
- `CoSType`: Classification (cessation, inception, continuation)
- `CoSEntry`: Lexical entry bundling form and type

### Core Semantic Functions
- `priorStatePresup t P`: What prior state is presupposed?
- `resultStateAssertion t P`: What result state is asserted?
- `cosSemantics t P`: Combined PrProp with both components

### Key Results
- `negation_preserves_presup`: Presupposition projects through negation
- `cessation_inception_complementary`: stop/start have opposite presupps
- `cessation_continuation_same_presup`: stop/continue share presupposition
- `cessation_assertion_negates_presup`: stop P: presup P, assert ¬P

### Projection Behavior (Class C)
- All CoS predicates: OLE=yes, SCF=no, shifts under belief

### Usage
RSA models and projection tests should import this module for the
compositional semantics. The `cosSemantics` function provides the
grounding for downstream pragmatic reasoning.
-/

end Montague.Verb.ChangeOfState
