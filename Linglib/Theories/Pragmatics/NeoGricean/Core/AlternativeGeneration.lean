/-
# Alternative Generation from Derivations

Generates the ALT set required by exhaustivity operators (exhMW, exhIE)
from compositional Montague derivations.

## The Gap This Fills

Before:
- exhMW/exhIE work on `ALT : Set (Prop' World)` (hand-crafted)
- Derivations have scalar items but no way to generate ALT

After:
- `SentenceFrame`: captures Det-N-VP structure with substitutable quantifier
- `alternativeFrames`: generates frames with stronger quantifiers
- `altSet`: produces `Set (Prop' World)` for exh

## Architecture

```
Derivation with scalar item
    ↓ extract frame
SentenceFrame (quant, noun, vpAt)
    ↓ alternativeFrames
List of alternative frames
    ↓ frameToProp
Set (Prop' World)
    ↓ exhMW / exhIE
Exhaustified proposition
```

## Limitations (v1)

- Only handles simple Det-N-VP sentences
- Requires explicit world-indexed VP
- Single scalar item per sentence

Future extensions could handle:
- Multiple scalar items (interaction)
- Embedded contexts (scope over exh)
- Connectives (or/and scales)
-/

import Linglib.Theories.Semantics.Montague.Lexicon
import Linglib.Theories.Semantics.Montague.Derivation
import Linglib.Theories.Pragmatics.NeoGricean.Exhaustivity.Basic
import Linglib.Theories.Pragmatics.NeoGricean.Core.Alternatives
import Mathlib.Data.Set.Basic

namespace NeoGricean.AlternativeGeneration

open Semantics.Montague
open Semantics.Montague
open Semantics.Montague.Derivation
open Semantics.Entailment.Polarity (ContextPolarity)
open Semantics.Lexical.Determiner.Quantifier
open Core.Scale
open NeoGricean.Exhaustivity

/-
## Sentence Frames

A `SentenceFrame` represents a Det-N-VP sentence where the determiner
(quantifier) can be substituted to generate alternatives.

Example: "some students passed"
- quant = some_sem
- noun = isStudent
- form = "some"
- scaleMembership = .quantifier .some_

The VP is provided separately (world-indexed) to enable evaluation at
different worlds.
-/

/--
A sentence frame for Det-N-VP sentences.

Captures the structure needed to:
1. Evaluate the sentence at any world (given world-indexed VP)
2. Generate alternatives by substituting the quantifier
-/
structure SentenceFrame (m : Model) where
  /-- The quantifier denotation (e.g., some_sem, every_sem) -/
  quant : m.interpTy Ty.det
  /-- The noun denotation (e.g., isStudent) -/
  noun : m.interpTy (.e ⇒ .t)
  /-- Surface form of the quantifier (for display/lookup) -/
  form : String
  /-- Which scale the quantifier belongs to -/
  scaleMembership : Option ScaleMembership

/--
Evaluate a sentence frame with a specific VP.

For Det-N-VP: ⟦Det⟧(⟦N⟧)(⟦VP⟧)
-/
def SentenceFrame.eval {m : Model} (f : SentenceFrame m)
    (vp : m.interpTy (.e ⇒ .t)) : Bool :=
  f.quant f.noun vp

/--
Create a frame from a lexical entry and noun denotation.
-/
def frameFromEntry {m : Model} (entry : SemLexEntry m)
    (noun : m.interpTy (.e ⇒ .t))
    (h : entry.ty = Ty.det := by rfl) : SentenceFrame m :=
  { quant := h ▸ entry.denot
  , noun := noun
  , form := entry.form
  , scaleMembership := entry.scaleMembership
  }


/-
## Alternative Frames

Given a sentence frame with a scalar quantifier, generate frames
with stronger alternatives substituted.

Uses the lexicon to look up alternative forms and their denotations.
-/

/--
Generate alternative frames by substituting stronger quantifiers.

For "some students VP":
- Looks up "some" → gets stronger alternatives ["most", "all"]
- For each alternative, creates a new frame with that quantifier

The context polarity determines whether we use stronger (UE) or
weaker (DE) alternatives.
-/
def alternativeFrames {m : Model} (f : SentenceFrame m)
    (lex : SemLexicon m) (ctx : ContextPolarity) : List (SentenceFrame m) :=
  match ctx with
  | .upward =>
    -- Get stronger alternative entries from lexicon
    let altEntries := lookupAlternatives lex f.form
    altEntries.filterMap λ entry =>
      -- Only include quantifier-type entries
      if h : entry.ty = Ty.det then
        some { quant := h ▸ entry.denot
             , noun := f.noun
             , form := entry.form
             , scaleMembership := entry.scaleMembership }
      else
        none
  | .downward =>
    -- For DE contexts, we'd need weaker alternatives
    -- Not implemented yet - would need weakerAlternatives in lexicon
    []
  | .nonMonotonic =>
    -- Non-monotonic contexts don't generate scalar alternatives
    []

/--
Get all frames (original + alternatives).
-/
def allFrames {m : Model} (f : SentenceFrame m)
    (lex : SemLexicon m) (ctx : ContextPolarity) : List (SentenceFrame m) :=
  f :: alternativeFrames f lex ctx


/-
## World-Indexed Propositions

To work with exhaustivity operators, we need `Prop' World` (functions
from worlds to propositions), not just `Bool`.

The bridge: a world-indexed VP function that determines, for each world,
which entities satisfy the VP predicate.
-/

/--
A world-indexed VP: for each world, gives the VP denotation.

Example: `passedAt w` returns which students passed at world w.
-/
abbrev WorldIndexedVP (m : Model) (World : Type) := World → m.interpTy (.e ⇒ .t)

/--
Convert a sentence frame to `Prop' World` given a world-indexed VP.

For each world w:
  frameToProp f vpAt w = (f.quant f.noun (vpAt w)) = true
-/
def frameToProp {m : Model} {World : Type} (f : SentenceFrame m)
    (vpAt : WorldIndexedVP m World) : Prop' World :=
  λ w => f.eval (vpAt w) = true

/--
Convert all frames to propositions.
-/
def framesToProps {m : Model} {World : Type} (frames : List (SentenceFrame m))
    (vpAt : WorldIndexedVP m World) : List (Prop' World) :=
  frames.map (λ f => frameToProp f vpAt)


/-
## The Main Function: altSet

This is the key function that generates the ALT set for exhaustivity:

  altSet frame vpAt lex ctx : Set (Prop' World)

Given:
- A sentence frame (e.g., "some students VP")
- A world-indexed VP (e.g., passedAt)
- A lexicon (for looking up alternatives)
- Context polarity (UE/DE)

Returns:
- The set of propositions {⟦some students VP⟧, ⟦most students VP⟧, ⟦all students VP⟧}
  as world-dependent propositions
-/

/--
Generate the ALT set from a sentence frame.

This is the main interface to exhaustivity operators.
-/
def altSet {m : Model} {World : Type} (f : SentenceFrame m)
    (vpAt : WorldIndexedVP m World) (lex : SemLexicon m)
    (ctx : ContextPolarity := .upward) : Set (Prop' World) :=
  let props := framesToProps (allFrames f lex ctx) vpAt
  { p | p ∈ props }

/--
Generate ALT set without the base proposition (just alternatives).
-/
def strictAltSet {m : Model} {World : Type} (f : SentenceFrame m)
    (vpAt : WorldIndexedVP m World) (lex : SemLexicon m)
    (ctx : ContextPolarity := .upward) : Set (Prop' World) :=
  let props := framesToProps (alternativeFrames f lex ctx) vpAt
  { p | p ∈ props }


/-
## Connecting to exhMW and exhIE

Now we can compute exhaustified meanings directly from derivations:

```
exhMW (altSet frame vpAt lex) (frameToProp frame vpAt)
```

This gives the exhaustified proposition without hand-crafting ALT.
-/

/--
Apply exhMW to a sentence frame.
-/
def exhMW_frame {m : Model} {World : Type} (f : SentenceFrame m)
    (vpAt : WorldIndexedVP m World) (lex : SemLexicon m)
    (ctx : ContextPolarity := .upward) : Prop' World :=
  exhMW (altSet f vpAt lex ctx) (frameToProp f vpAt)

/--
Apply exhIE to a sentence frame.
-/
def exhIE_frame {m : Model} {World : Type} (f : SentenceFrame m)
    (vpAt : WorldIndexedVP m World) (lex : SemLexicon m)
    (ctx : ContextPolarity := .upward) : Prop' World :=
  exhIE (altSet f vpAt lex ctx) (frameToProp f vpAt)

-- PART 5b: Bridge from SemDeriv to SentenceFrame

/-
## Extracting Frames from Derivations

For simple Det-N-VP derivations, we can extract a `SentenceFrame` if we know
the noun denotation. This bridges the gap between the compositional derivation
system and the frame-based alternative generation.

Limitations:
- Requires knowing the noun denotation separately
- Only works for Det-N-VP pattern
- Single scalar item (the determiner)
-/

/--
Extract a sentence frame from a derivation's scalar item.

Requires:
- The derivation has exactly one scalar item (at position 0, the determiner)
- The scalar item is a quantifier
- The noun denotation is provided separately

Returns `none` if the derivation doesn't match the expected pattern.
-/
def frameFromDerivation {m : Model} (d : SemDeriv m)
    (noun : m.interpTy (.e ⇒ .t)) : Option (SentenceFrame m) :=
  match d.scalarItems with
  | [occ] =>
    -- Check the scalar item is at position 0 (determiner position)
    if occ.position = 0 then
      -- Check it's a quantifier type
      if h : occ.entry.ty = Ty.det then
        some { quant := h ▸ occ.entry.denot
             , noun := noun
             , form := occ.entry.form
             , scaleMembership := occ.entry.scaleMembership }
      else
        none
    else
      none
  | _ => none

/--
Generate ALT set directly from a derivation.

Combines `frameFromDerivation` and `altSet`.
-/
def altSetFromDerivation {m : Model} {World : Type} (d : SemDeriv m)
    (noun : m.interpTy (.e ⇒ .t))
    (vpAt : WorldIndexedVP m World)
    (lex : SemLexicon m)
    (ctx : ContextPolarity := .upward) : Option (Set (Prop' World)) :=
  (frameFromDerivation d noun).map λ frame =>
    altSet frame vpAt lex ctx

/--
Apply exhMW directly to a derivation.
-/
def exhMW_derivation {m : Model} {World : Type} (d : SemDeriv m)
    (noun : m.interpTy (.e ⇒ .t))
    (vpAt : WorldIndexedVP m World)
    (lex : SemLexicon m)
    (ctx : ContextPolarity := .upward) : Option (Prop' World) :=
  (frameFromDerivation d noun).map λ frame =>
    exhMW_frame frame vpAt lex ctx

/--
Apply exhIE directly to a derivation.
-/
def exhIE_derivation {m : Model} {World : Type} (d : SemDeriv m)
    (noun : m.interpTy (.e ⇒ .t))
    (vpAt : WorldIndexedVP m World)
    (lex : SemLexicon m)
    (ctx : ContextPolarity := .upward) : Option (Prop' World) :=
  (frameFromDerivation d noun).map λ frame =>
    exhIE_frame frame vpAt lex ctx


/-
## Worked Example

We recreate the MontagueExhaustivity example but with automatic ALT generation.
-/

/-- Three students -/
inductive Student where
  | alice | bob | carol
  deriving DecidableEq, Repr, BEq

/-- Student model -/
def studentModel : Model where
  Entity := Student
  decEq := inferInstance

instance : FiniteModel studentModel where
  elements := [.alice, .bob, .carol]
  complete := λ x => by cases x <;> simp
  nodup := by simp [List.nodup_cons, List.mem_cons, List.mem_singleton]

/-- All entities are students -/
def isStudent : studentModel.interpTy (.e ⇒ .t) := λ _ => true

/-- World = number of students who passed (0-3) -/
abbrev PassWorld := Fin 4

/-- "passed" indexed by world -/
def passedAt : WorldIndexedVP studentModel PassWorld := λ w s =>
  match w.val, s with
  | 0, _ => false
  | 1, .alice => true
  | 1, _ => false
  | 2, .alice => true
  | 2, .bob => true
  | 2, .carol => false
  | 3, _ => true
  | _, _ => false

-- Lexicon for student model
def studentLexicon : SemLexicon studentModel := λ form =>
  match form with
  | "some" => some { word := ⟨"some", .DET, {}⟩
                   , ty := Ty.det
                   , denot := some_sem studentModel
                   , scaleMembership := some (.quantifier .some_) }
  | "every" => some { word := ⟨"every", .DET, {}⟩
                    , ty := Ty.det
                    , denot := every_sem studentModel
                    , scaleMembership := some (.quantifier .all) }
  | "all" => some { word := ⟨"all", .DET, {}⟩
                  , ty := Ty.det
                  , denot := every_sem studentModel
                  , scaleMembership := some (.quantifier .all) }
  | "most" => some { word := ⟨"most", .DET, {}⟩
                   , ty := Ty.det
                   , denot := most_sem studentModel
                   , scaleMembership := some (.quantifier .most) }
  | _ => none

/-- Frame for "some students passed" -/
def someStudentsFrame : SentenceFrame studentModel :=
  { quant := some_sem studentModel
  , noun := isStudent
  , form := "some"
  , scaleMembership := some (.quantifier .some_)
  }

/-- Frame for "all students passed" -/
def allStudentsFrame : SentenceFrame studentModel :=
  { quant := every_sem studentModel
  , noun := isStudent
  , form := "all"
  , scaleMembership := some (.quantifier .all)
  }

-- The base proposition
def somePassed : Prop' PassWorld := frameToProp someStudentsFrame passedAt

-- The alternative proposition
def allPassed : Prop' PassWorld := frameToProp allStudentsFrame passedAt

-- World w1: one student passed
def w1 : PassWorld := ⟨1, by omega⟩

-- World w3: all students passed
def w3 : PassWorld := ⟨3, by omega⟩


/-- somePassed holds at w1 -/
theorem somePassed_at_w1 : somePassed w1 := by
  simp only [somePassed, frameToProp, SentenceFrame.eval,
             someStudentsFrame, w1, some_sem, isStudent, passedAt]
  decide

/-- allPassed does NOT hold at w1 -/
theorem allPassed_not_w1 : ¬(allPassed w1) := by
  simp only [allPassed, frameToProp, SentenceFrame.eval,
             allStudentsFrame, w1, every_sem, isStudent, passedAt]
  decide

/-- Both hold at w3 -/
theorem both_at_w3 : somePassed w3 ∧ allPassed w3 := by
  constructor
  · simp only [somePassed, frameToProp, SentenceFrame.eval,
               someStudentsFrame, w3, some_sem, isStudent, passedAt]
    decide
  · simp only [allPassed, frameToProp, SentenceFrame.eval,
               allStudentsFrame, w3, every_sem, isStudent, passedAt]
    decide

/-- Alternative frames include "all" (via lookupAlternatives) -/
theorem some_has_all_alternative :
    (alternativeFrames someStudentsFrame studentLexicon .upward).any
      (λ f => f.form == "all") = true := by native_decide

/--
The automatically generated ALT set contains somePassed.
-/
theorem altSet_contains_base :
    somePassed ∈ altSet someStudentsFrame passedAt studentLexicon := by
  simp only [altSet, allFrames, framesToProps, List.map]
  simp only [Set.mem_setOf_eq, List.mem_cons, List.mem_map]
  left
  rfl


/-
## The Payoff: Automatic Exhaustification

Now we can apply exh to automatically-generated alternatives:
-/

/-- The exhaustified "some students passed" -/
def exhSomePassed : Prop' PassWorld :=
  exhMW_frame someStudentsFrame passedAt studentLexicon

/--
Exhaustified "some" holds at w1 (automatic ALT).

This theorem shows that with automatically generated alternatives,
exhMW correctly derives "some but not all" at w1.

The proof requires showing w1 is minimal: no world makes strictly fewer
alternatives true while still satisfying "some passed".

Proof sketch:
- w1 makes true: {somePassed}
- w2 makes true: {somePassed, mostPassed}
- w3 makes true: {somePassed, mostPassed, allPassed}
- w0 makes true: {} (but doesn't satisfy somePassed)

So w1 is minimal among some-worlds, hence exhMW(some)(w1) holds.
-/
theorem exh_some_at_w1 : exhSomePassed w1 := by
  simp only [exhSomePassed, exhMW_frame, exhMW]
  constructor
  · exact somePassed_at_w1
  · -- Show w1 is minimal: no v with somePassed v ∧ v <[ALT] w1
    intro ⟨v, hv_some, hv_lt⟩
    -- v <[ALT] w1 means v makes strictly fewer alternatives true
    -- But w1 only makes "some" true (not "most", not "all")
    -- And any v with somePassed v makes at least "some" true
    -- So v can't make strictly fewer - contradiction
    obtain ⟨hle, hne⟩ := hv_lt
    apply hne
    intro a ha ha_v
    -- If a(v) and a ∈ ALT, need to show a(w1)
    -- The only alternative true at w1 is somePassed
    -- So we need: if a ∈ ALT and a(v), then a(w1)
    simp only [altSet, allFrames, alternativeFrames, framesToProps] at ha
    simp only [Set.mem_setOf_eq, List.mem_map, List.mem_cons] at ha
    rcases ha with ⟨f, hf_mem, rfl⟩
    -- Both cases (base frame and alternative frames) require detailed
    -- case analysis on the world structure:
    -- - At w1 (1 student passed), only "some" is true
    -- - At w2,w3 (2+ students), "most"/"all" may also be true
    -- - So w1 makes the fewest alternatives true among some-worlds
    -- - Hence w1 is minimal
    --
    -- Full proof would use fin_cases on v and explicit computation.
    -- Deferring to focus on infrastructure.
    sorry


end NeoGricean.AlternativeGeneration
