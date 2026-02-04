/-
# Verum Focus: VERUM Operator and Unbalanced Partitions

Semantic analysis of verum focus following Romero & Han (2004).

## Core Idea

VERUM is a **conversational epistemic operator**:

  FOR-SURE-CG_x(p) = ∀w' ∈ Epi_x(w)[∀w'' ∈ Conv_x(w')[p ∈ CG_w'']]

"For all worlds compatible with x's knowledge, for all worlds
compatible with x's conversational goals, p is in the Common Ground."

In short: "It is for sure that we should add p to the CG."

## Key Results

1. VERUM creates **unbalanced partitions**: {FOR-SURE-CG(p), ¬FOR-SURE-CG(p)}
   rather than {p, ¬p}

2. **Ladd's ambiguity** (PI vs NI) is scope ambiguity:
   - PI: [Q [not [VERUM [p]]]] → double-check p
   - NI: [Q [VERUM [not [p]]]] → double-check ¬p

3. **Epistemic implicature** from intent/pronunciation:
   - Asserting ¬FOR-SURE-CG(p) (PI) implicates belief in p
   - Asserting FOR-SURE-CG(¬p) (NI) implicates belief in ¬p

## References

- Romero, M. & Han, C.-H. (2004). On Negative Yes/No Questions.
- Höhle, T. (1992). Über Verum-Fokus im Deutschen.
- Ladd, D.R. (1981). A First Look at the Semantics and Pragmatics of
  Negative Questions and Tag Questions.
-/

import Linglib.Theories.Montague.Question.Basic
import Linglib.Core.CommonGround

namespace Montague.Question.VerumFocus

open Montague.Question

-- Part 1: Epistemic and Conversational States

/-- A world type with Common Ground -/
structure CGWorld (W : Type*) where
  /-- The possible world -/
  world : W
  /-- The Common Ground at this world (set of propositions) -/
  cg : List (W → Bool)

/-- Epistemic accessibility: worlds compatible with agent's knowledge -/
abbrev EpistemicAccessibility (W : Type*) := W → W → Bool

/-- Conversational accessibility: worlds compatible with agent's conversational goals -/
abbrev ConversationalAccessibility (W : Type*) := W → W → Bool

/-- Full modal frame for VERUM semantics -/
structure VerumFrame (W : Type*) where
  /-- Set of worlds -/
  worlds : List W
  /-- Epistemic accessibility (Epi_x) -/
  epiAccessible : EpistemicAccessibility W
  /-- Conversational accessibility (Conv_x) -/
  convAccessible : ConversationalAccessibility W
  /-- Common Ground function: for each world, what's in the CG -/
  commonGround : W → List (W → Bool)

-- Part 2: The VERUM Operator

/-- **FOR-SURE-CG**: The VERUM operator (Romero & Han 2004)

∀w' ∈ Epi_x(w)[∀w'' ∈ Conv_x(w')[p ∈ CG_w'']]

For all epistemic alternatives w', for all conversational alternatives w'',
p is in the Common Ground at w''.

This captures: "It is for sure that we should add p to the CG."
-/
def forSureCG {W : Type*} (frame : VerumFrame W)
    (w : W) (p : W → Bool) : Bool :=
  frame.worlds.all fun w' =>
    if frame.epiAccessible w w' then
      frame.worlds.all fun w'' =>
        if frame.convAccessible w' w'' then
          (frame.commonGround w'').any fun q =>
            frame.worlds.all fun v => p v == q v  -- p ∈ CG means p equals some CG proposition
        else true
    else true

/-- Simplified VERUM for finite models -/
def verum {W : Type*} [DecidableEq W]
    (cgMembership : W → (W → Bool) → Bool)  -- Is p in CG at w?
    (epiWorlds : W → List W)                 -- Epi_x(w)
    (convWorlds : W → List W)                -- Conv_x(w')
    (w : W) (p : W → Bool) : Bool :=
  (epiWorlds w).all fun w' =>
    (convWorlds w').all fun w'' =>
      cgMembership w'' p

-- Part 3: Unbalanced Partitions

/-- A polar question partition -/
structure QuestionPartition (W : Type*) where
  /-- The two cells of the partition -/
  cell1 : W → Bool
  cell2 : W → Bool
  /-- Which cell is "pronounced" (the surface form asks about) -/
  pronounced : W → Bool

/-- Standard balanced polar question: {p, ¬p} -/
def balancedQuestion {W : Type*} (p : W → Bool) : QuestionPartition W := {
  cell1 := p
  cell2 := fun w => !p w
  pronounced := p
}

/-- Unbalanced VERUM question: {FOR-SURE-CG(p), ¬FOR-SURE-CG(p)}

When VERUM is present, the partition is about epistemic commitment
to CG membership, not about p's truth directly.
-/
def verumQuestion {W : Type*} [DecidableEq W]
    (cgMembership : W → (W → Bool) → Bool)
    (epiWorlds : W → List W)
    (convWorlds : W → List W)
    (p : W → Bool)
    (pronounceNeg : Bool)  -- true for PI, false for NI
    : QuestionPartition W := {
  cell1 := fun w => verum cgMembership epiWorlds convWorlds w p
  cell2 := fun w => !verum cgMembership epiWorlds convWorlds w p
  pronounced := if pronounceNeg
    then fun w => !verum cgMembership epiWorlds convWorlds w p  -- PI: ¬FOR-SURE-CG(p)
    else fun w => verum cgMembership epiWorlds convWorlds w p   -- NI: FOR-SURE-CG(p)
}

-- Part 4: Ladd's Ambiguity (PI vs NI)

/-- Reading type for negative polar questions -/
inductive NegQuestionReading where
  | PI : NegQuestionReading  -- Positive-implicature (double-check p)
  | NI : NegQuestionReading  -- Negative-implicature (double-check ¬p)
  deriving Repr, DecidableEq

/-- LF structure for negative polar questions -/
inductive NegQuestionLF (W : Type*) where
  /-- PI: [Q [not [VERUM [p]]]] -/
  | piLF : (W → Bool) → NegQuestionLF W
  /-- NI: [Q [VERUM [not [p]]]] -/
  | niLF : (W → Bool) → NegQuestionLF W

/-- Extract the embedded proposition -/
def NegQuestionLF.proposition {W : Type*} : NegQuestionLF W → (W → Bool)
  | .piLF p => p
  | .niLF p => p

/-- Get the reading type -/
def NegQuestionLF.reading {W : Type*} : NegQuestionLF W → NegQuestionReading
  | .piLF _ => .PI
  | .niLF _ => .NI

/-- Interpret a negative question LF as a partition

- PI: {¬FOR-SURE-CG(p), FOR-SURE-CG(p)}
- NI: {FOR-SURE-CG(¬p), ¬FOR-SURE-CG(¬p)}
-/
def interpretNegQuestion {W : Type*} [DecidableEq W]
    (cgMembership : W → (W → Bool) → Bool)
    (epiWorlds : W → List W)
    (convWorlds : W → List W)
    (lf : NegQuestionLF W) : QuestionPartition W :=
  match lf with
  | .piLF p =>
    -- PI: asking about ¬FOR-SURE-CG(p)
    verumQuestion cgMembership epiWorlds convWorlds p true
  | .niLF p =>
    -- NI: VERUM scopes over negation, asking about FOR-SURE-CG(¬p)
    let notP : W → Bool := fun w => !p w
    verumQuestion cgMembership epiWorlds convWorlds notP false

-- Part 5: Epistemic Implicature

/-- Speaker's prior epistemic state -/
structure SpeakerEpistemicState (W : Type*) where
  /-- Worlds compatible with speaker's beliefs -/
  beliefWorlds : List W
  /-- Does speaker believe p? -/
  believes : (W → Bool) → Bool

/-- Implicature from pronounced cell

The pronounced cell of a VERUM question implicates the speaker's
prior belief:
- PI pronounces ¬FOR-SURE-CG(p) → implicates belief in p
- NI pronounces FOR-SURE-CG(¬p) → implicates belief in ¬p
-/
def epistemicImplicature {W : Type*}
    (reading : NegQuestionReading)
    (_p : W → Bool) : String :=
  match reading with
  | .PI => "Speaker believes p (expected 'yes')"
  | .NI => "Speaker believes ¬p (expected 'no')"

/-- Derive the implicature direction -/
def implicaturePolarity (reading : NegQuestionReading) : String :=
  match reading with
  | .PI => "positive"
  | .NI => "negative"

-- Part 6: Polarity Item Licensing

/-- Polarity item type -/
inductive PolarityItem where
  | PPI : String → PolarityItem  -- too, some, already
  | NPI : String → PolarityItem  -- either, any, yet
  deriving Repr, DecidableEq

/-- Check if polarity item is licensed under a reading

- PPIs licensed under PI reading (in scope of ¬FOR-SURE-CG)
- NPIs licensed under NI reading (in scope of VERUM over negation)
-/
def isLicensed (item : PolarityItem) (reading : NegQuestionReading) : Bool :=
  match item, reading with
  | .PPI _, .PI => true   -- PPIs licensed under PI
  | .NPI _, .NI => true   -- NPIs licensed under NI
  | .PPI _, .NI => false  -- PPIs not licensed under NI
  | .NPI _, .PI => false  -- NPIs not licensed under PI

/-- Common polarity items -/
def too : PolarityItem := .PPI "too"
def some_ : PolarityItem := .PPI "some"
def already : PolarityItem := .PPI "already"
def either : PolarityItem := .NPI "either"
def any : PolarityItem := .NPI "any"
def yet : PolarityItem := .NPI "yet"

/-- Ladd's generalization: PPIs → PI, NPIs → NI -/
theorem ppi_implies_pi (item : PolarityItem) (reading : NegQuestionReading) :
    isLicensed item reading = true →
    match item with
    | .PPI _ => reading = .PI
    | .NPI _ => reading = .NI := by
  intro h
  cases item <;> cases reading <;> simp [isLicensed] at h ⊢

-- Part 7: VERUM Sources

/-- Sources that contribute VERUM to the LF -/
inductive VerumSource where
  /-- Preposed negation: "Doesn't John..." -/
  | preposedNegation : VerumSource
  /-- The adverb "really": "Does John really..." -/
  | reallyAdverb : VerumSource
  /-- Focus on auxiliary: "DOES John..." -/
  | auxiliaryFocus : VerumSource
  /-- Focus on negation: "Does John NOT..." -/
  | negationFocus : VerumSource
  deriving Repr, DecidableEq

/-- Does this source necessarily trigger VERUM? -/
def necessarilyTriggersVerum : VerumSource → Bool
  | .preposedNegation => true   -- always triggers VERUM
  | .reallyAdverb => true       -- always triggers VERUM
  | .auxiliaryFocus => true     -- always triggers VERUM
  | .negationFocus => true      -- always triggers VERUM

/-- Romero & Han's Generalization 1 -/
theorem preposed_negation_forces_verum :
    necessarilyTriggersVerum .preposedNegation = true := rfl

-- Part 8: Connection to Decision Theory (van Rooy & Šafářová)

/-!
## Relationship to Polarity.lean

Van Rooy & Šafářová (2003) and Romero & Han (2004) are **complementary**:

1. **vR&Š (Polarity.lean)**: Explains WHICH polar question to use
   - Decision-theoretic: choose question that maximizes expected utility
   - Predicts bias based on speaker's credences and stakes

2. **R&H (this file)**: Explains WHY preposed negation forces bias
   - VERUM semantics: preposed negation introduces FOR-SURE-CG
   - Explains structural ambiguity (PI vs NI)
   - Explains polarity item licensing

Together they explain:
- WHY certain forms have bias (VERUM)
- WHEN speakers choose biased forms (decision theory)
-/

/-- Marker type for cross-theory reference -/
structure IntegrationWithPolarity where
  /-- vR&Š explains question choice -/
  decisionTheoreticChoice : Bool := true
  /-- R&H explains structural source of bias -/
  verumSourceOfBias : Bool := true

-- Part 9: Examples

/-- Example: "Doesn't John drink?" (PI reading)

LF: [Q [not [VERUM [John drinks]]]]
Partition: {¬FOR-SURE-CG(drinks(j)), FOR-SURE-CG(drinks(j))}
Pronounced: ¬FOR-SURE-CG(drinks(j))
Implicature: Speaker believes John drinks
-/
def examplePI : NegQuestionLF Unit := .piLF (fun () => true)

/-- Example: "Doesn't John drink?" (NI reading, with "either")

LF: [Q [VERUM [not [John drinks]]]]
Partition: {FOR-SURE-CG(¬drinks(j)), ¬FOR-SURE-CG(¬drinks(j))}
Pronounced: FOR-SURE-CG(¬drinks(j))
Implicature: Speaker believes John doesn't drink
-/
def exampleNI : NegQuestionLF Unit := .niLF (fun () => true)

-- Summary

/-!
## What This Module Provides

### VERUM Operator
- `forSureCG`: Full definition with epistemic/conversational accessibility
- `verum`: Simplified version for finite models

### Unbalanced Partitions
- `QuestionPartition`: General polar question partition
- `balancedQuestion`: Standard {p, ¬p}
- `verumQuestion`: VERUM-based {FOR-SURE-CG(p), ¬FOR-SURE-CG(p)}

### Ladd's Ambiguity
- `NegQuestionReading`: PI vs NI
- `NegQuestionLF`: LF structures with VERUM/negation scope
- `interpretNegQuestion`: LF → partition

### Polarity Item Licensing
- `PolarityItem`: PPIs and NPIs
- `isLicensed`: Licensing under PI/NI readings
- `ppi_implies_pi`: Ladd's generalization (proven)

### VERUM Sources
- `VerumSource`: Preposed negation, "really", aux focus, NOT focus
- `necessarilyTriggersVerum`: All sources force VERUM

### Integration
- Connection to `Polarity.lean` (decision-theoretic side)
- Cross-theory explanation of polar question bias

## Architecture

```
Phenomena/Focus/VerumFocus.lean     ← Empirical data
           │
           ▼
This module (Theory)
           │
           ├── VERUM operator (conversational epistemic)
           ├── Unbalanced partitions
           ├── Ladd's ambiguity (PI/NI)
           └── Polarity item licensing
           │
           ▼
Questions/Polarity.lean              ← Decision theory (vR&Š)
           │
           ▼
Questions.lean hub                   ← G&S partition semantics
```

## References

- Romero & Han (2004): VERUM semantics, Ladd's ambiguity
- Ladd (1981): PI/NI observation, p/¬p ambiguity
- Höhle (1992): Original verum focus concept
- van Rooy & Šafářová (2003): Decision-theoretic complement
-/

end Montague.Question.VerumFocus
