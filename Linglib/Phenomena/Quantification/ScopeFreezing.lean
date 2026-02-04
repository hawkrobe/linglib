/-
# Scope Freezing Phenomena

Empirical data on configurations where inverse scope becomes unavailable.

## Overview

Scope freezing occurs when a sentence with two scope-bearing elements
allows only surface scope, despite structurally similar sentences
being ambiguous.

## Key Paradigm: Possessor Freezing

(1) A student attended every seminar.        → ∃>∀, ∀>∃ (AMBIGUOUS)
(2) A student's teacher attended every seminar. → ∃>∀ only (FROZEN)

The possessor in (2) "freezes" scope: inverse scope (∀>∃) is unavailable.

## Other Freezing Contexts

- **Double object construction**: "gave NP NP" freezes scope
- **Passive**: "was V-ed by NP" often freezes scope
- **Heavy NP**: Complex NPs resist inverse scope
- **Weak crossover**: Bound variable readings block inverse scope

## Theoretical Significance

Different theories explain freezing differently:
- **Minimalism**: QR is blocked by structural constraints (possessor, etc.)
- **CCG**: Derivational structure doesn't generate inverse reading
- **Processing**: Inverse scope is costly; freezing = extreme cost
- **Pragmatics**: Context could make "frozen" readings available

The key question: Is freezing **categorical** (grammatical) or **gradient** (preference)?

## Empirical Status

**No controlled experimental data known** for the baseline-vs-frozen contrasts.

The judgments in this file are from theoretical literature (introspective).
Scontras et al. (2014, 2017) tested baseline ambiguity (~53% inverse acceptance
for "A shark attacked every pirate") but not freezing configurations.

This is an empirical gap — a direct comparison study would be valuable.

## References

- May (1985). Logical Form.
- Larson (1988). On the double object construction.
- Bruening (2001). QR obeys Superiority.
- Antonyuk (2015). Quantifier scope and scope freezing in Russian.
- Scontras et al. (2014, 2017). Experimental studies on scope ambiguity (baseline only).
-/

namespace Phenomena.Quantification.ScopeFreezing

-- Scope Availability

/-- Available scope readings for a sentence -/
inductive Availability where
  | ambiguous     -- Both surface and inverse available
  | surfaceOnly   -- Only surface scope (inverse FROZEN)
  | inverseOnly   -- Only inverse scope (rare)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Confidence in the judgment -/
inductive Confidence where
  | clear         -- Native speakers agree (but introspective)
  | gradient      -- Some variation / context-dependent
  | controversial -- Theoretical disagreement
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Source of the judgment -/
inductive DataSource where
  | introspective   -- Linguist intuition (no experimental data)
  | experimental    -- Controlled experiment with ratings
  | corpus          -- Corpus-based evidence
  deriving DecidableEq, BEq, Repr, Inhabited

-- Freezing Context Types

/-- Types of configurations that induce scope freezing -/
inductive FreezingContext where
  | none              -- No freezing context (baseline ambiguous)
  | possessor         -- "A student's teacher..."
  | doubleObject      -- "gave NP NP" vs "gave NP to NP"
  | passive           -- "was V-ed by NP"
  | heavyNP           -- Complex/heavy NP in subject
  | weakCrossover     -- Bound variable blocks inverse
  | adjunct           -- Adjunct scope interactions
  | attitude          -- Attitude verb complements
  deriving DecidableEq, BEq, Repr, Inhabited

-- Scope Freezing Example Structure

/-- A scope freezing example with empirical judgment -/
structure Example where
  /-- Unique identifier -/
  id : String
  /-- The sentence -/
  sentence : String
  /-- Quantifier 1 (typically subject) -/
  quant1 : String
  /-- Quantifier 2 (typically object) -/
  quant2 : String
  /-- Type of freezing context -/
  context : FreezingContext
  /-- Observed availability -/
  observed : Availability
  /-- Confidence in judgment -/
  confidence : Confidence := .clear
  /-- Source of judgment -/
  source : DataSource := .introspective
  /-- Surface scope gloss -/
  surfaceGloss : String := ""
  /-- Inverse scope gloss -/
  inverseGloss : String := ""
  /-- Notes -/
  notes : String := ""
  deriving Repr


/-!
## Possessor Freezing

The canonical scope freezing paradigm from the literature.
When the subject contains a possessor, inverse scope disappears.
-/

def possessor_baseline : Example :=
  { id := "poss-1a"
  , sentence := "A student attended every seminar."
  , quant1 := "a student"
  , quant2 := "every seminar"
  , context := .none
  , observed := .ambiguous
  , confidence := .clear
  , surfaceGloss := "There's a student who attended every seminar"
  , inverseGloss := "For every seminar, some student attended it"
  , notes := "Baseline: both readings available" }

def possessor_frozen : Example :=
  { id := "poss-1b"
  , sentence := "A student's teacher attended every seminar."
  , quant1 := "a student's teacher"
  , quant2 := "every seminar"
  , context := .possessor
  , observed := .surfaceOnly
  , confidence := .clear
  , surfaceGloss := "There's a student whose teacher attended every seminar"
  , inverseGloss := "*For every seminar, some student's teacher attended it"
  , notes := "Possessor freezes scope" }

def possessor_variant1 : Example :=
  { id := "poss-2a"
  , sentence := "Someone from every city was present."
  , quant1 := "someone from every city"
  , quant2 := "every city"
  , context := .none
  , observed := .ambiguous
  , confidence := .clear
  , surfaceGloss := "There's someone who is from every city (impossible)"
  , inverseGloss := "For every city, someone from it was present"
  , notes := "Inverse scope is the sensible reading" }

def possessor_variant2 : Example :=
  { id := "poss-2b"
  , sentence := "Someone's friend from every city was present."
  , quant1 := "someone's friend"
  , quant2 := "every city"
  , context := .possessor
  , observed := .surfaceOnly
  , confidence := .gradient
  , notes := "Possessor blocks inverse; sentence is odd" }


/-!
## Double Object Freezing

The double object construction ("V NP NP") freezes scope,
while the prepositional dative ("V NP to NP") allows ambiguity.

Larson (1988), Bruening (2001)
-/

def dative_baseline : Example :=
  { id := "dat-1a"
  , sentence := "Someone gave a book to every student."
  , quant1 := "someone"
  , quant2 := "every student"
  , context := .none
  , observed := .ambiguous
  , confidence := .clear
  , surfaceGloss := "There's someone who gave a book to every student"
  , inverseGloss := "For every student, someone gave them a book"
  , notes := "PP dative: ambiguous" }

def dative_frozen : Example :=
  { id := "dat-1b"
  , sentence := "Someone gave every student a book."
  , quant1 := "someone"
  , quant2 := "every student"
  , context := .doubleObject
  , observed := .surfaceOnly
  , confidence := .clear
  , surfaceGloss := "There's someone who gave every student a book"
  , inverseGloss := "*For every student, someone gave them a book"
  , notes := "Double object: frozen (Barss & Lasnik 1986)" }

def dative_variant : Example :=
  { id := "dat-2"
  , sentence := "A teacher showed every student a new problem."
  , quant1 := "a teacher"
  , quant2 := "every student"
  , context := .doubleObject
  , observed := .surfaceOnly
  , confidence := .clear
  , notes := "Double object freezes subject-IO scope" }


/-!
## Passive Freezing

Passive constructions often show scope freezing,
though judgments are more gradient than possessor cases.
-/

def passive_baseline : Example :=
  { id := "pass-1a"
  , sentence := "Every professor saw a student."
  , quant1 := "every professor"
  , quant2 := "a student"
  , context := .none
  , observed := .ambiguous
  , confidence := .clear
  , surfaceGloss := "For every professor, they saw a (possibly different) student"
  , inverseGloss := "There's a student that every professor saw"
  , notes := "Active: ambiguous" }

def passive_frozen : Example :=
  { id := "pass-1b"
  , sentence := "A student was seen by every professor."
  , quant1 := "a student"
  , quant2 := "every professor"
  , context := .passive
  , observed := .surfaceOnly
  , confidence := .gradient
  , surfaceGloss := "There's a student that every professor saw"
  , inverseGloss := "?For every professor, some student was seen by them"
  , notes := "Passive: frozen (but judgments vary)" }

def passive_variant : Example :=
  { id := "pass-2"
  , sentence := "Someone was interviewed by every committee."
  , quant1 := "someone"
  , quant2 := "every committee"
  , context := .passive
  , observed := .surfaceOnly
  , confidence := .gradient
  , notes := "by-phrase scope is limited" }


/-!
## Heavy NP Effects

Complex/heavy NPs in subject position tend to resist inverse scope.
This may be processing-based rather than grammatical.
-/

def heavy_baseline : Example :=
  { id := "heavy-1a"
  , sentence := "A man read every book."
  , quant1 := "a man"
  , quant2 := "every book"
  , context := .none
  , observed := .ambiguous
  , confidence := .clear
  , notes := "Simple subject: ambiguous" }

def heavy_frozen : Example :=
  { id := "heavy-1b"
  , sentence := "A man who was sitting in the corner read every book."
  , quant1 := "a man who was sitting in the corner"
  , quant2 := "every book"
  , context := .heavyNP
  , observed := .surfaceOnly
  , confidence := .gradient
  , notes := "Heavy subject: inverse scope degraded" }


/-!
## Weak Crossover and Scope

When inverse scope would create a weak crossover configuration,
it's blocked.
-/

def crossover_baseline : Example :=
  { id := "wco-1a"
  , sentence := "Someone loves every city."
  , quant1 := "someone"
  , quant2 := "every city"
  , context := .none
  , observed := .ambiguous
  , confidence := .clear
  , notes := "No bound variable: ambiguous" }

def crossover_frozen : Example :=
  { id := "wco-1b"
  , sentence := "Someone from it loves every city."
  , quant1 := "someone from it"
  , quant2 := "every city"
  , context := .weakCrossover
  , observed := .surfaceOnly
  , confidence := .clear
  , surfaceGloss := "There's someone from some city who loves every city"
  , inverseGloss := "*For every city_i, someone from it_i loves it_i"
  , notes := "Bound pronoun blocks QR (weak crossover)" }


/-!
## Attitude Verb Scope

Quantifiers in attitude complements often can't scope out.
-/

def attitude_frozen : Example :=
  { id := "att-1"
  , sentence := "Someone believes that every student passed."
  , quant1 := "someone"
  , quant2 := "every student"
  , context := .attitude
  , observed := .surfaceOnly
  , confidence := .gradient
  , surfaceGloss := "Someone believes the proposition 'every student passed'"
  , inverseGloss := "?For every student, someone believes they passed"
  , notes := "Embedded universal can't easily scope over matrix" }

-- Collected Data

def possessorExamples : List Example :=
  [possessor_baseline, possessor_frozen, possessor_variant1, possessor_variant2]

def doubleObjectExamples : List Example :=
  [dative_baseline, dative_frozen, dative_variant]

def passiveExamples : List Example :=
  [passive_baseline, passive_frozen, passive_variant]

def heavyNPExamples : List Example :=
  [heavy_baseline, heavy_frozen]

def crossoverExamples : List Example :=
  [crossover_baseline, crossover_frozen]

def attitudeExamples : List Example :=
  [attitude_frozen]

def allExamples : List Example :=
  possessorExamples ++ doubleObjectExamples ++ passiveExamples ++
  heavyNPExamples ++ crossoverExamples ++ attitudeExamples

-- Key Empirical Generalizations

/-- Possessor freezing is robust (clear judgments) -/
def possessorFreezingIsClear : Bool :=
  possessor_frozen.confidence == .clear

/-- Double object freezing is robust -/
def doubleObjectFreezingIsClear : Bool :=
  dative_frozen.confidence == .clear

/-- Passive freezing is more gradient -/
def passiveFreezingIsGradient : Bool :=
  passive_frozen.confidence == .gradient

/-- Count frozen examples -/
def frozenCount : Nat :=
  allExamples.filter (·.observed == .surfaceOnly) |>.length

/-- Count ambiguous baselines -/
def ambiguousCount : Nat :=
  allExamples.filter (·.observed == .ambiguous) |>.length

#eval frozenCount      -- 9
#eval ambiguousCount   -- 6

-- Theoretical Predictions (to be tested in Theories/Comparisons/)

/-!
## What Theories Predict

### Minimalism (QR + Economy)
- Possessor blocks QR: the indefinite is "trapped" inside the DP
- Double object: indirect object c-commands direct object at LF
- Passive: by-phrase is an adjunct, can't undergo QR
- Prediction: **Categorical** freezing

### CCG (Derivational)
- Scope = derivational ambiguity
- Possessor: single derivation for complex DP
- Double object: different argument structure than PP dative
- Prediction: **Categorical** freezing (different cause)

### Processing
- Inverse scope requires holding material in memory
- Complex subjects increase memory load
- Prediction: **Gradient** freezing (difficulty, not impossibility)

### RSA / Pragmatics
- Listeners integrate over possible interpretations
- "Frozen" readings might be available but dispreferred
- Context could make frozen readings accessible
- Prediction: **Gradient** freezing (preference, not grammar)

### Key Differentiating Data
1. Can context ever rescue "frozen" readings? (Pragmatics: yes; Syntax: no)
2. Is there a sharp boundary or continuous degradation? (Syntax: sharp; Processing: continuous)
3. Do all freezing contexts behave identically? (Syntax: possibly not; Processing: graded by complexity)
-/

-- Summary

/-!
## What This Module Provides

### Types
- `Availability`: ambiguous | surfaceOnly | inverseOnly
- `FreezingContext`: possessor | doubleObject | passive | heavyNP | ...
- `Example`: structured representation of scope freezing data

### Data
- 15 examples across 6 freezing contexts
- Judgments with confidence levels
- Surface and inverse glosses

### Key Paradigms
1. **Possessor freezing**: most robust, clearest judgments
2. **Double object**: robust, structural explanation clear
3. **Passive**: more gradient, theoretical debate
4. **Heavy NP**: likely processing-based
5. **Weak crossover**: binding theory interaction
6. **Attitude verbs**: clause-boundedness

### What Belongs Elsewhere
- Formal derivations: `Theories/Minimalism/`, `Theories/CCG/`
- Theory comparison: `Theories/Comparisons/ScopeFreezing/`
- RSA modeling: `Theories/RSA/Implementations/`
-/

end Phenomena.Quantification.ScopeFreezing
