/-
# Scope Freezing Phenomena

Configurations where inverse scope becomes unavailable. No controlled experimental data exists for baseline-vs-frozen contrasts; judgments are introspective.

## Main definitions
- `Availability`, `FreezingContext`, `Example`

## References
- May (1985). Logical Form.
- Larson (1988). On the double object construction.
- Bruening (2001). QR obeys Superiority.
- Antonyuk (2015). Quantifier scope and scope freezing in Russian.
- Scontras et al. (2014, 2017). Experimental studies on scope ambiguity.
-/

namespace Phenomena.Quantification.ScopeFreezing

/-- Available scope readings for a sentence -/
inductive Availability where
  | ambiguous     -- Both surface and inverse available
  | surfaceOnly   -- Only surface scope (inverse frozen)
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

/-- A scope freezing example with empirical judgment -/
structure Example where
  id : String
  sentence : String
  quant1 : String
  quant2 : String
  context : FreezingContext
  observed : Availability
  confidence : Confidence := .clear
  source : DataSource := .introspective
  surfaceGloss : String := ""
  inverseGloss : String := ""
  notes : String := ""
  deriving Repr


-- Possessor Freezing

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


-- Double Object Freezing

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


-- Passive Freezing

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


-- Heavy NP Effects

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


-- Weak Crossover and Scope

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


-- Attitude Verb Scope

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


end Phenomena.Quantification.ScopeFreezing
