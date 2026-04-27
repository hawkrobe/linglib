import Linglib.Theories.Syntax.Minimalist.Scope
import Linglib.Features.ScopeTypes
import Linglib.Phenomena.ArgumentStructure.Studies.Pylkkanen2008

/-!
# @cite{bruening-2001} — QR Obeys Superiority
@cite{bruening-2001} @cite{larson-1988} @cite{may-1985}
@cite{pylkkanen-2008}

Bruening's *Linguistic Inquiry* paper "QR Obeys Superiority: Frozen
Scope and ACD" — both the empirical scope-freezing data set and the
theoretical Minimalist analysis (QR locality + superiority +
phase-theoretic barriers).

## Part I: Empirical data

Theory-neutral scope-freezing examples primarily compiled from
@cite{bruening-2001}, with contributions from @cite{larson-1988}
(double-object construction examples) and @cite{may-1985}
(foundational scope-availability vocabulary). Was formerly
`Phenomena/Quantification/Data.lean`; renamed per the
provenance-tracking policy.

Downstream consumer `Steedman2000.lean` imports from here.

## Part II: Theoretical analysis (Minimalist QR)

Bruening's central thesis — *QR obeys Superiority* — is derived
formally: double-object scope freezing follows from asymmetric
c-command in @cite{pylkkanen-2008}'s Voice + low-Appl tree, where the
goal asymmetrically c-commands the theme. Other freezing contexts
(possessor, passive, attitude) are analyzed via DP-phase /
adjunct-island / clause-boundary barriers.

Was formerly `Phenomena/Quantification/MinimalismScope.lean`;
absorbed here per the "study files own the analysis they advance"
policy (CLAUDE.md).

## Sections
- `ScopeFreezing`: Empirical configurations where inverse scope is unavailable
- `ScopeWordOrder`: Word order effects on scope in verb-final constructions
- `MinimalistAnalysis`: Theoretical derivation of freezing from Minimalist QR
-/

namespace Phenomena.Quantification.Bruening2001

-- ============================================================================
-- § Scope Freezing
-- ============================================================================

section ScopeFreezing

/-- Available scope readings for a sentence -/
inductive Availability where
  | ambiguous     -- Both surface and inverse available
  | surfaceOnly   -- Only surface scope (inverse frozen)
  | inverseOnly   -- Only inverse scope (rare)
  deriving DecidableEq, Repr, Inhabited

/-- Confidence in the judgment -/
inductive Confidence where
  | clear         -- Native speakers agree (but introspective)
  | gradient      -- Some variation / context-dependent
  | controversial -- Theoretical disagreement
  deriving DecidableEq, Repr, Inhabited

/-- Source of the judgment -/
inductive DataSource where
  | introspective   -- Linguist intuition (no experimental data)
  | experimental    -- Controlled experiment with ratings
  | corpus          -- Corpus-based evidence
  deriving DecidableEq, Repr, Inhabited

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
  deriving DecidableEq, Repr, Inhabited

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
  , notes := "Double object: frozen (@cite{barss-lasnik-1986})" }

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

#guard frozenCount == 9
#guard ambiguousCount == 6

end ScopeFreezing


-- ============================================================================
-- § Scope-Word Order Interactions
-- ============================================================================

section ScopeWordOrder

/-- Word order patterns in verb-final constructions. -/
inductive VerbOrder where
  | verbRaising          -- NP ... V_emb V_matrix (object precedes all verbs)
  | verbProjectionRaising -- V_matrix ... NP V_emb (object follows matrix verb)
  deriving DecidableEq, Repr, Inhabited

/-- Whether a word order blocks inverse scope -/
def blocksInverseScope : VerbOrder → Bool
  | .verbRaising => false          -- allows both readings
  | .verbProjectionRaising => true -- blocks inverse scope

/-- Available scope readings for a sentence. -/
inductive ScopeAvailability where
  | surfaceOnly  -- Only ∃>∀ or ∀>¬ (whichever is surface)
  | ambiguous    -- Both readings available
  deriving DecidableEq, Repr, Inhabited

/-- Convert word order to scope availability -/
def wordOrderToAvailability : VerbOrder → ScopeAvailability
  | .verbRaising => .ambiguous
  | .verbProjectionRaising => .surfaceOnly

/-- German sentence data from Bayer/Kayne. -/
structure GermanScopeExample where
  surface : String
  translation : String
  wordOrder : VerbOrder
  observed : ScopeAvailability
  deriving Repr

def german_96 : GermanScopeExample :=
  { surface := "(Weil) irgendjemand auf jeden gespannt ist"
  , translation := "Since someone is curious about everybody"
  , wordOrder := .verbRaising
  , observed := .ambiguous }

def german_97 : GermanScopeExample :=
  { surface := "(Weil) jemand versucht hat jeden reinzulegen"
  , translation := "Since someone has tried to cheat everyone"
  , wordOrder := .verbProjectionRaising
  , observed := .surfaceOnly }

/-- West Flemish data from @cite{haegeman-van-riemsdijk-1986}. -/
structure WestFlemishScopeExample where
  surface : String
  translation : String
  wordOrder : VerbOrder
  observed : ScopeAvailability
  deriving Repr

def westFlemish_98a : WestFlemishScopeExample :=
  { surface := "(da) Jan vee boeken hee willen lezen"
  , translation := "that Jan wanted to read many books"
  , wordOrder := .verbRaising
  , observed := .ambiguous }

def westFlemish_98b : WestFlemishScopeExample :=
  { surface := "(da) Jan hee willen vee boeken lezen"
  , translation := "that Jan wanted to read many books"
  , wordOrder := .verbProjectionRaising
  , observed := .surfaceOnly }

/-- Dutch equi verb data from @cite{steedman-2000}. -/
structure DutchScopeExample where
  surface : String
  translation : String
  wordOrder : VerbOrder
  observed : ScopeAvailability
  quantifiers : List String := []
  deriving Repr

def dutch_99a : DutchScopeExample :=
  { surface := "(omdat) Jan veel liederen probeert te zingen"
  , translation := "because Jan tries to sing many songs"
  , wordOrder := .verbRaising
  , observed := .ambiguous
  , quantifiers := ["veel/many"] }

def dutch_99b : DutchScopeExample :=
  { surface := "(omdat) Jan probeert veel liederen te zingen"
  , translation := "because Jan tries to sing many songs"
  , wordOrder := .verbProjectionRaising
  , observed := .surfaceOnly
  , quantifiers := ["veel/many"] }

def dutch_100a : DutchScopeExample :=
  { surface := "(omdat) iemand alle liederen probeert te zingen"
  , translation := "because someone tries to sing every song"
  , wordOrder := .verbRaising
  , observed := .ambiguous
  , quantifiers := ["iemand/someone", "alle/every"] }

def dutch_100b : DutchScopeExample :=
  { surface := "(omdat) iemand probeert alle liederen te zingen"
  , translation := "because someone tries to sing every song"
  , wordOrder := .verbProjectionRaising
  , observed := .surfaceOnly
  , quantifiers := ["iemand/someone", "alle/every"] }

-- Collected Data

def allDutchExamples : List DutchScopeExample :=
  [dutch_99a, dutch_99b, dutch_100a, dutch_100b]

def allWestFlemishExamples : List WestFlemishScopeExample :=
  [westFlemish_98a, westFlemish_98b]

def allGermanExamples : List GermanScopeExample :=
  [german_96, german_97]

/-- Word order correctly predicts scope availability -/
theorem wordOrder_predicts_dutch_99a :
    wordOrderToAvailability dutch_99a.wordOrder = dutch_99a.observed := rfl

theorem wordOrder_predicts_dutch_99b :
    wordOrderToAvailability dutch_99b.wordOrder = dutch_99b.observed := rfl

theorem wordOrder_predicts_dutch_100a :
    wordOrderToAvailability dutch_100a.wordOrder = dutch_100a.observed := rfl

theorem wordOrder_predicts_dutch_100b :
    wordOrderToAvailability dutch_100b.wordOrder = dutch_100b.observed := rfl

theorem wordOrder_predicts_german_96 :
    wordOrderToAvailability german_96.wordOrder = german_96.observed := rfl

theorem wordOrder_predicts_german_97 :
    wordOrderToAvailability german_97.wordOrder = german_97.observed := rfl

end ScopeWordOrder


-- ============================================================================
-- Part II: Minimalist Analysis (was Phenomena/Quantification/MinimalismScope.lean)
-- ============================================================================

section MinimalistAnalysis

open ScopeTheory
open Minimalist.Scope

/-! Connects Minimalist QR / Scope Economy theory to the empirical
scope-freezing data above. The central claim is Bruening's "QR obeys
superiority": double-object freezing falls out of asymmetric c-command
in the @cite{pylkkanen-2008} ditransitive tree. -/

-- Freezing Context Analysis

/-- Analyze why a freezing context blocks inverse scope in Minimalism. -/
def analyzeFreezingContext : FreezingContext → Option QRBarrier
  | .none => none                           -- No barrier
  | .possessor => some .dpPhase             -- Quantifier trapped in possessor DP
  | .doubleObject => some .superiority      -- IO c-commands DO
  | .passive => some .adjunctIsland         -- By-phrase is adjunct
  | .heavyNP => none                        -- Not grammatical (processing)
  | .weakCrossover => none                  -- Blocked by binding, not QR locality
  | .adjunct => some .adjunctIsland
  | .attitude => some .clauseBoundary

/-- Does Minimalism predict freezing for this context? -/
def predictsFreezing (ctx : FreezingContext) : Bool :=
  (analyzeFreezingContext ctx).isSome

-- Scope Availability in Minimalism

/-- Minimalist representation of a scope configuration. -/
structure MinimalistScopeConfig where
  /-- Higher quantifier (typically subject) -/
  q1 : PositionedQuantifier
  /-- Lower quantifier (typically object) -/
  q2 : PositionedQuantifier
  /-- Freezing context if any -/
  freezingContext : FreezingContext := .none
  /-- The tree in which q1 and q2 are positioned. When provided,
      superiority is derived from c-command rather than stipulated. -/
  tree : Option Minimalist.SyntacticObject := none
  deriving Repr

/-- Check if superiority blocks QR in this configuration.

    When a tree and SO positions are provided, superiority is DERIVED
    from asymmetric c-command. Otherwise falls back to the freezing
    context annotation. -/
def superiorityBlocked (config : MinimalistScopeConfig) : Bool :=
  match config.tree, config.q1.so, config.q2.so with
  | some t, some s1, some s2 =>
    -- DERIVED: q1 asymmetrically c-commands q2
    superiorityFromTree t s1 s2
  | _, _, _ =>
    -- FALLBACK: use the freezing context annotation
    config.freezingContext == .doubleObject

/-- Compute available scope readings in Minimalism. -/
def availableReadings (config : MinimalistScopeConfig) : Availability :=
  let q2Barrier := qrIsBlocked config.q2
  let contextBarrier := analyzeFreezingContext config.freezingContext
  let superiorityViolation := superiorityBlocked config
  if q2Barrier.isSome || contextBarrier.isSome || superiorityViolation then
    .surfaceOnly
  else
    .ambiguous

-- Predictions for Phenomena

/-- Build config from a freezing example (fallback path — no tree). -/
def configFromExample (ex : Example) : MinimalistScopeConfig :=
  { q1 := { quantifier := ex.quant1
          , position := .specTP
          , insideDP := ex.context == .possessor }
  , q2 := { quantifier := ex.quant2
          , position := if ex.context == .passive then .adjunct else .specVP }
  , freezingContext := ex.context }

/-- Minimalism's prediction for an example. -/
def predictAvailability (ex : Example) : Availability :=
  availableReadings (configFromExample ex)

/-- Check if Minimalism correctly predicts the example. -/
def correctlyPredicts (ex : Example) : Bool :=
  predictAvailability ex == ex.observed

-- Theoretical Claims as Theorems

/-- Possessor freezing follows from DP being a phase. -/
theorem possessor_freezes_scope :
    predictsFreezing .possessor = true := rfl

/-- Double object freezing follows from superiority. -/
theorem double_object_freezes_scope :
    predictsFreezing .doubleObject = true := rfl

/-- Passive freezing follows from adjunct island. -/
theorem passive_freezes_scope :
    predictsFreezing .passive = true := rfl

/-- Heavy NP is NOT predicted to freeze (it's processing). -/
theorem heavy_np_not_grammatically_frozen :
    predictsFreezing .heavyNP = false := rfl

/-- Baseline (no context) is predicted ambiguous. -/
theorem baseline_is_ambiguous :
    predictsFreezing .none = false := rfl

-- ============================================================================
-- DOC Scope Freezing — superiority derived from c-command
-- ============================================================================

/-! @cite{pylkkanen-2008}'s low-Appl tree (`ditransitiveTree`) produces
the DOC structure where V takes ApplP as complement, so the goal in
Spec-ApplP asymmetrically c-commands the theme in complement of Appl.
QR of the theme over the goal is blocked by superiority, derived
from c-command rather than stipulated. -/

open Pylkkanen2008 in
/-- DOC scope freezing config with @cite{pylkkanen-2008}'s tree:
    superiority is derived from goal asymmetrically c-commanding theme
    in the Voice + low-Appl structure. -/
def docScopeConfig : MinimalistScopeConfig :=
  { q1 := { quantifier := "every worker"
           , position := .specVP
           , so := some DP_mary_t }
  , q2 := { quantifier := "a paycheck"
           , position := .specVP
           , so := some DP_letter_t }
  , freezingContext := .doubleObject
  , tree := some ditransitiveTree }

open Pylkkanen2008 in
/-- Superiority in the DOC is DERIVED from c-command in
@cite{pylkkanen-2008}'s tree: goal (Mary) asymmetrically c-commands
theme (a letter) via low Appl, so QR of theme over goal is blocked. -/
theorem doc_superiority_from_tree :
    superiorityBlocked docScopeConfig = true := by decide

/-! ## Summary

| Context | Minimalist Explanation |
|---------|----------------------|
| Possessor | DP phase blocks QR |
| Double object | Superiority: goal c-commands theme (@cite{pylkkanen-2008} tree) |
| Passive | Adjunct island |
| Heavy NP | NOT grammatical (processing) |
| Attitude | Clause boundary |
-/

end MinimalistAnalysis

end Phenomena.Quantification.Bruening2001
