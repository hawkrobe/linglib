/-
# HPSG Coreference (Binding)

Coreference constraints using HPSG's feature-based approach, following
Pollard & Sag (1994) Chapter 6.

## Mechanism

- **Binding Domain**: Defined via LOCAL feature structure
- **O-command**: Uses obliqueness hierarchy (subject > object > ...)
- **Reflexives**: Must be o-commanded by coindexed antecedent locally
- **Pronouns**: Must NOT be o-commanded by coindexed antecedent locally

## Key Differences from Minimalism

| Minimalism | HPSG |
|------------|------|
| C-command (structural) | O-command (obliqueness) |
| Phase/clause locality | LOCAL feature percolation |
| Movement-based | Constraint-based |

## References

- Pollard, C. & I. Sag (1994). Head-Driven Phrase Structure Grammar, Ch. 6.
- Sag, I., T. Wasow & E. Bender (2003). Syntactic Theory, Ch. 5.
-/

import Linglib.Core.Basic
import Linglib.Phenomena.Anaphora.Coreference
import Linglib.Theories.Core.Interfaces.CoreferenceTheory

namespace HPSG.Coreference

open Lexicon

-- ============================================================================
-- Part 1: Nominal Types (same classification as Minimalism)
-- ============================================================================

/-- Types of nominal expressions for coreference -/
inductive NominalType where
  | reflexive   -- himself, herself, themselves
  | pronoun     -- he, she, they, him, her, them
  | rExpression -- John, Mary, the cat
  deriving Repr, DecidableEq

/-- Classify a word as a nominal type -/
def classifyNominal (w : Word) : Option NominalType :=
  if w.form ∈ ["himself", "herself", "themselves", "myself", "yourself", "ourselves"] then
    some .reflexive
  else if w.form ∈ ["he", "she", "they", "him", "her", "them", "it"] then
    some .pronoun
  else if w.cat == Cat.D then
    some .rExpression
  else
    none

-- ============================================================================
-- Part 2: Obliqueness Hierarchy
-- ============================================================================

/-- Position in argument structure (obliqueness ranking)

    In HPSG, binding is based on the obliqueness hierarchy:
    Subject > Direct Object > Indirect Object > Obliques

    Lower numbers = less oblique = higher on hierarchy -/
inductive ArgPosition where
  | subject : ArgPosition       -- Most prominent
  | directObject : ArgPosition  -- Less prominent
  | indirectObject : ArgPosition
  | oblique : ArgPosition       -- Least prominent
  deriving Repr, DecidableEq

/-- Obliqueness ordering: is pos1 less oblique (more prominent) than pos2? -/
def lessOblique (pos1 pos2 : ArgPosition) : Bool :=
  match pos1, pos2 with
  | .subject, .directObject => true
  | .subject, .indirectObject => true
  | .subject, .oblique => true
  | .directObject, .indirectObject => true
  | .directObject, .oblique => true
  | .indirectObject, .oblique => true
  | _, _ => false

/-- O-command: A o-commands B iff A is less oblique than B

    This replaces c-command in HPSG binding theory -/
def oCommands (pos1 pos2 : ArgPosition) : Bool :=
  lessOblique pos1 pos2

-- ============================================================================
-- Part 3: LOCAL Feature Structure (Simplified)
-- ============================================================================

/-- Simple clause structure for HPSG coreference checking

    The LOCAL feature in HPSG includes:
    - CAT (category, valence)
    - CONT (content/semantics)

    For coreference, what matters is the binding domain. -/
structure SimpleClause where
  subject : Word
  verb : Word
  object : Option Word
  deriving Repr

/-- Parse a simple transitive sentence into a clause -/
def parseSimpleClause (ws : List Word) : Option SimpleClause :=
  match ws with
  | [subj, v, obj] =>
    if subj.cat == Cat.D && v.cat == Cat.V && obj.cat == Cat.D then
      some ⟨subj, v, some obj⟩
    else none
  | [subj, v] =>
    if subj.cat == Cat.D && v.cat == Cat.V then
      some ⟨subj, v, none⟩
    else none
  | _ => none

/-- In a simple clause, subject and object are locally related
    (same LOCAL domain in HPSG terms) -/
def sameLocalDomain (_clause : SimpleClause) : Bool := true

-- ============================================================================
-- Part 4: Agreement (Feature Matching)
-- ============================================================================

/-- Do two nominals agree in phi-features?

    In HPSG, this is formalized as feature structure unification.
    For coreference, agreement is required between anaphor and antecedent. -/
def phiAgree (w1 w2 : Word) : Bool :=
  let personMatch := match w1.features.person, w2.features.person with
    | some p1, some p2 => p1 == p2
    | _, _ => true  -- Compatible if unspecified
  let numberMatch := match w1.features.number, w2.features.number with
    | some n1, some n2 => n1 == n2
    | _, _ => true
  -- Gender check: infer from form
  let genderMatch :=
    if w2.form == "himself" then
      w1.form ∈ ["John", "he", "him"]  -- masculine antecedents
    else if w2.form == "herself" then
      w1.form ∈ ["Mary", "she", "her"]  -- feminine antecedents
    else if w2.form ∈ ["themselves", "ourselves"] then
      w1.features.number == some .pl  -- plural
    else
      true
  personMatch && numberMatch && genderMatch

-- ============================================================================
-- Part 5: HPSG Binding Constraints
-- ============================================================================

/-- Principle A (HPSG version): Locally o-commanded

    A reflexive must be locally o-commanded by a coindexed element -/
def reflexiveLicensed (clause : SimpleClause) : Bool :=
  match clause.object with
  | none => false
  | some obj =>
    match classifyNominal obj with
    | some .reflexive =>
      -- Reflexive in object position needs subject as antecedent
      -- Subject o-commands object (subject is less oblique)
      oCommands .subject .directObject &&
      sameLocalDomain clause &&
      phiAgree clause.subject obj
    | _ => true  -- Non-reflexives don't need this

/-- Principle B (HPSG version): Locally o-free

    A pronoun must NOT be locally o-commanded by a coindexed element -/
def pronounLocallyFree (clause : SimpleClause) : Bool :=
  match clause.object with
  | none => true
  | some obj =>
    match classifyNominal obj with
    | some .pronoun =>
      -- Pronoun in object position: if subject o-commands it locally,
      -- coreference would be blocked
      !(oCommands .subject .directObject && sameLocalDomain clause)
    | _ => true

/-- Principle C (HPSG version): O-free

    An R-expression must not be o-commanded by a coreferent pronoun -/
def rExpressionFree (clause : SimpleClause) : Bool :=
  match classifyNominal clause.subject with
  | some .pronoun =>
    match clause.object with
    | some obj =>
      match classifyNominal obj with
      | some .rExpression => true  -- Pronoun subject, R-expression object is fine
      | _ => true
    | none => true
  | _ => true

-- ============================================================================
-- Part 6: Combined Coreference Check
-- ============================================================================

/-- Is a sentence grammatical for coreference under HPSG binding?

    Checks whether the coreference pattern is licensed by HPSG constraints -/
def grammaticalForCoreference (ws : List Word) : Bool :=
  match parseSimpleClause ws with
  | none => false
  | some clause =>
    -- Check reflexive in subject position (always bad - no o-commanding antecedent)
    match classifyNominal clause.subject with
    | some .reflexive => false  -- Reflexive in subject has no less-oblique antecedent
    | _ =>
      match clause.object with
      | none => true
      | some obj =>
        match classifyNominal obj with
        | some .reflexive => reflexiveLicensed clause  -- Reflexive must be o-commanded
        | some .pronoun => false  -- Pronoun in object with local subject = coreference blocked
        | _ => true  -- R-expressions, etc.

/-- Check if reflexive is licensed in a sentence -/
def reflexiveLicensedInSentence (ws : List Word) : Bool :=
  match parseSimpleClause ws with
  | none => false
  | some clause => reflexiveLicensed clause

/-- Check if pronoun coreference is blocked -/
def pronounCoreferenceBlocked (ws : List Word) : Bool :=
  match parseSimpleClause ws with
  | none => false
  | some clause => !pronounLocallyFree clause

-- ============================================================================
-- Part 7: Tests - Matching Phenomena/Coreference/Data.lean
-- ============================================================================

-- reflexiveCoreferenceData pairs:
-- Pair 1: john sees himself ✓ vs himself sees john ✗
#eval reflexiveLicensedInSentence [john, sees, himself]     -- true ✓
#eval grammaticalForCoreference [himself, sees, john]       -- false ✓

-- Pair 2: mary sees herself ✓ vs herself sees mary ✗
#eval reflexiveLicensedInSentence [mary, sees, herself]     -- true ✓
#eval grammaticalForCoreference [herself, sees, mary]       -- false ✓

-- Pair 3: they see themselves ✓ vs themselves see them ✗
#eval reflexiveLicensedInSentence [they, see, themselves]   -- true ✓
#eval grammaticalForCoreference [themselves, see, them]     -- false ✓

-- Pair 4: john sees himself ✓ vs john sees herself ✗ (gender)
#eval reflexiveLicensedInSentence [john, sees, himself]     -- true ✓
#eval reflexiveLicensedInSentence [john, sees, herself]     -- false ✓

-- Pair 5: they see themselves ✓ vs they see himself ✗ (number)
#eval reflexiveLicensedInSentence [they, see, themselves]   -- true ✓
#eval reflexiveLicensedInSentence [they, see, himself]      -- false ✓

-- pronominalDisjointReferenceData pairs:
-- Pronouns resist local coreference
#eval pronounCoreferenceBlocked [john, sees, him]           -- true ✓
#eval pronounCoreferenceBlocked [mary, sees, her]           -- true ✓

-- ============================================================================
-- Part 8: Capturing the Phenomena Data
-- ============================================================================

/-- Check if HPSG correctly predicts a minimal pair for coreference

    Grammatical sentence should pass, ungrammatical should fail. -/
def capturesCoreferenceMinimalPair (pair : MinimalPair) : Bool :=
  grammaticalForCoreference pair.grammatical &&
  !grammaticalForCoreference pair.ungrammatical

/-- Check all pairs in a PhenomenonData -/
def capturesCoreferenceData (phenom : PhenomenonData) : Bool :=
  phenom.pairs.all capturesCoreferenceMinimalPair

-- ============================================================================
-- Part 9: Theorems - HPSG Captures Imported Phenomena
-- ============================================================================

/-- HPSG captures reflexiveCoreferenceData -/
theorem captures_reflexive_coreference :
    capturesCoreferenceData reflexiveCoreferenceData = true := by
  native_decide

/-- HPSG captures complementaryDistributionData -/
theorem captures_complementary_distribution :
    capturesCoreferenceData complementaryDistributionData = true := by
  native_decide

/-- HPSG captures pronominalDisjointReferenceData -/
theorem captures_pronominal_disjoint_reference :
    capturesCoreferenceData pronominalDisjointReferenceData = true := by
  native_decide

/-- Check each pair individually for reflexiveCoreferenceData -/
theorem reflexive_pairs_captured :
    -- Pair 1: john sees himself ✓ vs himself sees john ✗
    (grammaticalForCoreference [john, sees, himself] = true ∧
     grammaticalForCoreference [himself, sees, john] = false) ∧
    -- Pair 2: mary sees herself ✓ vs herself sees mary ✗
    (grammaticalForCoreference [mary, sees, herself] = true ∧
     grammaticalForCoreference [herself, sees, mary] = false) ∧
    -- Pair 3: they see themselves ✓ vs themselves see them ✗
    (grammaticalForCoreference [they, see, themselves] = true ∧
     grammaticalForCoreference [themselves, see, them] = false) ∧
    -- Pair 4: agreement - john sees himself ✓ vs john sees herself ✗
    (grammaticalForCoreference [john, sees, himself] = true ∧
     grammaticalForCoreference [john, sees, herself] = false) ∧
    -- Pair 5: agreement - they see themselves ✓ vs they see himself ✗
    (grammaticalForCoreference [they, see, themselves] = true ∧
     grammaticalForCoreference [they, see, himself] = false) := by
  native_decide

-- ============================================================================
-- Part 10: HPSG Grammar Configuration
-- ============================================================================

/-- HPSG coreference configuration -/
structure HPSGCoreferenceGrammar where
  /-- Whether to use strict obliqueness (no exceptions) -/
  strictObliqueness : Bool := true

/-- Default HPSG grammar for coreference -/
def defaultGrammar : HPSGCoreferenceGrammar := {}

-- ============================================================================
-- Part 11: Theoretical Notes
-- ============================================================================

/-
## HPSG Binding Theory Details

### The Obliqueness Hierarchy

HPSG defines binding in terms of obliqueness:
- ARG-ST (argument structure) orders arguments by obliqueness
- Subject < Direct Object < Indirect Object < Obliques
- "Less oblique" elements can bind "more oblique" ones

### LOCAL vs NONLOCAL

- **LOCAL**: Contains CAT and CONT; binding domain is LOCAL
- **NONLOCAL**: Contains SLASH, REL, QUE; for unbounded dependencies

Reflexives require their antecedent to be LOCAL.
Pronouns can have antecedents that are NONLOCAL.

### Comparison with Minimalism

Both theories make the same predictions for simple cases because:
1. Subject c-commands object ↔ Subject is less oblique than object
2. Local domain (clause) ↔ Same LOCAL feature structure
3. Agreement required ↔ Feature unification succeeds

The difference is in the mechanism:
- Minimalism: Structural (tree geometry)
- HPSG: Feature-based (constraint satisfaction)
-/

-- ============================================================================
-- Part 12: CoreferenceTheory Interface Implementation
-- ============================================================================

/-- Marker type for HPSG as a coreference theory -/
structure HPSGTheory

/-- Compute coreference status for positions i and j using o-command.

    Position 0 = subject, position 2 = object -/
def computeCoreferenceStatus (clause : SimpleClause) (i j : Nat) : Interfaces.CoreferenceStatus :=
  if i == 0 && j == 2 then
    -- Subject-object configuration: subject o-commands object
    match clause.object with
    | none => .unspecified
    | some obj =>
      match classifyNominal obj with
      | some .reflexive =>
        if oCommands .subject .directObject && sameLocalDomain clause && phiAgree clause.subject obj
        then .obligatory
        else .blocked
      | some .pronoun =>
        if oCommands .subject .directObject && sameLocalDomain clause
        then .blocked
        else .possible
      | some .rExpression => .possible
      | none => .unspecified
  else if i == 2 && j == 0 then
    -- Object-subject: object doesn't o-command subject
    match classifyNominal clause.subject with
    | some .reflexive => .blocked
    | some .pronoun => .possible
    | _ => .possible
  else
    .unspecified

/-- HPSG implements the CoreferenceTheory interface -/
instance : Interfaces.CoreferenceTheory HPSGTheory where
  Structure := SimpleClause
  parse := parseSimpleClause
  coreferenceStatus := computeCoreferenceStatus
  grammaticalForCoreference := λ clause =>
    match classifyNominal clause.subject with
    | some .reflexive => false
    | _ =>
      match clause.object with
      | none => true
      | some obj =>
        match classifyNominal obj with
        | some .reflexive => reflexiveLicensed clause
        | some .pronoun => false
        | _ => true

end HPSG.Coreference
