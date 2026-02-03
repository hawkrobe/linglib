/-
# CoreferenceTheory: Abstract Interface for Coreference Predictions

This typeclass defines what it means for a theory to make predictions about
coreference. The interface is **theory-neutral**: it doesn't assume binding
theory, o-command, dependency paths, or any particular mechanism.

## Design Principle

Different theories use different mechanisms:
- Minimalism: C-command + phases (Binding Principles A/B/C)
- HPSG: O-command + LOCAL features (obliqueness hierarchy)
- Dependency Grammar: Dependency paths + graph reachability
- Construction Grammar: Coindexation slots in constructions
- Cognitive Grammar: Reference point relationships

But they all make **predictions** about when two expressions can/must/cannot
corefer. This interface captures that common ground.

## Usage

Each theory implements this interface in its own terms. Then comparison
theorems can prove when different theories make the same predictions.

```
Theories/Minimalism/Coreference.lean
  instance : CoreferenceTheory MinimalismTheory where ...

Theories/HPSG/Coreference.lean
  instance : CoreferenceTheory HPSGTheory where ...

Comparisons/CoreferenceComparison.lean
  theorem minimalism_hpsg_agree : ...
```

## References

- Chomsky (1981). Lectures on Government and Binding.
- Pollard & Sag (1994). Head-Driven Phrase Structure Grammar.
- Hudson (1990). English Word Grammar.
-/

import Linglib.Core.Basic
import Linglib.Phenomena.Anaphora.Coreference

namespace Interfaces

-- ============================================================================
-- Part 1: Coreference Status
-- ============================================================================

/-- The possible coreference relationships between two positions -/
inductive CoreferenceStatus where
  /-- Coreference is obligatory (reflexives with local antecedent) -/
  | obligatory
  /-- Coreference is possible but not required -/
  | possible
  /-- Coreference is blocked (Principle B/C violations) -/
  | blocked
  /-- No prediction (positions not in relevant configuration) -/
  | unspecified
  deriving Repr, DecidableEq

-- ============================================================================
-- Part 2: The Core Interface
-- ============================================================================

/-- A theory that makes predictions about coreference patterns.

    This is the **theory-neutral interface** that all frameworks implement.
    The interface says nothing about mechanism (c-command, o-command, etc.),
    only about observable predictions.

    Type parameter `T` is a marker type for the theory (e.g., `MinimalismTheory`). -/
class CoreferenceTheory (T : Type) where
  /-- The theory's internal representation of a sentence/structure -/
  Structure : Type

  /-- Parse a list of words into the theory's representation.
      Returns `none` if the theory can't parse this input. -/
  parse : List Word → Option Structure

  /-- Predict the coreference status between positions i and j.

      Positions are indexed from the word list:
      - "John sees himself" → position 0 = John, position 2 = himself

      Returns the theory's prediction about whether these positions
      can/must/cannot corefer. -/
  coreferenceStatus : Structure → Nat → Nat → CoreferenceStatus

  /-- Does the theory predict this sentence is grammatical for coreference?

      A sentence is "grammatical for coreference" if:
      - All obligatory coreferences have valid antecedents
      - No blocked coreferences are forced

      This is the primary prediction we test against empirical data. -/
  grammaticalForCoreference : Structure → Bool

-- ============================================================================
-- Part 3: Derived Operations
-- ============================================================================

variable {T : Type} [CoreferenceTheory T]

/-- Check if coreference is possible at positions i, j -/
def canCorefer (s : CoreferenceTheory.Structure T) (i j : Nat) : Bool :=
  match CoreferenceTheory.coreferenceStatus s i j with
  | .obligatory => true
  | .possible => true
  | .blocked => false
  | .unspecified => true  -- No constraint means possible

/-- Check if coreference is obligatory at positions i, j -/
def mustCorefer (s : CoreferenceTheory.Structure T) (i j : Nat) : Bool :=
  match CoreferenceTheory.coreferenceStatus s i j with
  | .obligatory => true
  | _ => false

/-- Check if coreference is blocked at positions i, j -/
def cannotCorefer (s : CoreferenceTheory.Structure T) (i j : Nat) : Bool :=
  match CoreferenceTheory.coreferenceStatus s i j with
  | .blocked => true
  | _ => false

-- ============================================================================
-- Part 4: Testing Against Empirical Data
-- ============================================================================

/-- Does the theory correctly predict a minimal pair?

    A theory "captures" a minimal pair if:
    - It predicts the grammatical sentence is grammatical
    - It predicts the ungrammatical sentence is ungrammatical -/
def capturesMinimalPair (pair : MinimalPair) : Bool :=
  match CoreferenceTheory.parse (T := T) pair.grammatical,
        CoreferenceTheory.parse (T := T) pair.ungrammatical with
  | some sg, some su =>
    CoreferenceTheory.grammaticalForCoreference sg &&
    !CoreferenceTheory.grammaticalForCoreference su
  | _, _ => false  -- Can't parse → doesn't capture

/-- Does the theory capture all pairs in a phenomenon dataset? -/
def capturesPhenomenon (data : PhenomenonData) : Bool :=
  data.pairs.all (capturesMinimalPair (T := T))

-- ============================================================================
-- Part 5: Theory Comparison
-- ============================================================================

variable {T1 T2 : Type} [CoreferenceTheory T1] [CoreferenceTheory T2]

/-- Two theories agree on a sentence if they make the same grammaticality prediction -/
def theoriesAgreeOn (ws : List Word) : Bool :=
  match CoreferenceTheory.parse (T := T1) ws,
        CoreferenceTheory.parse (T := T2) ws with
  | some s1, some s2 =>
    CoreferenceTheory.grammaticalForCoreference s1 ==
    CoreferenceTheory.grammaticalForCoreference s2
  | none, none => true   -- Both can't parse → vacuous agreement
  | _, _ => false        -- One parses, other doesn't → disagreement

/-- Two theories agree on all sentences in a list -/
def theoriesAgreeOnAll (sentences : List (List Word)) : Bool :=
  sentences.all (theoriesAgreeOn (T1 := T1) (T2 := T2))

/-- Two theories agree on a phenomenon dataset -/
def theoriesAgreeOnPhenomenon (data : PhenomenonData) : Bool :=
  data.pairs.all (λ pair =>
    theoriesAgreeOn (T1 := T1) (T2 := T2) pair.grammatical &&
    theoriesAgreeOn (T1 := T1) (T2 := T2) pair.ungrammatical)

-- ============================================================================
-- Part 6: Extensional Equivalence
-- ============================================================================

/-- Two theories are extensionally equivalent on a class of sentences if they
    always make the same predictions.

    This is the key notion for comparing frameworks: do they differ in
    observable predictions, or only in internal machinery? -/
def ExtensionallyEquivalentOn (sentences : List (List Word)) : Prop :=
  ∀ ws ∈ sentences, theoriesAgreeOn (T1 := T1) (T2 := T2) ws = true

-- ============================================================================
-- Part 7: Documentation
-- ============================================================================

/-
## How to Implement This Interface

Each theory provides an instance by defining:

1. `Structure`: The theory's internal representation
   - Minimalism: Syntactic tree with c-command relations
   - HPSG: Feature structure with LOCAL/NONLOCAL
   - DepGrammar: Dependency graph

2. `parse`: How to build the structure from words
   - Can be partial (return `none` for unparseable inputs)

3. `coreferenceStatus`: The theory's prediction for each position pair
   - This is where the theory's mechanism (c-command, etc.) gets applied

4. `grammaticalForCoreference`: Overall grammaticality judgment
   - Usually derived from checking all relevant position pairs

## Example: Minimalism

```
structure MinimalismTheory

instance : CoreferenceTheory MinimalismTheory where
  Structure := MinimalistTree
  parse := parseToMinimalistTree
  coreferenceStatus := λ tree i j =>
    let nodeI := tree.nodeAt i
    let nodeJ := tree.nodeAt j
    if isReflexive nodeJ then
      if cCommands nodeI nodeJ && isLocal nodeI nodeJ && agrees nodeI nodeJ
      then .obligatory
      else .blocked
    else if isPronoun nodeJ then
      if cCommands nodeI nodeJ && isLocal nodeI nodeJ
      then .blocked
      else .possible
    else .unspecified
  grammaticalForCoreference := ...
```

## What This Enables

1. **Automatic comparison**: Once theories implement the interface,
   we can test if they agree on any dataset.

2. **Contradiction detection**: If Theory A predicts grammatical and
   Theory B predicts ungrammatical, we've found a divergence point.

3. **Coverage tracking**: Which theories handle which phenomena?

4. **Empirical adjudication**: When theories diverge, empirical data
   can decide which prediction is correct.
-/

end Interfaces
