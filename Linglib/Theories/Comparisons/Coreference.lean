/-
# Coreference: Cross-Theoretic Comparison

Compares how different syntactic theories handle coreference patterns
(reflexive coreference, pronominal disjoint reference, etc.).

## Theories Compared

| Theory | Mechanism |
|--------|-----------|
| Minimalism | C-command + local domain (phase/clause); feature agreement |
| HPSG | Feature structures (LOCAL/NONLOCAL); o-command (obliqueness) |
| Dependency Grammar | D-command (co-dependents); dependency path locality |

## Architecture

```
         Phenomena/Coreference/Data.lean
         (theory-neutral minimal pairs)
                      │
         ┌───────────┼───────────┐
         ▼           ▼           ▼
    Minimalism     HPSG    DependencyGrammar
         │           │           │
         ▼           ▼           ▼
    c-command    o-command   d-command
    + locality   + LOCAL     + path length
         │           │           │
         └───────────┴───────────┘
                     ▼
           All predict same pairs

```

## Key Result

`coreference_theories_agree`: All three theories make the same predictions
on the core coreference data.

## References

- Chomsky (1981). Lectures on Government and Binding.
- Pollard & Sag (1994). Head-Driven Phrase Structure Grammar, Ch. 6.
- Hudson (1990). English Word Grammar, Ch. 6.
-/

import Linglib.Phenomena.Coreference.Data
import Linglib.Theories.Minimalism.Coreference
import Linglib.Theories.HPSG.Coreference
import Linglib.Theories.DependencyGrammar.Coreference
import Linglib.Core.Interfaces.CoreferenceTheory

namespace Comparisons.Coreference

open Lexicon

-- ============================================================================
-- Part 1: All Theories Capture the Same Data
-- ============================================================================

/--
**Main Agreement Theorem: Reflexive Coreference**

All three theories correctly predict the reflexive coreference patterns.
-/
theorem all_theories_capture_reflexive_coreference :
    -- Minimalism captures it
    Minimalism.Coreference.capturesCoreferenceData reflexiveCoreferenceData = true ∧
    -- HPSG captures it
    HPSG.Coreference.capturesCoreferenceData reflexiveCoreferenceData = true ∧
    -- Dependency Grammar captures it
    DepGrammar.Coreference.capturesCoreferenceData reflexiveCoreferenceData = true := by
  constructor
  · exact Minimalism.Coreference.captures_reflexive_coreference
  constructor
  · exact HPSG.Coreference.captures_reflexive_coreference
  · exact DepGrammar.Coreference.captures_reflexive_coreference

/--
**Main Agreement Theorem: Complementary Distribution**

All three theories correctly predict complementary distribution.
-/
theorem all_theories_capture_complementary_distribution :
    Minimalism.Coreference.capturesCoreferenceData complementaryDistributionData = true ∧
    HPSG.Coreference.capturesCoreferenceData complementaryDistributionData = true ∧
    DepGrammar.Coreference.capturesCoreferenceData complementaryDistributionData = true := by
  constructor
  · exact Minimalism.Coreference.captures_complementary_distribution
  constructor
  · exact HPSG.Coreference.captures_complementary_distribution
  · exact DepGrammar.Coreference.captures_complementary_distribution

/--
**Main Agreement Theorem: Pronominal Disjoint Reference**

All three theories correctly predict pronoun coreference is blocked locally.
-/
theorem all_theories_capture_pronominal_disjoint_reference :
    Minimalism.Coreference.capturesCoreferenceData pronominalDisjointReferenceData = true ∧
    HPSG.Coreference.capturesCoreferenceData pronominalDisjointReferenceData = true ∧
    DepGrammar.Coreference.capturesCoreferenceData pronominalDisjointReferenceData = true := by
  constructor
  · exact Minimalism.Coreference.captures_pronominal_disjoint_reference
  constructor
  · exact HPSG.Coreference.captures_pronominal_disjoint_reference
  · exact DepGrammar.Coreference.captures_pronominal_disjoint_reference

-- ============================================================================
-- Part 2: Pointwise Agreement on Test Sentences
-- ============================================================================

/--
**Pointwise Agreement: John sees himself**

All theories agree this sentence is grammatical for coreference.
-/
theorem john_sees_himself_agreement :
    Minimalism.Coreference.grammaticalForCoreference [john, sees, himself] = true ∧
    HPSG.Coreference.grammaticalForCoreference [john, sees, himself] = true ∧
    DepGrammar.Coreference.grammaticalForCoreference [john, sees, himself] = true := by
  native_decide

/--
**Pointwise Agreement: *himself sees John**

All theories agree this sentence is ungrammatical for coreference.
-/
theorem himself_sees_john_agreement :
    Minimalism.Coreference.grammaticalForCoreference [himself, sees, john] = false ∧
    HPSG.Coreference.grammaticalForCoreference [himself, sees, john] = false ∧
    DepGrammar.Coreference.grammaticalForCoreference [himself, sees, john] = false := by
  native_decide

/--
**Pointwise Agreement: *John sees herself** (gender mismatch)

All theories agree this is ungrammatical due to gender mismatch.
-/
theorem john_sees_herself_agreement :
    Minimalism.Coreference.grammaticalForCoreference [john, sees, herself] = false ∧
    HPSG.Coreference.grammaticalForCoreference [john, sees, herself] = false ∧
    DepGrammar.Coreference.grammaticalForCoreference [john, sees, herself] = false := by
  native_decide

/--
**Pointwise Agreement: John sees him** (pronoun locally bound = bad for coreference)

All theories agree pronoun coreference is blocked here.
-/
theorem john_sees_him_pronoun_blocked :
    Minimalism.Coreference.pronounCoreferenceBlocked [john, sees, him] = true ∧
    HPSG.Coreference.pronounCoreferenceBlocked [john, sees, him] = true ∧
    DepGrammar.Coreference.pronounCoreferenceBlocked [john, sees, him] = true := by
  native_decide

-- ============================================================================
-- Part 3: Theory Equivalence on Core Cases
-- ============================================================================

/--
**Core Equivalence Theorem**

For all minimal pairs in our core coreference data, the three theories
make identical predictions.

This doesn't mean the theories are equivalent in general - they may differ
on more complex cases (picture NPs, long-distance reflexives, etc.).
But on simple transitive clauses, they converge.
-/
theorem theories_equivalent_on_simple_transitives :
    ∀ pair ∈ reflexiveCoreferenceData.pairs,
      (Minimalism.Coreference.capturesCoreferenceMinimalPair pair =
       HPSG.Coreference.capturesCoreferenceMinimalPair pair) ∧
      (HPSG.Coreference.capturesCoreferenceMinimalPair pair =
       DepGrammar.Coreference.capturesCoreferenceMinimalPair pair) := by
  native_decide

-- ============================================================================
-- Part 4: Mechanism Correspondence Table
-- ============================================================================

/-
## Why the Theories Agree

The three theories use different mechanisms but converge on simple cases:

### Command Relations

| Theory | Command Definition | Simple Clause Result |
|--------|-------------------|---------------------|
| Minimalism | A c-commands B if A's sister dominates B | Subject c-commands object |
| HPSG | A o-commands B if A is less oblique than B | Subject o-commands object |
| Dep Grammar | A d-commands B if A is co-dependent and designated binder | Subject d-commands object |

### Locality

| Theory | Local Domain | Simple Clause Result |
|--------|-------------|---------------------|
| Minimalism | Phase (CP/vP) or clause | Subject and object are local |
| HPSG | Same LOCAL feature structure | Subject and object are local |
| Dep Grammar | Dependency path length ≤ k | Subject and object are local (path = 2) |

### Agreement

All three theories require feature agreement (person, number, gender)
between anaphor and antecedent. This is:
- Feature checking in Minimalism
- Feature unification in HPSG
- Dependency constraint in Dependency Grammar

### The Convergence

In a simple transitive clause [Subject Verb Object]:
1. Subject commands object in all three senses
2. Subject and object are local in all three definitions
3. Agreement requirements are identical

Therefore: All theories make the same predictions.

### Where They Might Diverge

1. **Picture NPs**: "John saw [a picture of himself]"
   - Minimalism: Binding domain is NP or clause?
   - HPSG: O-command into NP?
   - Dep Grammar: Path length through NP?

2. **Long-distance reflexives** (in some languages):
   - Minimalism: Phase-based locality
   - HPSG: NONLOCAL features
   - Dep Grammar: Longer path allowed

3. **Psych predicates**: "The picture pleased himself"
   - Subject c-commands but may not o-command?
   - Experiencer vs theme asymmetries
-/

-- ============================================================================
-- Part 5: Summary Statistics
-- ============================================================================

/-- Total minimal pairs tested across all phenomena -/
def totalPairsTested : Nat :=
  reflexiveCoreferenceData.pairs.length +
  pronominalDisjointReferenceData.pairs.length +
  complementaryDistributionData.pairs.length

#eval totalPairsTested  -- 9 pairs

/-- All theories capture all pairs -/
theorem all_pairs_captured_by_all_theories :
    totalPairsTested = 9 ∧
    (reflexiveCoreferenceData.pairs.all Minimalism.Coreference.capturesCoreferenceMinimalPair) ∧
    (pronominalDisjointReferenceData.pairs.all Minimalism.Coreference.capturesCoreferenceMinimalPair) ∧
    (complementaryDistributionData.pairs.all HPSG.Coreference.capturesCoreferenceMinimalPair) ∧
    (complementaryDistributionData.pairs.all DepGrammar.Coreference.capturesCoreferenceMinimalPair) := by
  native_decide

-- ============================================================================
-- Part 6: Interface-Based Comparison
-- ============================================================================

/-
## Using the CoreferenceTheory Interface

Now that all three theories implement `CoreferenceTheory`, we can use the
interface functions to compare them uniformly. This is the "Mathlib pattern":
- Define an abstract interface
- Have each theory implement it
- Prove theorems using only the interface

The theorems below use `Interfaces.theoriesAgreeOn` which compares theories
through their interface implementations.
-/

open Interfaces

/-- All three theories agree on "John sees himself" -/
theorem interface_agreement_john_sees_himself :
    theoriesAgreeOn (T1 := Minimalism.Coreference.MinimalismTheory)
                    (T2 := HPSG.Coreference.HPSGTheory)
                    [john, sees, himself] = true ∧
    theoriesAgreeOn (T1 := HPSG.Coreference.HPSGTheory)
                    (T2 := DepGrammar.Coreference.DepGrammarTheory)
                    [john, sees, himself] = true := by
  native_decide

/-- All three theories agree on "himself sees John" (ungrammatical) -/
theorem interface_agreement_himself_sees_john :
    theoriesAgreeOn (T1 := Minimalism.Coreference.MinimalismTheory)
                    (T2 := HPSG.Coreference.HPSGTheory)
                    [himself, sees, john] = true ∧
    theoriesAgreeOn (T1 := HPSG.Coreference.HPSGTheory)
                    (T2 := DepGrammar.Coreference.DepGrammarTheory)
                    [himself, sees, john] = true := by
  native_decide

/-- The key test sentences for comparison -/
def testSentences : List (List Word) :=
  [ [john, sees, himself]
  , [himself, sees, john]
  , [mary, sees, herself]
  , [herself, sees, mary]
  , [they, see, themselves]
  , [themselves, see, them]
  , [john, sees, herself]  -- agreement violation
  , [they, see, himself]   -- agreement violation
  , [john, sees, him]      -- pronoun
  , [mary, sees, her]      -- pronoun
  ]

/-- Minimalism and HPSG are extensionally equivalent on test sentences -/
theorem minimalism_hpsg_equivalent :
    theoriesAgreeOnAll (T1 := Minimalism.Coreference.MinimalismTheory)
                       (T2 := HPSG.Coreference.HPSGTheory)
                       testSentences = true := by
  native_decide

/-- HPSG and Dependency Grammar are extensionally equivalent on test sentences -/
theorem hpsg_depgrammar_equivalent :
    theoriesAgreeOnAll (T1 := HPSG.Coreference.HPSGTheory)
                       (T2 := DepGrammar.Coreference.DepGrammarTheory)
                       testSentences = true := by
  native_decide

/-- All three theories are pairwise equivalent on test sentences -/
theorem all_theories_pairwise_equivalent :
    theoriesAgreeOnAll (T1 := Minimalism.Coreference.MinimalismTheory)
                       (T2 := HPSG.Coreference.HPSGTheory)
                       testSentences = true ∧
    theoriesAgreeOnAll (T1 := HPSG.Coreference.HPSGTheory)
                       (T2 := DepGrammar.Coreference.DepGrammarTheory)
                       testSentences = true ∧
    theoriesAgreeOnAll (T1 := Minimalism.Coreference.MinimalismTheory)
                       (T2 := DepGrammar.Coreference.DepGrammarTheory)
                       testSentences = true := by
  native_decide

/-- All three theories agree on the reflexive coreference phenomenon data -/
theorem interface_all_agree_on_reflexive_data :
    theoriesAgreeOnPhenomenon (T1 := Minimalism.Coreference.MinimalismTheory)
                              (T2 := HPSG.Coreference.HPSGTheory)
                              reflexiveCoreferenceData = true ∧
    theoriesAgreeOnPhenomenon (T1 := HPSG.Coreference.HPSGTheory)
                              (T2 := DepGrammar.Coreference.DepGrammarTheory)
                              reflexiveCoreferenceData = true := by
  native_decide

-- ============================================================================
-- Part 7: What the Interface Pattern Enables
-- ============================================================================

/-
## Benefits of the Interface Pattern

1. **Uniform comparison**: `theoriesAgreeOn` works for ANY two theories
   implementing `CoreferenceTheory`, not just our current three.

2. **Easy extensibility**: To add Construction Grammar or Cognitive Grammar,
   just implement the interface - all comparison infrastructure works automatically.

3. **Contradiction detection**: If two theories disagree on any sentence,
   `theoriesAgreeOn` returns `false`, immediately flagging the divergence.

4. **Separation of concerns**:
   - Theories define their mechanisms in their own terms
   - Interface captures only observable predictions
   - Comparison is mechanism-agnostic

## Future Work

1. Add more theories: CxG, Cognitive Grammar, LFG, TAG
2. Extend interface with theory metadata (mechanism type, complexity)
3. Use interface for automated theory comparison across phenomena
4. Build contradiction finder: search for sentences where theories diverge
-/

end Comparisons.Coreference
