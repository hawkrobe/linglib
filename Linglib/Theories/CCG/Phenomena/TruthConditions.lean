/-
# CCG Truth Conditions: Syntax → Semantics Pipeline

This module demonstrates the complete CCG → Montague pipeline:
1. CCG derivations (syntax)
2. Compositional interpretation (syntax-semantics interface)
3. Truth conditions matching empirical judgments (semantics-data connection)

## The Pipeline

```
CCG.DerivStep                    TruthConditional.Ty
├── john_sleeps : DerivStep      ├── catToTy S = t (Bool)
└── .interp toySemLexicon        └── meaning : Bool
    ↓
TruthConditions.TruthJudgment
├── judgedTrue = true
└── CCG predicts this ✓
```
-/

import Linglib.Theories.CCG.Bridge.Interface
import Linglib.Phenomena.Entailment.Basic

namespace CCG.TruthConditions

open CCG
open TruthConditional
open Phenomena.Entailment

-- CCG Derivations for Test Sentences

/-- "John sleeps" - backward application -/
def ccg_john_sleeps : DerivStep :=
  .bapp (.lex ⟨"John", NP⟩) (.lex ⟨"sleeps", IV⟩)

/-- "Mary sleeps" - backward application -/
def ccg_mary_sleeps : DerivStep :=
  .bapp (.lex ⟨"Mary", NP⟩) (.lex ⟨"sleeps", IV⟩)

/-- "John laughs" - backward application -/
def ccg_john_laughs : DerivStep :=
  .bapp (.lex ⟨"John", NP⟩) (.lex ⟨"laughs", IV⟩)

/-- "Mary laughs" - backward application -/
def ccg_mary_laughs : DerivStep :=
  .bapp (.lex ⟨"Mary", NP⟩) (.lex ⟨"laughs", IV⟩)

/-- "John sees Mary" - forward then backward application -/
def ccg_john_sees_mary : DerivStep :=
  .bapp (.lex ⟨"John", NP⟩) (.fapp (.lex ⟨"sees", TV⟩) (.lex ⟨"Mary", NP⟩))

/-- "Mary sees John" - forward then backward application -/
def ccg_mary_sees_john : DerivStep :=
  .bapp (.lex ⟨"Mary", NP⟩) (.fapp (.lex ⟨"sees", TV⟩) (.lex ⟨"John", NP⟩))

/-- "John eats pizza" - forward then backward application -/
def ccg_john_eats_pizza : DerivStep :=
  .bapp (.lex ⟨"John", NP⟩) (.fapp (.lex ⟨"eats", TV⟩) (.lex ⟨"pizza", NP⟩))

-- Extended Semantic Lexicon (matching the toy model)

/-- Extended lexicon with all entities and predicates -/
def extendedLexicon : SemLexicon toyModel := λ word cat =>
  match word, cat with
  -- Proper names
  | "John", .atom .NP => some ⟨NP, ToyEntity.john⟩
  | "Mary", .atom .NP => some ⟨NP, ToyEntity.mary⟩
  | "pizza", .atom .NP => some ⟨NP, ToyEntity.pizza⟩
  | "book", .atom .NP => some ⟨NP, ToyEntity.book⟩
  -- Intransitive verbs
  | "sleeps", .lslash (.atom .S) (.atom .NP) => some ⟨IV, ToyLexicon.sleeps_sem⟩
  | "laughs", .lslash (.atom .S) (.atom .NP) => some ⟨IV, ToyLexicon.laughs_sem⟩
  -- Transitive verbs
  | "sees", .rslash (.lslash (.atom .S) (.atom .NP)) (.atom .NP) =>
      some ⟨TV, ToyLexicon.sees_sem⟩
  | "eats", .rslash (.lslash (.atom .S) (.atom .NP)) (.atom .NP) =>
      some ⟨TV, ToyLexicon.eats_sem⟩
  | "reads", .rslash (.lslash (.atom .S) (.atom .NP)) (.atom .NP) =>
      some ⟨TV, ToyLexicon.reads_sem⟩
  | _, _ => none

-- CCG Predictions

/-- Get truth value from CCG derivation -/
def ccgTruth (d : DerivStep) : Option Bool :=
  getMeaning (d.interp extendedLexicon)

-- Verify derivations parse correctly
#eval ccg_john_sleeps.cat       -- some S
#eval ccg_mary_sleeps.cat       -- some S
#eval ccg_john_sees_mary.cat    -- some S

-- Verify truth values
#eval ccgTruth ccg_john_sleeps      -- some true
#eval ccgTruth ccg_mary_sleeps      -- some false
#eval ccgTruth ccg_john_sees_mary   -- some true
#eval ccgTruth ccg_mary_sees_john   -- some true

-- Pipeline Theorems: CCG Matches Empirical Truth Judgments

/-- CCG correctly predicts "John sleeps" is true -/
theorem ccg_predicts_john_sleeps :
    ccgTruth ccg_john_sleeps = some johnSleepsTrue.judgedTrue := by
  native_decide

/-- CCG correctly predicts "Mary sleeps" is false -/
theorem ccg_predicts_mary_sleeps :
    ccgTruth ccg_mary_sleeps = some marySleepsFalse.judgedTrue := by
  native_decide

/-- CCG correctly predicts "John laughs" is true -/
theorem ccg_predicts_john_laughs :
    ccgTruth ccg_john_laughs = some johnLaughsTrue.judgedTrue := by
  native_decide

/-- CCG correctly predicts "Mary laughs" is true -/
theorem ccg_predicts_mary_laughs :
    ccgTruth ccg_mary_laughs = some maryLaughsTrue.judgedTrue := by
  native_decide

/-- CCG correctly predicts "John sees Mary" is true -/
theorem ccg_predicts_john_sees_mary :
    ccgTruth ccg_john_sees_mary = some johnSeesMaryTrue.judgedTrue := by
  native_decide

/-- CCG correctly predicts "Mary sees John" is true -/
theorem ccg_predicts_mary_sees_john :
    ccgTruth ccg_mary_sees_john = some marySeesJohnTrue.judgedTrue := by
  native_decide

-- Universal Coverage Theorem

/-- A test case: derivation paired with expected judgment -/
structure TestCase where
  deriv : DerivStep
  expected : Bool

/-- All intransitive verb test cases -/
def intransitiveTestCases : List TestCase :=
  [ ⟨ccg_john_sleeps, true⟩
  , ⟨ccg_mary_sleeps, false⟩
  , ⟨ccg_john_laughs, true⟩
  , ⟨ccg_mary_laughs, true⟩
  ]

/-- All transitive verb test cases -/
def transitiveTestCases : List TestCase :=
  [ ⟨ccg_john_sees_mary, true⟩
  , ⟨ccg_mary_sees_john, true⟩
  ]

/-- Check if CCG predicts a test case correctly -/
def ccgPredictsCorrectly (tc : TestCase) : Bool :=
  ccgTruth tc.deriv == some tc.expected

/--
**CCG correctly predicts ALL intransitive test cases.**

This is the key theorem: compositional semantics via CCG
produces exactly the empirically observed truth values.
-/
theorem ccg_predicts_all_intransitive :
    intransitiveTestCases.all ccgPredictsCorrectly = true := by
  native_decide

/--
**CCG correctly predicts ALL transitive test cases.**
-/
theorem ccg_predicts_all_transitive :
    transitiveTestCases.all ccgPredictsCorrectly = true := by
  native_decide

/--
**CCG correctly predicts ALL test cases.**

The syntax → semantics pipeline produces correct truth conditions
for the entire test suite.
-/
theorem ccg_predicts_all_cases :
    (intransitiveTestCases ++ transitiveTestCases).all ccgPredictsCorrectly = true := by
  native_decide

-- Summary: Complete Pipeline

/-
## What This Module Demonstrates

### The Syntax → Semantics Pipeline

1. **Syntax (CCG)**: `DerivStep` encodes combinatory derivations
2. **Interface**: `catToTy` maps CCG categories to semantic types
3. **Interpretation**: `interp` computes meanings compositionally
4. **Data Match**: Theorems prove predictions match empirical judgments

### Theorems

- `ccg_predicts_john_sleeps`: CCG derives correct truth for intransitive
- `ccg_predicts_mary_sleeps`: CCG derives correct falsity for intransitive
- `ccg_predicts_john_sees_mary`: CCG derives correct truth for transitive

### Architecture

```
Phenomena/Semantics/TruthConditions.lean
    ↑ empirical data (judgedTrue = true/false)

Theories/CCG/TruthConditions.lean (this file)
    ↑ proves: ccgTruth d = some judgment.judgedTrue

Theories/CCG/Semantics.lean
    ↑ provides: interp, catToTy, SemLexicon

Theories/CCG/Basic.lean
    ↑ provides: DerivStep, Cat, combinatory rules
```

This is the **second complete pipeline analysis** in Linglib (after Scontras & Pearl 2021),
demonstrating that the architecture generalizes across phenomena.
-/

end CCG.TruthConditions
