/-
# Franke & Bergen (2020): Nested Aristotelian Interpretation Data

Empirical data on interpretation of doubly-quantified sentences and
model comparison results for RSA variants.

## Key Empirical Findings

**Domain**: Nested Aristotelian sentences like "Some aliens drank some water"
with combinations of {none, some, all} × {none, some, all} = 9 sentence types.

**Model Comparison** (Franke & Bergen 2020, Table 2):
| Model | Posterior Probability |
|-------|----------------------|
| Vanilla RSA | 0.000 |
| Lexical Uncertainty (LU) | 0.044 |
| Lexical Intentions (LI) | 0.000 |
| Global Intentions (GI) | 0.956 |

**Key Result**: Global Intentions (where speakers jointly choose utterance
and grammatical parse) dramatically outperforms other models.

## Reference

Franke, M. & Bergen, L. (2020). "Theory-driven statistical modeling for
semantics and pragmatics". Annual Review of Linguistics, Vol. 6, pp. 533–562.
-/

namespace Phenomena.Quantification.Studies.FrankeBergen2020

-- Sentence Types: Nested Aristotelians

/-- Aristotelian quantifiers -/
inductive AristQuant where
  | none : AristQuant  -- "No X"
  | some : AristQuant  -- "Some X"
  | all : AristQuant   -- "All X"
  deriving DecidableEq, BEq, Repr, Inhabited

/-- A nested Aristotelian: "Q1 Xs V'd Q2 Ys"
    Example: "Some aliens drank all the water" = ⟨some, all⟩ -/
structure NestedAristotelian where
  outer : AristQuant
  inner : AristQuant
  deriving DecidableEq, BEq, Repr

/-- Short notation -/
def NestedAristotelian.abbrev : NestedAristotelian → String
  | ⟨.none, .none⟩ => "NN" | ⟨.none, .some⟩ => "NS" | ⟨.none, .all⟩ => "NA"
  | ⟨.some, .none⟩ => "SN" | ⟨.some, .some⟩ => "SS" | ⟨.some, .all⟩ => "SA"
  | ⟨.all, .none⟩ => "AN"  | ⟨.all, .some⟩ => "AS"  | ⟨.all, .all⟩ => "AA"

instance : ToString NestedAristotelian := ⟨NestedAristotelian.abbrev⟩

/-- All 9 nested Aristotelians -/
def allSentences : List NestedAristotelian :=
  [⟨.none, .none⟩, ⟨.none, .some⟩, ⟨.none, .all⟩,
   ⟨.some, .none⟩, ⟨.some, .some⟩, ⟨.some, .all⟩,
   ⟨.all, .none⟩, ⟨.all, .some⟩, ⟨.all, .all⟩]

-- Model Types

/-- RSA model variants compared in the paper -/
inductive RSAModel where
  | vanilla : RSAModel          -- Basic RSA
  | lexicalUncertainty : RSAModel  -- LU (Bergen et al. 2016)
  | lexicalIntentions : RSAModel   -- LI
  | globalIntentions : RSAModel    -- GI (best performer)
  deriving DecidableEq, BEq, Repr

/-- Model description -/
def RSAModel.description : RSAModel → String
  | .vanilla => "Vanilla RSA: literal semantics only"
  | .lexicalUncertainty => "LU: lexicon as input, listener marginalizes"
  | .lexicalIntentions => "LI: lexicon as output, speaker chooses"
  | .globalIntentions => "GI: parse as output, speaker chooses (u,g) pairs"

-- Model Comparison Data (Table 2)

/-- Posterior probability for each model -/
structure ModelResult where
  model : RSAModel
  posteriorProb : Nat  -- Stored as thousandths (956 = 0.956)
  deriving Repr

/-- Table 2 results: Model comparison by posterior probability -/
def modelComparisonResults : List ModelResult :=
  [ ⟨.vanilla, 0⟩              -- 0.000
  , ⟨.lexicalUncertainty, 44⟩  -- 0.044
  , ⟨.lexicalIntentions, 0⟩    -- 0.000
  , ⟨.globalIntentions, 956⟩   -- 0.956
  ]

/-- Get posterior for a model -/
def getPosterior (m : RSAModel) : Nat :=
  match modelComparisonResults.find? (fun r => r.model == m) with
  | some r => r.posteriorProb
  | none => 0

-- Key Empirical Facts

/-- GI achieves highest posterior -/
theorem gi_best : getPosterior .globalIntentions = 956 := rfl

/-- Vanilla RSA fails completely -/
theorem vanilla_fails : getPosterior .vanilla = 0 := rfl

/-- GI dramatically outperforms LU -/
theorem gi_beats_lu : getPosterior .globalIntentions > getPosterior .lexicalUncertainty := by
  native_decide

/-- GI captures almost all posterior mass -/
theorem gi_dominates :
    getPosterior .globalIntentions >
    getPosterior .vanilla + getPosterior .lexicalUncertainty + getPosterior .lexicalIntentions := by
  native_decide

-- Parse Types (for GI model)

/-- EXH positions in doubly-quantified sentences -/
inductive ExhPosition where
  | M : ExhPosition  -- Matrix
  | O : ExhPosition  -- Outer quantifier
  | I : ExhPosition  -- Inner quantifier
  deriving DecidableEq, BEq, Repr

/-- A parse = which positions have EXH -/
abbrev GrammaticalParse := List ExhPosition

/-- All 8 parses -/
def allParses : List GrammaticalParse :=
  [[], [.M], [.O], [.I], [.M, .O], [.M, .I], [.O, .I], [.M, .O, .I]]

/-- Number of parses -/
theorem parse_count : allParses.length = 8 := rfl

-- Dimension Facts

/-- Total cells in the model: 9 sentences × 8 parses = 72 -/
theorem model_dimensions :
    allSentences.length * allParses.length = 72 := by native_decide

-- Theoretical Predictions

/-- Key theoretical claim: GI succeeds because parse is speaker's OUTPUT.

    In GI, the speaker jointly optimizes (utterance, parse), signaling
    both WHAT to say and HOW to parse it.

    In LU, lexicon is speaker's INPUT - the listener reasons about which
    lexicon the speaker was using, but the speaker doesn't actively choose.

    This distinction matters for embedded implicatures. -/
def giKeyInsight : String :=
  "GI treats grammatical parse as speaker's OUTPUT (choice), not INPUT (given). " ++
  "The speaker jointly optimizes (utterance, parse) pairs, allowing pragmatic " ++
  "pressure to select parses with embedded exhaustification."

-- Summary

/-
## What This Module Provides

### Data Types
- `AristQuant`: Aristotelian quantifiers (none, some, all)
- `NestedAristotelian`: Doubly-quantified sentences
- `RSAModel`: Model variants (Vanilla, LU, LI, GI)
- `ExhPosition`: EXH positions (M, O, I)
- `GrammaticalParse`: List of EXH positions

### Experimental Data
- `modelComparisonResults`: Posterior probabilities (Table 2)
- `allSentences`: 9 nested Aristotelians
- `allParses`: 8 grammatical parses

### Key Theorems
- `gi_best`: GI achieves 0.956 posterior
- `gi_dominates`: GI captures almost all posterior mass
- `model_dimensions`: 9 × 8 = 72 cells

### Theoretical Claims
- GI succeeds because parse is speaker OUTPUT
- LU fails because lexicon is speaker INPUT
-/

end FrankeBergen2020
