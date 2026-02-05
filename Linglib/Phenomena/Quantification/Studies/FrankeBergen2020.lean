/-
# Franke & Bergen (2020): Nested Aristotelian Interpretation

Model comparison for doubly-quantified sentences. Global Intentions (GI) achieves 0.956 posterior probability, dramatically outperforming vanilla RSA (0.000) and lexical uncertainty (0.044).

## Main definitions
- `NestedAristotelian`, `RSAModel`, `ModelResult`
- `GrammaticalParse`, `ExhPosition`

## References
- Franke & Bergen (2020). Theory-driven statistical modeling for semantics and pragmatics. Annual Review of Linguistics, 6:533–562.
-/

namespace Phenomena.Quantification.Studies.FrankeBergen2020

/-- Aristotelian quantifiers -/
inductive AristQuant where
  | none : AristQuant  -- "No X"
  | some : AristQuant  -- "Some X"
  | all : AristQuant   -- "All X"
  deriving DecidableEq, BEq, Repr, Inhabited

/-- A nested Aristotelian: "Q1 Xs V'd Q2 Ys" -/
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
  match modelComparisonResults.find? (λ r => r.model == m) with
  | some r => r.posteriorProb
  | none => 0

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

/-- Total cells in the model: 9 sentences × 8 parses = 72 -/
theorem model_dimensions :
    allSentences.length * allParses.length = 72 := by native_decide


end FrankeBergen2020
