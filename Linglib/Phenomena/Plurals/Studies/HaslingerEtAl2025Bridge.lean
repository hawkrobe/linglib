/-
# Haslinger et al. (2025): Distributivity ≠ Maximality

Empirical data from "On the relation between distributivity and maximality"
(Semantics & Pragmatics 18, Article 1).

## Main Finding

German *jeweils* is obligatorily distributive but permits non-maximal
interpretations for some speakers, while *jeder* requires maximality.
This demonstrates that distributivity and maximality are independent.

## Theoretical Connection

The theory in `Theories/Montague/Plural/Distributivity.lean` predicts:
- *jeder* uses `distMaximal` (identity tolerance)
- *jeweils* uses `distTolerant` (context-sensitive tolerance)

## References

- Haslinger, Rosina, Schmitt & Wurm (2025). On the relation between
  distributivity and maximality. Semantics & Pragmatics 18.
-/

import Linglib.Theories.Semantics.Lexical.Plural.Distributivity

namespace Phenomena.Plurals.Studies.HaslingerEtAl2025

open Semantics.Lexical.Plural.Distributivity (DistMaxClass)

-- German Distributive Lexical Items

/-- Syntactic distribution of a distributive element -/
inductive SyntacticUse where
  | dpInternal   -- "jeder Hund" (every dog)
  | distance     -- "Die Hunde haben jeweils/jeder..."
  deriving DecidableEq, Repr, BEq

/-- A German distributive item with its properties -/
structure LexicalItem where
  form : String
  gloss : String
  uses : List SyntacticUse
  semanticClass : DistMaxClass
  deriving Repr

/-- jeder (DP-internal and distance): +distributive, +maximal -/
def jeder : LexicalItem :=
  { form := "jeder"
  , gloss := "every/each"
  , uses := [.dpInternal, .distance]
  , semanticClass := .distMax }

/-- jeweils (distance only): +distributive, -maximal -/
def jeweils : LexicalItem :=
  { form := "jeweils"
  , gloss := "each/respectively"
  , uses := [.distance]  -- No DP-internal use!
  , semanticClass := .distNonMax }

/-- alle (DP-internal): -distributive, +maximal -/
def alle : LexicalItem :=
  { form := "alle"
  , gloss := "all"
  , uses := [.dpInternal]
  , semanticClass := .nonDistMax }

/-- Definite plurals: -distributive, -maximal -/
def definitePlural : LexicalItem :=
  { form := "die NPs"
  , gloss := "the NPs"
  , uses := [.dpInternal]
  , semanticClass := .nonDistNonMax }

-- Experimental Data (Section 3)

/-- Context for testing non-maximality (QUD makes exceptions irrelevant) -/
structure NonMaxContext where
  description : String
  totalItems : Nat
  exceptions : Nat
  implicitQUD : String
  deriving Repr

/-- Magnets scenario (example 23): 5 boxes, 4 have 2 magnets, 1 has 1 -/
def magnetsContext : NonMaxContext :=
  { description := "Magnets that shouldn't be stored together"
  , totalItems := 5
  , exceptions := 1
  , implicitQUD := "Is there explosion risk?" }

/-- Experimental observation -/
structure Observation where
  item : LexicalItem
  context : NonMaxContext
  /-- Proportion accepting (rating ≥ 4 on 7-point scale) -/
  acceptanceRate : Float
  deriving Repr

/-- jeder rejected in non-maximal contexts (Figure 1) -/
def jederInNonMax : Observation :=
  { item := jeder
  , context := magnetsContext
  , acceptanceRate := 0.15 }

/-- jeweils shows mixed judgments (Figure 1) -/
def jeweilsInNonMax : Observation :=
  { item := jeweils
  , context := magnetsContext
  , acceptanceRate := 0.45 }

-- Key Empirical Generalizations

/-- Both jeder and jeweils are distributive -/
def isDistributive : DistMaxClass → Bool
  | .distMax => true
  | .distNonMax => true
  | .nonDistMax => false
  | .nonDistNonMax => false

/-- The independence claim: same distributivity, different maximality -/
theorem independence_attested :
    isDistributive jeder.semanticClass = isDistributive jeweils.semanticClass ∧
    jeder.semanticClass ≠ jeweils.semanticClass := by
  constructor <;> native_decide

/-- Correlation (Section 4): No DP use ↔ permits non-maximality? -/
def hasDPUse (item : LexicalItem) : Bool :=
  item.uses.contains .dpInternal

-- jeder has DP use and requires maximality
example : hasDPUse jeder = true := rfl
example : jeder.semanticClass = .distMax := rfl

-- jeweils lacks DP use and permits non-maximality
example : hasDPUse jeweils = false := rfl
example : jeweils.semanticClass = .distNonMax := rfl

/-- The typological table (5) from the paper -/
def typologyTable : List (String × Bool × Bool) :=
  [ ("definite DP",      false, false)  -- -dist, -max
  , ("alle",             false, true)   -- -dist, +max
  , ("numeral indef",    false, true)   -- -dist, +max
  , ("jeder (DP)",       true,  true)   -- +dist, +max
  , ("jeder (distance)", true,  true)   -- +dist, +max
  , ("jeweils",          true,  false)  -- +dist, -max  ← KEY
  ]

end Phenomena.Plurals.Studies.HaslingerEtAl2025
