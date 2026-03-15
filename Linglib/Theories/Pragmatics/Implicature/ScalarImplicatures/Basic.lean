/-
# Neo-Gricean Pragmatics: Scalar Implicatures

Scalar implicature derivation using Horn scales from
`Alternatives/Lexical.lean` and semantic entailment.

## Key Topics

1. DE Environment Handling
   In DE contexts, the entailment pattern reverses:
   - "No one ate some" entails "No one ate all"
   - So "some" is stronger than "all" at sentence level
   - This blocks the standard "not all" implicature

2. Disjunction: Exclusivity vs Ignorance
   - Exclusivity: "A or B" → "not both" (scalar implicature from ⟨or, and⟩)
   - Ignorance: "A or B" → "speaker doesn't know which"

3. Long Disjunction Problem (p.61-64)
   For n>2 disjuncts, substitution method fails.
   Need closure under conjunction for all alternatives.

Reference: @cite{geurts-2010}

Scale semantics (SemanticScale, HurfordSemantic, SinghSemantic) and
exhaustification predictions live in `Alternatives/Lexical.lean` and
`Exhaustification/ScalePredictions.lean`.
-/

import Linglib.Theories.Pragmatics.Implicature.Core.Basic
import Linglib.Theories.Semantics.Alternatives.Lexical
import Linglib.Theories.Semantics.Entailment.Polarity
import Linglib.Core.Interface
import Linglib.Core.Lexical.Word

namespace Implicature.ScalarImplicatures

open Implicature
open Semantics.Entailment.Polarity (ContextPolarity)
open Alternatives.Quantifiers (QuantExpr)
open Alternatives.Connectives (ConnExpr)
open Alternatives (ScaleMembership)


-- ============================================================
-- Scalar Alternative Computation (via HornScale + entailment)
-- ============================================================

/-- Filter HornScale members to those that are context-appropriate alternatives.
    In UE: alternatives that entail the term (stronger).
    In DE: alternatives that the term entails (reversed).
    In NM: no alternatives. -/
private def filterAlts {α : Type} [BEq α] [ToString α]
    (scale : Alternatives.HornScale α) (pos : α) (entailsFn : α → α → Bool)
    (ctx : ContextPolarity) : List String :=
  match ctx with
  | .nonMonotonic => []
  | .upward =>
    scale.members.filter (λ alt => alt != pos && entailsFn alt pos) |>.map toString
  | .downward =>
    scale.members.filter (λ alt => alt != pos && entailsFn pos alt) |>.map toString

/-- Get scalar alternatives for a scale member in context.
    Delegates to `HornScale` members filtered by semantic entailment,
    polarity-aware. -/
def scaleAlternatives (sm : ScaleMembership) (ctx : ContextPolarity) : List String :=
  match sm with
  | .quantifier pos =>
    filterAlts Alternatives.Quantifiers.quantScale pos Alternatives.Quantifiers.entails ctx
  | .connective pos =>
    filterAlts Alternatives.Connectives.connScale pos Alternatives.Connectives.entails ctx
  | .modal pos =>
    filterAlts Alternatives.Modals.modalScale pos Alternatives.Modals.entails ctx


-- ============================================================
-- DE Blocking (using HornScale directly)
-- ============================================================

/-- Lightweight wrapper preserving the `.implicatureArises` accessor. -/
structure ImplicatureCheck where
  implicatureArises : Bool
  deriving Repr, DecidableEq

/-- Does an alternative arise as a scalar implicature of a quantifier term? -/
def quantImplicatureArises (term alt : QuantExpr) (ctx : ContextPolarity) : Bool :=
  (scaleAlternatives (.quantifier term) ctx).contains (toString alt)

/--
Example: "some" → "not all" in UE context
-/
def someNotAll_UE : ImplicatureCheck :=
  ⟨quantImplicatureArises .some_ .all .upward⟩

/--
Example: "some" → "not all" blocked in DE context
-/
def someNotAll_DE : ImplicatureCheck :=
  ⟨quantImplicatureArises .some_ .all .downward⟩

/--
Theorem: DE Blocks "Some → Not All"

In UE context, the implicature arises.
In DE context, the implicature is blocked.
-/
theorem de_blocks_some_not_all :
    someNotAll_UE.implicatureArises = true ∧
    someNotAll_DE.implicatureArises = false := by
  native_decide

/--
Theorem: In DE, "All" Has Implicatures

In DE context, "all" can implicate "not some" (reversed!).
-/
def allNotSome_DE : ImplicatureCheck :=
  ⟨quantImplicatureArises .all .some_ .downward⟩

theorem de_all_has_implicature :
    allNotSome_DE.implicatureArises = true := by
  native_decide


/--
Two types of inferences from disjunction.

1. Exclusivity (scalar): "A or B" → "not (A and B)"
   Derived from Horn set ⟨or, and⟩.

2. Ignorance (non-scalar): "A or B" → "speaker doesn't know which"
   Derived from competence failure for individual disjuncts.
-/
inductive DisjunctionInference where
  | exclusivity  -- "not both" (from ⟨or, and⟩ scale)
  | ignorance    -- "speaker doesn't know which"
  deriving DecidableEq, BEq, Repr

/--
Result of analyzing a disjunctive utterance.
-/
structure DisjunctionAnalysis where
  /-- The disjunctive statement -/
  statement : String
  /-- Does exclusivity implicature arise? -/
  exclusivityArises : Bool
  /-- Does ignorance implicature arise? -/
  ignoranceArises : Bool
  /-- Can both arise together? -/
  compatible : Bool
  deriving Repr


/--
Analyze a simple disjunction in context.

Both exclusivity AND ignorance can arise together.
-/
def analyzeDisjunction (ctx : ContextPolarity) : DisjunctionAnalysis :=
  let exclusivity := (scaleAlternatives (.connective .or_) ctx).contains "and"
  { statement := "A or B"
  , exclusivityArises := exclusivity
  , ignoranceArises := true  -- Typically arises for disjunctions
  , compatible := true       -- Both can hold simultaneously
  }

/--
Theorem: Disjunction in UE Has Exclusivity
-/
theorem disjunction_exclusivity_ue :
    (analyzeDisjunction .upward).exclusivityArises = true := by
  native_decide

/--
Theorem: Both Inferences Are Compatible

"A or B" can simultaneously implicate:
- "not both" (exclusivity)
- "speaker doesn't know which" (ignorance)
-/
theorem exclusivity_ignorance_compatible :
    (analyzeDisjunction .upward).compatible = true := by
  native_decide


/--
The long disjunction problem (@cite{geurts-2010} p.61-64).

For "A or B or C", the alternatives are not just {A, B, C}.
We need ALL conjunctive closures:
- Core: A, B, C
- Binary: A∧B, A∧C, B∧C
- Full: A∧B∧C

The substitution method (replacing "or" with "and") fails
to generate all necessary alternatives for n > 2.
-/
structure LongDisjunction where
  /-- The disjuncts -/
  disjuncts : List String
  /-- Core alternatives (individual disjuncts) -/
  coreAlternatives : List String
  /-- Derived alternatives (conjunctions) -/
  derivedAlternatives : List String
  deriving Repr

/--
Generate all binary conjunctions from a list.
-/
def binaryConjunctions (terms : List String) : List String :=
  terms.flatMap λ t1 =>
    terms.filterMap λ t2 =>
      if t1 < t2 then some s!"{t1}∧{t2}" else none

/--
Generate the full conjunction of all terms.
-/
def fullConjunction (terms : List String) : String :=
  "∧".intercalate terms

/--
Analyze a long disjunction, computing all alternatives.
-/
def analyzeLongDisjunction (disjuncts : List String) : LongDisjunction :=
  { disjuncts := disjuncts
  , coreAlternatives := disjuncts
  , derivedAlternatives :=
      binaryConjunctions disjuncts ++
      [fullConjunction disjuncts]
  }

/--
Example: Three-way disjunction

"A or B or C" has alternatives:
- Core: A, B, C
- Derived: A∧B, A∧C, B∧C, A∧B∧C
-/
def threeWayExample : LongDisjunction :=
  analyzeLongDisjunction ["A", "B", "C"]

/--
Theorem: Three-way disjunction has 3 core alternatives
-/
theorem three_way_core :
    threeWayExample.coreAlternatives.length = 3 := by
  native_decide

/--
Theorem: Three-way disjunction has 4 derived alternatives

The 4 derived alternatives are: A∧B, A∧C, B∧C, A∧B∧C
-/
theorem three_way_derived :
    threeWayExample.derivedAlternatives.length = 4 := by
  native_decide

/--
Theorem: Total alternatives for 3-way = 7

Core (3) + Derived (4) = 7 alternatives
-/
theorem three_way_total :
    Nat.add threeWayExample.coreAlternatives.length
    threeWayExample.derivedAlternatives.length = 7 := by
  native_decide


/--
The simple substitution method: replace "or" with "and".

For "A or B": substitute to get "A and B" ✓
For "A or B or C": substitute to get "A and B and C" ✓
  But MISSES: "A and B", "A and C", "B and C" ✗

This is why we need closure under conjunction.
-/
def substitutionAlternative (disjuncts : List String) : String :=
  fullConjunction disjuncts

/--
What substitution method produces vs what's needed.
-/
structure SubstitutionComparison where
  /-- Number of disjuncts -/
  n : Nat
  /-- What substitution gives -/
  substitutionResult : Nat
  /-- What's actually needed -/
  neededAlternatives : Nat
  /-- Does substitution suffice? -/
  substitutionSuffices : Bool
  deriving Repr

/--
Compare substitution method to full closure.
-/
def compareSubstitution (n : Nat) : SubstitutionComparison :=
  -- Substitution gives 1 alternative (full conjunction)
  -- Needed: all subsets of size ≥ 2, which is 2^n - n - 1
  let needed := 2^n - n - 1
  { n := n
  , substitutionResult := 1
  , neededAlternatives := needed
  , substitutionSuffices := needed == 1
  }

/--
Theorem: Substitution Works for n=2

For "A or B", substitution gives "A and B" which is the only alternative.
-/
theorem substitution_works_n2 :
    (compareSubstitution 2).substitutionSuffices = true := by
  native_decide

/--
Theorem: Substitution Fails for n=3

For "A or B or C", substitution gives 1 alternative
but we need 4 (A∧B, A∧C, B∧C, A∧B∧C).
-/
theorem substitution_fails_n3 :
    (compareSubstitution 3).substitutionSuffices = false ∧
    (compareSubstitution 3).neededAlternatives = 4 := by
  native_decide


/--
Complete scalar implicature derivation result.
-/
structure ScalarImplicatureResult where
  /-- The original utterance's scalar term -/
  term : String
  /-- Stronger alternatives found -/
  strongerAlts : List String
  /-- Implicatures derived (negations of stronger alternatives) -/
  implicatures : List String
  deriving Repr

/--
Derive all scalar implicatures for a term via HornScale.
-/
def deriveScalarImplicatures
    (term : String)
    (sm : ScaleMembership)
    (ctx : ContextPolarity) : ScalarImplicatureResult :=
  let alts := scaleAlternatives sm ctx
  { term := term
  , strongerAlts := alts
  , implicatures := alts.map λ a => s!"not({a})"
  }

/--
Example: Complete derivation for "some" in UE context
-/
def someUE : ScalarImplicatureResult :=
  deriveScalarImplicatures "some" (.quantifier .some_) .upward

/--
Theorem: "some" in UE derives "not(most)" and "not(all)"
-/
theorem some_ue_implicatures :
    someUE.implicatures = ["not(most)", "not(all)"] := by
  native_decide

/--
Example: Complete derivation for "some" in DE context
-/
def someDE : ScalarImplicatureResult :=
  deriveScalarImplicatures "some" (.quantifier .some_) .downward

/--
Theorem: "some" in DE derives NO implicatures
-/
theorem some_de_no_implicatures :
    someDE.implicatures = ([] : List String) := by
  native_decide


/-
## Scalar Implicatures from Word Forms

Derives implicatures from words by looking up their Horn scale
positions via `Alternatives.scaleOf`.
-/

/-- Derive scalar implicatures from a list of words.
    Each word is looked up in the scale registry; scalar words
    produce implicatures based on polarity context. -/
def deriveFromWords (words : List String) (ctx : ContextPolarity)
    : List ScalarImplicatureResult :=
  words.filterMap λ word =>
    match Alternatives.scaleOf word with
    | none => none
    | some sm => some (deriveScalarImplicatures word sm ctx)

/--
Check if any implicature in the results negates a given alternative.
-/
def hasImplicature (results : List ScalarImplicatureResult) (alt : String) : Bool :=
  results.any λ r => r.implicatures.contains s!"not({alt})"

/-- "some students sleep": scalar item is "some" -/
def someStudentsSleep_result : List ScalarImplicatureResult :=
  deriveFromWords ["some", "students", "sleep"] .upward

/-- "some students sleep" derives "not(all)" -/
theorem some_students_derives_not_all :
    hasImplicature someStudentsSleep_result "all" = true := by
  native_decide

/-- "some students sleep" derives "not(most)" -/
theorem some_students_derives_not_most :
    hasImplicature someStudentsSleep_result "most" = true := by
  native_decide

/-- "every student sleeps": "every" is scale-top, no stronger alternatives -/
def everyStudentsSleeps_result : List ScalarImplicatureResult :=
  deriveFromWords ["every", "student", "sleeps"] .upward

/-- "every student sleeps" has no implicatures -/
theorem every_students_no_implicatures :
    everyStudentsSleeps_result.all (·.implicatures.isEmpty) = true := by
  native_decide

/-- "some students sleep" in DE: implicature blocked -/
def someStudentsSleep_DE_result : List ScalarImplicatureResult :=
  deriveFromWords ["some", "students", "sleep"] .downward

/-- "some" in DE has no "not all" implicature -/
theorem some_students_de_no_not_all :
    hasImplicature someStudentsSleep_DE_result "all" = false := by
  native_decide


/-
## Comparing Neo-Gricean Variants

Both Defaultism (Levinson) and Contextualism (Geurts) are Neo-Gricean theories.
They share the Standard Recipe but differ on WHEN SIs get triggered.
-/

/--
Derived: Defaultism predicts high neutral rate
-/
theorem defaultism_predicts_high_rate :
    predictsHighNeutralRate levinsonParams = true := by native_decide

/--
Derived: Contextualism predicts moderate neutral rate
-/
theorem contextualism_predicts_moderate_rate :
    predictsHighNeutralRate geurtsParams = false := by native_decide

/--
Derived: Only contextualism predicts task effect
-/
theorem only_contextualism_predicts_task_effect :
    predictsTaskEffect levinsonParams = false ∧
    predictsTaskEffect geurtsParams = true := by native_decide

/--
Derived: The two variants make different predictions

This is what makes them empirically distinguishable.
-/
theorem variants_make_different_predictions :
    levinsonParams.predictedNeutralRate ≠ geurtsParams.predictedNeutralRate ∧
    predictsTaskEffect levinsonParams ≠ predictsTaskEffect geurtsParams := by
  native_decide


end Implicature.ScalarImplicatures


namespace Implicature

open Semantics.Entailment.Polarity (ContextPolarity)

/-- Implicature's internal representation for implicature analysis.

    Bundles the Standard Recipe result with context information. -/
structure NeoGriceanStructure where
  /-- The Standard Recipe result (weak/strong implicature, competence) -/
  result : StandardRecipeResult
  /-- Context polarity (upward vs downward entailing) -/
  polarity : ContextPolarity
  /-- Position of the scalar item (if any) -/
  scalarPosition : Option Nat
  /-- Which variant of Implicature (for baseline rate) -/
  params : NeoGriceanParams := geurtsParams
  deriving Repr

-- Parsing

/-- Check if a word is a scalar quantifier -/
def isScalarQuantifierWord (w : Word) : Bool :=
  w.form == "some" || w.form == "every" || w.form == "all" || w.form == "most"

/-- Find the position of a scalar item in a word list -/
def findScalarPositionInWords (ws : List Word) : Option Nat :=
  ws.findIdx? isScalarQuantifierWord

/-- Determine context polarity from words.
    Simplified: checks for negation markers. -/
def determinePolarityFromWords (ws : List Word) : ContextPolarity :=
  if ws.any (λ w => w.form == "no" || w.form == "not" || w.form == "never")
  then .downward
  else .upward

/-- Parse words into Implicature structure.

    For now, uses a simplified analysis:
    - Finds scalar item position
    - Determines polarity from negation markers
    - Assumes competence holds and derives strong implicature in UE -/
def parseToNeoGricean (ws : List Word) : Option NeoGriceanStructure :=
  let scalarPos := findScalarPositionInWords ws
  let polarity := determinePolarityFromWords ws
  -- Determine belief state based on polarity
  let beliefState : BeliefState :=
    match scalarPos, polarity with
    | some _, .upward => .disbelief  -- Strong implicature in UE
    | some _, .downward => .noOpinion  -- Blocked in DE
    | some _, .nonMonotonic => .noOpinion  -- Blocked in NM
    | none, _ => .belief  -- No scalar item
  let result := applyStandardRecipe beliefState
  some { result := result
       , polarity := polarity
       , scalarPosition := scalarPos
       , params := geurtsParams
       }

-- Example Derivations

/-- Example: "some students sleep" in UE context -/
def someStudentsSleepNG : NeoGriceanStructure :=
  { result := applyStandardRecipe .disbelief
  , polarity := .upward
  , scalarPosition := some 0
  , params := geurtsParams
  }

/-- Example: "some students sleep" in DE context (under negation) -/
def someStudentsSleepDE : NeoGriceanStructure :=
  { result := applyStandardRecipe .noOpinion
  , polarity := .downward
  , scalarPosition := some 0
  , params := geurtsParams
  }

end Implicature
