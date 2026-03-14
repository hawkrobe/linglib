/-
# Neo-Gricean Pragmatics: Scalar Implicatures

Scalar implicature specifics from @cite{geurts-2010} Chapter 3.2-3.3,
plus scale semantics and predictions.

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

Reference: Geurts, B. (2010). Quantity Implicatures. Cambridge University Press.

Scale semantics (SemanticScale, HurfordSemantic, SinghSemantic) and
exhaustification predictions live in `Alternatives/HornScale.lean` and
`Exhaustification/SemanticScales.lean`.
-/

import Linglib.Theories.Pragmatics.Implicature.Core.Basic
import Linglib.Theories.Semantics.Alternatives.HornScale
import Linglib.Theories.Semantics.Exhaustification.SemanticScales
import Linglib.Theories.Semantics.Entailment.Basic
import Linglib.Theories.Semantics.Montague.Derivation
import Linglib.Core.Interface

namespace Implicature.ScalarImplicatures

open Implicature
open Exhaustification
open Semantics.Entailment.Polarity (ContextPolarity)
open Alternatives.Quantifiers (QuantExpr)
open Alternatives.Connectives (ConnExpr)

-- ============================================================
-- Q-Alternative Infrastructure
-- ============================================================

/-- An unordered set of expressions (following @cite{geurts-2010} p.58). -/
structure HornSet (α : Type) where
  members : List α
  deriving Repr

def HornSet.otherMembers {α : Type} [BEq α] (h : HornSet α) (x : α) : List α :=
  h.members.filter (· != x)

/-- A sentence context determines alternative strength via polarity. -/
structure SentenceContext where
  polarity : ContextPolarity
  description : String
  deriving Repr

def simpleAssertion : SentenceContext :=
  { polarity := .upward, description := "Simple assertion" }

def underNegation : SentenceContext :=
  { polarity := .downward, description := "Under negation" }

/-- Abstract entailment checker for sentences. -/
structure EntailmentChecker (α : Type) where
  isStronger : ContextPolarity → α → α → Bool

/-- An alternative with its context-dependent strength. -/
structure Alternative (α : Type) where
  term : α
  isStrongerInContext : Bool
  deriving Repr

def generateAlternatives {α : Type} [BEq α]
    (hornSet : HornSet α) (checker : EntailmentChecker α)
    (context : SentenceContext) (term : α) : List (Alternative α) :=
  hornSet.otherMembers term |>.map λ alt =>
    { term := alt, isStrongerInContext := checker.isStronger context.polarity alt term }

def strongerAlternatives {α : Type} [BEq α]
    (hornSet : HornSet α) (checker : EntailmentChecker α)
    (context : SentenceContext) (term : α) : List α :=
  (generateAlternatives hornSet checker context term).filter (·.isStrongerInContext) |>.map (·.term)

-- Quantifier checkers (grounded in Alternatives.Quantifiers.entails)
private def quantifierChecker : EntailmentChecker QuantExpr :=
  { isStronger := λ pol q1 q2 =>
      match pol with
      | .upward => Alternatives.Quantifiers.entails q1 q2 && q1 != q2
      | .downward => Alternatives.Quantifiers.entails q2 q1 && q1 != q2
      | .nonMonotonic => false }

private def connectiveChecker : EntailmentChecker ConnExpr :=
  { isStronger := λ pol c1 c2 =>
      match pol with
      | .upward => Alternatives.Connectives.entails c1 c2 && c1 != c2
      | .downward => Alternatives.Connectives.entails c2 c1 && c1 != c2
      | .nonMonotonic => false }

def quantifierCheckerString : EntailmentChecker String :=
  { isStronger := λ pol s1 s2 =>
      match QuantExpr.ofString? s1, QuantExpr.ofString? s2 with
      | some q1, some q2 => quantifierChecker.isStronger pol q1 q2
      | _, _ => false }

def connectiveCheckerString : EntailmentChecker String :=
  { isStronger := λ pol s1 s2 =>
      match ConnExpr.ofString? s1, ConnExpr.ofString? s2 with
      | some c1, some c2 => connectiveChecker.isStronger pol c1 c2
      | _, _ => false }

def quantifierSetString : HornSet String := ⟨["some", "most", "all"]⟩
def connectiveSetString : HornSet String := ⟨["or", "and"]⟩


/--
A scalar implicature derivation attempt.

Records whether the implicature arises and why/why not.
-/
structure ImplicatureDerivation where
  /-- The scalar term used -/
  term : String
  /-- The potential stronger alternative -/
  alternative : String
  /-- The context polarity -/
  polarity : ContextPolarity
  /-- Does the alternative count as stronger in this context? -/
  alternativeIsStronger : Bool
  /-- Does the implicature arise? -/
  implicatureArises : Bool
  deriving Repr

/--
Attempt to derive a scalar implicature.
-/
def deriveImplicature
    (term alternative : String)
    (ctx : SentenceContext)
    (checker : EntailmentChecker String) : ImplicatureDerivation :=
  let stronger := checker.isStronger ctx.polarity alternative term
  { term := term
  , alternative := alternative
  , polarity := ctx.polarity
  , alternativeIsStronger := stronger
  , implicatureArises := stronger
  }

/--
Example: "some" → "not all" in UE context
-/
def someNotAll_UE : ImplicatureDerivation :=
  deriveImplicature "some" "all" simpleAssertion quantifierCheckerString

/--
Example: "some" → "not all" blocked in DE context
-/
def someNotAll_DE : ImplicatureDerivation :=
  deriveImplicature "some" "all" underNegation quantifierCheckerString

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
def allNotSome_DE : ImplicatureDerivation :=
  deriveImplicature "all" "some" underNegation quantifierCheckerString

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
Analyze a simple disjunction in UE context.

Both exclusivity AND ignorance can arise together.
-/
def analyzeDisjunction (ctx : SentenceContext) : DisjunctionAnalysis :=
  let exclusivity := connectiveCheckerString.isStronger ctx.polarity "and" "or"
  -- Ignorance arises when competence is not assumed (for disjuncts)
  -- In standard disjunction contexts, ignorance typically arises
  { statement := "A or B"
  , exclusivityArises := exclusivity
  , ignoranceArises := true  -- Typically arises for disjunctions
  , compatible := true       -- Both can hold simultaneously
  }

/--
Theorem: Disjunction in UE Has Exclusivity
-/
theorem disjunction_exclusivity_ue :
    (analyzeDisjunction simpleAssertion).exclusivityArises = true := by
  native_decide

/--
Theorem: Both Inferences Are Compatible

"A or B" can simultaneously implicate:
- "not both" (exclusivity)
- "speaker doesn't know which" (ignorance)
-/
theorem exclusivity_ignorance_compatible :
    (analyzeDisjunction simpleAssertion).compatible = true := by
  native_decide


/--
The long disjunction problem (Geurts p.61-64).

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
  /-- The Horn set used -/
  hornSet : HornSet String
  /-- The context -/
  context : SentenceContext
  /-- Stronger alternatives found -/
  strongerAlts : List String
  /-- Implicatures derived (negations of stronger alternatives) -/
  implicatures : List String
  deriving Repr

/--
Derive all scalar implicatures for a term.
-/
def deriveScalarImplicatures
    (term : String)
    (hornSet : HornSet String)
    (checker : EntailmentChecker String)
    (context : SentenceContext) : ScalarImplicatureResult :=
  let alts := strongerAlternatives hornSet checker context term
  { term := term
  , hornSet := hornSet
  , context := context
  , strongerAlts := alts
  , implicatures := alts.map λ a => s!"not({a})"
  }

/--
Example: Complete derivation for "some" in UE context
-/
def someUE : ScalarImplicatureResult :=
  deriveScalarImplicatures "some" quantifierSetString quantifierCheckerString simpleAssertion

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
  deriveScalarImplicatures "some" quantifierSetString quantifierCheckerString underNegation

/--
Theorem: "some" in DE derives NO implicatures
-/
theorem some_de_no_implicatures :
    someDE.implicatures = ([] : List String) := by
  native_decide


/-
## Connection to Syntax via SemDeriv.Derivation

This part connects Implicature pragmatics to the syntax-semantics pipeline.
Any syntax theory (CCG, HPSG, Minimalism) that produces a `SemDeriv.Derivation`
can feed into these functions.

```
CCG/HPSG/Minimalism → SemDeriv.Derivation → deriveFromDerivation → ScalarImplicatureResult
```
-/

open Semantics.Montague
open Semantics.Montague.SemDeriv
open Semantics.Montague

/--
Map scale membership to the appropriate HornSet and EntailmentChecker.

Uses string-based versions for interface with SemDeriv, but these
are backed by type-safe implementations grounded in Alternatives.
-/
def getScaleInfo (sm : ScaleMembership) : HornSet String × EntailmentChecker String :=
  match sm with
  | .quantifier _ => (quantifierSetString, quantifierCheckerString)
  | .connective _ => (connectiveSetString, connectiveCheckerString)
  | .modal _ => (connectiveSetString, connectiveCheckerString)  -- simplified for now

/--
Create a SentenceContext from a ContextPolarity.
-/
def toSentenceContext (ctx : ContextPolarity) : SentenceContext :=
  { polarity := ctx
  , description := match ctx with
    | .upward => "Upward-entailing context"
    | .downward => "Downward-entailing context"
    | .nonMonotonic => "Non-monotonic context"
  }

/--
Derive scalar implicatures from a semantic derivation.

This is the key function that connects syntax to pragmatics:
1. Takes a SemDeriv.Derivation (produced by any syntax theory)
2. Extracts scalar items from the derivation
3. For each scalar item, derives implicatures based on its scale
4. Returns all derived implicatures

Syntax-agnostic: Works with CCG, HPSG, Minimalism, or any theory
that implements the SemDeriv interface.
-/
def deriveFromDerivation {m : Model} (d : Derivation m) (ctx : ContextPolarity)
    : List ScalarImplicatureResult :=
  d.scalarItems.filterMap λ occ =>
    match occ.entry.scaleMembership with
    | none => none
    | some sm =>
      let (hornSet, checker) := getScaleInfo sm
      let sentCtx := toSentenceContext ctx
      some (deriveScalarImplicatures occ.entry.form hornSet checker sentCtx)

/--
Check if any implicature in the results negates a given alternative.
-/
def hasImplicature (results : List ScalarImplicatureResult) (alt : String) : Bool :=
  results.any λ r => r.implicatures.contains s!"not({alt})"

/--
Example: "some students sleep" via CCG

Using the CCG derivation from CCG/Interpret.lean:
-/
def someStudentsSleep_result : List ScalarImplicatureResult :=
  deriveFromDerivation Semantics.Montague.SemDeriv.someStudentsSleep .upward

/--
Theorem: "some students sleep" derives "not(all)"

This is the key milestone theorem: starting from a semantic derivation
(which could come from CCG), Implicature pragmatics derives "not all".
-/
theorem some_students_derives_not_all :
    hasImplicature someStudentsSleep_result "all" = true := by
  native_decide

/--
Theorem: "some students sleep" derives "not(most)" as well
-/
theorem some_students_derives_not_most :
    hasImplicature someStudentsSleep_result "most" = true := by
  native_decide

/--
Example: "every student sleeps" in UE

"every" is at the top of the quantifier scale, so no stronger alternatives.
-/
def everyStudentsSleeps_result : List ScalarImplicatureResult :=
  deriveFromDerivation Semantics.Montague.SemDeriv.everyStudentSleeps .upward

/--
Theorem: "every student sleeps" has no implicatures

Since "every/all" is the strongest quantifier, there are no stronger
alternatives to negate.
-/
theorem every_students_no_implicatures :
    everyStudentsSleeps_result.all (·.implicatures.isEmpty) = true := by
  native_decide

/--
Example: "some students sleep" in DE context

In a downward-entailing context (e.g., "No one thinks some students sleep"),
the "not all" implicature is blocked.
-/
def someStudentsSleep_DE_result : List ScalarImplicatureResult :=
  deriveFromDerivation Semantics.Montague.SemDeriv.someStudentsSleep .downward

/--
Theorem: "some" in DE has no "not all" implicature

Downward-entailing contexts block the standard scalar implicature.
-/
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
