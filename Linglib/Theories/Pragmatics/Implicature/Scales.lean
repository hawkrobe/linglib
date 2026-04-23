import Linglib.Theories.Pragmatics.Implicature.Basic
import Linglib.Theories.Semantics.Alternatives.Lexical
import Linglib.Theories.Semantics.Entailment.Polarity

/-!
# Generic Scalar Implicature Helpers
@cite{geurts-2010}

Generic scalar-implicature computation built on `HornScale` (from
`Theories/Semantics/Alternatives/Lexical.lean`) and contextual polarity
(from `Theories/Semantics/Entailment/Polarity.lean`).

## Key operations

- `scaleAlternatives`: filter Horn-scale members by polarity, returning the
  context-appropriate alternatives (UE: stronger; DE: weaker; NM: none).
- `quantImplicatureArises`: does a particular alternative arise as a scalar
  implicature for a given quantifier in context?
- `deriveScalarImplicatures` / `deriveFromWords` / `hasImplicature`:
  produce the negation-of-stronger-alternative implicatures from a scalar
  term and scan a word list for them.

## Scope

Generic infrastructure only — no paper-specific worked examples. Examples
live in the `Phenomena/ScalarImplicatures/Studies/*.lean` files that
exercise this API (e.g., `GeurtsPouscoulous2009.lean`).

Scale semantics (`SemanticScale`, `HurfordSemantic`, `SinghSemantic`) and
exhaustification predictions live in `Alternatives/Lexical.lean` and
`Exhaustification/ScalePredictions.lean`.
-/

namespace Implicature.Scales

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


-- ============================================================
-- Disjunction Inferences (Exclusivity vs Ignorance)
-- ============================================================

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
  deriving DecidableEq, Repr

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


-- ============================================================
-- Long Disjunction Problem (@cite{geurts-2010} p.61-64)
-- ============================================================

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


-- ============================================================
-- Complete Implicature Derivation
-- ============================================================

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


-- ============================================================
-- Word-driven Derivation
-- ============================================================

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

end Implicature.Scales
