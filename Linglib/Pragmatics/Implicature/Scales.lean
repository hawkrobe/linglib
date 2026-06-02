import Linglib.Pragmatics.Implicature.Basic
import Linglib.Semantics.Alternatives.Lexical
import Linglib.Semantics.Entailment.Polarity

/-!
# Generic Scalar Implicature Helpers
[geurts-2010]

Generic scalar-implicature computation built on `HornScale` (from
`Semantics/Alternatives/Lexical.lean`) and contextual polarity
(from `Semantics/Entailment/Polarity.lean`).

## Key operations

- `scaleAlternatives`: filter Horn-scale members by polarity, returning the
  context-appropriate alternatives (UE: stronger; DE: weaker; NM: none).
- `quantImplicatureArises`: does a particular alternative arise as a scalar
  implicature for a given quantifier in context?
- `deriveScalarImplicatures` / `deriveFromWords` / `hasImplicature`:
  produce the negation-of-stronger-alternative implicatures from a scalar
  term and scan a word list for them.

## Scope

Generic infrastructure only — no paper-specific worked examples. Worked
examples live in the `Studies/*.lean`
files that exercise this API.

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

/-- Does an alternative arise as a scalar implicature of a quantifier term?
    True iff `alt` is among the polarity-appropriate Horn-scale alternatives
    of `term`. -/
def QuantImplicatureArises (term alt : QuantExpr) (ctx : ContextPolarity) : Prop :=
  toString alt ∈ scaleAlternatives (.quantifier term) ctx

instance (term alt : QuantExpr) (ctx : ContextPolarity) :
    Decidable (QuantImplicatureArises term alt ctx) :=
  inferInstanceAs (Decidable (_ ∈ _))


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
Does any implicature in the results negate a given alternative?
-/
def HasImplicature (results : List ScalarImplicatureResult) (alt : String) : Prop :=
  ∃ r ∈ results, s!"not({alt})" ∈ r.implicatures

instance (results : List ScalarImplicatureResult) (alt : String) :
    Decidable (HasImplicature results alt) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

end Implicature.Scales
