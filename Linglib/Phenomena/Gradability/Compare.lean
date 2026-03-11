import Linglib.Theories.Semantics.Supervaluation.Basic
import Linglib.Theories.Semantics.Supervaluation.TCS

/-!
# Vagueness Theory Comparison
@cite{keefe-2000} @cite{williamson-1994}

Theory-comparative infrastructure for vagueness: characterizes what each major
theoretical position (epistemicism, supervaluationism, degree theory, contextualism)
predicts about borderline cases, sorites, higher-order vagueness, and classical logic.

This is cross-theory comparison, not empirical data — hence lives in `Comparisons/`
rather than `Phenomena/`.

-/

namespace Phenomena.Gradability.Compare

/--
Major theoretical positions on vagueness.

This is a theory-neutral characterization of what each position claims.

Source: @cite{keefe-2000}, @cite{williamson-1994}
-/
inductive VaguenessTheoryType where
  | epistemicism       -- Sharp boundaries exist but are unknowable
  | supervaluationism  -- Truth = truth on all precisifications
  | degreeTheory       -- Truth comes in degrees (fuzzy logic)
  | contextualism      -- Vagueness = context-sensitivity
  | nihilism           -- Vague predicates have no extension
  | tcs                -- Three notions of truth + non-transitive st-consequence
  deriving Repr, DecidableEq, BEq

/--
Data characterizing what each theory says about key phenomena.

This allows us to track which theories predict which patterns.

Source: @cite{keefe-2000}
-/
structure TheoryPredictionProfile where
  theory : VaguenessTheoryType
  hasSharpBoundaries : Bool
  preservesClassicalLogic : Bool
  allowsTruthValueGaps : Bool
  allowsDegreesOfTruth : Bool
  soritesResolution : String
  higherOrderResponse : String
  deriving Repr

def epistemicismProfile : TheoryPredictionProfile :=
  { theory := .epistemicism
  , hasSharpBoundaries := true
  , preservesClassicalLogic := true
  , allowsTruthValueGaps := false
  , allowsDegreesOfTruth := false
  , soritesResolution := "One premise is false; we just don't know which"
  , higherOrderResponse := "Sharp boundary exists; we don't know where"
  }

def supervaluationismProfile : TheoryPredictionProfile :=
  { theory := .supervaluationism
  , hasSharpBoundaries := false  -- no single boundary
  , preservesClassicalLogic := true  -- globally
  , allowsTruthValueGaps := true  -- borderline cases
  , allowsDegreesOfTruth := false
  , soritesResolution := "Induction premise is super-false (false on some precisification)"
  , higherOrderResponse := "Problematic - precisifications may themselves be vague"
  }

def degreeTheoryProfile : TheoryPredictionProfile :=
  { theory := .degreeTheory
  , hasSharpBoundaries := false
  , preservesClassicalLogic := false  -- LEM fails locally
  , allowsTruthValueGaps := false
  , allowsDegreesOfTruth := true
  , soritesResolution := "Each step slightly lowers truth value; cumulative effect is large"
  , higherOrderResponse := "Can iterate degrees: degree of being degree 0.5 tall"
  }

def contextualismProfile : TheoryPredictionProfile :=
  { theory := .contextualism
  , hasSharpBoundaries := true  -- in each context
  , preservesClassicalLogic := true
  , allowsTruthValueGaps := false
  , allowsDegreesOfTruth := false
  , soritesResolution := "Context shifts mid-argument, making it equivocal"
  , higherOrderResponse := "Higher-order vagueness = higher-order context-sensitivity"
  }

/-- TCS (@cite{cobreros-etal-2012}): similarity-based semantics with
    three notions of truth (tolerant, classical, strict) and non-transitive
    st-consequence. Distinct from supervaluationism: allows borderline
    contradictions (Pa ∧ ¬Pa tolerantly true). -/
def tcsProfile : TheoryPredictionProfile :=
  { theory := .tcs
  , hasSharpBoundaries := false  -- no sharp boundary; borderline region
  , preservesClassicalLogic := false  -- st-consequence is non-transitive
  , allowsTruthValueGaps := true  -- borderline cases: tolerant P ∧ tolerant ¬P
  , allowsDegreesOfTruth := false  -- three truth *statuses*, not degrees
  , soritesResolution := "st-consequence validates each tolerance step but blocks chaining (non-transitivity)"
  , higherOrderResponse := "Borderline of borderline = second-order similarity; not explored in the 2012 paper"
  }

def theoryProfiles : List TheoryPredictionProfile :=
  [epistemicismProfile, supervaluationismProfile, degreeTheoryProfile,
   contextualismProfile, tcsProfile]

-- ════════════════════════════════════════════════════
-- § Verification: Supervaluationism backed by proofs
-- ════════════════════════════════════════════════════

/-! The supervaluationism profile's claims are backed by formal proofs in
    `Theories/Semantics/Supervaluation/Basic.lean`:

    - `preservesClassicalLogic = true`: super-validity ↔ classical validity
    - `allowsTruthValueGaps = true`: indefiniteness ↔ witnesses on both sides
    - `soritesResolution`: tolerance premise fails at every threshold boundary

    These verification theorems re-export the key results, making the
    connection between the comparison profile and the proved framework
    explicit and machine-checkable. -/

open Core.Duality (Truth3)
open Semantics.Supervaluation

/-- Classical logic preservation: super-validity ↔ classical validity.
    The supervaluationism profile claims `preservesClassicalLogic = true`;
    this theorem proves the claim. -/
theorem supervaluationism_classical_verified {Spec : Type*} [DecidableEq Spec]
    (eval : Spec → Bool) :
    (∀ S : SpecSpace Spec, superTrue eval S = Truth3.true) ↔ (∀ s, eval s = true) :=
  superValid_iff_classical eval

/-- Truth-value gaps: indefiniteness ↔ witnesses exist on both sides.
    The supervaluationism profile claims `allowsTruthValueGaps = true`;
    this theorem proves gap existence is well-defined. -/
theorem supervaluationism_gaps_verified {Spec : Type*}
    (eval : Spec → Bool) (S : SpecSpace Spec) :
    superTrue eval S = Truth3.indet ↔
    (∃ s ∈ S.admissible, eval s = true) ∧ (∃ s ∈ S.admissible, eval s = false) :=
  superTrue_indet_iff eval S

/-- Consequence preservation: super-consequence ↔ classical consequence.
    Supervaluationism makes a difference to truth but not to logic. -/
theorem supervaluationism_consequence_verified {Spec : Type*} [DecidableEq Spec]
    (evalA evalB : Spec → Bool) :
    superConsequence evalA evalB ↔ (∀ s, evalA s = true → evalB s = true) :=
  superConsequence_iff_classical evalA evalB

/-- The D operator eliminates borderline cases: DA → A is super-valid
    (T axiom), but A → DA is not. -/
theorem supervaluationism_D_verified {Spec : Type*}
    (eval : Spec → Bool) (S : SpecSpace Spec) :
    superTrue (fun s => !definitely eval S || eval s) S = Truth3.true :=
  D_implies_A eval S

-- ════════════════════════════════════════════════════
-- § TCS verification: backed by formal proofs
-- ════════════════════════════════════════════════════

/-! The TCS profile's claims are backed by formal proofs in
    `Theories/Semantics/Supervaluation/TCS.lean`:

    - `allowsTruthValueGaps = true`: borderline cases exist and
      tolerantly satisfy contradictions
    - `soritesResolution`: st-consequence blocks sorites chaining
      (non-transitivity demonstrated on concrete model)
    - `preservesClassicalLogic = false`: st-consequence is non-transitive

    These verification theorems re-export the key results. -/

open Semantics.Supervaluation.TCS

/-- TCS allows borderline contradictions: in the 4-element sorites
    model, borderline individuals tolerantly satisfy P ∧ ¬P. -/
theorem tcs_borderline_contradiction_verified :
    isBorderline soritesModel .tall .b = true ∧
    isBorderline soritesModel .tall .c = true :=
  ⟨b_is_borderline, c_is_borderline⟩

/-- TCS resolves the sorites: the full chain is st-invalid. -/
theorem tcs_sorites_resolution_verified :
    ¬tcsConsequence (D := Elt) (Pred := VPred) .strict .tolerant
      [.atom .tall .a] (.atom .tall .d) :=
  sorites_chain_invalid

/-- TCS validates tolerance: the extension hierarchy s ⊆ c ⊆ t. -/
theorem tcs_hierarchy_verified :
    ∀ (M : TModel Elt VPred) (φ : TCSFormula VPred Elt),
      (sat M .strict φ = true → sat M .classical φ = true) ∧
      (sat M .classical φ = true → sat M .tolerant φ = true) :=
  fun M φ => sat_hierarchy M φ

end Phenomena.Gradability.Compare
