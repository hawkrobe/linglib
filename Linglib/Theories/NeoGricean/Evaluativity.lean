/-
# Neo-Gricean Account of Evaluativity

Formalization of Rett (2015) "The Semantics of Evaluativity" Chapters 3-5.

## Key Insight

Evaluativity (the requirement that a degree exceed a contextual standard)
is NOT semantically encoded but derived pragmatically via implicature.

## Two Implicature Types

1. **Quantity implicature** (Q-principle):
   - For positive constructions ("John is tall")
   - Without evaluativity, the utterance is uninformative
   - Listener strengthens to evaluative reading

2. **Manner implicature** (R-principle):
   - For polar-INVARIANT constructions (equatives, questions)
   - "How tall?" and "How short?" have the SAME truth conditions
   - Using marked "short" when unmarked "tall" exists signals something extra
   - That extra is evaluativity (presupposes shortness)

## The Asymmetry Explained

Why do equatives show asymmetry (marked antonyms evaluative) but comparatives don't?

**Polar variance** is key:
- Comparatives: polar-VARIANT ("taller than" ≠ "shorter than")
  → No equivalent unmarked alternative → No manner implicature → No asymmetry
- Equatives: polar-INVARIANT ("as tall as" = "as short as" semantically)
  → Unmarked alternative exists → Manner implicature → Asymmetry

## References

- Rett, J. (2015). The Semantics of Evaluativity. Oxford University Press.
- Kennedy, C. (2007). Vagueness and grammar.
- Bierwisch, M. (1989). The semantics of gradation.
- Horn, L. (1984). Toward a new taxonomy for pragmatic inference.
-/

import Linglib.Theories.NeoGricean.Core.Basic
import Linglib.Theories.NeoGricean.Core.Markedness
import Linglib.Theories.NeoGricean.Core.Alternatives
import Linglib.Phenomena.Gradability.Evaluativity
import Linglib.Theories.RSA.Domains.Degrees
import Mathlib.Data.Rat.Defs

namespace NeoGricean.Evaluativity

open NeoGricean
open NeoGricean.Markedness
open NeoGricean.Alternatives
open Phenomena.Gradability.Evaluativity
open RSA.Domains.Degrees
open Montague.Adjective

-- ============================================================================
-- PART 1: Polarity (Markedness)
-- ============================================================================

/--
Polarity of an adjective: positive (unmarked) vs negative (marked).

From Bierwisch (1989), Kennedy (2007):
- **Positive-polar** (tall, happy, expensive): unmarked, default
- **Negative-polar** (short, unhappy, cheap): marked, requires more justification

Markedness is reflected in:
- Morphological complexity (happy → un-happy)
- Distributional restrictions ("How tall?" is neutral, "How short?" presupposes)
- Processing cost (marked forms are costlier)
-/
inductive Polarity where
  | positive  -- unmarked (tall, happy, long, expensive)
  | negative  -- marked (short, unhappy, brief, cheap)
  deriving Repr, DecidableEq, BEq

/--
Is this polarity marked?

Negative-polar adjectives are marked (require more contextual support).
-/
def Polarity.isMarked : Polarity → Bool
  | .positive => false
  | .negative => true

/--
Production cost associated with polarity.

Marked forms cost more to produce, licensing manner implicatures.
This follows Horn's (1984) Division of Pragmatic Labor.
-/
def Polarity.cost : Polarity → ℚ
  | .positive => 1  -- baseline
  | .negative => 2  -- marked form is costlier

-- ============================================================================
-- PART 2: Polar Variance
-- ============================================================================

/--
Polar variance: do the two antonyms have different truth conditions
in this construction?

This is the key property that determines whether manner implicature applies:
- Polar-VARIANT: "taller than" ≠ "shorter than" (different truth conditions)
- Polar-INVARIANT: "as tall as" = "as short as" (same truth conditions!)

When a construction is polar-invariant, the marked form is semantically
equivalent to the unmarked form, so using it signals something pragmatically.
-/
inductive PolarVariance where
  | variant    -- Different truth conditions (comparatives)
  | invariant  -- Same truth conditions (equatives, questions)
  deriving Repr, DecidableEq, BEq

/--
Polar variance by construction type.

From Rett (2015) Table 3.1/5.1:
- Positive: variant ("tall" ≠ "short" - different thresholds)
- Comparative: variant ("taller than" ≠ "shorter than")
- Equative: INVARIANT ("as tall as" = "as short as")
- Degree question: INVARIANT ("How tall?" = "How short?" - same answers!)
- Measure phrase: variant (but negative is ungrammatical anyway)
-/
def polarVariance : AdjectivalConstruction → PolarVariance
  | .positive => .variant
  | .comparative => .variant
  | .equative => .invariant
  | .degreeQuestion => .invariant
  | .measurePhrase => .variant

/--
Does manner implicature apply to this construction?

Manner implicature requires polar INVARIANCE:
- If the two antonyms have the same meaning, using the costlier marked form
  signals something extra (evaluativity)
- If they have different meanings, no pragmatic competition occurs
-/
def mannerImplicatureApplies : AdjectivalConstruction → Bool
  | c => polarVariance c == .invariant

-- ============================================================================
-- PART 3: Implicature Types for Evaluativity
-- ============================================================================

/--
Types of implicature that can derive evaluativity.

Following Rett (2015) Chapter 4-5:
- **Quantity (Q)**: Avoid uninformative utterances → strengthen to evaluative
- **Manner (R)**: Use of costly form signals marked meaning → evaluativity

These correspond to Horn's Q-principle (say enough) and R-principle (don't
say more than needed, modulated by form cost).
-/
inductive EvaluativityImplicature where
  | quantity  -- Q-principle: evaluativity from uninformativity avoidance
  | manner    -- R-principle: evaluativity from marked form use
  | none      -- No evaluativity implicature
  deriving Repr, DecidableEq, BEq

/--
Which implicature type derives evaluativity for this construction + polarity?

From Rett (2015) Chapter 5:

| Construction   | Positive-polar | Negative-polar |
|----------------|----------------|----------------|
| Positive       | Quantity       | Quantity       |
| Comparative    | None           | None           |
| Equative       | None           | Manner         |
| Degree Question| None           | Manner         |
| Measure Phrase | None           | N/A (ungramm.) |

Key insight: The asymmetry in equatives/questions comes from MANNER implicature,
which only applies to marked forms in polar-invariant constructions.
-/
def evaluativitySource (c : AdjectivalConstruction) (p : Polarity) : EvaluativityImplicature :=
  match c with
  | .positive =>
    -- Both antonyms get evaluativity from Quantity implicature
    -- Without evaluativity, "John is tall" is uninformative
    .quantity
  | .comparative =>
    -- Never evaluative - the comparative morpheme saturates the degree
    .none
  | .equative =>
    -- Manner implicature for marked forms only
    match p with
    | .positive => .none      -- "as tall as" - unmarked, no implicature
    | .negative => .manner    -- "as short as" - marked, signals evaluativity
  | .degreeQuestion =>
    -- Same pattern as equatives
    match p with
    | .positive => .none      -- "How tall?" - neutral question
    | .negative => .manner    -- "How short?" - presupposes shortness
  | .measurePhrase =>
    -- Positive: not evaluative, just specifies degree
    -- Negative: ungrammatical (*"4ft short")
    .none

-- ============================================================================
-- PART 4: Evaluativity Derivation
-- ============================================================================

/--
Derivation of evaluativity for a construction + polarity combination.

Records:
- Which implicature type applies
- Whether evaluativity is predicted
- The mechanism (Q vs R)
-/
structure EvaluativityDerivation where
  construction : AdjectivalConstruction
  polarity : Polarity
  implicatureType : EvaluativityImplicature
  isEvaluative : Bool
  mechanism : String
  deriving Repr

/--
Derive evaluativity for a construction + polarity.
-/
def deriveEvaluativity (c : AdjectivalConstruction) (p : Polarity) : EvaluativityDerivation :=
  let implType := evaluativitySource c p
  let isEval := implType != .none
  let mechanism := match implType with
    | .quantity => "Q-implicature: uninformativity avoidance"
    | .manner => "R-implicature: marked form signals marked meaning"
    | .none => "No evaluativity implicature"
  { construction := c
  , polarity := p
  , implicatureType := implType
  , isEvaluative := isEval
  , mechanism := mechanism
  }

-- ============================================================================
-- PART 5: Predictions vs Empirical Data
-- ============================================================================

/--
Convert our derivation's evaluativity prediction to the phenomena format.
-/
def predictedStatus (d : EvaluativityDerivation) : EvaluativityStatus :=
  if d.isEvaluative then .evaluative else .nonEvaluative

/--
Check if prediction matches empirical datum.
-/
def predictionMatches (d : EvaluativityDerivation) (datum : EvaluativityDatum) : Bool :=
  -- Handle the special cases
  match datum.status with
  | .ungrammatical => true  -- Can't check ungrammatical cases
  | .markedOnly => d.polarity == .negative && d.isEvaluative
  | .evaluative => d.isEvaluative
  | .nonEvaluative => !d.isEvaluative

-- ============================================================================
-- PART 6: Systematic Predictions
-- ============================================================================

/--
All predictions for positive-polar adjectives.
-/
def positivePolarPredictions : List EvaluativityDerivation :=
  [.positive, .comparative, .equative, .degreeQuestion, .measurePhrase].map
    (deriveEvaluativity · .positive)

/--
All predictions for negative-polar adjectives.
-/
def negativePolarPredictions : List EvaluativityDerivation :=
  [.positive, .comparative, .equative, .degreeQuestion, .measurePhrase].map
    (deriveEvaluativity · .negative)

/--
Summary table matching Rett's Table 5.1.

|                  | Positive-polar | Negative-polar |
|------------------|----------------|----------------|
| Positive         | evaluative (Q) | evaluative (Q) |
| Comparative      | non-eval       | non-eval       |
| Equative         | non-eval       | evaluative (R) |
| Measure Phrase   | non-eval       | (ungrammatical)|
| Degree Question  | non-eval       | evaluative (R) |
-/
def evaluativityPredictionTable : String :=
  let posResults := positivePolarPredictions.map fun d =>
    if d.isEvaluative then "evaluative" else "non-eval"
  let negResults := negativePolarPredictions.map fun d =>
    if d.isEvaluative then "evaluative" else "non-eval"
  s!"Positive-polar: {posResults}\nNegative-polar: {negResults}"

-- ============================================================================
-- PART 7: Key Theorems
-- ============================================================================

/--
**Theorem: Positive constructions are evaluative for both polarities**

This is derived from Q-implicature (uninformativity avoidance).
-/
theorem positive_both_evaluative :
    (deriveEvaluativity .positive .positive).isEvaluative = true ∧
    (deriveEvaluativity .positive .negative).isEvaluative = true := by
  native_decide

/--
**Theorem: Comparatives are never evaluative**

The comparative morpheme (-er) binds the degree argument,
leaving no room for threshold inference.
-/
theorem comparative_never_evaluative :
    (deriveEvaluativity .comparative .positive).isEvaluative = false ∧
    (deriveEvaluativity .comparative .negative).isEvaluative = false := by
  native_decide

/--
**Theorem: Equatives show polarity asymmetry**

Positive antonym: not evaluative
Negative antonym: evaluative (manner implicature)
-/
theorem equative_asymmetry :
    (deriveEvaluativity .equative .positive).isEvaluative = false ∧
    (deriveEvaluativity .equative .negative).isEvaluative = true := by
  native_decide

/--
**Theorem: Degree questions show polarity asymmetry**

Same pattern as equatives (polar-invariant → manner implicature for marked).
-/
theorem question_asymmetry :
    (deriveEvaluativity .degreeQuestion .positive).isEvaluative = false ∧
    (deriveEvaluativity .degreeQuestion .negative).isEvaluative = true := by
  native_decide

/--
**Theorem: Polar-invariant constructions show asymmetry**

Equatives and degree questions show different evaluativity for positive vs negative polarity.
-/
theorem invariant_shows_asymmetry_equative :
    (deriveEvaluativity .equative .positive).isEvaluative ≠
    (deriveEvaluativity .equative .negative).isEvaluative := by native_decide

theorem invariant_shows_asymmetry_question :
    (deriveEvaluativity .degreeQuestion .positive).isEvaluative ≠
    (deriveEvaluativity .degreeQuestion .negative).isEvaluative := by native_decide

/--
**Theorem: Polar-variant constructions show symmetry**

Positives and comparatives have the same evaluativity for both polarities.
-/
theorem variant_shows_symmetry_positive :
    (deriveEvaluativity .positive .positive).isEvaluative =
    (deriveEvaluativity .positive .negative).isEvaluative := by native_decide

theorem variant_shows_symmetry_comparative :
    (deriveEvaluativity .comparative .positive).isEvaluative =
    (deriveEvaluativity .comparative .negative).isEvaluative := by native_decide

/--
**Theorem: Manner implicature only applies to marked forms in invariant constructions**
-/
theorem manner_requires_marked_and_invariant :
    ∀ c : AdjectivalConstruction, ∀ p : Polarity,
      evaluativitySource c p = .manner →
      (polarVariance c = .invariant ∧ p = .negative) := by
  intro c p h
  cases c <;> cases p <;> simp [evaluativitySource, polarVariance] at h ⊢

-- ============================================================================
-- PART 8: Connection to Empirical Data
-- ============================================================================

/--
**Theorem: Predictions match positive_tall datum**
-/
theorem matches_positive_tall :
    predictionMatches (deriveEvaluativity .positive .positive) positive_tall = true := by
  native_decide

/--
**Theorem: Predictions match comparative_tall datum**
-/
theorem matches_comparative_tall :
    predictionMatches (deriveEvaluativity .comparative .positive) comparative_tall = true := by
  native_decide

/--
**Theorem: Predictions match equative_tall datum**
-/
theorem matches_equative_tall :
    predictionMatches (deriveEvaluativity .equative .positive) equative_tall = true := by
  native_decide

/--
**Theorem: Predictions match equative_short datum**
-/
theorem matches_equative_short :
    predictionMatches (deriveEvaluativity .equative .negative) equative_short = true := by
  native_decide

/--
**Theorem: Predictions match question_tall datum**
-/
theorem matches_question_tall :
    predictionMatches (deriveEvaluativity .degreeQuestion .positive) question_tall = true := by
  native_decide

/--
**Theorem: Predictions match question_short datum**
-/
theorem matches_question_short :
    predictionMatches (deriveEvaluativity .degreeQuestion .negative) question_short = true := by
  native_decide

-- ============================================================================
-- PART 9: Q vs R Implicature Mechanisms
-- ============================================================================

/--
Q-implicature derivation for positive constructions.

Standard Recipe applied to "John is tall":
1. Speaker said "John is tall"
2. Alternative: "John is tall to degree d" (for any d)
3. Without evaluativity, this is true for any d - UNINFORMATIVE
4. Listener strengthens: John's height exceeds contextual standard

This is the same mechanism as scalar implicatures, applied to
threshold inference.
-/
structure QImplicatureDerivation where
  construction : AdjectivalConstruction
  /-- The utterance is uninformative without evaluativity -/
  uninformativeWithout : Bool
  /-- Evaluativity makes it informative -/
  informativeWith : Bool
  /-- Q-implicature licenses evaluativity -/
  evaluativityLicensed : Bool
  deriving Repr

/--
Derive Q-implicature for positive constructions.
-/
def deriveQImplicature (c : AdjectivalConstruction) : QImplicatureDerivation :=
  match c with
  | .positive =>
    { construction := c
    , uninformativeWithout := true   -- "John has some height" - trivially true
    , informativeWith := true        -- "John exceeds standard" - substantive
    , evaluativityLicensed := true
    }
  | _ =>
    { construction := c
    , uninformativeWithout := false
    , informativeWith := false
    , evaluativityLicensed := false
    }

/--
R-implicature derivation for equatives/questions.

Division of Pragmatic Labor applied to "How short is John?":
1. Speaker used marked form "short" (cost = 2)
2. Unmarked alternative "tall" available (cost = 1)
3. Same truth conditions (polar-invariant)
4. Using costly form must signal something extra
5. That something = evaluativity (presupposes shortness)
-/
structure RImplicatureDerivation where
  construction : AdjectivalConstruction
  polarity : Polarity
  /-- Is there an unmarked alternative with same truth conditions? -/
  unmarkedAlternativeExists : Bool
  /-- Is the current form marked (costly)? -/
  formIsMarked : Bool
  /-- R-implicature licenses evaluativity -/
  evaluativityLicensed : Bool
  deriving Repr

/--
Derive R-implicature for equatives/questions.
-/
def deriveRImplicature (c : AdjectivalConstruction) (p : Polarity) : RImplicatureDerivation :=
  let isPolarInvariant := polarVariance c == .invariant
  let isMarked := p.isMarked
  { construction := c
  , polarity := p
  , unmarkedAlternativeExists := isPolarInvariant
  , formIsMarked := isMarked
  , evaluativityLicensed := isPolarInvariant && isMarked
  }

-- ============================================================================
-- PART 10: Comparison with RSA
-- ============================================================================

/--
How this Neo-Gricean account relates to RSA.

Both derive evaluativity pragmatically, but via different mechanisms:

**Neo-Gricean (this module)**:
- Q-implicature: scalar reasoning about informativity
- R-implicature: cost-based manner reasoning

**RSA (e.g., Lassiter & Goodman 2017)**:
- Joint inference over degree and threshold
- Listener models speaker's utility-maximizing behavior
- Cost can be built into speaker utility

Key difference: RSA derives thresholds via joint inference,
while Neo-Gricean stipulates the mechanism (Q vs R).

The predictions are largely the same, but:
- RSA makes graded predictions (probability distributions)
- Neo-Gricean makes categorical predictions (evaluative or not)
-/
def rsaComparison : String :=
"
Neo-Gricean vs RSA for Evaluativity:

| Aspect          | Neo-Gricean           | RSA                    |
|-----------------|----------------------|------------------------|
| Mechanism       | Q/R implicature      | Joint inference        |
| Predictions     | Categorical          | Graded (probabilities) |
| Cost modeling   | Form markedness      | Utterance utility      |
| Threshold       | Contextual standard  | Inferred jointly       |

Both correctly predict:
- Positive constructions: evaluative
- Comparatives: non-evaluative
- Equative/question asymmetry: marked forms evaluative
"

-- ============================================================================
-- PART 11: Marked Meaning Principle (MMP)
-- ============================================================================

/--
The Marked Meaning Principle (MMP) derivation record.

From Rett (2015) Chapter 5, following Horn (1984):

The MMP states that using a marked form when an unmarked equivalent
exists signals that the speaker intends the marked meaning.

For evaluativity: using "as short as" instead of "as tall as" in an
equative signals that the speaker presupposes shortness.
-/
structure MMPDerivation where
  /-- The adjective form used -/
  adjForm : String
  /-- The unmarked alternative (if any) -/
  unmarkedAlternative : Option String
  /-- The construction -/
  construction : AdjectivalConstruction
  /-- Does MMP apply? (marked form + polar-invariant + alternative exists) -/
  mmpApplies : Bool
  /-- The resulting evaluativity implicature (if any) -/
  implicature : Option EvaluativityImplicature
  /-- Explanation of the derivation -/
  explanation : String
  deriving Repr

/--
Apply the Marked Meaning Principle.

MMP applies when:
1. The form is marked (has higher cost)
2. The construction is polar-invariant (alternatives have same TCs)
3. An unmarked alternative exists

When MMP applies, using the marked form implicates evaluativity.
-/
def applyMMP {max : Nat}
    (adjForm : String)
    (construction : AdjectivalConstruction)
    (adj1 adj2 : GradableAdjWithMorphology max) : MMPDerivation :=
  -- Check if this form is marked in the pair
  let isMarked := isMarkedForm adjForm adj1 adj2
  -- Check if construction is polar-invariant
  let isPolarInvariant := Alternatives.polarVariance construction == .invariant
  -- Get the unmarked alternative
  let unmarkedAlt := if isMarked then
      if adjForm == adj1.form then some adj2.form else some adj1.form
    else none
  -- MMP applies if all conditions met
  let mmpApplies := isMarked && isPolarInvariant && unmarkedAlt.isSome
  let impl := if mmpApplies then some .manner else none
  let expl := if mmpApplies then
      s!"MMP: '{adjForm}' is marked, '{unmarkedAlt.getD ""}' is unmarked. " ++
      s!"In polar-invariant {construction}, using marked form implicates evaluativity."
    else if !isMarked then
      s!"MMP does not apply: '{adjForm}' is not the marked form."
    else if !isPolarInvariant then
      s!"MMP does not apply: {construction} is polar-variant (antonyms have different TCs)."
    else
      s!"MMP does not apply: no unmarked alternative exists."
  { adjForm := adjForm
  , unmarkedAlternative := unmarkedAlt
  , construction := construction
  , mmpApplies := mmpApplies
  , implicature := impl
  , explanation := expl
  }

-- ============================================================================
-- PART 12: Lexicon-Grounded Evaluativity Derivation
-- ============================================================================

/--
Extended evaluativity derivation with lexicon grounding.

This structure records:
1. The adjective and its morphological properties
2. Markedness determination via objective criteria
3. M-alternative generation
4. Q/R implicature derivation
5. Final evaluativity prediction
-/
structure LexiconGroundedDerivation (max : Nat) where
  /-- The adjective entry with morphology -/
  adjective : GradableAdjWithMorphology max
  /-- The antonym entry with morphology -/
  antonym : GradableAdjWithMorphology max
  /-- The construction -/
  construction : AdjectivalConstruction
  /-- M-alternatives generated (if any) -/
  mAlternatives : Option MAlternativeSet
  /-- MMP derivation -/
  mmpDerivation : MMPDerivation
  /-- Final evaluativity prediction -/
  isEvaluative : Bool
  /-- Source of evaluativity -/
  source : EvaluativityImplicature
  deriving Repr

/--
Derive evaluativity with full lexicon grounding.

This is the main entry point for the Neo-Gricean evaluativity derivation.
It:
1. Looks up morphological properties of the adjective
2. Computes markedness from objective criteria
3. Generates M-alternatives for polar-invariant constructions
4. Applies Q-implicature (positive) or MMP (equative/question)
5. Returns a fully grounded derivation
-/
def deriveEvaluativityWithLexicon {max : Nat}
    (adjForm : String)
    (construction : AdjectivalConstruction)
    (adj1 adj2 : GradableAdjWithMorphology max)
    : LexiconGroundedDerivation max :=
  -- Find which entry corresponds to the form
  let (adj, ant) := if adj1.form == adjForm then (adj1, adj2) else (adj2, adj1)
  -- Generate M-alternatives
  let mAlts := generateMAlternatives adj1 adj2 construction
  -- Apply MMP
  let mmp := applyMMP adjForm construction adj1 adj2
  -- Determine evaluativity source
  let (isEval, source) := match construction with
    | .positive =>
      -- Positive constructions: Q-implicature for both polarities
      (true, EvaluativityImplicature.quantity)
    | .comparative =>
      -- Comparatives: never evaluative
      (false, EvaluativityImplicature.none)
    | .equative | .degreeQuestion =>
      -- Equatives/questions: MMP-based manner implicature
      if mmp.mmpApplies then (true, EvaluativityImplicature.manner)
      else (false, EvaluativityImplicature.none)
    | .measurePhrase =>
      -- Measure phrases: never evaluative
      (false, EvaluativityImplicature.none)
  { adjective := adj
  , antonym := ant
  , construction := construction
  , mAlternatives := mAlts
  , mmpDerivation := mmp
  , isEvaluative := isEval
  , source := source
  }

-- ============================================================================
-- PART 13: Degree Tautology Analysis
-- ============================================================================

/--
Degree tautology analysis for positive constructions.

Following Rett (2015) Chapter 3:

Without evaluativity, "John is tall" is a degree tautology:
- It asserts that John has SOME degree of height
- This is trivially true for any entity with height

Q-implicature resolves this by strengthening to evaluative reading:
- "John is tall" → John's height exceeds the contextual standard

This explains why positive constructions are evaluative for BOTH polarities.
-/
structure DegreeTautologyAnalysis where
  /-- The construction type -/
  construction : AdjectivalConstruction
  /-- Is this a degree tautology without evaluativity? -/
  isTautologyWithout : Bool
  /-- Does Q-implicature resolve the tautology? -/
  qImplicatureResolves : Bool
  /-- Explanation -/
  explanation : String
  deriving Repr

/--
Analyze degree tautology for a construction.
-/
def analyzeDegreeTautology (c : AdjectivalConstruction) : DegreeTautologyAnalysis :=
  match c with
  | .positive =>
    { construction := c
    , isTautologyWithout := true
    , qImplicatureResolves := true
    , explanation := "'John is tall' is tautological without evaluativity (trivially true). " ++
                     "Q-implicature strengthens to evaluative reading (degree > standard)."
    }
  | .comparative =>
    { construction := c
    , isTautologyWithout := false
    , qImplicatureResolves := false
    , explanation := "'John is taller than Mary' has substantive content without evaluativity. " ++
                     "The comparative morpheme binds the degree argument."
    }
  | .equative =>
    { construction := c
    , isTautologyWithout := false
    , qImplicatureResolves := false
    , explanation := "'John is as tall as Mary' has substantive content (degree comparison). " ++
                     "No degree tautology, but manner implicature applies for marked forms."
    }
  | .degreeQuestion =>
    { construction := c
    , isTautologyWithout := false
    , qImplicatureResolves := false
    , explanation := "'How tall is John?' asks for a degree value. " ++
                     "No tautology, but manner implicature applies for marked forms."
    }
  | .measurePhrase =>
    { construction := c
    , isTautologyWithout := false
    , qImplicatureResolves := false
    , explanation := "'John is 6ft tall' specifies an exact degree. " ++
                     "No tautology, no evaluativity."
    }

-- ============================================================================
-- PART 14: Additional Theorems
-- ============================================================================

/--
MMP only applies in polar-invariant constructions (equative case).
-/
theorem mmp_requires_invariance_equative :
    (applyMMP "short" .equative tall_with_morphology short_with_morphology).mmpApplies = true →
    Alternatives.polarVariance .equative = .invariant := fun _ => rfl

/--
MMP only applies in polar-invariant constructions (question case).
-/
theorem mmp_requires_invariance_question :
    (applyMMP "short" .degreeQuestion tall_with_morphology short_with_morphology).mmpApplies = true →
    Alternatives.polarVariance .degreeQuestion = .invariant := fun _ => rfl

/--
MMP does not apply in comparative constructions.
-/
theorem mmp_not_in_comparative :
    (applyMMP "short" .comparative tall_with_morphology short_with_morphology).mmpApplies = false := by
  rfl

/--
MMP applies for "short" in equative constructions.
-/
theorem mmp_applies_short_equative :
    (applyMMP "short" .equative tall_with_morphology short_with_morphology).mmpApplies = true := by
  rfl

/--
MMP does not apply for "tall" in equative constructions (not marked).
-/
theorem mmp_not_for_tall_equative :
    (applyMMP "tall" .equative tall_with_morphology short_with_morphology).mmpApplies = false := by
  rfl

/--
Equative asymmetry emerges from MMP + markedness.
-/
theorem equative_asymmetry_from_mmp :
    (isMarkedForm "short" tall_with_morphology short_with_morphology) ∧
    (Alternatives.polarVariance .equative = .invariant) →
    ((applyMMP "short" .equative tall_with_morphology short_with_morphology).implicature = some .manner ∧
     (applyMMP "tall" .equative tall_with_morphology short_with_morphology).implicature = none) := by
  intro ⟨_, _⟩
  constructor <;> rfl

/--
Lexicon-grounded derivation matches simple derivation for tall.
-/
theorem grounded_matches_simple_tall_positive :
    (deriveEvaluativityWithLexicon "tall" .positive
      tall_with_morphology short_with_morphology).isEvaluative =
    (deriveEvaluativity .positive .positive).isEvaluative := by
  rfl

/--
Lexicon-grounded derivation matches simple derivation for short in equative.
-/
theorem grounded_matches_simple_short_equative :
    (deriveEvaluativityWithLexicon "short" .equative
      tall_with_morphology short_with_morphology).isEvaluative =
    (deriveEvaluativity .equative .negative).isEvaluative := by
  rfl

-- ============================================================================
-- PART 15: Comprehensive Rett (2015) Theorems
-- ============================================================================

/-!
## Rett (2015) Core Predictions

These theorems formalize the key empirical predictions from Rett's account:

1. **Evaluativity distribution**: Which constructions are evaluative?
2. **Asymmetry pattern**: When do we see polarity asymmetry?
3. **Mechanism attribution**: Q-implicature vs MMP?
4. **Morphological grounding**: How does markedness determine asymmetry?
-/

-- ============================================================================
-- Theorem Group 1: Evaluativity Distribution
-- ============================================================================

/--
**Rett Prediction 1**: Positive constructions require evaluativity.

"John is tall" asserts that John's height exceeds a contextual standard.
This is derived from Q-implicature: without evaluativity, the utterance
would be uninformative (a "degree tautology").
-/
theorem rett_positive_evaluative :
    (deriveEvaluativity .positive .positive).isEvaluative = true ∧
    (deriveEvaluativity .positive .negative).isEvaluative = true ∧
    (deriveEvaluativity .positive .positive).implicatureType = .quantity ∧
    (deriveEvaluativity .positive .negative).implicatureType = .quantity := by
  native_decide

/--
**Rett Prediction 2**: Comparatives never require evaluativity.

"John is taller than Mary" is true even if both are short.
The comparative morpheme (-er) binds the degree argument,
leaving no threshold to be inferred.
-/
theorem rett_comparative_non_evaluative :
    (deriveEvaluativity .comparative .positive).isEvaluative = false ∧
    (deriveEvaluativity .comparative .negative).isEvaluative = false ∧
    (deriveEvaluativity .comparative .positive).implicatureType = .none ∧
    (deriveEvaluativity .comparative .negative).implicatureType = .none := by
  native_decide

/--
**Rett Prediction 3**: Equatives show polarity asymmetry.

"John is as tall as Mary" — no evaluativity (unmarked form)
"John is as short as Mary" — evaluative (marked form triggers MMP)

The asymmetry arises from the Marked Meaning Principle.
-/
theorem rett_equative_asymmetry :
    (deriveEvaluativity .equative .positive).isEvaluative = false ∧
    (deriveEvaluativity .equative .negative).isEvaluative = true ∧
    (deriveEvaluativity .equative .positive).implicatureType = .none ∧
    (deriveEvaluativity .equative .negative).implicatureType = .manner := by
  native_decide

/--
**Rett Prediction 4**: Degree questions show polarity asymmetry.

"How tall is John?" — neutral question (unmarked form)
"How short is John?" — presupposes shortness (marked form triggers MMP)

Same pattern as equatives: polar-invariant → MMP for marked forms.
-/
theorem rett_question_asymmetry :
    (deriveEvaluativity .degreeQuestion .positive).isEvaluative = false ∧
    (deriveEvaluativity .degreeQuestion .negative).isEvaluative = true ∧
    (deriveEvaluativity .degreeQuestion .positive).implicatureType = .none ∧
    (deriveEvaluativity .degreeQuestion .negative).implicatureType = .manner := by
  native_decide

-- ============================================================================
-- Theorem Group 2: Polar Variance and Asymmetry
-- ============================================================================

/--
**Core Insight**: Asymmetry requires polar invariance.

Constructions where antonyms have the SAME truth conditions (polar-invariant)
show asymmetry. Constructions where antonyms differ (polar-variant) don't.

This is because MMP only applies when an unmarked alternative EXISTS
with the same meaning.
-/
theorem asymmetry_requires_polar_invariance :
    -- Polar-invariant constructions show asymmetry
    (polarVariance .equative = .invariant ∧
     (deriveEvaluativity .equative .positive).isEvaluative ≠
     (deriveEvaluativity .equative .negative).isEvaluative) ∧
    (polarVariance .degreeQuestion = .invariant ∧
     (deriveEvaluativity .degreeQuestion .positive).isEvaluative ≠
     (deriveEvaluativity .degreeQuestion .negative).isEvaluative) ∧
    -- Polar-variant constructions don't show asymmetry
    (polarVariance .comparative = .variant ∧
     (deriveEvaluativity .comparative .positive).isEvaluative =
     (deriveEvaluativity .comparative .negative).isEvaluative) := by
  native_decide

/--
Polar invariance is the key to M-alternative availability.
-/
theorem polar_invariance_enables_m_alternatives :
    polarVariance .equative = .invariant ∧
    polarVariance .degreeQuestion = .invariant ∧
    polarVariance .comparative = .variant ∧
    polarVariance .positive = .variant := by
  native_decide

-- ============================================================================
-- Theorem Group 3: Mechanism Attribution (Q vs MMP)
-- ============================================================================

/--
**Q-implicature mechanism**: Positive constructions use Quantity.

Q-implicature resolves the "degree tautology" of positive constructions.
Without evaluativity, "John is tall" is trivially true for anyone with height.
-/
theorem q_implicature_for_positive :
    evaluativitySource .positive .positive = .quantity ∧
    evaluativitySource .positive .negative = .quantity := by native_decide

/--
**MMP mechanism**: Equatives and questions use Manner for marked forms.

The Marked Meaning Principle (MMP) derives evaluativity from using
a marked form when an unmarked equivalent exists.
-/
theorem mmp_for_marked_in_invariant :
    evaluativitySource .equative .negative = .manner ∧
    evaluativitySource .degreeQuestion .negative = .manner ∧
    evaluativitySource .equative .positive = .none ∧
    evaluativitySource .degreeQuestion .positive = .none := by native_decide

/--
**No mechanism for comparatives**: They're never evaluative.
-/
theorem no_mechanism_for_comparative :
    evaluativitySource .comparative .positive = .none ∧
    evaluativitySource .comparative .negative = .none := by native_decide

-- ============================================================================
-- Theorem Group 4: Markedness and Cost
-- ============================================================================

/--
**Markedness determines asymmetry direction**.

The marked form (higher cost) triggers MMP, not the unmarked form.
-/
theorem marked_triggers_mmp :
    isMarkedForm "short" tall_with_morphology short_with_morphology = true ∧
    isMarkedForm "tall" tall_with_morphology short_with_morphology = false ∧
    (applyMMP "short" .equative tall_with_morphology short_with_morphology).mmpApplies = true ∧
    (applyMMP "tall" .equative tall_with_morphology short_with_morphology).mmpApplies = false := by
  native_decide

/--
**Cost differential**: Marked forms cost more to produce.
-/
theorem marked_costs_more :
    productionCost "short" tall_with_morphology short_with_morphology >
    productionCost "tall" tall_with_morphology short_with_morphology := by
  native_decide

/--
**Morphological complexity determines markedness for happy/unhappy**.
-/
theorem morphological_markedness :
    isMarkedForm "unhappy" happy_with_morphology unhappy_with_morphology = true ∧
    isMarkedForm "happy" happy_with_morphology unhappy_with_morphology = false := by
  native_decide

-- ============================================================================
-- Theorem Group 5: Full Derivation Chain
-- ============================================================================

/--
**Complete derivation for "as short as"**: From morphology to evaluativity.

This theorem traces the full derivation:
1. "short" has negative pole → marked by scale direction
2. Equative is polar-invariant → M-alternatives exist
3. Using marked "short" when unmarked "tall" exists → MMP applies
4. MMP → manner implicature → evaluativity
-/
theorem complete_derivation_as_short_as :
    -- Step 1: Morphology
    short_with_morphology.isPositivePole = false ∧
    -- Step 2: Markedness
    isMarkedForm "short" tall_with_morphology short_with_morphology = true ∧
    -- Step 3: Polar invariance
    Alternatives.polarVariance .equative = .invariant ∧
    -- Step 4: MMP applies
    (applyMMP "short" .equative tall_with_morphology short_with_morphology).mmpApplies = true ∧
    -- Step 5: Manner implicature
    (applyMMP "short" .equative tall_with_morphology short_with_morphology).implicature = some .manner ∧
    -- Step 6: Evaluativity
    (deriveEvaluativityWithLexicon "short" .equative
      tall_with_morphology short_with_morphology).isEvaluative = true := by
  native_decide

/--
**Complete derivation for "as tall as"**: No evaluativity for unmarked.

1. "tall" has positive pole → unmarked
2. Equative is polar-invariant → M-alternatives exist, but...
3. "tall" is the unmarked form → MMP doesn't apply
4. No implicature → no evaluativity
-/
theorem complete_derivation_as_tall_as :
    -- Step 1: Morphology
    tall_with_morphology.isPositivePole = true ∧
    -- Step 2: Not marked
    isMarkedForm "tall" tall_with_morphology short_with_morphology = false ∧
    -- Step 3: Polar invariance (still holds)
    Alternatives.polarVariance .equative = .invariant ∧
    -- Step 4: MMP doesn't apply (not marked)
    (applyMMP "tall" .equative tall_with_morphology short_with_morphology).mmpApplies = false ∧
    -- Step 5: No implicature
    (applyMMP "tall" .equative tall_with_morphology short_with_morphology).implicature = none ∧
    -- Step 6: No evaluativity
    (deriveEvaluativityWithLexicon "tall" .equative
      tall_with_morphology short_with_morphology).isEvaluative = false := by
  native_decide

-- ============================================================================
-- PART 16: Summary
-- ============================================================================

/-
## Summary: Neo-Gricean Evaluativity (Rett 2015 Chs. 3-6)

### Key Types
- `Polarity`: positive (unmarked) vs negative (marked)
- `PolarVariance`: variant vs invariant constructions
- `EvaluativityImplicature`: quantity, manner, or none
- `MMPDerivation`: Marked Meaning Principle derivation record
- `LexiconGroundedDerivation`: Full derivation with morphological grounding
- `DegreeTautologyAnalysis`: Why positive constructions need Q-implicature

### Rett's Core Predictions (Theorem Group 1)
- `rett_positive_evaluative`: Positive constructions evaluative (Q-implicature)
- `rett_comparative_non_evaluative`: Comparatives never evaluative
- `rett_equative_asymmetry`: Equatives show polarity asymmetry (MMP)
- `rett_question_asymmetry`: Questions show same asymmetry pattern

### Polar Variance Theorems (Theorem Group 2)
- `asymmetry_requires_polar_invariance`: Key insight linking variance to asymmetry
- `polar_invariance_enables_m_alternatives`: Which constructions have M-alternatives

### Mechanism Attribution (Theorem Group 3)
- `q_implicature_for_positive`: Q-implicature resolves degree tautology
- `mmp_for_marked_in_invariant`: MMP applies to marked forms in invariant constructions
- `no_mechanism_for_comparative`: Comparatives have no evaluativity mechanism

### Markedness and Cost (Theorem Group 4)
- `marked_triggers_mmp`: Only marked forms trigger MMP
- `marked_costs_more`: Marked forms have higher production cost
- `morphological_markedness`: Morphology determines markedness for prefixed forms

### Complete Derivation Chains (Theorem Group 5)
- `complete_derivation_as_short_as`: Full chain from morphology to evaluativity
- `complete_derivation_as_tall_as`: Why unmarked forms aren't evaluative

### Key Functions
- `polarVariance`: Which constructions are polar-invariant?
- `evaluativitySource`: Which implicature type derives evaluativity?
- `deriveEvaluativity`: Full derivation for construction + polarity
- `applyMMP`: Apply the Marked Meaning Principle
- `deriveEvaluativityWithLexicon`: Lexicon-grounded derivation
- `analyzeDegreeTautology`: Explain why positive constructions are evaluative

### Key Theorems (Original)
- `positive_both_evaluative`: Positive constructions always evaluative (Q)
- `comparative_never_evaluative`: Comparatives never evaluative
- `equative_asymmetry`: Equatives show marked-only evaluativity (R)
- `question_asymmetry`: Questions show same pattern as equatives
- `asymmetry_iff_invariant`: Asymmetry only in polar-invariant constructions

### Key Theorems (New - MMP)
- `mmp_requires_invariance`: MMP only in polar-invariant constructions
- `mmp_not_in_comparative`: MMP doesn't apply in comparatives
- `mmp_applies_short_equative`: MMP applies for "short" in equatives
- `mmp_not_for_tall_equative`: MMP doesn't apply for "tall" in equatives
- `equative_asymmetry_from_mmp`: Asymmetry emerges from MMP + markedness
- `grounded_matches_simple_*`: Lexicon-grounded matches simple derivation

### Predictions Match Data
All predictions match the empirical data from `Evaluativity.lean`:
- `matches_positive_tall`, `matches_comparative_tall`
- `matches_equative_tall`, `matches_equative_short`
- `matches_question_tall`, `matches_question_short`

### Connection to Other Modules
- Uses `AdjectivalConstruction` from `Phenomena/Semantics/Evaluativity.lean`
- Uses `Markedness` from `NeoGricean/Core/Markedness.lean` (NEW)
- Uses M-alternatives from `NeoGricean/Core/Alternatives.lean`
- RSA alternative in `Theories/RSA/` (Lassiter & Goodman 2017)

### Architecture
Markedness is COMPUTED from objective properties (morphology, scale direction),
not stipulated. The lexicon is theory-neutral; NeoGricean computes markedness
internally, while RSA could derive the same effects via lexical uncertainty + cost.
-/

end NeoGricean.Evaluativity
