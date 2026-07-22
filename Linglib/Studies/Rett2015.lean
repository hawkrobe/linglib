import Linglib.Pragmatics.NeoGricean.Markedness
import Linglib.Fragments.English.Predicates.Adjectival
import Linglib.Semantics.Degree.Adjective
import Linglib.Semantics.Degree.Basic
import Linglib.Semantics.Degree.Defs

/-!
# Rett (2015): evaluativity as implicature
[rett-2015] [horn-1984] [bierwisch-1989] [kennedy-2007]

This file formalizes [rett-2015]: the empirical distribution of evaluativity
across degree constructions (the book's Table 3.1) and its Neo-Gricean
derivation (Chapters 3–5) — a Quantity implicature strengthens otherwise
tautological positive constructions, and the Marked Meaning Principle
([horn-1984]) derives evaluativity for marked antonyms in polar-invariant
constructions.

## Main definitions

- `EvaluativityDatum` / `allEvaluativityData`: the Table 3.1 judgment data
- `evaluativitySource` / `deriveEvaluativity`: the implicature-based derivation
- `applyMMP` / `deriveEvaluativityWithLexicon`: the lexicon-grounded pipeline

## Main results

- `rett_positive_evaluative`, `rett_comparative_non_evaluative`,
  `rett_equative_asymmetry`, `rett_question_asymmetry`: the distribution
  predictions
- `asymmetry_requires_polar_invariance`, `manner_requires_marked_and_invariant`:
  polarity asymmetry tracks polar invariance
- `exact_equative_antonym_invariant`, `comparative_antonym_variant`: the
  polar-variance classification derived from `Degree.equativeSem` /
  `Degree.comparativeSem` mutual entailment rather than stipulated
- `predictions_match_all_data`: the predictions match every judgment datum
-/

namespace Rett2015

open NeoGricean.Markedness
open English.Predicates.Adjectival
  (tall_with_morphology short_with_morphology happy_with_morphology
    unhappy_with_morphology)
open Degree (Construction)
open Degree

/-! ### Judgment data (Table 3.1)

Evaluativity by construction and antonym polarity:

|                  | Positive-polar (tall) | Negative-polar (short) |
|------------------|-----------------------|------------------------|
| Positive         | evaluative            | evaluative             |
| Comparative      | non-evaluative        | non-evaluative         |
| Equative         | non-evaluative        | evaluative             |
| Measure Phrase   | non-evaluative        | *ungrammatical         |
| Degree Question  | non-evaluative        | evaluative             |

The measure-phrase restriction to positive-polar adjectives is
[schwarzschild-2005]'s interval-boundedness effect ([kennedy-mcnally-2005]).
-/

/-- Evaluativity status of a construction-adjective pair. -/
inductive EvaluativityStatus where
  | evaluative
  | nonEvaluative
  | markedOnly
  | ungrammatical
  deriving Repr, DecidableEq

/-- An evaluativity judgment for one construction-adjective pair. -/
structure EvaluativityDatum where
  construction : Construction
  adjective : String
  isPositivePolar : Bool
  exampleSentence : String
  status : EvaluativityStatus
  presupposition : Option String := none
  notes : String := ""
  deriving Repr

def positive_tall : EvaluativityDatum :=
  { construction := .positive
  , adjective := "tall"
  , isPositivePolar := true
  , exampleSentence := "Adam is tall."
  , status := .evaluative
  , presupposition := some "Adam's height exceeds the standard for tallness"
  }

def positive_short : EvaluativityDatum :=
  { construction := .positive
  , adjective := "short"
  , isPositivePolar := false
  , exampleSentence := "Adam is short."
  , status := .evaluative
  , presupposition := some "Adam's height is below the standard for shortness"
  }

def comparative_tall : EvaluativityDatum :=
  { construction := .comparative
  , adjective := "tall"
  , isPositivePolar := true
  , exampleSentence := "Adam is taller than Doug."
  , status := .nonEvaluative
  , notes := "True even if both Adam and Doug are short"
  }

def comparative_short : EvaluativityDatum :=
  { construction := .comparative
  , adjective := "short"
  , isPositivePolar := false
  , exampleSentence := "Adam is shorter than Doug."
  , status := .nonEvaluative
  , notes := "True even if both Adam and Doug are tall"
  }

def equative_tall : EvaluativityDatum :=
  { construction := .equative
  , adjective := "tall"
  , isPositivePolar := true
  , exampleSentence := "Adam is as tall as Doug."
  , status := .nonEvaluative
  }

def equative_short : EvaluativityDatum :=
  { construction := .equative
  , adjective := "short"
  , isPositivePolar := false
  , exampleSentence := "Adam is as short as Doug."
  , status := .evaluative
  , presupposition := some "Both Adam and Doug are short"
  }

def mp_tall : EvaluativityDatum :=
  { construction := .measurePhrase
  , adjective := "tall"
  , isPositivePolar := true
  , exampleSentence := "Adam is 6ft tall."
  , status := .nonEvaluative
  }

def mp_short : EvaluativityDatum :=
  { construction := .measurePhrase
  , adjective := "short"
  , isPositivePolar := false
  , exampleSentence := "*Adam is 4ft short."
  , status := .ungrammatical
  , notes := "MPs don't combine with negative-polar adjectives"
  }

def question_tall : EvaluativityDatum :=
  { construction := .degreeQuestion
  , adjective := "tall"
  , isPositivePolar := true
  , exampleSentence := "How tall is Adam?"
  , status := .nonEvaluative
  }

def question_short : EvaluativityDatum :=
  { construction := .degreeQuestion
  , adjective := "short"
  , isPositivePolar := false
  , exampleSentence := "How short is Adam?"
  , status := .evaluative
  , presupposition := some "Adam is short"
  }

/-- The pooled Table 3.1 judgment data. -/
def allEvaluativityData : List EvaluativityDatum :=
  [ positive_tall, positive_short
  , comparative_tall, comparative_short
  , equative_tall, equative_short
  , mp_tall, mp_short
  , question_tall, question_short
  ]

/-! ### Polarity and implicature types -/

/-- Antonym polarity: positive-polar adjectives (*tall*, *happy*) are
unmarked; negative-polar ones (*short*, *unhappy*) are marked
([bierwisch-1989], [kennedy-2007]). -/
inductive Polarity where
  | positive
  | negative
  deriving Repr, DecidableEq

/-- Negative-polar adjectives are the marked members of their pairs. -/
def Polarity.IsMarked (p : Polarity) : Prop :=
  p = .negative

instance : DecidablePred Polarity.IsMarked :=
  fun _ => inferInstanceAs (Decidable (_ = _))

/-- The implicature route deriving evaluativity: Quantity (uninformativity
avoidance, [rett-2015] Chapter 3's degree tautology) or Manner (marked-form
use, the Marked Meaning Principle of Chapter 5). -/
inductive EvaluativityImplicature where
  | quantity
  | manner
  | none
  deriving Repr, DecidableEq

/-! ### The implicature-based derivation -/

/-- The implicature route deriving evaluativity for each construction and
polarity: positives are strengthened by Quantity for both antonyms;
equatives and degree questions get Manner-derived evaluativity for the
marked antonym only; comparatives and measure phrases get none. -/
def evaluativitySource (c : Construction) (p : Polarity) : EvaluativityImplicature :=
  match c with
  | .positive => .quantity
  | .comparative => .none
  | .equative | .degreeQuestion =>
    match p with
    | .positive => .none
    | .negative => .manner
  | .measurePhrase => .none

/-- The evaluativity prediction for one construction-polarity pair. -/
structure EvaluativityDerivation where
  construction : Construction
  polarity : Polarity
  implicatureType : EvaluativityImplicature
  isEvaluative : Bool
  deriving Repr

/-- Derive evaluativity for a construction and polarity. -/
def deriveEvaluativity (c : Construction) (p : Polarity) : EvaluativityDerivation :=
  let implType := evaluativitySource c p
  { construction := c
  , polarity := p
  , implicatureType := implType
  , isEvaluative := implType != .none
  }

theorem positive_both_evaluative :
    (deriveEvaluativity .positive .positive).isEvaluative = true ∧
    (deriveEvaluativity .positive .negative).isEvaluative = true :=
  ⟨rfl, rfl⟩

theorem comparative_never_evaluative :
    (deriveEvaluativity .comparative .positive).isEvaluative = false ∧
    (deriveEvaluativity .comparative .negative).isEvaluative = false :=
  ⟨rfl, rfl⟩

theorem equative_asymmetry :
    (deriveEvaluativity .equative .positive).isEvaluative = false ∧
    (deriveEvaluativity .equative .negative).isEvaluative = true :=
  ⟨rfl, rfl⟩

theorem question_asymmetry :
    (deriveEvaluativity .degreeQuestion .positive).isEvaluative = false ∧
    (deriveEvaluativity .degreeQuestion .negative).isEvaluative = true :=
  ⟨rfl, rfl⟩

/-- Polar-invariant constructions show polarity asymmetry. -/
theorem invariant_shows_asymmetry_equative :
    (deriveEvaluativity .equative .positive).isEvaluative ≠
    (deriveEvaluativity .equative .negative).isEvaluative := by decide

theorem invariant_shows_asymmetry_question :
    (deriveEvaluativity .degreeQuestion .positive).isEvaluative ≠
    (deriveEvaluativity .degreeQuestion .negative).isEvaluative := by decide

/-- Polar-variant constructions show no polarity asymmetry. -/
theorem variant_shows_symmetry_positive :
    (deriveEvaluativity .positive .positive).isEvaluative =
    (deriveEvaluativity .positive .negative).isEvaluative :=
  rfl

theorem variant_shows_symmetry_comparative :
    (deriveEvaluativity .comparative .positive).isEvaluative =
    (deriveEvaluativity .comparative .negative).isEvaluative :=
  rfl

/-- Manner-derived evaluativity requires a polar-invariant construction and
the marked antonym. -/
theorem manner_requires_marked_and_invariant :
    ∀ c : Construction, ∀ p : Polarity,
      evaluativitySource c p = .manner →
      (polarVariance c = .invariant ∧ p = .negative) := by
  intro c p h
  cases c <;> cases p <;> simp [evaluativitySource, polarVariance] at h ⊢

/-! ### The Marked Meaning Principle -/

/-- The result of applying the Marked Meaning Principle to an adjective form
in a construction. -/
structure MMPDerivation where
  adjForm : String
  unmarkedAlternative : Option String
  construction : Construction
  mmpApplies : Bool
  implicature : Option EvaluativityImplicature
  deriving Repr

/-- Apply the Marked Meaning Principle: the marked member of an antonym
pair, used in a polar-invariant construction where an unmarked alternative
exists, implicates evaluativity ([rett-2015] Chapter 5, after
[horn-1984]'s Division of Pragmatic Labor). -/
def applyMMP (adjForm : String) (construction : Construction)
    (adj1 adj2 : GradableAdjWithMorphology) : MMPDerivation :=
  let isMarked := isMarkedForm adjForm adj1 adj2
  let isPolarInvariant := polarVariance construction == .invariant
  let unmarkedAlt := if isMarked then
      if adjForm == adj1.form then some adj2.form else some adj1.form
    else none
  let mmpApplies := isMarked && isPolarInvariant && unmarkedAlt.isSome
  { adjForm := adjForm
  , unmarkedAlternative := unmarkedAlt
  , construction := construction
  , mmpApplies := mmpApplies
  , implicature := if mmpApplies then some .manner else none
  }

theorem mmp_requires_invariance_equative :
    (applyMMP "short" .equative tall_with_morphology short_with_morphology).mmpApplies = true →
    polarVariance .equative = .invariant := λ _ => rfl

theorem mmp_requires_invariance_question :
    (applyMMP "short" .degreeQuestion tall_with_morphology short_with_morphology).mmpApplies = true →
    polarVariance .degreeQuestion = .invariant := λ _ => rfl

theorem mmp_not_in_comparative :
    (applyMMP "short" .comparative tall_with_morphology short_with_morphology).mmpApplies = false :=
  rfl

theorem mmp_applies_short_equative :
    (applyMMP "short" .equative tall_with_morphology short_with_morphology).mmpApplies = true :=
  rfl

theorem mmp_not_for_tall_equative :
    (applyMMP "tall" .equative tall_with_morphology short_with_morphology).mmpApplies = false :=
  rfl

/-- The equative asymmetry emerges from the MMP plus markedness. -/
theorem equative_asymmetry_from_mmp :
    (isMarkedForm "short" tall_with_morphology short_with_morphology) ∧
    (polarVariance .equative = .invariant) →
    ((applyMMP "short" .equative tall_with_morphology short_with_morphology).implicature = some .manner ∧
     (applyMMP "tall" .equative tall_with_morphology short_with_morphology).implicature = none) :=
  λ _ => ⟨rfl, rfl⟩

/-! ### Polar variance grounded in the comparison semantics

[rett-2015] §3.2.3 reduces polar (in)variance to mutual entailment of the
antonyms' non-evaluative readings (the book's (38)–(42)): the strengthened
("exactly") equatives of the two antonyms share truth conditions, so a
truth-conditionally equivalent unmarked alternative exists and the MMP can
fire; the antonym comparatives exclude each other, so no such alternative
exists. Degree questions pattern with the equative — both antonyms' true
answers are the subject's actual measure. This grounds the `.equative` and
`.comparative` rows of `NeoGricean.Markedness.polarVariance` in
`Degree.equativeSem` / `Degree.comparativeSem` rather than stipulation. -/

section PolarVarianceGrounding

variable {Entity D : Type*} [LinearOrder D] (μ : Entity → D) (a b : Entity)

/-- "A is exactly as tall as B" and "A is exactly as short as B" are mutually
entailing: each strengthened equative reduces to `μ a = μ b`. -/
theorem exact_equative_antonym_invariant :
    (equativeSem μ a b .positive ∧ ¬ comparativeSem μ a b .positive) ↔
      (equativeSem μ a b .negative ∧ ¬ comparativeSem μ a b .negative) := by
  simp only [equativeSem, comparativeSem, ge_iff_le, not_lt]
  exact and_comm

/-- Both strengthened antonym equatives are the "exactly" reading
`Degree.equativeStrengthened`. -/
theorem exact_equative_eq_strengthened :
    (equativeSem μ a b .positive ∧ ¬ comparativeSem μ a b .positive) ↔
      equativeStrengthened μ a b := by
  simp only [equativeSem, comparativeSem, equativeStrengthened, ge_iff_le, not_lt,
    le_antisymm_iff]
  exact and_comm

/-- The antonym comparatives exclude each other: "A is taller than B" and
"A is shorter than B" cannot both hold. -/
theorem comparative_antonyms_exclusive :
    comparativeSem μ a b .positive → ¬ comparativeSem μ a b .negative :=
  λ h => lt_asymm h

/-- Whenever the antonyms could differ (`μ a ≠ μ b`), they do: the antonym
comparatives have complementary truth conditions, so no truth-conditionally
equivalent unmarked alternative exists. -/
theorem comparative_antonym_variant (h : μ a ≠ μ b) :
    comparativeSem μ a b .positive ↔ ¬ comparativeSem μ a b .negative := by
  simp only [comparativeSem, not_lt]
  exact ⟨le_of_lt, λ hle => hle.lt_of_ne h.symm⟩

end PolarVarianceGrounding

/-! ### Lexicon-grounded derivation -/

/-- An evaluativity derivation grounded in lexical morphology: markedness is
computed from the adjective entries rather than stipulated. -/
structure LexiconGroundedDerivation where
  adjective : GradableAdjWithMorphology
  antonym : GradableAdjWithMorphology
  construction : Construction
  mAlternatives : Option MAlternativeSet
  mmpDerivation : MMPDerivation
  isEvaluative : Bool
  source : EvaluativityImplicature
  deriving Repr

/-- Derive evaluativity from lexical entries: compute markedness from
morphology, generate M-alternatives, and apply the Quantity route
(positives) or the MMP route (equatives and degree questions). -/
def deriveEvaluativityWithLexicon (adjForm : String) (construction : Construction)
    (adj1 adj2 : GradableAdjWithMorphology) : LexiconGroundedDerivation :=
  let (adj, ant) := if adj1.form == adjForm then (adj1, adj2) else (adj2, adj1)
  let mAlts := generateMAlternatives adj1 adj2 construction
  let mmp := applyMMP adjForm construction adj1 adj2
  let (isEval, source) := match construction with
    | .positive => (true, EvaluativityImplicature.quantity)
    | .equative | .degreeQuestion =>
      if mmp.mmpApplies then (true, EvaluativityImplicature.manner)
      else (false, EvaluativityImplicature.none)
    | .comparative | .measurePhrase => (false, EvaluativityImplicature.none)
  { adjective := adj
  , antonym := ant
  , construction := construction
  , mAlternatives := mAlts
  , mmpDerivation := mmp
  , isEvaluative := isEval
  , source := source
  }

theorem grounded_matches_simple_tall_positive :
    (deriveEvaluativityWithLexicon "tall" .positive
      tall_with_morphology short_with_morphology).isEvaluative =
    (deriveEvaluativity .positive .positive).isEvaluative :=
  rfl

theorem grounded_matches_simple_short_equative :
    (deriveEvaluativityWithLexicon "short" .equative
      tall_with_morphology short_with_morphology).isEvaluative =
    (deriveEvaluativity .equative .negative).isEvaluative :=
  rfl

/-! ### Core predictions -/

/-- Positive constructions are evaluative for both antonyms, via Quantity
implicature (the degree tautology of [rett-2015] Chapter 3). -/
theorem rett_positive_evaluative :
    (deriveEvaluativity .positive .positive).isEvaluative = true ∧
    (deriveEvaluativity .positive .negative).isEvaluative = true ∧
    (deriveEvaluativity .positive .positive).implicatureType = .quantity ∧
    (deriveEvaluativity .positive .negative).implicatureType = .quantity :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Comparatives are never evaluative: the comparative morpheme binds the
degree argument, leaving no threshold to infer. -/
theorem rett_comparative_non_evaluative :
    (deriveEvaluativity .comparative .positive).isEvaluative = false ∧
    (deriveEvaluativity .comparative .negative).isEvaluative = false ∧
    (deriveEvaluativity .comparative .positive).implicatureType = .none ∧
    (deriveEvaluativity .comparative .negative).implicatureType = .none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Equatives show polarity asymmetry: only the marked antonym is
evaluative, via the MMP. -/
theorem rett_equative_asymmetry :
    (deriveEvaluativity .equative .positive).isEvaluative = false ∧
    (deriveEvaluativity .equative .negative).isEvaluative = true ∧
    (deriveEvaluativity .equative .positive).implicatureType = .none ∧
    (deriveEvaluativity .equative .negative).implicatureType = .manner :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Degree questions show the same asymmetry as equatives. -/
theorem rett_question_asymmetry :
    (deriveEvaluativity .degreeQuestion .positive).isEvaluative = false ∧
    (deriveEvaluativity .degreeQuestion .negative).isEvaluative = true ∧
    (deriveEvaluativity .degreeQuestion .positive).implicatureType = .none ∧
    (deriveEvaluativity .degreeQuestion .negative).implicatureType = .manner :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Polarity asymmetry appears exactly in the polar-invariant constructions:
the MMP requires an unmarked alternative with the same truth conditions. -/
theorem asymmetry_requires_polar_invariance :
    (polarVariance .equative = .invariant ∧
     (deriveEvaluativity .equative .positive).isEvaluative ≠
     (deriveEvaluativity .equative .negative).isEvaluative) ∧
    (polarVariance .degreeQuestion = .invariant ∧
     (deriveEvaluativity .degreeQuestion .positive).isEvaluative ≠
     (deriveEvaluativity .degreeQuestion .negative).isEvaluative) ∧
    (polarVariance .comparative = .variant ∧
     (deriveEvaluativity .comparative .positive).isEvaluative =
     (deriveEvaluativity .comparative .negative).isEvaluative) := by
  decide

theorem polar_invariance_enables_m_alternatives :
    polarVariance .equative = .invariant ∧
    polarVariance .degreeQuestion = .invariant ∧
    polarVariance .comparative = .variant ∧
    polarVariance .positive = .variant :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem q_implicature_for_positive :
    evaluativitySource .positive .positive = .quantity ∧
    evaluativitySource .positive .negative = .quantity :=
  ⟨rfl, rfl⟩

theorem mmp_for_marked_in_invariant :
    evaluativitySource .equative .negative = .manner ∧
    evaluativitySource .degreeQuestion .negative = .manner ∧
    evaluativitySource .equative .positive = .none ∧
    evaluativitySource .degreeQuestion .positive = .none :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem no_mechanism_for_comparative :
    evaluativitySource .comparative .positive = .none ∧
    evaluativitySource .comparative .negative = .none :=
  ⟨rfl, rfl⟩

/-- The marked form, not the unmarked one, triggers the MMP. -/
theorem marked_triggers_mmp :
    isMarkedForm "short" tall_with_morphology short_with_morphology = true ∧
    isMarkedForm "tall" tall_with_morphology short_with_morphology = false ∧
    (applyMMP "short" .equative tall_with_morphology short_with_morphology).mmpApplies = true ∧
    (applyMMP "tall" .equative tall_with_morphology short_with_morphology).mmpApplies = false := by
  decide

/-- Marked forms cost more to produce ([horn-1984]). -/
theorem marked_costs_more :
    productionCost "short" tall_with_morphology short_with_morphology >
    productionCost "tall" tall_with_morphology short_with_morphology := by
  have hs : isMarkedForm "short" tall_with_morphology short_with_morphology = true := by decide
  have ht : isMarkedForm "tall" tall_with_morphology short_with_morphology = false := by decide
  simp [productionCost, hs, ht, costDifference]

/-- Morphological complexity determines markedness for *happy* ~ *unhappy*. -/
theorem morphological_markedness :
    isMarkedForm "unhappy" happy_with_morphology unhappy_with_morphology = true ∧
    isMarkedForm "happy" happy_with_morphology unhappy_with_morphology = false := by
  decide

/-- The full derivation chain for "as short as": negative pole → marked →
polar-invariant equative → MMP → manner implicature → evaluative. -/
theorem complete_derivation_as_short_as :
    short_with_morphology.isPositivePole = false ∧
    isMarkedForm "short" tall_with_morphology short_with_morphology = true ∧
    polarVariance .equative = .invariant ∧
    (applyMMP "short" .equative tall_with_morphology short_with_morphology).mmpApplies = true ∧
    (applyMMP "short" .equative tall_with_morphology short_with_morphology).implicature = some .manner ∧
    (deriveEvaluativityWithLexicon "short" .equative
      tall_with_morphology short_with_morphology).isEvaluative = true := by
  decide

/-- The full derivation chain for "as tall as": unmarked form → MMP does not
apply → no implicature → non-evaluative. -/
theorem complete_derivation_as_tall_as :
    tall_with_morphology.isPositivePole = true ∧
    isMarkedForm "tall" tall_with_morphology short_with_morphology = false ∧
    polarVariance .equative = .invariant ∧
    (applyMMP "tall" .equative tall_with_morphology short_with_morphology).mmpApplies = false ∧
    (applyMMP "tall" .equative tall_with_morphology short_with_morphology).implicature = none ∧
    (deriveEvaluativityWithLexicon "tall" .equative
      tall_with_morphology short_with_morphology).isEvaluative = false := by
  decide

/-! ### Predictions match the judgment data -/

/-- A derivation's prediction agrees with a judgment datum. -/
def predictionMatches (d : EvaluativityDerivation) (datum : EvaluativityDatum) : Bool :=
  match datum.status with
  | .ungrammatical => true
  | .markedOnly => d.polarity == .negative && d.isEvaluative
  | .evaluative => d.isEvaluative
  | .nonEvaluative => !d.isEvaluative

/-- Every Table 3.1 judgment is matched by the implicature-based
derivation. -/
theorem predictions_match_all_data :
    allEvaluativityData.all (λ datum =>
      predictionMatches
        (deriveEvaluativity datum.construction
          (if datum.isPositivePolar then .positive else .negative))
        datum) = true := by
  decide

end Rett2015
