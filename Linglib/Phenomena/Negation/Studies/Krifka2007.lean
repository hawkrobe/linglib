import Linglib.Theories.Semantics.Lexical.Adjective.Antonymy
import Linglib.Theories.Pragmatics.Implicature.Core.Markedness
import Linglib.Phenomena.Negation.FlexibleNegation
import Linglib.Core.Logic.OT

/-!
# @cite{krifka-2007b} — Negated Antonyms: Creating and Filling the Gap
@cite{krifka-2007b}

In:, Presupposition and Implicature in
Compositional Semantics, Palgrave Macmillan.

## Krifka's Thesis

Krifka argues, against the received view (@cite{cruse-1986}, @cite{horn-1989}),
that antonyms like happy/unhappy are **literally contradictory** — they
exhaustively partition the scale with a single threshold. The gap between
"not unhappy" and "happy" arises through **pragmatic strengthening**, not
through the semantics of contrary negation.

### Three Hypotheses (§3)

1. **Epistemic vagueness**: Speakers avoid borderline cases to ensure safe
   communication (following Williamson 1994).
2. **Exhaustive antonymy**: happy and unhappy are contradictories — they
   literally exhaust their scale. Evidence: unconditionals like
   "Regardless whether you are happy or unhappy, you should read this book"
   (ex. 22) entail the predicate covers everyone.
3. **M-principle**: Of two expressions with similar meaning, the simpler one
   is restricted to stereotypical interpretations, the complex one to
   non-stereotypical interpretations (@cite{horn-1984}).

### Central Argument

Under contradictory semantics (single θ), "not unhappy" = "happy" (DNE).
The M-principle breaks this synonymy: since "not unhappy" is more complex
than "happy" (5 vs 0 cost units), the complex form is pragmatically
restricted to the non-stereotypical region — the plateau/gap between clearly
happy and clearly unhappy.

### Quadruplet Structure (ex. 1)

Krifka's analysis centers on quadruplets:
  happy, not happy, unhappy, not unhappy
with form complexity: |happy| < |unhappy| < |not happy| < |not unhappy|

## Verification

Formalizes the quadruplet structure, proves the contradictory synonymy
puzzle and its resolution via ThresholdPair, and bridges to the empirical
data in `FlexibleNegation.lean`. The pragmatic mechanism connecting
contradictory base → effective ThresholdPair is derived via two routes:
1. **Bidirectional OT** (§ 9 below): @cite{blutner-2000}'s weak BiOT (eq. 14)
   derives the four-way form-meaning assignment via the greatest-fixed-point
   computation in `Core.ConstraintEvaluation.superoptimal`.
2. **RSA model**: @cite{tessler-franke-2019} (`Studies/TesslerFranke2020.lean`)
   derives the same effect through Bayesian pragmatic reasoning.
-/

set_option autoImplicit false

namespace Phenomena.Negation.Studies.Krifka2007

open Core.Scale (Degree Threshold deg thr)
open Semantics.Lexical.Adjective (ThresholdPair inGapRegion
  positiveMeaning' contraryNegMeaning notContraryNegMeaning contradictoryNeg)
open Semantics.Lexical.Adjective.Antonymy
open Semantics.Degree (positiveMeaning)
open Phenomena.Negation.FlexibleNegation
open Core.ConstraintEvaluation (superoptimal)
open Core.OT (NamedConstraint)

-- ════════════════════════════════════════════════════
-- § 1. Quadruplet: The Central Data Structure
-- ════════════════════════════════════════════════════

/-- Krifka's quadruplet (ex. 1): the four forms generated from an adjective
    and its antonym by applying syntactic negation. -/
inductive QuadForm where
  | positive     -- "happy"
  | notPositive  -- "not happy"
  | negative     -- "unhappy"
  | notNegative  -- "not unhappy"
  deriving Repr, DecidableEq

/-- Form complexity ordering:
    |happy| < |unhappy| < |not happy| < |not unhappy|

    Matches `utteranceCost` in @cite{tessler-franke-2019}'s RSA model. -/
def QuadForm.complexity : QuadForm → Nat
  | .positive    => 0   -- monomorphemic
  | .negative    => 2   -- un- prefix (morphologically complex)
  | .notPositive => 3   -- syntactic not (syntactically complex)
  | .notNegative => 5   -- not + un- (both)

/-- Form complexity is monotonically increasing across the quadruplet. -/
theorem complexity_ordering :
    QuadForm.complexity .positive < QuadForm.complexity .negative ∧
    QuadForm.complexity .negative < QuadForm.complexity .notPositive ∧
    QuadForm.complexity .notPositive < QuadForm.complexity .notNegative := by
  decide

-- ════════════════════════════════════════════════════
-- § 2. Contradictory Base: The Literal Semantics
-- ════════════════════════════════════════════════════

/-- Krifka's H2: Antonyms are literally contradictory (single threshold θ).
    All four quadruplet forms derive from Boolean operations on `d > θ`. -/
def contradictoryQuad {max : Nat} (θ : Threshold max)
    (q : QuadForm) (d : Degree max) : Bool :=
  match q with
  | .positive    => positiveMeaning d θ    -- d > θ
  | .notPositive => !positiveMeaning d θ   -- d ≤ θ (contradictory)
  | .negative    => !positiveMeaning d θ   -- d ≤ θ (same! contradictory antonym)
  | .notNegative => positiveMeaning d θ    -- d > θ (DNE restores positive)

/-- **The puzzle**: Under contradictory semantics, "unhappy" = "not happy"
    and "not unhappy" = "happy". Each pair is synonymous. -/
theorem contradictory_synonymy {max : Nat} (d : Degree max) (θ : Threshold max) :
    contradictoryQuad θ .negative d = contradictoryQuad θ .notPositive d ∧
    contradictoryQuad θ .notNegative d = contradictoryQuad θ .positive d :=
  ⟨rfl, rfl⟩

/-- The puzzle makes a prediction: "not unhappy" should mean the same as
    "happy". But empirically it doesn't (@cite{tessler-franke-2019}).
    `contradictory_dne` from `Antonymy` proves this synonymy formally. -/
theorem dne_synonymy {max : Nat} (d : Degree max) (θ : Threshold max) :
    contradictoryQuad θ .notNegative d = contradictoryQuad θ .positive d := rfl

-- ════════════════════════════════════════════════════
-- § 3. Strengthened Semantics: Breaking Synonymy
-- ════════════════════════════════════════════════════

/-- After pragmatic strengthening (M-principle), the effective semantics uses
    two thresholds. The M-principle assigns different scale regions to forms
    of different complexity:
    - "happy" (simple) → stereotypical positive (d > θ_pos)
    - "unhappy" (moderate) → stereotypical negative (d < θ_neg)
    - "not happy" (complex) → includes borderline low
    - "not unhappy" (most complex) → borderline high / plateau -/
def strengthenedQuad {max : Nat} (tp : ThresholdPair max)
    (q : QuadForm) (d : Degree max) : Bool :=
  match q with
  | .positive    => positiveMeaning' d tp       -- d > θ_pos
  | .notPositive => contradictoryNeg d tp.pos   -- d ≤ θ_pos
  | .negative    => contraryNegMeaning d tp     -- d < θ_neg
  | .notNegative => notContraryNegMeaning d tp  -- d ≥ θ_neg

/-- **The solution**: With ThresholdPair, "not unhappy" ≠ "happy" when
    the gap is strict. The M-principle-derived two-threshold model breaks
    the synonymy that contradictory semantics creates. -/
theorem strengthened_breaks_synonymy {max : Nat} (tp : ThresholdPair max)
    (h : (tp.neg : Degree max) < (tp.pos : Degree max)) :
    ∃ d : Degree max,
      strengthenedQuad tp .notNegative d ≠ strengthenedQuad tp .positive d := by
  obtain ⟨d, h1, h2⟩ := contrary_gap_exists tp h
  exact ⟨d, by simp [strengthenedQuad, h1, h2]⟩

-- ════════════════════════════════════════════════════
-- § 4. Concrete Scale: Happy/Unhappy on Degree 4
-- ════════════════════════════════════════════════════

/-- 5-point happiness scale (matching @cite{tessler-franke-2019}'s model). -/
abbrev HappyDeg := Degree 4

/-- Contradictory boundary at θ = 2 (the literal semantics). -/
abbrev happyθ : Threshold 4 := thr 2

/-- Effective threshold pair after pragmatic strengthening:
    θ_pos = 2, θ_neg = 1. The gap [1, 2] is the plateau region where
    "not unhappy" lands. -/
def happyTP : ThresholdPair 4 where
  pos := thr 2
  neg := thr 1
  gap_exists := by decide

theorem happy_gap_strict :
    (happyTP.neg : HappyDeg) < (happyTP.pos : HappyDeg) := by decide

-- ════════════════════════════════════════════════════
-- § 5. Core Predictions
-- ════════════════════════════════════════════════════

/-- **Prediction 1**: Under contradictory semantics, all degrees are
    classified. No gap exists. (Krifka's H2: literal exhaustivity.) -/
theorem contradictory_exhaustive_concrete :
    ∀ d : HappyDeg, contradictoryQuad happyθ .positive d = true ∨
                     contradictoryQuad happyθ .negative d = true := by
  native_decide

/-- **Prediction 2**: Under contradictory semantics, "not unhappy" = "happy"
    at every degree. (The puzzle.) -/
theorem contradictory_not_unhappy_eq_happy :
    ∀ d : HappyDeg, contradictoryQuad happyθ .notNegative d =
                     contradictoryQuad happyθ .positive d := by
  intro d; rfl

/-- **Prediction 3**: After strengthening, the gap breaks synonymy. -/
theorem strengthened_not_unhappy_ne_happy :
    ∃ d : HappyDeg,
      strengthenedQuad happyTP .notNegative d ≠
      strengthenedQuad happyTP .positive d :=
  strengthened_breaks_synonymy happyTP happy_gap_strict

/-- **Prediction 4**: The gap region is nonempty (degrees 1 and 2). -/
theorem gap_degrees :
    inGapRegion (deg 1 : HappyDeg) happyTP = true ∧
    inGapRegion (deg 2 : HappyDeg) happyTP = true :=
  ⟨by native_decide, by native_decide⟩

/-- **Prediction 5**: Degree 0 is "unhappy", degree 4 is "happy". -/
theorem extreme_degrees :
    contraryNegMeaning (deg 0 : HappyDeg) happyTP = true ∧
    positiveMeaning' (deg 4 : HappyDeg) happyTP = true :=
  ⟨by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 6. Bridge to FlexibleNegation Data
-- ════════════════════════════════════════════════════

/-- FlexibleNegation classifies "unhappy" as contrary — this is the
    *effective* (post-strengthening) semantics, consistent with Krifka's
    analysis where the contrary behavior is pragmatically derived. -/
theorem unhappy_effectively_contrary :
    unhappy_contrary.expectedInterpretation = .contrary := rfl

/-- The empirical double-negation non-equivalence is derived from
    the strengthened model (§3): synonymy is broken by the gap. -/
theorem double_neg_nonequivalence :
    happy_double_neg.areEquivalent = false := rfl

/-- The gap prediction from FlexibleNegation data corresponds to
    `contrary_gap_exists` applied to the strengthened model. -/
theorem gap_prediction_derived :
    prediction_double_neg_gap.statement =
      "∃d, P(d | 'not unhappy') > 0 ∧ P(d | 'happy') = 0" ∧
    (∃ d : HappyDeg, notContraryNegMeaning d happyTP = true
                    ∧ positiveMeaning' d happyTP = false) :=
  ⟨rfl, contrary_gap_exists happyTP happy_gap_strict⟩

-- ════════════════════════════════════════════════════
-- § 7. Bridge to Markedness Infrastructure
-- ════════════════════════════════════════════════════

/-- Krifka's form complexity ordering matches the markedness infrastructure.
    "unhappy" is marked over "happy" by morphological complexity. -/
theorem unhappy_marked_by_morphology :
    Implicature.Markedness.computeMarked
      Implicature.Markedness.happy_with_morphology
      Implicature.Markedness.unhappy_with_morphology = some "unhappy" := by
  native_decide

/-- Cost asymmetry in FlexibleNegation data reflects Krifka's
    form complexity ordering. -/
theorem cost_asymmetry_reflects_complexity :
    unhappy_vs_not_happy.cheapForm = "unhappy" ∧
    unhappy_vs_not_happy.costlyForm = "not happy" ∧
    unhappy_vs_not_happy.cheapMeaning = .contrary ∧
    unhappy_vs_not_happy.costlyMeaning = .contradictory := by
  simp [unhappy_vs_not_happy]

-- ════════════════════════════════════════════════════
-- § 8. Unconditionals: Evidence for Contradictory Base
-- ════════════════════════════════════════════════════

/-- Krifka's unconditional argument:
    "Regardless whether you are happy or unhappy, you should read this book."

    This sentence entails the predicate covers EVERYONE — no gap.
    Under the contradictory model, happy ∨ unhappy = universal (exhaustive).
    Under a contrary model, this would exclude the gap region.

    Unconditionals provide evidence that the literal semantics IS
    contradictory, with the gap being purely pragmatic. -/
theorem unconditional_exhaustive :
    ∀ d : HappyDeg, contradictoryQuad happyθ .positive d = true ∨
                     contradictoryQuad happyθ .negative d = true :=
  contradictory_exhaustive_concrete

/-- Contrast: the strengthened model does NOT exhaust the scale.
    There exist degrees in the gap that are neither "happy" nor "unhappy". -/
theorem strengthened_not_exhaustive :
    ∃ d : HappyDeg, strengthenedQuad happyTP .positive d = false ∧
                     strengthenedQuad happyTP .negative d = false := by
  exact ⟨deg 1, by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 9. Bidirectional OT: Deriving the Quadruplet
-- ════════════════════════════════════════════════════

/-! @cite{blutner-2000}'s weak Bidirectional OT (eq. 14, "weak optimality")
    derives the form-meaning assignment from constraint competition. Krifka
    explicitly invokes this version (p. 6, citing @cite{blutner-2000} and
    @cite{jaeger-2002}). The evaluation uses `superoptimal` from
    `Core.Logic.ConstraintEvaluation`.

    Two ranked constraints:
    1. **M-principle** (@cite{horn-1984}): simple forms pair with stereotypical
       meanings; complex forms pair with non-stereotypical meanings.
    2. **Economy**: minimize form complexity.

    Under weak BiOT, the four-way form-meaning assignment emerges from the
    greatest-fixed-point computation regardless of ranking. This is because
    the weak BiOT fixed point re-admits pairs whose blockers were themselves
    eliminated — producing Horn's division of pragmatic labour in all cases
    where each form has a unique best meaning and vice versa. -/

/-- Meaning regions on the scale after pragmatic strengthening.
    The contradictory threshold θ splits into four regions:
    two stereotypical (clearly above/below) and two non-stereotypical
    (borderline, the plateau that becomes the "gap"). -/
inductive Region where
  | positive     -- clearly happy (d >> θ)
  | plateauHigh  -- borderline high: "not unhappy" territory
  | plateauLow   -- borderline low: "not happy" territory
  | negative     -- clearly unhappy (d << θ)
  deriving Repr, DecidableEq

/-- Semantically compatible form-meaning pairs.
    Under contradictory semantics (H2), forms partition by literal denotation:
    - Literally positive (happy, not unhappy): d > θ → positive or plateauHigh
    - Literally negative (unhappy, not happy): d ≤ θ → negative or plateauLow -/
def biotPairs : List (QuadForm × Region) :=
  [ (.positive,    .positive),    (.positive,    .plateauHigh),
    (.notNegative, .positive),    (.notNegative, .plateauHigh),
    (.negative,    .negative),    (.negative,    .plateauLow),
    (.notPositive, .negative),    (.notPositive, .plateauLow) ]

/-- **M-Principle** constraint (@cite{horn-1984}, Horn's Division of Pragmatic
    Labor): penalizes mismatch between form complexity and meaning
    stereotypicality.
    - Simple form + stereotypical meaning → 0 violations (match)
    - Complex form + non-stereotypical meaning → 0 violations (match)
    - Cross-assignment → 1 violation (mismatch) -/
def mPrinciple : NamedConstraint (QuadForm × Region) where
  name := "M-Principle"
  family := .markedness
  eval
    | (.positive,    .positive)    => 0  -- simple + stereotypical
    | (.positive,    .plateauHigh) => 1  -- simple + non-stereotypical
    | (.notNegative, .positive)    => 1  -- complex + stereotypical
    | (.notNegative, .plateauHigh) => 0  -- complex + non-stereotypical
    | (.negative,    .negative)    => 0
    | (.negative,    .plateauLow)  => 1
    | (.notPositive, .negative)    => 1
    | (.notPositive, .plateauLow)  => 0
    | _ => 0

/-- **Economy** constraint: penalizes form complexity.
    Violation count = `QuadForm.complexity`. -/
def economyQ : NamedConstraint (QuadForm × Region) where
  name := "Economy"
  family := .faithfulness
  eval p := p.1.complexity

/-- Build the violation profile for a ranking of constraints. -/
def biotProfile (ranking : List (NamedConstraint (QuadForm × Region)))
    (p : QuadForm × Region) : List Nat :=
  ranking.map fun c => c.eval p

/-- **Main BiOT result**: M-Principle >> Economy derives
    Krifka's quadruplet assignment. Each form gets a unique meaning region:
    - "happy" → clearly positive (stereotypical)
    - "not unhappy" → borderline positive / plateau (non-stereotypical)
    - "unhappy" → clearly negative (stereotypical)
    - "not happy" → borderline negative / plateau (non-stereotypical) -/
theorem krifka_biot_prediction :
    superoptimal biotPairs (biotProfile [mPrinciple, economyQ]) =
      [(.positive, .positive), (.notNegative, .plateauHigh),
       (.negative, .negative), (.notPositive, .plateauLow)] := by
  native_decide

/-- Each quadruplet form receives a unique meaning: the BiOT assignment
    is a bijection between the four forms and the four regions. -/
theorem biot_covers_all_forms :
    (superoptimal biotPairs (biotProfile [mPrinciple, economyQ])).map Prod.fst =
      [.positive, .notNegative, .negative, .notPositive] := by
  native_decide

/-- Each region is assigned to exactly one form. -/
theorem biot_covers_all_regions :
    (superoptimal biotPairs (biotProfile [mPrinciple, economyQ])).map Prod.snd =
      [.positive, .plateauHigh, .negative, .plateauLow] := by
  native_decide

/-- Under weak BiOT, Economy >> M produces the **same** four-way assignment
    as M >> Economy. The greatest-fixed-point computation re-admits the
    complex forms after their blockers are removed: pairs like
    ⟨notNegative, plateauHigh⟩ are initially blocked by
    ⟨positive, plateauHigh⟩, but that pair is itself blocked by
    ⟨positive, positive⟩, so ⟨notNegative, plateauHigh⟩ returns.

    This ranking-independence is a general property of weak BiOT for
    form-meaning games where each form has a unique best meaning. Under
    strong BiOT (`strongOptimal`), Economy >> M would collapse the
    quadruplet to only two pairs. -/
theorem economy_ranking_independent :
    superoptimal biotPairs (biotProfile [economyQ, mPrinciple]) =
    superoptimal biotPairs (biotProfile [mPrinciple, economyQ]) := by
  native_decide

/-- The full quadruplet survives under both rankings. -/
theorem both_rankings_give_quadruplet :
    (superoptimal biotPairs (biotProfile [mPrinciple, economyQ])).length = 4 ∧
    (superoptimal biotPairs (biotProfile [economyQ, mPrinciple])).length = 4 := by
  exact ⟨by native_decide, by native_decide⟩

/-- The BiOT derivation agrees with the strengthened semantics (§ 3):
    "happy" and "not unhappy" are assigned to different meaning regions,
    breaking the synonymy that holds under contradictory semantics (§ 2). -/
theorem biot_breaks_synonymy :
    let result := superoptimal biotPairs (biotProfile [mPrinciple, economyQ])
    (result.any (· == (.positive, Region.positive)) &&
     result.any (· == (.notNegative, Region.plateauHigh))) = true := by
  native_decide

end Phenomena.Negation.Studies.Krifka2007
