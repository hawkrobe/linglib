import Linglib.Fragments.English.FocusParticles
import Linglib.Phenomena.Focus.Basic

/-!
# @cite{francescotti-1995}

Even: The Conventional Implicature Approach Reconsidered.
Linguistics and Philosophy 18: 153–173.

Francescotti defends and revises the Implicature Account (IA) of "even"
against Lycan's quantifier approach. The core contribution is a revised
felicity condition: S* must be more surprising than MOST (not ONE, not ALL)
of its true neighbors.

## Key Claims

(a) "Even" does not make a truth-functional difference; it contributes via
    conventional implicature (Equivalence Thesis).
(b) "Even" is epistemic: it implies surprise, unexpectedness, or unlikelihood.
(c) "Even" is scalar: unexpectedness comes in degrees.
(d) Felicity requires S* to be more surprising than MOST true neighbors —
    not just one (@cite{bennett-1982}), not all (@cite{karttunen-peters-1979}).

## Formalization

We derive the Equivalence Thesis and threshold choice from the English
fragment entry, then encode the two key counterexamples as finite scenarios
and prove that only Francescotti's "most" threshold gives the correct
predictions for both.
-/

namespace Phenomena.Focus.Studies.Francescotti1995

open Semantics.FocusParticles (EvenThreshold evenPresupWith)
open Fragments.English.FocusParticles (even_)

-- ============================================================
-- Section 1: Equivalence Thesis (from fragment)
-- ============================================================

/-- **Equivalence Thesis** (§V(a)): "Even A is F" is true just in case
    "A is F" is true. "Even" does not make a truth-functional difference.
    Derived from the fragment entry. -/
theorem equivalence_thesis :
    even_.truthFunctional = false := rfl

/-- "Even" contributes via conventional implicature, not assertion.
    Derived from the fragment entry. -/
theorem even_contributes_via_ci :
    even_.contributionLayer = .implicature := rfl

/-- The fragment specifies Francescotti's "most" threshold. -/
theorem even_threshold_is_most :
    even_.threshold = some .most := rfl

-- ============================================================
-- Section 2: Threshold Predictions
-- ============================================================

/-- A scenario for testing "even" felicity predictions.
    Each scenario specifies surprise levels for the prejacent and its
    contextually-determined neighbors, plus the observed felicity judgment. -/
structure EvenScenario where
  /-- Description -/
  description : String
  /-- Surprise level of S* (higher = more surprising = less likely) -/
  prejacent : Nat
  /-- Surprise levels of the neighbor alternatives -/
  neighbors : List Nat
  /-- Observed felicity (true = felicitous) -/
  felicitous : Bool
  deriving Repr

/-- Predict felicity for a scenario under a given threshold. -/
def predict (s : EvenScenario) (t : EvenThreshold) : Bool :=
  evenPresupWith s.prejacent s.neighbors (fun a b => decide (a > b)) t

/-- Predict felicity using the threshold from the English fragment. -/
def predictFromFragment (s : EvenScenario) : Bool :=
  match even_.threshold with
  | some t => predict s t
  | none => false

-- ============================================================
-- Scenario 1: Bennett's threshold is too weak (p. 155)
-- ============================================================

/-!
## Scenario 1: "Even Albert passed the exam"

Albert is one of the best chemistry students. He and Marie (the very best)
are both very likely to pass. Three weaker students have higher surprise
for passing.

Bennett predicts felicitous (Albert exceeds Marie), but the sentence is
actually infelicitous — Albert's passing is completely unsurprising.
-/

/-- Albert passing is unsurprising (level 2); Marie even less so (level 1).
    Three other students have high surprise (5, 7, 8). -/
def scenario1 : EvenScenario :=
  { description := "Even Albert passed the exam (Albert is one of the best students)"
    prejacent := 2              -- Albert: very likely to pass, low surprise
    neighbors := [1, 5, 7, 8]   -- Marie(1), Tom(5), Sue(7), Bob(8)
    felicitous := false }        -- Actually infelicitous

/-- Bennett (∃) wrongly predicts felicitous: Albert(2) exceeds Marie(1). -/
theorem bennett_wrong_on_scenario1 :
    predict scenario1 .existential ≠ scenario1.felicitous := by native_decide

/-- K-P (∀) correctly predicts infelicitous here (but will fail on scenario 2). -/
theorem kp_correct_on_scenario1 :
    predict scenario1 .universal = scenario1.felicitous := by native_decide

/-- Francescotti (most) correctly predicts infelicitous:
    Albert(2) exceeds only 1 of 4 neighbors (25% < 50%). -/
theorem francescotti_correct_on_scenario1 :
    predict scenario1 .most = scenario1.felicitous := by native_decide

-- ============================================================
-- Scenario 2: K-P's threshold is too strong (p. 156)
-- ============================================================

/-!
## Scenario 2: "Even Albert failed the exam"

Albert is one of the best students, so failing is very surprising.
Marie is even better, so her failing would be even MORE surprising.
Three weaker students have low surprise for failing.

K-P predicts infelicitous (Albert doesn't exceed Marie), but the sentence
is actually felicitous — Albert failing IS very surprising.
-/

/-- Albert failing is very surprising (level 8); Marie even more so (level 9).
    Three weaker students have low surprise for failing (3, 2, 1). -/
def scenario2 : EvenScenario :=
  { description := "Even Albert failed the exam (Albert is one of the best students)"
    prejacent := 8              -- Albert: very unlikely to fail, high surprise
    neighbors := [9, 3, 2, 1]   -- Marie(9), Tom(3), Sue(2), Bob(1)
    felicitous := true }         -- Actually felicitous

/-- Bennett (∃) correctly predicts felicitous here. -/
theorem bennett_correct_on_scenario2 :
    predict scenario2 .existential = scenario2.felicitous := by native_decide

/-- K-P (∀) wrongly predicts infelicitous: Albert(8) doesn't exceed Marie(9). -/
theorem kp_wrong_on_scenario2 :
    predict scenario2 .universal ≠ scenario2.felicitous := by native_decide

/-- Francescotti (most) correctly predicts felicitous:
    Albert(8) exceeds 3 of 4 neighbors (75% > 50%). -/
theorem francescotti_correct_on_scenario2 :
    predict scenario2 .most = scenario2.felicitous := by native_decide

-- ============================================================
-- Section 3: Summary and fragment-derived predictions
-- ============================================================

/-- Francescotti's "most" threshold is the only one that matches
    observed felicity judgments on both scenarios. -/
theorem francescotti_uniquely_correct :
    predict scenario1 .most = scenario1.felicitous ∧
    predict scenario2 .most = scenario2.felicitous ∧
    predict scenario1 .existential ≠ scenario1.felicitous ∧
    predict scenario2 .universal ≠ scenario2.felicitous := by native_decide

/-- The English fragment entry for "even" gives correct predictions
    on both scenarios (since it specifies `.most`). -/
theorem fragment_predictions_correct :
    predictFromFragment scenario1 = scenario1.felicitous ∧
    predictFromFragment scenario2 = scenario2.felicitous := by native_decide

-- ============================================================
-- Section 4: Gradient felicity (pp. 163–164)
-- ============================================================

/-!
## Gradient Felicity

Francescotti argues that felicity comes in degrees, determined by:
(a) how much S* surpasses neighbors in surprise (degree of excess), and
(b) how many neighbors S* surpasses (proportion exceeded).

The Andre/height example (p. 164): if Andre is BY FAR the tallest
person, "Even Andre cannot reach the top shelf" is VERY felicitous.
If he's tallest by a small margin, it's less felicitous.
-/

/-- Proportion of alternatives exceeded, as a rational in [0, 1].
    Captures Francescotti's gradient: higher = more felicitous. -/
def proportionExceeded (s : EvenScenario) : Rat :=
  let exceeded := (s.neighbors.filter (· < s.prejacent)).length
  if s.neighbors.length = 0 then 0
  else (exceeded : Rat) / (s.neighbors.length : Rat)

/-- Average surprise margin over exceeded alternatives.
    Captures how MUCH S* surpasses its neighbors (dimension (a)). -/
def meanExcess (s : EvenScenario) : Rat :=
  let exceeded := s.neighbors.filter (· < s.prejacent)
  if exceeded.length = 0 then 0
  else let total : Rat := exceeded.foldl (fun acc n => acc + (s.prejacent : Rat) - (n : Rat)) 0
       total / (exceeded.length : Rat)

/-- Combined felicity degree: proportion × mean excess.
    Higher values = more felicitous. -/
def felicityDegree (s : EvenScenario) : Rat :=
  proportionExceeded s * meanExcess s

/-- Scenario 2 (Albert failing) has higher felicity degree than scenario 1
    (Albert passing), matching the intuition that scenario 2 is felicitous
    and scenario 1 is not. -/
theorem scenario2_more_felicitous_than_scenario1 :
    felicityDegree scenario1 < felicityDegree scenario2 := by native_decide

/-- Andre far above average: very high felicity degree. -/
def scenarioAndreFar : EvenScenario :=
  { description := "Even Andre cannot reach the top shelf (by far the tallest)"
    prejacent := 9
    neighbors := [3, 4, 5, 2, 3]
    felicitous := true }

/-- Andre barely tallest: lower felicity degree. -/
def scenarioAndreBarely : EvenScenario :=
  { description := "Even Andre cannot reach the top shelf (barely tallest)"
    prejacent := 6
    neighbors := [5, 5, 4, 5, 5]
    felicitous := true }

/-- Andre by far exceeds more, matching Francescotti's gradient intuition. -/
theorem andre_far_more_felicitous :
    felicityDegree scenarioAndreBarely < felicityDegree scenarioAndreFar := by
  native_decide

end Phenomena.Focus.Studies.Francescotti1995
