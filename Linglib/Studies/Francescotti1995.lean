import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Linglib.Semantics.Focus.Particles

/-!
# [francescotti-1995]

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
    not just one ([bennett-1982]), not all ([karttunen-peters-1979]).

## Formalization

We encode the two key counterexamples as finite scenarios and prove that
only Francescotti's "most" threshold gives the correct predictions for both.
-/

namespace Francescotti1995

open Focus.Particles (EvenThreshold evenPresupWith)

/-! ### Francescotti's threshold -/

/-- Francescotti's revised felicity condition (§IV, p. 162; restated as
    Conclusion §V(d)): S* must be more surprising than MOST of its true
    neighbors — pace [bennett-1982]'s one-neighbor condition and
    [karttunen-peters-1979]'s all-neighbors condition. -/
def evenThreshold : EvenThreshold := .most

/-! ### Threshold predictions -/

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
  decide (evenPresupWith s.prejacent s.neighbors (· > ·) t)

/-!
### Scenario 1: Bennett's threshold is too weak (p. 155)

"Even Albert passed the exam"

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
    predict scenario1 .existential ≠ scenario1.felicitous := by decide

/-- K-P (∀) correctly predicts infelicitous here (but will fail on scenario 2). -/
theorem kp_correct_on_scenario1 :
    predict scenario1 .universal = scenario1.felicitous := by decide

/-- Francescotti (most) correctly predicts infelicitous:
    Albert(2) exceeds only 1 of 4 neighbors (25% < 50%). -/
theorem francescotti_correct_on_scenario1 :
    predict scenario1 evenThreshold = scenario1.felicitous := by decide

/-!
### Scenario 2: K-P's threshold is too strong (p. 156)

"Even Albert failed the exam"

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
    predict scenario2 .existential = scenario2.felicitous := by decide

/-- K-P (∀) wrongly predicts infelicitous: Albert(8) doesn't exceed Marie(9). -/
theorem kp_wrong_on_scenario2 :
    predict scenario2 .universal ≠ scenario2.felicitous := by decide

/-- Francescotti (most) correctly predicts felicitous:
    Albert(8) exceeds 3 of 4 neighbors (75% > 50%). -/
theorem francescotti_correct_on_scenario2 :
    predict scenario2 evenThreshold = scenario2.felicitous := by decide

/-! ### Summary -/

/-- Francescotti's "most" threshold is the only one that matches
    observed felicity judgments on both scenarios. -/
theorem francescotti_uniquely_correct :
    predict scenario1 evenThreshold = scenario1.felicitous ∧
    predict scenario2 evenThreshold = scenario2.felicitous ∧
    predict scenario1 .existential ≠ scenario1.felicitous ∧
    predict scenario2 .universal ≠ scenario2.felicitous := by decide

/-!
### Gradient felicity (pp. 163–164)

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
  else let total : Rat := exceeded.foldl (fun (acc : Rat) (n : Nat) => acc + (s.prejacent : Rat) - (n : Rat)) 0
       total / (exceeded.length : Rat)

/-- Combined felicity degree: proportion × mean excess.
    Higher values = more felicitous. -/
def felicityDegree (s : EvenScenario) : Rat :=
  proportionExceeded s * meanExcess s

/-- Scenario 2 (Albert failing) has higher felicity degree than scenario 1
    (Albert passing), matching the intuition that scenario 2 is felicitous
    and scenario 1 is not. -/
theorem scenario2_more_felicitous_than_scenario1 :
    felicityDegree scenario1 < felicityDegree scenario2 := by
  norm_num [felicityDegree, proportionExceeded, meanExcess, scenario1, scenario2]

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
  norm_num [felicityDegree, proportionExceeded, meanExcess, scenarioAndreBarely,
    scenarioAndreFar]

end Francescotti1995
