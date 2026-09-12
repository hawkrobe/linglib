import Linglib.Data.Examples.Khoo2015

/-!
# Khoo (2015): Modal Disagreements

This file records the experiment of [khoo-2015] on disagreements over epistemic modal claims.
Participants read a control vignette with a non-modal assertion and a modal vignette in which
Smith, having examined evidence consistent with Fat Tony's death, says *Fat Tony might be dead*
while Beth knows him to be alive, and rated on a seven-point scale either whether what the
speaker said is false or whether they would respond *No, ...* (Section II). The Difference
Observation is that the modal claim is rejected readily yet not judged false, a dissociation the
control assertion lacks (`difference_observation`): speakers reject the might-claim without
judging it false.

## Implementation notes

The four cell means and standard deviations, times one hundred, are the rows of
`Data/Examples/Khoo2015.json`, read with `nat?`; the paper's account of the observation is not
formalized.

## References

* [khoo-2015]
-/

namespace Khoo2015

open Data.Examples

/-- The sentence type of a vignette. -/
inductive Sentence where
  | control
  | modal
  deriving DecidableEq, Repr

/-- The question put to participants. -/
inductive Response where
  | false_
  | rejection
  deriving DecidableEq, Repr

def Sentence.tag : Sentence → String
  | .control => "control"
  | .modal => "modal"

def Response.tag : Response → String
  | .false_ => "false"
  | .rejection => "rejection"

/-- The mean rating of a cell, times one hundred. -/
def mean (s : Sentence) (r : Response) : ℕ :=
  ((Examples.all.filter λ e =>
      e.feature? "sentence" = some s.tag ∧ e.feature? "response" = some r.tag).filterMap
    (·.nat? "mean")).headD 0

/-- The Difference Observation: the modal claim is rejected above the scale's midpoint yet
judged false below it, while the control assertion is judged false at least as readily as it
is rejected. -/
theorem difference_observation :
    (400 < mean .modal .rejection ∧ mean .modal .false_ < 400) ∧
      mean .control .rejection ≤ mean .control .false_ := by
  decide

end Khoo2015
