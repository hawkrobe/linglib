import Linglib.Semantics.Tense.Evidential

/-!
# Korean tense under the evidentials

The cells of Korean tense under the evidentials *-te* and *-ney* as Cumming tabulates them
after Lee: under either evidential the tense fixes the perspective of the evidence, while
*-te* places the sensory evidence before the utterance and *-ney* at the utterance, so that the
utterance perspective follows.

## References

* [cumming-2026]
* [lee-2011]
* [lee-2013]
-/

namespace Korean.Evidentials

open Tense.Evidential

/-! ### *-te* -/

/-- Past under *-te*: the event precedes the past sensory evidence. -/
def tePast : TAMEEntry where
  label := "-te PAST"
  ep := .strictDownstream
  up := .past

/-- Present under *-te*: the event coincides with the past sensory evidence. -/
def tePresent : TAMEEntry where
  label := "-te PRES"
  ep := .contemporaneous
  up := .past

/-- Future under *-te*: prospective evidence, the utterance perspective open. -/
def teFuture : TAMEEntry where
  label := "-te FUT"
  ep := .prospective
  up := .unconstrained

/-! ### *-ney* -/

/-- Past under *-ney*: the event precedes the present sensory evidence. -/
def neyPast : TAMEEntry where
  label := "-ney PAST"
  ep := .strictDownstream
  up := .past

/-- Present under *-ney*: the event coincides with the present sensory evidence. -/
def neyPresent : TAMEEntry where
  label := "-ney PRES"
  ep := .contemporaneous
  up := .present

/-- Future under *-ney*: prospective present evidence for a future event. -/
def neyFuture : TAMEEntry where
  label := "-ney FUT"
  ep := .prospective
  up := .future

/-- The cells under *-te*. -/
def teEntries : List TAMEEntry :=
  [tePast, tePresent, teFuture]

/-- The cells under *-ney*. -/
def neyEntries : List TAMEEntry :=
  [neyPast, neyPresent, neyFuture]

/-- The Korean evidential cells. -/
def allEntries : List TAMEEntry :=
  teEntries ++ neyEntries

end Korean.Evidentials
