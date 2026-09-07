import Linglib.Semantics.Tense.Evidential

/-!
# Korean evidential fragment
[cumming-2026]

Paradigm cells for Korean tense under the evidentials *-te* (table (18)) and *-ney*
(table (19)) of [cumming-2026], following [lee-2011] and [lee-2013]: under either
evidential, tense fixes the evidential perspective, while *-te* places the sensory evidence
in the past of speech and *-ney* at speech, so that the utterance perspective is derived. The
printed rows of table (19) are labelled *-te* under the *-ney* heading.
-/

namespace Korean.Evidentials

open Tense.Evidential

/-! ### *-te* (table (18)) -/

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

/-! ### *-ney* (table (19)) -/

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
