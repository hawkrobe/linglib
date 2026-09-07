import Linglib.Semantics.Tense.Evidential

/-!
# Bulgarian evidential fragment
[cumming-2026]

Paradigm cells for Bulgarian tense under the evidential *-l* (table (17)) of
[cumming-2026], following [koev-2017]: the nonfuture requires evidence downstream of the
event, the future prospective evidence, and the event may lie in the past under either.
-/

namespace Bulgarian.Evidentials

open Tense.Evidential

/-- Nonfuture under *-l*: downstream evidence for a nonfuture event. -/
def nfutL : TAMEEntry where
  label := "NFUT + -l"
  ep := .downstream
  up := .nonfuture

/-- Future under *-l*: prospective evidence, the utterance perspective open. -/
def futL : TAMEEntry where
  label := "FUT + -l"
  ep := .prospective
  up := .unconstrained

/-- The Bulgarian evidential cells. -/
def allEntries : List TAMEEntry :=
  [nfutL, futL]

end Bulgarian.Evidentials
