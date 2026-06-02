import Linglib.Semantics.Evidential.Defs

/-!
# Quechua (Cuzco) Evidentiality
@cite{aikhenvald-2004}

Three-or-more system: direct *-mi*, reportative *-si*, conjectural *-chá*.
Obligatory enclitics on finite clauses. Canonical Andean evidential system.
WALS Ch 77 has no entry for Cuzco Quechua (`quz`); the fallback fires.

The local `EvidentialSystem` enum extends WALS Ch 77's 3-way to a 4-way
by adding `threeOrMore` precisely to capture this Andean pattern.
-/

namespace Quechua.Evidentiality

/-! ### Typed evidential inventory

Cuzco Quechua's canonical B1 Andean system: direct `-mi`, reportative
`-si`, conjectural/inferential `-chá`. Obligatory second-position
clitics on finite clauses. -/

open Semantics.Evidential

def evidentials : List Entry :=
  [ .direct      { form := "-mi",   exponent := .clitic2P },
    .reportative { form := "-si",   exponent := .clitic2P,
                   sourceIdentity := .unidentified },
    .inferential { form := "-chá",  exponent := .clitic2P } ]

example : evidentials.length = 3 := by decide
example : (evidentials.filter Entry.IsDirect).length = 1 := by decide
example : (evidentials.filter Entry.IsReportative).length = 1 := by decide
example : (evidentials.filter Entry.IsInferential).length = 1 := by decide

end Quechua.Evidentiality
