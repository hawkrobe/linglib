import Linglib.Semantics.Evidential.Defs

/-!
# Quechua (Cuzco) Evidentiality
[aikhenvald-2004]

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

def evidentials : List Evidential :=
  [ { form := "-mi", exponent := .clitic2P, covers := {.visual, .sensory} },
    { form := "-si", exponent := .clitic2P, covers := {.hearsay} },
    { form := "-chá", exponent := .clitic2P, covers := {.inference, .assumption} } ]

end Quechua.Evidentiality
