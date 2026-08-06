/-!
# German Clause Types

German clause-type taxonomy: five clause types distinguished by verb
position (V2 vs verb-last) and complementizer presence (dass vs not).
Descriptive German syntax; the sentence-mood analysis built on this
taxonomy ([gutzmann-2015], Ch 5: which mood operators each clause type
composes) lives in `Studies/Gutzmann2015.lean`.

| Clause type       | Example                |
|-------------------|------------------------|
| dass-VL           | "Dass du kommst!"      |
| V2-declarative    | "Jim wohnt in Berlin." |
| VL-interrogative  | "Wann Peter kommt?"    |
| V2-interrogative  | "Kommt Peter?"         |
| Imperative        | "Tritt zurück!"        |
-/

namespace German.ClauseTypes

/-- German clause types distinguished by verb position and
complementizer presence. -/
inductive GermanClauseType where
  /-- dass-VL: complementizer clause, verb-last. -/
  | dassVL
  /-- V2-declarative: finite verb in C⁰. -/
  | v2Declarative
  /-- V2-interrogative: verb-second. -/
  | v2Interrogative
  /-- VL-interrogative: verb-last. -/
  | vlInterrogative
  /-- Imperative. -/
  | imperative
  deriving DecidableEq, Repr

end German.ClauseTypes
