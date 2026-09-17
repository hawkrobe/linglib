import Linglib.Syntax.Category.Determiner.Basic

/-!
# ASL quantifier signs

The quantificational signs of American Sign Language attested with locus and height
modification in [davidson-gagne-2022], as marked `QuantifierDeterminer` records under the ASL
Signbank ID glosses: `FS(ALL)` is the fingerspelled universal, `ALL-b` its two-handed form,
`NONEsym` the symmetrical negative quantifier. Which of them carry a height-marked locus
themselves and which take a following `IX-arc` is a matter of their phonological form and is
classified in the
study, not here.

## References

* [K. Davidson and D. Gagne, *"More is up" for domain restriction in ASL*
  (2022)][davidson-gagne-2022]
-/

namespace ASL.Determiners

/-- `FS(ALL)`: the fingerspelled universal quantifier. -/
def fsAll : QuantifierDeterminer := { form := "FS(ALL)", numberRestriction := some .plural }

/-- `ALL-b`: the two-handed universal quantifier. -/
def allB : QuantifierDeterminer := { form := "ALL-b", numberRestriction := some .plural }

/-- `NONEsym`: the symmetrical negative quantifier. -/
def noneSym : QuantifierDeterminer := { form := "NONEsym" }

/-- `SOMEONE`: the existential over persons. -/
def someone : QuantifierDeterminer := { form := "SOMEONE", numberRestriction := some .singular }

/-- `SOMETHING`: the existential over things. -/
def something : QuantifierDeterminer :=
  { form := "SOMETHING", numberRestriction := some .singular }

/-- `ONE` as a quantifier. -/
def one : QuantifierDeterminer := { form := "ONE", numberRestriction := some .singular }

/-- `TWO` as a quantifier. -/
def two : QuantifierDeterminer := { form := "TWO", numberRestriction := some .plural }

/-- `MANY`. -/
def many : QuantifierDeterminer := { form := "MANY", numberRestriction := some .plural }

/-- `FEW`. -/
def few : QuantifierDeterminer := { form := "FEW", numberRestriction := some .plural }

/-- `EACH`. -/
def each : QuantifierDeterminer := { form := "EACH", numberRestriction := some .singular }

/-- `MOST`. -/
def most : QuantifierDeterminer := { form := "MOST", numberRestriction := some .plural }

/-- The quantifier signs attested in the paper. -/
def all : List QuantifierDeterminer :=
  [fsAll, allB, noneSym, someone, something, one, two, many, few, each, most]

end ASL.Determiners
