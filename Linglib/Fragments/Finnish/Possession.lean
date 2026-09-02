import Linglib.Features.Number.Basic

/-!
# Finnish Possessive Constructions
[stassen-2009] [nichols-1986] [heine-1997]

Finnish (Uralic) derives its primary have-construction from the **Location
Schema** ("Y is located at X" → "X has Y"): possessor in the adessive
(-lla / -llä 'on, at'), possessum in the nominative as grammatical subject,
copula `olla` 'to be'. The adessive is etymologically locative ('on the
surface of'), grammaticalized to mark the possessor; in possessive use it is
no longer interpreted as locative by speakers ([heine-1997] Overlap Model,
Stage III). The typological codings (WALS 24A, 58A, 59A, 117A) are read from
`Data/WALS/Features/`; this file holds the possessive suffix paradigm.

## Examples

- `Minulla on kirja.` 'I have a book.' (I.ADESS is book)
- `Isällä on auto.` 'Father has a car.' (father.ADESS is car)
- `Minulla ei ole rahaa.` 'I have no money.' (I.ADESS not be money.PART)
-/

namespace Finnish.Possession

/-- Finnish possessive suffixes on the possessum (attributive possession).
    These are declining in spoken Finnish but required in formal/written
    registers. -/
inductive FiPossPerson where | first | second | third
  deriving DecidableEq, Repr

inductive FiPossNumber where | sg | pl
  deriving DecidableEq, Repr

/-- The possessive paradigm's number dimension, canonically. -/
def FiPossNumber.toNumber : FiPossNumber → Number
  | .sg => .singular
  | .pl => .plural

def possSuffix : FiPossPerson → FiPossNumber → String
  | .first,  .sg => "-ni"
  | .second, .sg => "-si"
  | .third,  _   => "-nsa/-nsä"
  | .first,  .pl => "-mme"
  | .second, .pl => "-nne"

end Finnish.Possession
