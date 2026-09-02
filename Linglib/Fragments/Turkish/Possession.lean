import Linglib.Features.Number.Basic

/-!
# Turkish Possessive Constructions
[stassen-2009] [nichols-1986] [heine-1997]

Turkish (Turkic) derives its primary have-construction from the **Genitive
Schema** ("X's Y exists" → "X has Y"): possessor in the genitive (`-(n)In`),
possessum with a possessive agreement suffix (`-(s)I`), and the non-verbal
existential predicate `var` 'existent' (or `yok` 'non-existent'), which takes
no tense/aspect morphology in its base form. Turkish also has a Goal Schema
variant using the dative (`-A`) with existential `var`, and the Equation
Schema for belong-constructions (`Kitap Hasan-ın.` 'The book is Hasan's.').
The typological codings (WALS 24A, 58A, 59A, 117A) are read from
`Data/WALS/Features/`; this file holds the possessive suffix paradigm and the
existential predicate.

## Examples

- `Hasan-ın inek-i var.` 'Hasan has a cow.' (Hasan-GEN cow-POSS existent)
- `Bende kitap var.` 'I have a book.' (at-me book existent; Location variant)
- `Kitab-ım var.` 'I have a book.' (book-POSS.1SG existent; Genitive)
-/

namespace Turkish.Possession

/-- Turkish possessive suffix paradigm. These suffixes appear on the
    possessum and agree with the possessor in person and number. -/
inductive PossPerson where
  | first | second | third
  deriving DecidableEq, Repr

inductive PossNumber where
  | sg | pl
  deriving DecidableEq, Repr

/-- The possessive paradigm's number dimension, canonically. -/
def PossNumber.toNumber : PossNumber → Number
  | .sg => .singular
  | .pl => .plural

/-- Possessive suffix forms (after consonant-final stems). -/
def possSuffix : PossPerson → PossNumber → String
  | .first,  .sg => "-(I)m"
  | .second, .sg => "-(I)n"
  | .third,  .sg => "-(s)I"
  | .first,  .pl => "-(I)mIz"
  | .second, .pl => "-(I)nIz"
  | .third,  .pl => "-lArI"

/-- The existential predicate in Turkish possessive constructions: a non-verbal
    predicate that takes no tense/aspect morphology in the base form. -/
inductive ExistPred where
  /-- `var` 'existent, there is' — affirmative possession -/
  | var
  /-- `yok` 'non-existent, there is not' — negative possession -/
  | yok
  deriving DecidableEq, Repr

end Turkish.Possession
