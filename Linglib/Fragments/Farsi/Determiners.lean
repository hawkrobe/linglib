import Linglib.Data.UD.Basic
import Linglib.Semantics.Quantification.ChoiceFunction
import Mathlib.Data.Rat.Defs

/-!
# Farsi determiners and indefinites

The numeral *yek* (*ye* in the informal register) forms *yek* DPs with a bare NP and
*yek-i* DPs with an NP carrying the indefinite enclitic *-i*; the latter are existential free
choice items ([alonso-ovalle-moghiseh-2025a]). The plain indefinites *ye*, *čand-ta*, and
*do-ta* are choice-function indefinites with an independent world variable
([mirrazi-2024]).
-/

namespace Farsi.Determiners

/-- A Farsi indefinite determiner. -/
structure IndefiniteDeterminer where
  /-- Surface form (Persian script) -/
  form : String
  /-- Romanization -/
  romanization : String
  /-- Gloss -/
  gloss : String
  /-- Is this an existential free choice item? -/
  isEFCI : Bool := false
  deriving Repr, BEq

/-- *yek-i*: the numeral with an *-i*-marked NP, an existential free choice item. -/
def yeki : IndefiniteDeterminer :=
  { form := "یکی", romanization := "yek-i", gloss := "one-INDF", isEFCI := true }

/-- *yek*: the plain numeral. -/
def yek : IndefiniteDeterminer := { form := "یک", romanization := "yek", gloss := "one" }

/-- The indefinite enclitic *-i*. -/
def indef_i : IndefiniteDeterminer := { form := "ـی", romanization := "-i", gloss := "-INDF" }

open Quantification.ChoiceFunction (IndefType SkolemCF)

/-- A plain indefinite with the choice-function properties of [mirrazi-2024]. -/
structure PlainIndefiniteEntry extends IndefiniteDeterminer where
  /-- Semantic analysis: choice function or ∃-quantifier. -/
  indefType : IndefType
  /-- Does this determiner carry an independent world/situation variable? -/
  hasWorldVar : Bool
  /-- Number: singular or plural. -/
  isPlural : Bool
  deriving Repr

/-- *ye*: the singular indefinite determiner, with wide pseudo-scope de dicto readings under
negated intensional operators ([mirrazi-2024] exx. (1), (4)). -/
def ye : PlainIndefiniteEntry :=
  { form := "یه", romanization := "ye", gloss := "some", indefType := .choiceFunction,
    hasWorldVar := true, isPlural := false }

/-- *čand-ta*: the plural classifier indefinite, alternating with *ye* in [mirrazi-2024]'s
key examples. -/
def candTa : PlainIndefiniteEntry :=
  { form := "چندتا", romanization := "čand-ta", gloss := "some.PL-CL",
    indefType := .choiceFunction, hasWorldVar := true, isPlural := true }

/-- *do-ta*: the numeral classifier indefinite ([mirrazi-2024] exx. (8a), (9a)). -/
def doTa : PlainIndefiniteEntry :=
  { form := "دوتا", romanization := "do-ta", gloss := "two-CL", indefType := .choiceFunction,
    hasWorldVar := true, isPlural := true }

end Farsi.Determiners
