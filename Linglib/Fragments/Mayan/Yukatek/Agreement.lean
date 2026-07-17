import Linglib.Features.Case.Basic
import Linglib.Features.Prominence
import Linglib.Fragments.Mayan.Params

/-!
# Yucatec Maya Agreement Fragment

Typological metadata for Yucatec Maya (Yucatecan, Mayan) agreement
morphology, following [hofling-2017]: paradigm exponents and argument
positions.

Yucatec person markers divide into Set A prefixes/proclitics and Set B
suffixes. Set A marks transitive subjects, intransitive subjects in the
incompletive status, and possessors; Set B marks transitive objects,
intransitive subjects in the completive and dependent statuses, and
stative subjects — the Yucatecan status-based split. The verbal complex
runs aspect–Set A–root–status–Set B (*táan u-muk-ik-en* 's/he is
burying me', [hofling-2017] Table 24.15): Yucatec is LOW-ABS.

## Main declarations

* `Yukatek.setAExponent`, `Yukatek.setBExponent`: the Set A and Set B
  exponent tables ([hofling-2017] Tables 24.8, 24.12).
* `Yukatek.absPosition`: LOW-ABS morpheme placement.
* `Yukatek.ArgPosition` with `.case`, `.accCase`: argument positions and
  their completive (ergative) and incompletive (extended-ergative) case.

## Implementation notes

The six-cell tables use the exclusive base for 1PL (*k-* Set A, *-o'on*
Set B; the inclusives add *-e'ex*) and the table's parenthesized
prevocalic allomorphs (*inw-*, *aw-*, *uy-*). Plural 2nd/3rd Set A
combine the singular prefix with *-e'ex* and *-o'ob'*. Set B 3SG is
written `-∅` per the family convention (`-Ø` in the source). Case wiring
reuses `Mayan.caseYukatek`; the AF construction (marked by the absence
of expected morphology, [aissen-2017] rather than a dedicated morpheme)
is not yet encoded.
-/

namespace Yukatek

open Mayan (ExponentTable)

/-! ### ABS position (LOW-ABS) -/

/-- LOW-ABS: the Set B suffixes follow the stem and status suffix. -/
def absPosition : Mayan.ABSPosition := .low

/-! ### Set A exponents -/

/-- Set A markers ([hofling-2017] Table 24.8). -/
def setAExponent : ExponentTable :=
  [(.pn .first .Sing, "in(w)-"), (.pn .second .Sing, "a(w)-"), (.pn .third .Sing, "u(y)-"),
   (.pn .first .Plur, "k-"), (.pn .second .Plur, "a(w)-…-e'ex"),
   (.pn .third .Plur, "u(y)-…-o'ob'")]

/-! ### Set B exponents -/

/-- Set B markers; ∅ 3SG ([hofling-2017] Table 24.12). -/
def setBExponent : ExponentTable :=
  [(.pn .first .Sing, "-en"), (.pn .second .Sing, "-ech"), (.pn .third .Sing, "-∅"),
   (.pn .first .Plur, "-o'on"), (.pn .second .Plur, "-e'ex"), (.pn .third .Plur, "-o'ob'")]

/-- 3rd person absolutive is null, as across the standard Mayan
    branches ([kaufman-norman-1984] Table 8). -/
theorem p3sg_abs_null : setBExponent.realize (.pn .third .Sing) = some "-∅" := rfl

/-! ### Argument positions -/

/-- Argument positions, aliased to the canonical
    `Features.Prominence.ArgumentRole` (S/A/P/R/T). -/
abbrev ArgPosition := Features.Prominence.ArgumentRole

/-- Completive (ergative) case assignment: `Mayan.ergCaseYukatek`
    (A → ERG, S/P → ABS). -/
abbrev ArgPosition.case : ArgPosition → Case := Mayan.ergCaseYukatek

/-- Incompletive (extended-ergative) case assignment:
    `Mayan.accCaseYukatek` (S/A → Set A, P → Set B; [hofling-2017]
    p. 692). -/
abbrev ArgPosition.accCase : ArgPosition → Case := Mayan.accCaseYukatek

end Yukatek
