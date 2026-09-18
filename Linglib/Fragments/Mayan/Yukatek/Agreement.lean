import Linglib.Syntax.Case.Basic
import Linglib.Phonology.Segmental.Defs
import Linglib.Semantics.Reference.Prominence
import Linglib.Fragments.Mayan.Agreement
import Linglib.Syntax.Clause.ArgumentRole

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
* `Yukatek.template`, `Yukatek.assignCase`: the verbal complex, with Set B after
  the status suffix, and case ergative in the completive and extended-ergative
  in the incompletive.

## Implementation notes

The six-cell tables use the exclusive base for 1PL (*k-* Set A, *-o'on*
Set B; the inclusives add *-e'ex*) and the table's parenthesized
prevocalic allomorphs (*inw-*, *aw-*, *uy-*). Plural 2nd/3rd Set A
combine the singular prefix with *-e'ex* and *-o'ob'*. Set B 3SG is
written `-∅` per the family convention (`-Ø` in the source). The AF construction (marked by
the absence
of expected morphology, [aissen-2017] rather than a dedicated morpheme)
is not yet encoded.
-/

namespace Yukatek

open Mayan (ExponentTable)

/-! ### The verbal complex -/

/-- The position classes of the Yucatec verbal complex: the aspect marker and Set A before the
stem, the status suffix and then Set B after it ([hofling-2017]). -/
def template : Morphology.AffixTemplate Mayan.VerbSlot := ⟨[.aspect, .setA], [.status, .setB]⟩

/-- Yucatec is ergative in the completive, the perfective, and puts Set A on every subject in
the incompletive aspects ([hofling-2017]). -/
def assignCase : UD.Aspect → ArgumentRole → Case
  | .Perf => Alignment.ergative
  | .Imp | .Prog | .Prosp | .Hab | .Iter => Alignment.extendedErgative

/-! ### Set A exponents -/

/-- Set A markers by following-segment environment ([hofling-2017]
    Table 24.8, where the pre-vocalic glide is parenthesized:
    *in(w)-*, *a(w)-*, *u(y)-*). 2pl/3pl are discontinuous: person
    prefix plus the plural suffixes *-e'ex*/*-o'ob'*. -/
def setAExponent : Phonology.Segment.Class → ExponentTable
  | .consonant =>
    [(.pn .first .singular, [.pref "in"]), (.pn .second .singular, [.pref "a"]),
     (.pn .third .singular, [.pref "u"]), (.pn .first .plural, [.pref "k"]),
     (.pn .second .plural, [.pref "a", .suff "e'ex"]),
     (.pn .third .plural, [.pref "u", .suff "o'ob'"])]
  | .vowel =>
    [(.pn .first .singular, [.pref "inw"]), (.pn .second .singular, [.pref "aw"]),
     (.pn .third .singular, [.pref "uy"]), (.pn .first .plural, [.pref "k"]),
     (.pn .second .plural, [.pref "aw", .suff "e'ex"]),
     (.pn .third .plural, [.pref "uy", .suff "o'ob'"])]

/-! ### Set B exponents -/

/-- Set B markers; zero-exponence 3SG ([hofling-2017] Table 24.12). -/
def setBExponent : ExponentTable :=
  [(.pn .first .singular, [.suff "en"]), (.pn .second .singular, [.suff "ech"]),
   (.pn .third .singular, []), (.pn .first .plural, [.suff "o'on"]),
   (.pn .second .plural, [.suff "e'ex"]), (.pn .third .plural, [.suff "o'ob'"])]

/-- 3rd person absolutive is null, as across the standard Mayan
    branches ([kaufman-norman-1984] Table 8). -/
theorem p3sg_abs_null : setBExponent.realize (.pn .third .singular) = some [] := rfl

end Yukatek
