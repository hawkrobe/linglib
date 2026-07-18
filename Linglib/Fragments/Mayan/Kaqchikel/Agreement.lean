import Linglib.Features.Case.Basic
import Linglib.Features.Prominence
import Linglib.Fragments.Mayan.Params

/-!
# Kaqchikel Agreement Fragment

Typological metadata for Kaqchikel (K'ichean, Mayan) agreement
morphology, following [preminger-2014]: paradigm exponents,
person-number cells, and argument positions.

Kaqchikel cross-references both transitive arguments. Set A (ERG)
prefixes index the transitive agent; Set B (ABS) pre-stem markers
index the absolutive argument (transitive patient or intransitive S);
morpheme order is aspect–ABS–ERG–stem, so Set B precedes Set A
([preminger-2014] (12)). In Agent Focus constructions the two slots
collapse to a single marker drawn from the Set B paradigm.

## Main declarations

* `Kaqchikel.setAExponent`, `Kaqchikel.setBExponent`: the Set A (ERG)
  and Set B (ABS) exponent tables ([preminger-2014] table (29)).
* `Kaqchikel.absPosition`: HIGH-ABS morpheme placement.
* `Kaqchikel.ArgPosition` with `.case`, `.accCase`, `.IsPhiAgreed`:
  argument positions, their case wiring, and the (non-differential)
  φ-agreement status of each position.
* `Kaqchikel.caseInventory`: the {ERG, ABS} case inventory, validated
  against [blake-1994]'s hierarchy.

## Implementation notes

Hosting Set A on Voice/v and Set B on Infl/T follows the standard
high-abs analysis (consistent with [preminger-2014] and
[coon-mateo-pedro-preminger-2014]). Kaqchikel indexes every core
argument, in contrast with San Juan Atitán Mam, where Infl's φ-probe
is blocked in transitives and the patient goes unagreed ([scott-2023];
see `Mam/Agreement.lean`) — the non-differential/differential pair
consumed by `Studies/Aissen2003Agreement.lean`. The AF agreement table
([preminger-2014] §3.2, table (22)) and the choice rule that predicts
it live in `Studies/Preminger2014.lean`. The non-perfective `accCase`
records [imanishi-2014]'s analysis of the progressive *ajin*
construction — an analysis, not consensus typology; the derivation
lives with `Mayan.accCaseKaqchikel` in `Fragments/Mayan/Params.lean`.
Parenthesized exponent segments drop in certain phonological contexts.
Person-number cells come from the canonical `Agreement.Cell`
(`Syntax/Agreement/Paradigm.lean`).
-/

namespace Kaqchikel

open Mayan (ExponentTable)
open Agreement
open Features.Prominence (ArgumentRole)

/-! ### ABS position (HIGH-ABS) -/

/-- HIGH-ABS: the absolutive markers sit between the aspect marker and the stem. -/
def absPosition : Mayan.ABSPosition := .high

/-! ### Set A (ERG) exponents -/

/-- Set A (ERG) markers ([preminger-2014] ex. (29)) by
    following-segment environment. Preminger's table glosses its
    parenthesized segments only as "dropped in certain phonological
    contexts"; the pre-consonantal vs pre-vocalic assignment below is
    the standard K'ichean reading (cognate with the verified K'iche'
    paradigm, [mondloch-2017]). 3sg pre-consonantal *ru-* has a
    dialectal variant *u-* (Preminger's "r(u)/u-"). -/
def setAExponent : Morphology.Following → ExponentTable
  | .consonant =>
    [(.pn .first .Sing, [.pref "n"]), (.pn .second .Sing, [.pref "a"]),
     (.pn .third .Sing, [.pref "ru"]), (.pn .first .Plur, [.pref "qa"]),
     (.pn .second .Plur, [.pref "i"]), (.pn .third .Plur, [.pref "ki"])]
  | .vowel =>
    [(.pn .first .Sing, [.pref "w"]), (.pn .second .Sing, [.pref "aw"]),
     (.pn .third .Sing, [.pref "r"]), (.pn .first .Plur, [.pref "q"]),
     (.pn .second .Plur, [.pref "iw"]), (.pn .third .Plur, [.pref "k"])]

/-! ### Set B (ABS) exponents -/

/-- Set B (ABS) markers; ∅ 3SG doubles as the Elsewhere default
    ([preminger-2014] table (29), Ch. 5). -/
def setBExponent : ExponentTable :=
  [(.pn .first .Sing, [.pref "in"]), (.pn .second .Sing, [.pref "at"]),
   (.pn .third .Sing, []), (.pn .first .Plur, [.pref "oj"]),
   (.pn .second .Plur, [.pref "ix"]), (.pn .third .Plur, [.pref "e"])]

/-! ### Argument positions -/

/-- Argument positions, aliased to the canonical
    `Features.Prominence.ArgumentRole` (S/A/P/R/T). -/
abbrev ArgPosition := Features.Prominence.ArgumentRole

/-- Perfective (ergative) case assignment: `Mayan.ergCaseKaqchikel`
    (A → ERG, S/P → ABS). -/
abbrev ArgPosition.case : ArgPosition → Case :=
  Mayan.ergCaseKaqchikel

/-- Non-perfective (PROG *ajin*) case assignment: `Mayan.accCaseKaqchikel`
    (S/A → ABS, P → ERG/GEN, per [imanishi-2014]). -/
abbrev ArgPosition.accCase : ArgPosition → Case :=
  Mayan.accCaseKaqchikel

/-- Every position triggers φ-agreement — Kaqchikel is non-differential
    (contrast `Mam.ArgPosition.IsPhiAgreed`); R/T default to
    participating. -/
def ArgPosition.IsPhiAgreed : ArgPosition → Prop
  | .A | .P | .S | .R | .T => True

instance : DecidablePred ArgPosition.IsPhiAgreed := fun p =>
  match p with
  | .A | .P | .S | .R | .T => isTrue trivial

/-! ### Verification: argument positions

Each fact below re-exports its `Alignment.ergative` lemma; the
family-level statement is
`CoonMateoPedroPreminger2014.mayan_perfective_ergative`. -/

/-- Agent gets ERG (from Voice). -/
theorem A_case : ArgPosition.case .A = .erg := Alignment.ergative.assignCase_A

/-- Patient gets ABS (from Infl). -/
theorem P_case : ArgPosition.case .P = .abs := Alignment.ergative.assignCase_P

/-- Intransitive S gets ABS (from Infl). -/
theorem S_case : ArgPosition.case .S = .abs := Alignment.ergative.assignCase_S

/-- Ergative-absolutive alignment: the agent is distinguished (ERG)
    while patient and intranS share a case value (ABS). -/
theorem erg_abs_alignment :
    ArgPosition.case .A ≠ ArgPosition.case .P ∧
    ArgPosition.case .P = ArgPosition.case .S :=
  Alignment.ergative_distinguishes_A

/-- All core argument positions trigger φ-agreement. -/
theorem all_positions_agreed (p : ArgPosition) (_ : p ∈ ArgumentRole.core) :
    ArgPosition.IsPhiAgreed p := by
  cases p <;> trivial

/-! ### Case inventory ([blake-1994]) -/

/-- The case inventory realized by the core positions: {ERG, ABS}. -/
def caseInventory : Finset Case := (ArgumentRole.core.map ArgPosition.case).toFinset

/-- The inventory covers all argument positions: every position's case
    is in the inventory. -/
theorem inventory_covers_positions :
    ∀ p ∈ ArgumentRole.core, ArgPosition.case p ∈ caseInventory := by decide

-- Kaqchikel's {ERG, ABS} inventory is valid per Blake's case hierarchy
-- (both are core cases at the top `hierarchyRank`, trivially no gaps).
example : Case.IsValidInventory caseInventory := by decide

end Kaqchikel
