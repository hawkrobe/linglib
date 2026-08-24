import Linglib.Features.Case.Basic
import Linglib.Phonology.Segmental.Defs
import Linglib.Features.Prominence
import Linglib.Fragments.Mayan.Params
import Linglib.Syntax.Clause.ArgumentRole
import Linglib.Features.Person.Basic

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
* Case assignment over `ArgumentRole` via `(Mayan.caseKaqchikel .Perf)` and
  `(Mayan.caseKaqchikel .Prog)`; `IsPhiAgreed` records the (non-differential)
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
consumed by `Studies/Just2024.lean`. The AF agreement table
([preminger-2014] §3.2, table (22)) and the choice rule that predicts
it live in `Studies/Preminger2014.lean`. The non-perfective case pattern
(`Mayan.caseKaqchikel .Prog`) records [imanishi-2014]'s analysis of the
progressive *ajin* construction — an analysis, not consensus typology;
the derivation lives in `Fragments/Mayan/Params.lean`.
Parenthesized exponent segments drop in certain phonological contexts.
Person-number cells come from the canonical `Agreement.Cell`
(`Syntax/Agreement/Paradigm.lean`).
-/

namespace Kaqchikel

open Mayan (ExponentTable)
open Agreement

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
def setAExponent : Phonology.Segment.Class → ExponentTable
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

/-- Every position triggers φ-agreement — Kaqchikel is non-differential
    (contrast `Mam.IsPhiAgreed`); R/T default to
    participating. -/
def IsPhiAgreed : ArgumentRole → Prop
  | .A | .P | .S | .R | .T => True

instance : DecidablePred IsPhiAgreed := fun p =>
  match p with
  | .A | .P | .S | .R | .T => isTrue trivial

/-! ### Verification: argument positions

Each fact below re-exports its `Alignment.ergative` lemma; the
family-level statement is
`CoonMateoPedroPreminger2014.mayan_perfective_ergative`. -/

/-- Agent gets ERG (from Voice). -/
theorem A_case : (Mayan.caseKaqchikel .Perf) .A = .erg := Alignment.ergative.assignCase_A

/-- Patient gets ABS (from Infl). -/
theorem P_case : (Mayan.caseKaqchikel .Perf) .P = .abs := Alignment.ergative.assignCase_P

/-- Intransitive S gets ABS (from Infl). -/
theorem S_case : (Mayan.caseKaqchikel .Perf) .S = .abs := Alignment.ergative.assignCase_S

/-- Ergative-absolutive alignment: the agent is distinguished (ERG)
    while patient and intranS share a case value (ABS). -/
theorem erg_abs_alignment :
    (Mayan.caseKaqchikel .Perf) .A ≠ (Mayan.caseKaqchikel .Perf) .P ∧
    (Mayan.caseKaqchikel .Perf) .P = (Mayan.caseKaqchikel .Perf) .S :=
  Alignment.ergative_distinguishes_A

/-- All core argument positions trigger φ-agreement. -/
theorem all_positions_agreed (p : ArgumentRole) (_ : p ∈ ArgumentRole.core) :
    IsPhiAgreed p := by
  cases p <;> trivial

/-! ### Case inventory ([blake-1994]) -/

/-- The case inventory realized by the core positions: {ERG, ABS}. -/
def caseInventory : Finset Case := (ArgumentRole.core.map (Mayan.caseKaqchikel .Perf)).toFinset

/-- The inventory covers all argument positions: every position's case
    is in the inventory. -/
theorem inventory_covers_positions :
    ∀ p ∈ ArgumentRole.core, (Mayan.caseKaqchikel .Perf) p ∈ caseInventory := by decide

-- Kaqchikel's {ERG, ABS} inventory is valid per Blake's case hierarchy
-- (both are core cases at the top `hierarchyRank`, trivially no gaps).
example : Case.IsValidInventory caseInventory := by decide

end Kaqchikel
