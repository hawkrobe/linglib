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
Person-number cells come from the canonical `Agreement.Cell`
(`Syntax/Agreement/Paradigm.lean`).
-/

namespace Kaqchikel

open Mayan (ExponentTable)
open Agreement
open Features.Prominence (ArgumentRole)

/-! ### ABS position (HIGH-ABS) -/

/-- Kaqchikel's absolutive morphemes appear in HIGH position (between
    the aspect marker and the verb stem): aspect–ABS–ERG–stem
    ([preminger-2014] (12)). -/
def absPosition : Mayan.ABSPosition := .high

/-! ### Set A (ERG) exponents -/

/-- Set A (ERG) markers: prefixes on Voice/v cross-referencing the
    transitive agent ([preminger-2014] Ch. 3, table (29)).
    Parenthesized segments are dropped in certain phonological
    contexts. -/
def setAExponent : ExponentTable :=
  [(.pn .first .Sing, "n/w-"), (.pn .second .Sing, "a(w)-"), (.pn .third .Sing, "r(u)/u-"),
   (.pn .first .Plur, "q(a)-"), (.pn .second .Plur, "i(w)-"), (.pn .third .Plur, "k(i)-")]

/-! ### Set B (ABS) exponents -/

/-- Set B (ABS) markers: pre-stem markers on Infl/T cross-referencing
    the absolutive argument ([preminger-2014] table (29)). The 3SG form
    (∅) is also the Elsewhere entry — the default when no more specific
    entry matches, as in the failure case of obligatory agreement
    (Ch. 5). Citation forms: 1SG and 2SG are *i(n)-* and *a(t)-*, whose
    parenthesized segments drop in certain phonological contexts (e.g.,
    1SG surfaces as *i-* in *x-i-tz'et-ö*); the grapheme *j* (as in
    *oj-*) is a voiceless velar fricative. -/
def setBExponent : ExponentTable :=
  [(.pn .first .Sing, "in-"), (.pn .second .Sing, "at-"), (.pn .third .Sing, "∅"),
   (.pn .first .Plur, "oj-"), (.pn .second .Plur, "ix-"), (.pn .third .Plur, "e-")]

/-! ### Argument positions -/

/-- Argument positions in a Kaqchikel clause. Aliased to the canonical
    `Features.Prominence.ArgumentRole` (S/A/P/R/T) so cross-Mayan and
    cross-framework code shares one inventory. Use the canonical
    constructor names `.A` (transitive agent), `.P` (transitive
    patient), `.S` (intransitive subject) directly. -/
abbrev ArgPosition := Features.Prominence.ArgumentRole

/-- Perfective (ergative) case assignment for Kaqchikel — definitionally
    `Mayan.ergCaseKaqchikel`, derived from `Alignment.ergative.assignCase`
    in `Syntax/Case/Alignment.lean`: A → ERG, S/P → ABS. -/
abbrev ArgPosition.case : ArgPosition → Case :=
  Mayan.ergCaseKaqchikel

/-- Non-perfective (PROG *ajin*) case assignment — definitionally
    `Mayan.accCaseKaqchikel`: [imanishi-2014]'s inverted pattern
    (S/A → ABS, P → ERG/GEN); see `Fragments/Mayan/Params.lean` for the
    derivation and [imanishi-2020] for the parameterization. -/
abbrev ArgPosition.accCase : ArgPosition → Case :=
  Mayan.accCaseKaqchikel

/-- Does this position participate in φ-Agree?
    In Kaqchikel, ALL core argument positions trigger agreement:
    agent via Set A on Voice/v, patient and intranS via Set B on
    Infl/T. This contrasts with San Juan Atitán Mam, where the patient
    is NOT agreed with (Infl's probe is blocked by VoiceP;
    [scott-2023]). Ditransitive R/T default to participating
    (Kaqchikel ditransitive agreement not modeled in this fragment). -/
def ArgPosition.IsPhiAgreed : ArgPosition → Prop
  | .A | .P | .S | .R | .T => True

instance : DecidablePred ArgPosition.IsPhiAgreed := fun p =>
  match p with
  | .A | .P | .S | .R | .T => isTrue trivial

/-! ### Verification: argument positions

The per-position case facts are the ergative-alignment facts
(`Alignment.ergative`) — Kaqchikel's perfective case function is
`Alignment.ergative.assignCase` by definition, so each theorem below is
a re-export of the substrate lemma, and the family-level statement
(every standard Mayan language shares them) is
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

/-- The Kaqchikel case inventory, derived from the core argument
    positions' case values: {ERG, ABS}. -/
def caseInventory : Finset Case := (ArgumentRole.core.map ArgPosition.case).toFinset

/-- The inventory covers all argument positions: every position's case
    is in the inventory. -/
theorem inventory_covers_positions :
    ∀ p ∈ ArgumentRole.core, ArgPosition.case p ∈ caseInventory := by decide

-- Kaqchikel's {ERG, ABS} inventory is valid per Blake's case hierarchy
-- (both are core cases at the top `hierarchyRank`, trivially no gaps).
example : Case.IsValidInventory caseInventory := by decide

end Kaqchikel
