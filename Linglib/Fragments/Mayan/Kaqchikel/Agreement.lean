module

public import Linglib.Syntax.Case.Basic
public import Linglib.Phonology.Segmental.Defs
public import Linglib.Semantics.Reference.Prominence
public import Linglib.Fragments.Mayan.Agreement
public import Linglib.Syntax.Clause.ArgumentRole
public import Linglib.Syntax.Person.Basic

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
* `Kaqchikel.template`, `Kaqchikel.assignCase`: the verbal complex, with Set B
  between the aspect marker and the stem, and case ergative outside the
  progressive; `IsPhiAgreed` records the (non-differential) φ-agreement
  status of each position.
* `Kaqchikel.caseInventory`: the {ERG, ABS} case inventory.

## Implementation notes

Hosting Set A on Voice/v and Set B on Infl/T follows the standard
high-abs analysis (consistent with [preminger-2014] and
[coon-mateo-pedro-preminger-2014]). Kaqchikel indexes every core
argument, in contrast with San Juan Atitán Mam, where Infl's φ-probe
is blocked in transitives and the patient goes unagreed ([scott-2023];
see `Mam/Agreement.lean`). The AF agreement table
([preminger-2014] §3.2, table (22)) and the choice rule that predicts
it live in `Studies/Preminger2014.lean`. The progressive case pattern
(`Kaqchikel.assignCase .Prog`) records [imanishi-2014]'s analysis of the
progressive *ajin* construction — an analysis, not consensus typology;
the derivation lives in `Studies/Imanishi2014.lean`.
Parenthesized exponent segments drop in certain phonological contexts.
Person-number cells come from the canonical `Agreement.Bundle`
(`Syntax/Agreement/Paradigm.lean`).
-/

@[expose] public section

namespace Kaqchikel

open Mayan (ExponentTable)
open Agreement

/-! ### The verbal complex -/

/-- The Kaqchikel verbal complex has the aspect marker, Set B and Set A before the stem and the
status suffix after it ([preminger-2014]). -/
def template : Morphology.AffixTemplate Mayan.VerbSlot := ⟨[.aspect, .setB, .setA], [.status]⟩

/-- Kaqchikel is ergative in every aspect but the progressive, where in the construction with
the matrix predicate *ajin* Set A cross-references the object rather than the subject, the
inverted alignment [imanishi-2014] analyses; some varieties lack the pattern. -/
def assignCase : UD.Aspect → ArgumentRole → Case
  | .Prog => Alignment.invertedErgative
  | .Perf | .Imp | .Prosp | .Hab | .Iter => Alignment.ergative

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
    [(.personNumber .first .singular, [.pref "n"]), (.personNumber .second .singular, [.pref "a"]),
     (.personNumber .third .singular, [.pref "ru"]), (.personNumber .first .plural, [.pref "qa"]),
     (.personNumber .second .plural, [.pref "i"]), (.personNumber .third .plural, [.pref "ki"])]
  | .vowel =>
    [(.personNumber .first .singular, [.pref "w"]), (.personNumber .second .singular, [.pref "aw"]),
     (.personNumber .third .singular, [.pref "r"]), (.personNumber .first .plural, [.pref "q"]),
     (.personNumber .second .plural, [.pref "iw"]), (.personNumber .third .plural, [.pref "k"])]

/-! ### Set B (ABS) exponents -/

/-- Set B (ABS) markers; ∅ 3SG doubles as the Elsewhere default
    ([preminger-2014] table (29), Ch. 5). -/
def setBExponent : ExponentTable :=
  [(.personNumber .first .singular, [.pref "in"]), (.personNumber .second .singular, [.pref "at"]),
   (.personNumber .third .singular, []), (.personNumber .first .plural, [.pref "oj"]),
   (.personNumber .second .plural, [.pref "ix"]), (.personNumber .third .plural, [.pref "e"])]

/-! ### Argument positions -/

/-- Every position triggers φ-agreement — Kaqchikel is non-differential, where San Juan
    Atitán Mam leaves objects unagreed (`Mam.defaultSetB`); R/T default to participating. -/
def IsPhiAgreed : ArgumentRole → Prop
  | .A | .P | .S | .R | .T => True

instance : DecidablePred IsPhiAgreed := fun p =>
  match p with
  | .A | .P | .S | .R | .T => isTrue trivial

/-! ### Alignment -/

/-- The perfective is ergatively aligned: A apart, S with P; the family-level statement is
`CoonMateoPedroPreminger2014.isErgativePerfective_iff`. -/
theorem isErgative_perfective : Alignment.IsErgative (assignCase .Perf) :=
  Alignment.isErgative_ergative

/-- All core argument positions trigger φ-agreement. -/
theorem all_positions_agreed (p : ArgumentRole) (_ : p ∈ ArgumentRole.core) :
    IsPhiAgreed p := by
  cases p <;> trivial

/-! ### Case inventory -/

/-- The core positions realize the cases ERG and ABS. -/
def caseInventory : Finset Case := (ArgumentRole.core.map (assignCase .Perf)).toFinset

/-- The inventory covers all argument positions: every position's case
    is in the inventory. -/
theorem inventory_covers_positions :
    ∀ p ∈ ArgumentRole.core, (assignCase .Perf) p ∈ caseInventory := by decide

end Kaqchikel
