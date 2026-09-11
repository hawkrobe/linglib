import Linglib.Data.Examples.Karlsson2017
import Linglib.Features.Case.Basic
import Linglib.Semantics.Aspect.Basic

/-!
# Karlsson (2017): Finnish: A Comprehensive Grammar

This file formalizes the object-case rules of [karlsson-2017], the alternation between the
partitive and the total object in Finnish. The grammar orders the rules: the object is partitive
if the sentence is negative, the action irresultative, or the quantity indefinite
(section 12.2.2); only otherwise does it take a total-object case, the accusative for a personal
pronoun, the nominative for a plural nominal or a numeral head, and for a singular nominal the
genitive, or the nominative under an imperative, a passive, an obligation, or an infinitive
phrase acting as subject (section 13.3.2). `Object.case` is that procedure, and the grammar's
examples, as rows, agree with it (`rows_agree`).

The partitive is the stronger object case (`case_eq_part_iff`), and in an affirmative sentence
about a definite quantity the object is partitive exactly when the action is irresultative
(`part_iff_atelic`), the case marking of aspect the grammar describes.

## Implementation notes

Resultative and irresultative action are read as the telic and atelic values of
`Aspect.Telicity`. The grammar lists the constructions under which a singular total object
drops its ending rather than unifying them; `Clause` lists them likewise.

## References

* [karlsson-2017]
-/

open Data.Examples Aspect

namespace Karlsson2017

/-- The kind of nominal serving as object, as the total-object endings of section 13.3.2 read
it. -/
inductive Nominal
  | personalPronoun | plural | numeral | singular
  deriving DecidableEq, Repr

/-- The clause types, the last four being those under which a singular total object is in the
nominative (section 13.3.2, rule 4). -/
inductive Clause
  | finite | imperative | passive | obligation | infinitival
  deriving DecidableEq, Repr

/-- An object and the factors the grammar's rules read: the polarity of the sentence, the
resultativity of the action, the definiteness of the quantity, the kind of nominal, and the
clause type. -/
structure Object where
  negated : Bool
  telicity : Telicity
  definite : Bool
  nominal : Nominal
  clause : Clause
  deriving DecidableEq, Repr

namespace Object

/-- The partitive conditions of section 12.2.2: negation, irresultative action, indefinite
quantity. -/
def IsPartitive (o : Object) : Prop := o.negated ∨ o.telicity = .atelic ∨ ¬ o.definite

instance : DecidablePred IsPartitive := λ _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The total-object ending of section 13.3.2. -/
def totalCase (o : Object) : Case :=
  match o.nominal with
  | .personalPronoun => .acc
  | .plural | .numeral => .nom
  | .singular => if o.clause = .finite then .gen else .nom

/-- The case of the object: partitive under any partitive condition, else the total-object
ending (section 13.3.1). -/
def case (o : Object) : Case := if o.IsPartitive then .part else o.totalCase

theorem totalCase_ne_part (o : Object) : o.totalCase ≠ .part := by
  unfold totalCase
  split <;> first | decide | split <;> decide

/-- The partitive is the stronger object case: the object is partitive exactly under a
partitive condition. -/
theorem case_eq_part_iff (o : Object) : o.case = .part ↔ o.IsPartitive := by
  unfold case
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (totalCase_ne_part o) h

/-- In an affirmative sentence about a definite quantity, the object is partitive exactly when
the action is irresultative: the case marks the aspect. -/
theorem part_iff_atelic {o : Object} (hn : ¬ o.negated) (hd : o.definite) :
    o.case = .part ↔ o.telicity = .atelic := by
  rw [case_eq_part_iff, IsPartitive]
  simp [hn, hd]

/-- A negated sentence has a partitive object whatever the nominal. -/
theorem case_eq_part_of_negated {o : Object} (h : o.negated) : o.case = .part :=
  (case_eq_part_iff o).mpr (Or.inl h)

/-- A personal pronoun is a total object in the accusative alone. -/
theorem case_of_personalPronoun {o : Object} (h : o.nominal = .personalPronoun)
    (hp : ¬ o.IsPartitive) : o.case = .acc := by
  rw [case, if_neg hp, totalCase, h]

end Object

/-- A row: the object and the case the grammar gives it. -/
structure Row where
  object : Object
  case : Case

private def nominalOf : List (String × Nominal) :=
  [("personalPronoun", .personalPronoun), ("plural", .plural), ("numeral", .numeral),
    ("singular", .singular)]

private def clauseOf : List (String × Clause) :=
  [("finite", .finite), ("imperative", .imperative), ("passive", .passive),
    ("obligation", .obligation), ("infinitival", .infinitival)]

private def caseOf : List (String × Case) :=
  [("part", .part), ("acc", .acc), ("nom", .nom), ("gen", .gen)]

/-- A row from the grammar's features. -/
def Row.ofExample (e : LinguisticExample) : Option Row := do
  let n ← e.parse? "nominal" nominalOf
  let cl ← e.parse? "clause" clauseOf
  let c ← e.parse? "case" caseOf
  some ⟨⟨e.feature? "negated" == some "yes",
    if e.feature? "aspect" == some "resultative" then .telic else .atelic,
    e.feature? "quantity" == some "definite", n, cl⟩, c⟩

/-- The object-case examples of sections 12.2.2 and 13.3. -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-- The grammar's examples take the case its rules assign. -/
theorem rows_agree : ∀ r ∈ rows, r.object.case = r.case := by decide

end Karlsson2017
