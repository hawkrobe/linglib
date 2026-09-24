module

public import Linglib.Data.Examples.Karlsson2017
public import Linglib.Data.Forms.Karlsson2017
public import Linglib.Fragments.Finnish.Infinitives
public import Linglib.Fragments.Finnish.Possession
public import Linglib.Semantics.Aspect.Defs

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

The word forms of the grammar's tables of endings are derived from the Finnish Fragment
(`forms_derived`). A form is its stem followed by the function ending of an infinitive, an ending
of its case and a possessive ending, in the archiphonemic spelling of the tables, and vowel copy
and palatal harmony give its surface. The tables are those of the cases, the possessive endings
and the structure of nominals and of non-finite forms (section 3), of the possessive endings
after a case ending (section 14.1), of the A infinitive translative (section 22.2.2) and of the
MA infinitive (section 22.4.1).

## Implementation notes

Resultative and irresultative action are read as the telic and atelic values of
`Aspect.Telicity`. The grammar lists the constructions under which a singular total object
drops its ending rather than unifying them; `Clause` lists them likewise.

The forms of the tables are those with no plural or clitic ending, and none in which a possessive
ending follows an alternant of the partitive or of the illative other than the first, since the
Fragment represents neither the number and clitic endings nor the choice of alternant before a
possessive ending.

## References

* [karlsson-2017]
-/

@[expose] public section

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

instance : DecidablePred IsPartitive := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _ ∨ _))

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
  rw [case, ite_eq_right hp, totalCase, h]

end Object

/-- A row: the object and the case the grammar gives it. -/
structure Row where
  object : Object
  case : Case

def nominalOf : List (String × Nominal) :=
  [("personalPronoun", .personalPronoun), ("plural", .plural), ("numeral", .numeral),
    ("singular", .singular)]

def clauseOf : List (String × Clause) :=
  [("finite", .finite), ("imperative", .imperative), ("passive", .passive),
    ("obligation", .obligation), ("infinitival", .infinitival)]

def caseOf : List (String × Case) :=
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

/-! ### Word structure -/

section WordStructure

open Finnish Phonology Data.Forms

/-- A word of the tables: its stem, the infinitive built on it, its case and its possessor. -/
structure Word where
  stem : List Segment
  infinitive : Option Infinitive
  case : Case
  possessor : Option Agreement.Bundle

def caseLabels : List (String × Case) :=
  [("nom", .nom), ("gen", .gen), ("acc", .acc), ("part", .part), ("ine", .ine), ("ela", .ela),
    ("ill", .ill), ("ade", .ade), ("abl", .abl), ("all", .all), ("ess", .ess),
    ("transl", .transl), ("com", .com), ("abess", .abess), ("inst", .inst)]

def possessorLabels : List (String × Agreement.Bundle) :=
  [("1sg", .pn .first .singular), ("2sg", .pn .second .singular), ("3sg", .pn .third .singular),
    ("1pl", .pn .first .plural), ("2pl", .pn .second .plural), ("3pl", .pn .third .plural)]

def infinitiveLabels : List (String × Infinitive) := [("a", .a), ("e", .e), ("ma", .ma)]

/-- The phonemes a word writes, a capital as its small letter. -/
def spell (w : String) : Option (List Segment) := (w.toList.map Char.toLower).mapM ofChar

/-- The value of a column that may be empty, read through a table. -/
def optionalColumn {α : Type} (f : Form) (key : String) (table : List (String × α)) :
    Option (Option α) :=
  match f.column? key with
  | none | some "" => some none
  | some v => (List.lookup v table).map some

/-- A word from a form's segmentation and columns. -/
def Word.ofForm (f : Form) : Option Word := do
  let stem ← f.segments.head?.bind spell
  let c ← (f.column? "Case").bind (List.lookup · caseLabels)
  let inf ← optionalColumn f "Infinitive" infinitiveLabels
  let p ← optionalColumn f "Possessor" possessorLabels
  some ⟨stem, inf, c, p⟩

/-- The surface forms the Fragment gives a word: its stem with the function ending of its
infinitive, followed by an ending of its case, or by its case and possessive endings. -/
def Word.forms (w : Word) : List (List Segment) :=
  let base := (w.infinitive.map (·.base w.stem)).getD w.stem
  let endings := match w.possessor with
    | some p => (Possession.inflection w.case p).toList
    | none => Declension.endings w.case
  endings.map fun e ↦ surface (base ++ e)

/-- Every form of the tables is a word. -/
theorem isSome_ofForm : ∀ f ∈ Forms.all, (Word.ofForm f).isSome := by
  decide +kernel

/-- The Fragment gives each form of the tables. -/
theorem forms_derived :
    ∀ f ∈ Forms.all, ∀ w ∈ Word.ofForm f, ∃ x ∈ spell f.form, x ∈ w.forms := by
  decide +kernel

end WordStructure

end Karlsson2017
