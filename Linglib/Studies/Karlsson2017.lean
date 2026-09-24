module

public import Linglib.Data.Examples.Karlsson2017
public import Linglib.Data.Forms.Karlsson2017
public import Linglib.Fragments.Finnish.Morphotactics
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

The word forms of the grammar's tables of endings are words of the Finnish Fragment's
morphotactics (`wellFormed_forms`) and derived by it (`forms_derived`). A form is its stem
followed by the function ending of an infinitive, a number, a case and a possessive ending and
a clitic, in the order of the grammar's diagrams and in the archiphonemic spelling of its
tables, and vowel copy and palatal harmony give its surface. The tables are those of the cases,
the possessive endings and the structure of nominals and of non-finite forms (section 3), of the
plural (section 5.4), of the partitive and genitive plural (section 13.1.2), of the possessive
endings after a case ending (section 14.1), of the A infinitive translative (section 22.2.2) and
of the MA infinitive (section 22.4.1).

## Implementation notes

Resultative and irresultative action are read as the telic and atelic values of
`Aspect.Telicity`. The grammar lists the constructions under which a singular total object
drops its ending rather than unifying them; `Clause` lists them likewise.

The forms of the tables are those whose genitive plural, if any, follows the plural -i, since
the Fragment does not represent -ten on the consonant stem, as in *nais-ten* 'of the women'. A
nominative form has no case ending.

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

/-- A word of the tables: its stem and its endings. -/
structure Word where
  stem : List Segment
  endings : List (Σ σ, Nominal.Exponent σ)

/-- The case endings, the nominative having none. -/
def caseLabels : List (String × Option Case) :=
  [("nom", none), ("gen", some .gen), ("acc", some .acc), ("part", some .part),
    ("ine", some .ine), ("ela", some .ela), ("ill", some .ill), ("ade", some .ade),
    ("abl", some .abl), ("all", some .all), ("ess", some .ess), ("transl", some .transl),
    ("com", some .com), ("abess", some .abess), ("inst", some .inst)]

def possessorLabels : List (String × Agreement.Bundle) :=
  [("1sg", .pn .first .singular), ("2sg", .pn .second .singular), ("3sg", .pn .third .singular),
    ("1pl", .pn .first .plural), ("2pl", .pn .second .plural), ("3pl", .pn .third .plural)]

def infinitiveLabels : List (String × Infinitive) := [("a", .a), ("e", .e), ("ma", .ma)]

def numberLabels : List (String × Nominal.Exponent .number) :=
  [("t", .nominativePlural), ("i", .plural)]

def cliticLabels : List (String × Clitic) :=
  [("kO", .kO), ("kin", .kin), ("kAAn", .kAAn), ("hAn", .hAn), ("pA", .pA)]

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
  let inf ← optionalColumn f "Infinitive" infinitiveLabels
  let num ← optionalColumn f "Number" numberLabels
  let c ← (f.column? "Case").bind (List.lookup · caseLabels)
  let p ← optionalColumn f "Possessor" possessorLabels
  let k ← optionalColumn f "Clitic" cliticLabels
  some ⟨stem, (inf.map (⟨_, .infinitive ·⟩)).toList ++ (num.map (⟨_, ·⟩)).toList ++
    (c.map (⟨_, .case ·⟩)).toList ++ (p.map (⟨_, .possessive ·⟩)).toList ++
    (k.map (⟨_, .clitic ·⟩)).toList⟩

/-- Every form of the tables is a word. -/
theorem isSome_ofForm : ∀ f ∈ Forms.all, (Word.ofForm f).isSome := by
  decide +kernel

/-- The endings of each form make a word. -/
theorem wellFormed_forms :
    ∀ f ∈ Forms.all, ∀ w ∈ Word.ofForm f, Nominal.WellFormed w.endings := by
  decide +kernel

/-- The Fragment gives each form of the tables. -/
theorem forms_derived : ∀ f ∈ Forms.all, ∀ w ∈ Word.ofForm f,
    ∃ x ∈ spell f.form, x ∈ Nominal.realize w.stem w.endings := by
  decide +kernel

end WordStructure

end Karlsson2017
