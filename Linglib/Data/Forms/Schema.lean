/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Data.Examples.Schema
public import Linglib.Core.Order.Flat

/-!
# CLDF word forms

This file defines the types for word-level data, aligned with the Wordlist module of the
Cross-Linguistic Data Formats of Forkel and colleagues, version 1.3, and the lookups a study
makes on a paper's forms. It is the morphological counterpart of the Examples component in
`Data/Examples/`: the datum is a word and its parts rather than an utterance and its gloss.

## Main definitions

* `Data.Forms.Form`: a row of the `FormTable`, a form of a language expressing a concept, with
  its segmentation.
* `Data.Forms.Parameter`: a row of the `ParameterTable`, the concept.
* `Data.Forms.FormRelation`: a row of `FormRelationTable`, a linglib extension table for the
  paradigmatic pairs a paper asserts between forms (a stem and its past, an adjective and its
  comparative, a base and its reduplicant); CLDF has no standard component for these and permits
  custom tables.
* `Data.Forms.Form.column?`, `Data.Forms.Form.columnAs?`: the value of a custom column, as
  printed or read through a table of labels.
* `Data.Forms.matching`: every form of a list that expresses a concept and carries given values
  in given custom columns.

## Implementation notes

* Per-paper data lives in `Linglib/Data/Forms/{AuthorYear}.json`, an object whose keys are CLDF
  table names holding arrays of rows under the CLDF column names, and is compiled by
  `scripts/gen_forms.py` into `Linglib/Data/Forms/{AuthorYear}.lean`, declaring
  `namespace {AuthorYear}.Forms`.
* `Language_ID` is a Glottocode rather than a foreign key into a `LanguageTable`, as in
  `Data/Examples/`. `Source` follows the CLDF reference syntax `bibkey[label]` in JSON and is
  parsed into `SourceRef` values.
* `Segments` is the paper's own tokenization of the form, which may be coarser than a
  phonemic segmentation: a long vowel as one segment, or a residue the paper treats as one
  variable. `Form.slots` reads the segments as a slot-indexed item on the flat carrier, the
  shape the schema substrate consumes.
* CLDF lets any table carry custom columns. A form's are kept as `columns`, name-value pairs
  under the column names of the JSON, for the per-form codes a paper assigns (a case, a
  canonicity judgment, a tone class).
* `matching` returns every matching row rather than the first, so a cell a paper fills with two
  alternants yields both.
* Identifiers follow the CLDF `id` format `[a-zA-Z0-9_-]+`, enforced by the generator.

## References

* [forkel-etal-2018]
* [forkel-etal-2024]
-/

@[expose] public section

namespace Data.Forms

open Data.Examples

/-- A `Form` is a row of a CLDF `FormTable`, a word form of a language expressing a concept,
with its segmentation. -/
structure Form where
  /-- The `ID` column holds a stable identifier keyed to the paper. -/
  id : String
  /-- The `Language_ID` column holds the Glottocode of the language. -/
  languageId : Glottocode
  /-- The `Parameter_ID` column names the concept the form expresses. -/
  parameterId : String
  /-- The `Form` column holds the written form. -/
  form : String
  /-- The `Segments` column holds the form's segmentation. -/
  segments : List String
  /-- The `Comment` column holds a free-text comment. -/
  comment : String := ""
  /-- The `Source` column holds the references, each a bibkey with a locator. -/
  source : List SourceRef := []
  /-- The custom columns of the table hold further values of the form, by column name. -/
  columns : List (String × String) := []
  deriving DecidableEq, Repr

/-- `f.slots` reads the segments of `f` as a slot-indexed item on the flat carrier. -/
def Form.slots (f : Form) (i : Fin f.segments.length) : Flat String := ↑(f.segments.get i)

/-- `f.column? name` is the value of `f` in the custom column `name`, if `f` has one. -/
def Form.column? (f : Form) (name : String) : Option String := f.columns.lookup name

/-- `f.columnAs? name table` is the entry of `table` under the value of `f` in the custom column
`name`, if `f` has that column and `table` lists its value. -/
def Form.columnAs? {α : Type*} (f : Form) (name : String) (table : List (String × α)) :
    Option α :=
  (f.column? name).bind (List.lookup · table)

/-- `matching forms pid cols` is the list of every form in `forms` that expresses the concept
`pid` and has the value `v` in the custom column `c` for each pair `(c, v)` of `cols`, in the
order of `forms`. -/
def matching (forms : List Form) (pid : String) (cols : List (String × String)) : List Form :=
  forms.filter fun f ↦ f.parameterId == pid && cols.all fun c ↦ f.column? c.1 == some c.2

@[simp]
theorem mem_matching {forms : List Form} {pid : String} {cols : List (String × String)}
    {f : Form} : f ∈ matching forms pid cols ↔
      f ∈ forms ∧ f.parameterId = pid ∧ ∀ c ∈ cols, f.column? c.1 = some c.2 := by
  simp [matching]

/-- A `Parameter` is a row of a CLDF `ParameterTable`, a concept that forms express. -/
structure Parameter where
  /-- The `ID` column holds the concept's identifier. -/
  id : String
  /-- The `Name` column holds the concept's name. -/
  name : String
  /-- The `Description` column holds a description of the concept. -/
  description : String := ""
  deriving DecidableEq, Repr

/-- A `FormRelation` is a row of the `FormRelationTable`, a paradigmatic relation that a paper
asserts from one form to another, named by the paper's term for it. -/
structure FormRelation where
  /-- The `ID` column holds the relation's identifier. -/
  id : String
  /-- The `Form_ID` column names the first form. -/
  formId : String
  /-- The `Target_ID` column names the second form. -/
  targetId : String
  /-- The `Relation` column holds the paper's name for the relation. -/
  relation : String
  /-- The `Source` column holds the references, each a bibkey with a locator. -/
  source : List SourceRef := []
  deriving DecidableEq, Repr

end Data.Forms
