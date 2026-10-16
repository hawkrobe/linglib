/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Data.Examples.Schema
public import Linglib.Data.UD.Features

/-!
# Paradigms

This file defines the rows of a paper's paradigm data, after the Paralex standard for lexicons of
inflected forms: the lexemes, the form of a lexeme in each cell of its paradigm, and a source's
judgment of which of those forms share a root. It is the paradigm counterpart of `Data/Forms/`,
whose rows are CLDF word forms.

## Main definitions

* `Data.Paradigms.Lexeme`: a row of the `lexemes` table.
* `Data.Paradigms.Form`: a row of the `forms` table, a lexeme's form in a cell.
* `Data.Paradigms.RootClasses`: a row of the `root_classes` table, a linglib extension: a source's
  judgment that the cells of some forms of a lexeme divide into classes sharing a root.

## Implementation notes

* Per-paper data lives in `Linglib/Data/Paradigms/{AuthorYear}.json`, an object holding the Paralex
  tables `cells`, `lexemes` and `forms` under Paralex column names and the extension table
  `root_classes`, and is compiled by `scripts/gen_paradigms.py` into `{AuthorYear}.lean`, declaring
  `namespace {AuthorYear}.Paradigms`.
* A cell is given in the JSON by its Universal Dependencies features in the CoNLL-U syntax, such as
  `Degree=Cmp`, and becomes a `UD.MorphFeatures`.
* A form keeps the source's segmentation as `analysed`, Paralex's `analysed_orth_form`; `form` is
  `analysed` without its hyphens.
* A form carries the source's `Judgment`, a linglib extension column after CLDF's
  `grammaticalityJudgement`, which Paralex lacks. A source that rejects a form another source
  gives is a row of its own, marked `ungrammatical`, so disagreeing sources sit side by side.
* Root identity is a judgment rather than a function of the forms: *better* and *best* share a
  root that no identity of strings shows. A source's classes are therefore rows of their own,
  citing where the source states them, and a root pattern over cells is computed from them.
* Comments and the cognates a source lists are its record: the generator validates them and does
  not emit them.

## TODO

* Cite the paper that introduces the Paralex standard (Beniamine and colleagues, 2023) once its
  bibliographic record is verified.

## References

* [bobaljik-2012]
-/

@[expose] public section

namespace Data.Paradigms

/-- A `Lexeme` is a row of a Paralex `lexemes` table, a word of a language by its meaning. -/
structure Lexeme where
  /-- The `lexeme_id` column holds a stable identifier keyed to the paper. -/
  id : String
  /-- The `language_ID` column holds the Glottocode of the language. -/
  languageId : Glottocode
  /-- The `label` column holds the citation form. -/
  label : String
  /-- The `meaning` column holds a gloss. -/
  meaning : String
  deriving DecidableEq, Repr

/-- A `Form` is a row of a Paralex `forms` table, the form of a lexeme in a cell. -/
structure Form where
  /-- The `form_id` column holds a stable identifier keyed to the paper. -/
  id : String
  /-- The lexeme that the `lexeme` column names. -/
  lexeme : Lexeme
  /-- The cell that the `cell` column names, by its features. -/
  cell : UD.MorphFeatures
  /-- The form, the source's segmented form without its hyphens. -/
  form : String
  /-- The `analysed_orth_form` column holds the form as the source segments it. -/
  analysed : String
  /-- The `judgment` column holds the source's mark on the form in the cell; a form the source
  rejects is a candidate for the cell, not its content. -/
  judgment : Judgment := .acceptable
  /-- The `source` column holds the references, each a bibkey with a locator. -/
  source : List SourceRef := []
  deriving DecidableEq, Repr

/-- A `RootClasses` is a source's judgment that the cells of some forms of a lexeme divide into
classes of cells whose forms share a root, each cell with the index of its class. -/
structure RootClasses where
  /-- The `classes_id` column holds a stable identifier keyed to the paper. -/
  id : String
  /-- The lexeme whose forms are judged. -/
  lexeme : Lexeme
  /-- The forms judged. -/
  forms : List Form
  /-- The class of each cell, `A` as `0`, `B` as `1`, and so on. -/
  classes : List (UD.MorphFeatures × ℕ)
  /-- The references where the source states the classes. -/
  source : List SourceRef := []
  deriving DecidableEq, Repr

/-- `r.classOf c` is the class of the cell `c` in the judgment `r`, if `r` classes `c`. -/
def RootClasses.classOf (r : RootClasses) (c : UD.MorphFeatures) : Option ℕ := r.classes.lookup c

end Data.Paradigms
