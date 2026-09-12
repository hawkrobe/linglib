/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Data.Examples.Schema
import Linglib.Core.Order.Flat

/-!
# CLDF word forms

Substrate types for word-level data, aligned with the Wordlist module of the Cross-Linguistic
Data Formats ([forkel-etal-2018]), version 1.3 ([forkel-etal-2024]): a `Form` is a row of the
`FormTable` (a form of a language expressing a concept,
with its segmentation), and a `Parameter` is a row of the `ParameterTable` (the concept). The
sentence-level `LinguisticExample` of `Data/Examples/` is the Examples component; this is its
counterpart for morphology, where the datum is a word and its parts rather than an utterance
and its gloss.

Per-paper data lives in `Linglib/Data/Forms/{AuthorYear}.json`, an object whose keys are CLDF
table names holding arrays of rows under the CLDF column names, and is compiled by
`scripts/gen_forms.py` into `Linglib/Data/Forms/{AuthorYear}.lean`, declaring
`namespace {AuthorYear}.Forms`.

`FormRelation` is a linglib extension table, `FormRelationTable`, for the paradigmatic pairs a
paper asserts between forms (a stem and its past, an adjective and its comparative, a base
and its reduplicant); CLDF has no standard component for these and permits custom tables.

## Implementation notes

* `Language_ID` is a Glottocode rather than a foreign key into a `LanguageTable`, as in
  `Data/Examples/`. `Source` follows the CLDF reference syntax `bibkey[label]` in JSON and is
  parsed into `SourceRef` values.
* `Segments` is the paper's own tokenization of the form, which may be coarser than a
  phonemic segmentation: a long vowel as one segment, or a residue the paper treats as one
  variable. `Form.slots` reads the segments as a slot-indexed item on the flat carrier, the
  shape the schema substrate consumes.
* Identifiers follow the CLDF `id` format `[a-zA-Z0-9_-]+`, enforced by the generator.

## References

* [forkel-etal-2018]
* [forkel-etal-2024]
-/

namespace Data.Forms

open Data.Examples

/-- A row of a CLDF `FormTable`: a word form of a language expressing a concept, with its
segmentation. -/
structure Form where
  /-- `ID`: a stable, paper-keyed identifier. -/
  id : String
  /-- `Language_ID`: the Glottocode of the language. -/
  languageId : Glottocode
  /-- `Parameter_ID`: the concept the form expresses. -/
  parameterId : String
  /-- `Form`: the written form. -/
  form : String
  /-- `Segments`: the form's segmentation. -/
  segments : List String
  /-- `Comment`. -/
  comment : String := ""
  /-- `Source`: the references, each a bibkey with a locator. -/
  source : List SourceRef := []
  deriving DecidableEq, Repr

/-- The segments of a form as a slot-indexed item on the flat carrier. -/
def Form.slots (f : Form) (i : Fin f.segments.length) : Flat String := ↑(f.segments.get i)

/-- A row of a CLDF `ParameterTable`: a concept forms express. -/
structure Parameter where
  /-- `ID`. -/
  id : String
  /-- `Name`. -/
  name : String
  /-- `Description`. -/
  description : String := ""
  deriving DecidableEq, Repr

/-- A row of the `FormRelationTable`: a paradigmatic relation a paper asserts from one form to
another, named by the paper's term for it. -/
structure FormRelation where
  /-- `ID`. -/
  id : String
  /-- `Form_ID`: the first form. -/
  formId : String
  /-- `Target_ID`: the second form. -/
  targetId : String
  /-- `Relation`: the paper's name for the relation. -/
  relation : String
  /-- `Source`. -/
  source : List SourceRef := []
  deriving DecidableEq, Repr

end Data.Forms
