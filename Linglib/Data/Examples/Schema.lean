/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Tactic.TypeStar
public import Linglib.Data.Examples.Judgment

/-!
# CLDF examples

This file defines the type of example data, aligned with the Examples component of the
Cross-Linguistic Data Formats [forkel-etal-2018] in version 1.3 [forkel-etal-2024], and the lookups
a study makes on a paper's examples. The datum is an utterance with its interlinear gloss, its
translation and the judgment the paper reports; it is the sentence-level counterpart of
`Data/Forms/`.

## Main definitions

* `Data.Examples.LinguisticExample`: a row of the `ExampleTable`, with the judgment layer
  (`judgment`, `alternatives`, `readings`) and the paper's own columns (`paperFeatures`).
* `Data.Examples.SourceRef`: a reference to a paper, a bibkey with a locator.
* `Data.Examples.LinguisticExample.feature?`, `Data.Examples.LinguisticExample.features`: the first
  value and every value of a key of `paperFeatures`.
* `Data.Examples.LinguisticExample.parse?`: the first value of a key read through a table.
* `Data.Examples.digits?`, `Data.Examples.LinguisticExample.nat?`,
  `Data.Examples.LinguisticExample.int?`: numerals.

## Main statements

* `mem_features`, `features_eq_nil`, `head?_features`, `feature?_eq_none`: the lookups in terms of
  membership in `paperFeatures`, in the shape of `List.mem_lookupAll`, `List.lookupAll_eq_nil`,
  `List.head?_lookupAll` and `List.dlookup_eq_none`.

## Implementation notes

* Per-paper data lives in `Linglib/Data/Examples/{AuthorYear}.json` and is compiled by
  `scripts/gen_examples.py` into `Linglib/Data/Examples/{AuthorYear}.lean`, declaring
  `namespace {AuthorYear}.Examples`. The JSON keys are the field names, and `id` uses only the
  characters of a CLDF identifier. `scripts/export_examples_cldf.py` writes the data as a CLDF
  dataset, which CI validates.
* `language` is a Glottocode, which the generator checks against `languages.csv`, the language
  table of the data drawn from Glottolog; it is empty for a constructed string that belongs to no
  language, such as a pattern of a formal language.
* `glossedTokens` pairs each analysed word with its gloss, so the word-by-word alignment of Rule 1
  of [comrie-haspelmath-bickel-2008] holds by construction. CLDF's `LGR_Conformance` column is not
  stored: whether a gloss also aligns morpheme by morpheme (Rule 2) is a property of the pairs.
* Translations are into English, the default of CLDF's `Meta_Language_ID`, which is therefore not
  stored; `translation` is empty when the example is itself English.
* A discourse is one example: `discourseSegments` are its utterances in order, `primaryText` is
  their concatenation with single spaces, and the judgment is of the last utterance in the context
  of the others.
* `paperFeatures` are the paper's own columns: what the paper states about the example, such as
  the cell of its design or the class it assigns. The results a paper prints for an experiment
  belong in `Data/Experiments/`, and an analysis the formaliser derives belongs in the study. A key
  repeats when the example bears the property twice (two indefinite series in one clause), so the
  list is not a map: `feature?` reads the first value, `features` every value.
* Studies decide propositions over rows, so every lookup reduces in the kernel. `digits?` reads a
  numeral by a fold over its characters because `String.toNat?` is well-founded recursive and
  does not.
* The file imports no tactic library: every module with example data imports it, and names such
  a library brings into scope (mathlib's root `Tree`) would reach every study that reads rows.

## TODO

* 266 rows in 29 papers with `discourseSegments` do not have their concatenation as
  `primaryText`: some give only the last utterance (RoelofsenFarkas2015, FarkasBruce2010), some
  join the utterances with a dash (Holmberg2016), and some keep a judgment mark in a segment
  (CoppockBeaver2015).

## References

* [forkel-etal-2018]
* [forkel-etal-2024]
* [comrie-haspelmath-bickel-2008]
-/

@[expose] public section

namespace Data.Examples

/-- A Glottolog language identifier, such as `"stan1293"` for Standard English. -/
abbrev Glottocode := String

/-- A `SourceRef` is a CLDF source reference `bibkey[locator]` with its two parts kept apart. -/
structure SourceRef where
  /-- The key of the paper's entry in `references.bib`. -/
  bibkey : String
  /-- The locator in the paper: its example number, table or page. -/
  paperLabel : String
  deriving DecidableEq, Repr

/-- A `LinguisticExample` is a row of a CLDF `ExampleTable`: an example of a language with its
gloss, its translation, the judgment its source reports, the forms and readings the source judges
with it, and the source's own classifications of it. -/
structure LinguisticExample where
  /-- The `ID` column holds a stable identifier keyed to the paper, `{authoryear}_{label}`. -/
  id : String
  /-- The paper that introduced the example. -/
  source : SourceRef
  /-- The paper whose data file holds the row, when it only reports an example from `source`. -/
  reportedIn : Option SourceRef := none
  /-- The `Language_ID` column holds the Glottocode of the language of the example; empty for a
  constructed string of no language. -/
  language : Glottocode
  /-- The `Primary_Text` column holds the example without judgment marks. -/
  primaryText : String
  /-- The utterances of a discourse, in order; empty for a single sentence. -/
  discourseSegments : List String := []
  /-- The `Analyzed_Word` and `Gloss` columns paired, each word with its gloss; empty when the
  source gives no gloss. -/
  glossedTokens : List (String × String)
  /-- The `Translated_Text` column holds the source's English translation; empty for an English
  example. -/
  translation : String
  /-- The scenario the source gives for the judgment; empty when it gives none. -/
  context : String
  /-- The judgment the source reports for the example. -/
  judgment : Judgment
  /-- The other forms the source judges in the same frame, each a whole sentence, with their
  judgments. -/
  alternatives : List (String × Judgment) := []
  /-- The readings the source distinguishes for the example, each with its judgment. -/
  readings : List (String × Judgment) := []
  /-- The paper's own columns, as key-value pairs. -/
  paperFeatures : List (String × String) := []
  /-- The `Comment` column holds free-text notes. -/
  comment : String
  deriving DecidableEq, Repr

/-- `digits? cs` is the number that the nonempty string of decimal digits `cs` denotes. -/
def digits? (cs : List Char) : Option ℕ :=
  if cs ≠ [] ∧ cs.all Char.isDigit then
    some (cs.foldl (fun n c ↦ 10 * n + (c.toNat - '0'.toNat)) 0)
  else none

namespace LinguisticExample

variable (e : LinguisticExample) (key : String)

/-- `e.surfaceTokens` is the `Analyzed_Word` column, the words of `e.glossedTokens`. -/
def surfaceTokens : List String := e.glossedTokens.map Prod.fst

/-- `e.glossLine` is the `Gloss` column, the glosses of `e.glossedTokens`. -/
def glossLine : List String := e.glossedTokens.map Prod.snd

/-- `e.feature? key` is the first value of `key` in `e.paperFeatures`, if there is one. -/
def feature? : Option String := e.paperFeatures.lookup key

/-- `e.features key` is the list of values of `key` in `e.paperFeatures`, in order. -/
def features : List String :=
  e.paperFeatures.filterMap fun kv ↦ if kv.1 = key then some kv.2 else none

/-- `e.parse? key table` is the entry of `table` under the first value of `key` in `e`, if `e`
has the key and `table` lists its value. -/
def parse? {α : Type*} (table : List (String × α)) : Option α :=
  (e.feature? key).bind (List.lookup · table)

/-- `e.nat? key` is the first value of `key` in `e` read as a decimal numeral. -/
def nat? : Option ℕ := (e.feature? key).bind fun s ↦ digits? s.toList

/-- `e.int? key` is the first value of `key` in `e` read as a decimal integer, an optional `-`
followed by digits. -/
def int? : Option ℤ :=
  (e.feature? key).bind fun s ↦
    match s.toList with
    | '-' :: cs => (digits? cs).map fun n ↦ -(n : ℤ)
    | cs => (digits? cs).map fun n ↦ (n : ℤ)

variable {e key} {v : String}

@[simp]
theorem mem_features : v ∈ e.features key ↔ (key, v) ∈ e.paperFeatures := by
  simp [features, and_comm, eq_comm]

theorem features_eq_nil : e.features key = [] ↔ ∀ v, (key, v) ∉ e.paperFeatures := by
  simp [List.eq_nil_iff_forall_not_mem]

@[simp]
theorem head?_features : (e.features key).head? = e.feature? key := by
  simp only [features, feature?, List.head?_filterMap, List.lookup_eq_findSome?, beq_iff_eq]
  congr 1; funext kv; simp only [eq_comm]

theorem feature?_eq_none : e.feature? key = none ↔ ∀ v, (key, v) ∉ e.paperFeatures := by
  rw [← head?_features, List.head?_eq_none_iff, features_eq_nil]

end LinguisticExample

end Data.Examples
