import Linglib.Morphology.Exponence.Containment.Contiguity
import Linglib.Studies.Haspelmath1997
import Linglib.Data.Examples.Dekier2021

/-!
# Dekier (2021): Morphosyntax of specific and non-specific indefinite markers

This file formalizes the nanosyntactic analysis of [dekier-2021] of the markers of the
non-specific, specific unknown and specific known functions of [haspelmath-1997]'s map. Across
a sample of 45 languages the three markers show the syncretism patterns AAA, ABB, AAB and ABC
and never ABA, Table 7, the generalization of [bobaljik-2012], so they spell out a hierarchy of
structural containment, (4): the non-specific layer inside the specific unknown one inside the
specific known one, the direction fixed by functional complexity, (37). A language's lexicon
stores for each marker the largest layer it spells out; the Superset Principle of
[starke-2009] and [caha-2009], (42), lets an entry spell out any layer it contains and the
Elsewhere Principle, (47), picks the smallest match, so the lexicon read off the coverage
[haspelmath-1997] draws for each paradigm reproduces that coverage by spellout, the absence of
ABA is the contiguity of spellout, (48), and a paradigm gap, Table 6, sits above every filled
layer, since an entry spelling out a layer spells out every layer below it. An interrogative pronoun
can be spelled out as a subset of an indefinite entry, (78) and (79), and suffixes arise by
spellout-driven movement where prefixes arise by subderivation, (57).

## Implementation notes

Layers are the grades `Fin 3` of the containment substrate and entries its context-free span
rules, with `spellout` the exponent of the Superset-and-Elsewhere winner. The paradigms are
those of `Studies/Haspelmath1997.lean`, a series covering a layer when the layer's function lies
in the region the book draws for it. Their forms are whole pronouns where the paper lists
markers, so the theorems over them compare coverage patterns and the paper's marker tables are
rows; a layer's form is the one series covering its function, `none` at a gap or where series
overlap. The paper's Russian row has the three series that divide the hierarchy and not
*-libo*, which the book draws over the non-specific function beside *-nibud'*; the book draws
*-to* over that function too, so Russian's coverage has no single non-specific form and its
ABC pattern is the work of the Elsewhere Principle (`russian_elsewhere`). The derivations of
prefixes and suffixes in §4.2 are not modelled.

## References

* [dekier-2021]
* [haspelmath-1997]
* [bobaljik-2012]
* [starke-2009]
* [caha-2009]
-/

namespace Dekier2021

open Morphology Morphology.Containment Indefinite
open Data.Examples (LinguisticExample)
open Haspelmath1997 (Series english yakut latin kannada)

/-! ### The hierarchy -/

/-- The layer of the hierarchy (4) a specificity function's marker spells out: the non-specific
function the lowest and the specific known the highest. -/
def layer : SpecificityFunction ≃ Fin 3 where
  toFun
    | .nonSpecific => 0
    | .specificUnknown => 1
    | .specificKnown => 2
  invFun := ![.nonSpecific, .specificUnknown, .specificKnown]
  left_inv := by decide
  right_inv := by decide

/-- The function of the map each layer spells out. -/
def function (g : Fin 3) : HaspelmathFunction := (layer.symm g).toFunction

/-- The form of a paradigm at a function, when one series covers it: `none` at a gap or where
series overlap. -/
def formAt (p : List Series) (f : HaspelmathFunction) : Option String :=
  match p.filter (f ∈ ·.functions) with
  | [e] => some e.pronoun.form
  | _ => none

/-- A paradigm's forms over the three layers, the triple the syncretism patterns classify. -/
def pattern (p : List Series) : Paradigm 3 (Option String) :=
  fun g ↦ formAt p (function g)

/-- The layers a series covers. -/
def layers (e : Series) : Finset (Fin 3) :=
  Finset.univ.filter (function · ∈ e.functions)

/-- The nanosyntactic lexicon of a paradigm: each form stores the largest layer it covers, the
Superset and Elsewhere Principles deriving the rest of its coverage. -/
def lexicon (p : List Series) : List (SpanRule 3 String) :=
  p.filterMap fun e ↦ (layers e).max.map (⟨e.pronoun.form, ·, none⟩)

/-- The Russian series of the paper's row: *koe-*, *-to* and *-nibud'*. -/
def russian : List Series :=
  Haspelmath1997.russian.filter fun e ↦
    e.pronoun ∈ [Russian.Indefinites.koeEntry, Russian.Indefinites.toEntry,
      Russian.Indefinites.nibudEntry]

/-! ### Syncretism and its absence -/

/-- The syncretism patterns of Table 1 from the paradigms' coverage of the map: English AAA,
Yakut ABB and Latin AAB. -/
theorem map_syncretism :
    syncretism (pattern english) = syncretism Paradigm.aaa ∧
      syncretism (pattern yakut) = syncretism Paradigm.abb ∧
      syncretism (pattern latin) = syncretism Paradigm.aab := by
  decide

/-- Russian's ABC is the Elsewhere Principle at work: *-to* covers the non-specific function
beside *-nibud'*, so coverage gives that layer no single form, and the lexicon, storing *-to* at
the specific unknown layer, gives it to the smaller match *-nibud'*. -/
theorem russian_elsewhere :
    pattern russian 0 = none ∧
      spellout (lexicon russian) = ![some "kto-nibud'", some "kto-to", some "koe-kto"] ∧
      syncretism (spellout (lexicon russian)) = syncretism Paradigm.abc := by
  decide

/-- Kannada's paradigm has a gap at the specific known layer. -/
theorem kannada_gap : pattern kannada 2 = none := by decide

/-- The lexicon read off each paradigm reproduces its coverage of the three functions by
spellout: (59) English, (67) Yakut, (70) Latin, and Kannada with its gap. -/
theorem spellout_lexicon :
    ∀ p ∈ [english, yakut, latin, kannada], spellout (lexicon p) = pattern p := by
  decide

/-- The Elsewhere Principle rules out ABA, (48): spellout is contiguous, so a marker spelling
out both the non-specific and the specific known layer spells out the specific unknown one. -/
theorem not_aba {v : List (SpanRule 3 String)} (hv : Antihomophonous v)
    (h : spellout v 0 = spellout v 2) : spellout v 0 = spellout v 1 :=
  isContiguous_spellout hv (by decide) (by decide) h

/-- A paradigm gap sits above every filled layer, §6.3: an entry spelling out a layer spells
out every layer it contains, so a lone gap is the specific known type and two gaps are the
specific types. -/
theorem ne_none_of_le {v : List (SpanRule 3 String)} {g g' : Fin 3} (h : g ≤ g')
    (hg' : spellout v g' ≠ none) : spellout v g ≠ none :=
  fun hg ↦ hg' (spellout_eq_none_of_le hg h)

/-- With the interrogative pronoun as a layer below the hierarchy, (78) and (79): Mandarin
*shénme* spells out the interrogative and the non-specific layer, Dutch *wat* all four. -/
theorem interrogative_subset :
    spellout [(⟨"shénme", 1, none⟩ : SpanRule 4 String)] =
        ![some "shénme", some "shénme", none, none] ∧
      spellout [(⟨"wat", 3, none⟩ : SpanRule 4 String)] = fun _ ↦ some "wat" := by
  decide

/-! ### The sample -/

/-- A row's markers over the three layers, a gap read as `none`. -/
private def rowPattern (e : LinguisticExample) : Paradigm 3 (Option String) :=
  ![e.feature? "nonSpecific", e.feature? "specificUnknown", e.feature? "specificKnown"]

/-- Table 7: every paradigm of the sample is contiguous, so none is ABA. -/
theorem rows_contiguous : ∀ e ∈ Examples.all, IsContiguous (rowPattern e) := by
  decide

/-- Table 6: every gap of the sample sits above the filled layers. -/
theorem rows_gap_above : ∀ e ∈ Examples.all, ∀ g g' : Fin 3, g ≤ g' →
    rowPattern e g' ≠ none → rowPattern e g ≠ none := by
  decide

end Dekier2021
