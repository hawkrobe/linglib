import Linglib.Morphology.Exponence.Containment.Contiguity
import Linglib.Syntax.Category.Pronoun.IndefiniteParadigm
import Linglib.Fragments.English.Indefinites
import Linglib.Fragments.Slavic.Russian.Indefinites
import Linglib.Fragments.Yakut.Indefinites
import Linglib.Fragments.Latin.Indefinites
import Linglib.Fragments.Kannada.Indefinites
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
Elsewhere Principle, (47), picks the smallest match, so the lexicon read off each Fragment
paradigm's coverage of the map reproduces that coverage by spellout, the absence of ABA is
the contiguity of spellout, (48), and a paradigm gap, Table 6, sits above every filled layer,
since an entry spelling out a layer spells out every layer below it. An interrogative pronoun
can be spelled out as a subset of an indefinite entry, (78) and (79), and suffixes arise by
spellout-driven movement where prefixes arise by subderivation, (57).

## Implementation notes

Layers are the grades `Fin 3` of the containment substrate and entries its context-free span
rules, with `spellout` the exponent of the Superset-and-Elsewhere winner. Fragment forms are
whole pronouns where the paper lists markers, so the Fragment-side theorems compare coverage
patterns and the paper's marker tables are rows. The derivations of prefixes and suffixes in
§4.2 are not modelled.

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

/-! ### The hierarchy -/

/-- The layer of the hierarchy (4) a function's marker spells out: the non-specific (irrealis)
function the lowest and the specific known the highest, the other functions of the map lying
outside the hierarchy. -/
def layer : HaspelmathFunction → Option (Fin 3)
  | .irrealis => some 0
  | .specificUnknown => some 1
  | .specificKnown => some 2
  | _ => none

/-- The function each layer spells out. -/
def function : Fin 3 → HaspelmathFunction := ![.irrealis, .specificUnknown, .specificKnown]

/-- A paradigm's forms over the three layers, the triple the syncretism patterns classify. -/
def pattern (p : IndefiniteParadigm) : Paradigm 3 (Option String) :=
  λ g => p.formAt (function g)

/-- The nanosyntactic lexicon of a paradigm: each form stores the largest layer it covers, the
Superset and Elsewhere Principles deriving the rest of its coverage. -/
def lexicon (p : IndefiniteParadigm) : List (SpanRule 3 String) :=
  p.forms.filterMap λ e => (e.functionList.filterMap layer).max?.map (⟨e.form, ·, none⟩)

/-! ### Syncretism and its absence -/

/-- The syncretism patterns of Table 1 from the Fragments' coverage of the map: English AAA,
Yakut ABB, Latin AAB, Russian ABC, and none for Kannada, whose paradigm has a gap. -/
theorem fragment_syncretism :
    English.Indefinites.paradigm.syncretism = some .AAA ∧
      Yakut.Indefinites.paradigm.syncretism = some .ABB ∧
      Latin.Indefinites.paradigm.syncretism = some .AAB ∧
      Russian.Indefinites.paradigm.syncretism = some .ABC ∧
      Kannada.Indefinites.paradigm.syncretism = none := by
  decide

/-- The lexicon read off each Fragment paradigm reproduces its coverage of the three functions
by spellout: (59) English, (63) Russian, (67) Yakut, (70) Latin, and Kannada with its gap. -/
theorem spellout_lexicon :
    spellout (lexicon English.Indefinites.paradigm) = pattern English.Indefinites.paradigm ∧
      spellout (lexicon Russian.Indefinites.paradigm) = pattern Russian.Indefinites.paradigm ∧
      spellout (lexicon Yakut.Indefinites.paradigm) = pattern Yakut.Indefinites.paradigm ∧
      spellout (lexicon Latin.Indefinites.paradigm) = pattern Latin.Indefinites.paradigm ∧
      spellout (lexicon Kannada.Indefinites.paradigm) = pattern Kannada.Indefinites.paradigm := by
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
  λ hg => hg' (spellout_eq_none_of_le hg h)

/-- With the interrogative pronoun as a layer below the hierarchy, (78) and (79): Mandarin
*shénme* spells out the interrogative and the non-specific layer, Dutch *wat* all four. -/
theorem interrogative_subset :
    spellout [(⟨"shénme", 1, none⟩ : SpanRule 4 String)] =
        ![some "shénme", some "shénme", none, none] ∧
      spellout [(⟨"wat", 3, none⟩ : SpanRule 4 String)] = λ _ => some "wat" := by
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
