import Linglib.Syntax.Minimalist.Features
import Linglib.Syntax.Agreement.Paradigm
import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic

/-!
# Vocabulary insertion over Minimalist bundles

The bridge from Agree, which values features in narrow syntax, to PF: a
valued `FeatureBundle` is spelled out by the Subset Principle over Vocabulary
Items on `GramFeature`s, and a vocabulary is built from a paradigm's cells.

## Main definitions

* `Minimalist.spellout` — the Subset Principle over a bundle's features.
* `Agreement.Cell.toPhiFeatures`, `Minimalist.vocabularyOfCells` — a
  vocabulary from paradigm cells.
-/

/-- The φ-feature list of a person-number cell, in the shape
`Minimalist.vocabularyOfCells` consumes. -/
def Agreement.Cell.toPhiFeatures (c : Agreement.Cell) : List Minimalist.PhiFeature :=
  [.person c.toPerson, .number (if c.isPlural then .plural else .singular)]

namespace Minimalist

open DistributedMorphology

/-- Spell out a valued bundle: the Subset Principle over its features;
`none` is the zero exponent. -/
def spellout (vocab : List (VocabularyItem GramFeature String)) (target : FeatureBundle) :
    Option String :=
  subsetPrinciple vocab target.toGramFeatures

/-- One item per paradigm cell: the cell's φ-features as valued features and
its exponent. Elsewhere items are appended by the caller. -/
def vocabularyOfCells {PN : Type*} (cells : List PN) (toPhi : PN → List PhiFeature)
    (exponentOf : PN → String) : List (VocabularyItem GramFeature String) :=
  cells.map fun pn =>
    ⟨((toPhi pn).map fun p => GramFeature.valued (.phi p) : List GramFeature), exponentOf pn⟩

end Minimalist
