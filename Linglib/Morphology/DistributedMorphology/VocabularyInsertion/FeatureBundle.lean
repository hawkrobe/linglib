module

public import Linglib.Syntax.Minimalist.Features
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic

/-!
# Vocabulary insertion over Minimalist bundles

The bridge from Agree, which values features in narrow syntax, to PF: a
valued `FeatureBundle` is spelled out by the Subset Principle over Vocabulary
Items on `GramFeature`s.

## Main definitions

* `Minimalist.spellout` — the Subset Principle over a bundle's features.
-/

@[expose] public section

namespace Minimalist

open DistributedMorphology

/-- A valued bundle is spelled out by the Subset Principle over its features, `none` being the
zero exponent. -/
def spellout (vocab : List (VocabularyItem GramFeature String)) (target : FeatureBundle) :
    Option String :=
  subsetPrinciple vocab target.toGramFeatures

end Minimalist
