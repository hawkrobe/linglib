import Linglib.Processing.Memory.SurprisalTradeoff
import Linglib.Syntax.DependencyGrammar.Length
import Linglib.Fragments.Japanese.Morph
import Linglib.Fragments.Sesotho.Morph
import Linglib.Studies.Bybee1985
import Linglib.Data.Examples.HahnDegenFutrell2021

/-!
# Hahn, Degen, and Futrell (2021): Modeling Word and Morpheme Order in Natural Language as an Efficient Trade-Off of Memory and Surprisal

This file formalizes the structural claims of [hahn-degen-futrell-2021] that its three studies
rest on. A listener with a lossy memory of the past pays average surprisal for what the memory
drops (section 3.3), and the Information Locality Bound, Theorem 1, says that with memory below
the weighted sum of the conditional mutual information up to distance `T`, surprisal exceeds
the entropy rate by the information beyond `T`; `Processing/Memory/SurprisalTradeoff.lean`
carries the bound and its marginal analysis, and the Efficient Tradeoff Hypothesis (section
3.2) is `Processing.MemorySurprisal.efficientTradeoffHypothesis`, a comparison of the areas
under two trade-off curves. Information locality generalizes dependency locality (sections 3.4
and 7.4), and the paper's dependency-length illustration is heavy NP shift (2): moving the
long object after the prepositional phrase shortens the verb's dependency to the phrase by more
than it lengthens the one to the object, `heavyNPShift_shorter`, over the dependency graphs of
(2c) and (2d). Study 3's morpheme orders are the affix templates of
`Fragments/Japanese/Morph.lean` and `Fragments/Sesotho/Morph.lean`, which the paper compares
with [bybee-1985]'s relevance hierarchy (section 6.3): Sesotho's suffixes are sorted by it,
`sesotho_suffixes_respect_relevance`, while Japanese places the desiderative mood before tense,
against the surveyed order, `japanese_violates_surveyed_relevance`, which is what the paper's
"broadly in agreement" leaves room for. The measured trade-off curves of Studies 1 to 3 belong
to the paper and its data release, not to this file.

## Implementation notes

The mutual information profile, memory cost, and surplus surprisal are the substrate's
`ℕ`-valued millibit approximations, and Theorem 1 is its comprehension postulate rather than a
theorem proved here, since its proof needs the data processing inequality over a stationary
process. The dependency graphs of (2) follow Universal Dependencies conventions, with the comma
dropped; the paper's own claim is about the two distances the shift trades, which the
per-dependency lengths make explicit.

## References

* [hahn-degen-futrell-2021]
* [bybee-1985]
* [futrell-mahowald-gibson-2015]
-/

namespace HahnDegenFutrell2021

open DependencyGrammar Morphology
open Morphology (Word)

/-! ### Dependency locality, section 2.2 -/

/-- (2c): the object precedes the prepositional phrase, ten arcs over eleven words. -/
private def longObjectFirst : Graph 11 :=
  .ofArcs
    [Word.mk' "Lucy" .PROPN, Word.mk' "ate" .VERB, Word.mk' "the" .DET,
      Word.mk' "extremely" .ADV, Word.mk' "delicious" .ADJ, Word.mk' "bright" .ADV,
      Word.mk' "green" .ADJ, Word.mk' "broccoli" .NOUN, Word.mk' "with" .ADP,
      Word.mk' "a" .DET, Word.mk' "fork" .NOUN]
    1 [(1, 0, .nsubj), (1, 7, .obj), (7, 2, .det), (4, 3, .advmod), (7, 4, .amod),
      (6, 5, .advmod), (7, 6, .amod), (10, 8, .case_), (10, 9, .det), (1, 10, .obl)]

/-- (2d), heavy NP shift: the prepositional phrase precedes the long object. -/
private def shifted : Graph 11 :=
  .ofArcs
    [Word.mk' "Lucy" .PROPN, Word.mk' "ate" .VERB, Word.mk' "with" .ADP, Word.mk' "a" .DET,
      Word.mk' "fork" .NOUN, Word.mk' "the" .DET, Word.mk' "extremely" .ADV,
      Word.mk' "delicious" .ADJ, Word.mk' "bright" .ADV, Word.mk' "green" .ADJ,
      Word.mk' "broccoli" .NOUN]
    1 [(1, 0, .nsubj), (1, 10, .obj), (10, 5, .det), (7, 6, .advmod), (10, 7, .amod),
      (9, 8, .advmod), (10, 9, .amod), (4, 2, .case_), (4, 3, .det), (1, 4, .obl)]

/-- (2): the shift cuts the verb's distance to the prepositional phrase from nine to three and
raises its distance to the object from six to nine, so the total dependency length falls. -/
theorem heavyNPShift_shorter : shifted.totalLength < longObjectFirst.totalLength := by decide

/-! ### Morpheme order and the relevance hierarchy, section 6.3 -/

/-- The template's suffix order is sorted by the relevance hierarchy. -/
def _root_.Morphology.AffixTemplate.suffixRespectsRelevance
    (t : AffixTemplate MorphCategory) : Prop :=
  RespectsRelevanceHierarchy t.suffixSlots

instance (t : AffixTemplate MorphCategory) : Decidable t.suffixRespectsRelevance :=
  inferInstanceAs (Decidable (RespectsRelevanceHierarchy _))

/-- Sesotho's suffixes, valence, voice, tense, mood, and the final interrogative or relative
slot, are sorted by the relevance hierarchy, which on the surveyed categories is
[bybee-1985]'s order, `Bybee1985.survey_order_iso_relevance`. -/
theorem sesotho_suffixes_respect_relevance :
    Sesotho.verbAffixTemplate.suffixRespectsRelevance := by decide

/-- Japanese respects the hierarchy up to its mood slot: derivation, valence, voice, mood. -/
theorem japanese_partial_relevance :
    RespectsRelevanceHierarchy [MorphCategory.derivation, .valence, .voice, .mood] := by
  decide

/-- [bybee-1985]'s survey ranks tense closer to the stem than mood,
`Bybee1985.SurveyedCloser`, yet the Japanese desiderative, a mood suffix, precedes tense and
negation, so the full suffix order is not sorted by the relevance hierarchy: the paper's
"broadly in agreement" is not agreement. -/
theorem japanese_violates_surveyed_relevance :
    Bybee1985.SurveyedCloser .tense .mood ∧
      ¬ Japanese.verbAffixTemplate.suffixRespectsRelevance := by
  decide

end HahnDegenFutrell2021
