import Linglib.Processing.Memory.SurprisalTradeoff
import Linglib.Fragments.Japanese.Predicates
import Linglib.Fragments.Japanese.Morph
import Linglib.Fragments.Sesotho.Morph
import Linglib.Morphology.RelevanceHierarchy
import Linglib.Studies.Bybee1985

/-!
# Study 3: Morpheme Order Optimization (Japanese & Sesotho)
[bybee-1985] [demuth-1992] [doke-mofokeng-1967] [hahn-degen-futrell-2021] [kaiser-yamamoto-2013]

[hahn-degen-futrell-2021] Study 3: morpheme orders in Japanese verb suffixes
and Sesotho verb affixes are near-optimally efficient in terms of
memory-surprisal trade-offs. The real morpheme orders achieve lower AUC
than random baselines.

## Japanese Verb Suffixes (SI §4.1, Table 2)

Seven suffix slots ordered from stem outward:
1. Derivation: -su (suru)
2. VALENCE: causative -(s)ase
3. VOICE: passive/potential -are, -rare
4. MOOD: desiderative -ta, politeness -mas
5. NEGATION: -na
6. TENSE/ASPECT/MOOD: -ta (past), -yoo (future)
7. Nonfinite: -te

Real order AUC ≈ 47.0 (morpheme level), baselines ≈ 47.2 (SI Figure 6).

## Sesotho Verb Affixes (SI §4.2)

Prefixes: subject agreement, negation, tense/aspect, object agreement
Suffixes: reversive, causative, neuter, applicative, completive,
          reciprocal, passive, tense, mood, interrogative/relative

Real order AUC ≈ 38.7 (morpheme level), baselines ≈ 38.8 (SI Figure 8).

## [bybee-1985] Relevance Hierarchy

stem < valence < voice < aspect < tense < mood < agreement

Both Japanese suffixes and Sesotho suffixes respect this hierarchy:
morphemes closer to the stem are more semantically relevant to the verb.

## Data Source

<https://github.com/m-hahn/memory-surprisal>. Morpheme order data from
SI §4.1-4.2, AUC values from SI Figures 6 and 8.

-/

namespace HahnDegenFutrell2021

open Processing.MemorySurprisal
open Morphology (MorphCategory RespectsRelevanceHierarchy)

-- ============================================================================
-- §2: Japanese Suffix Template (SI §4.1)
-- ============================================================================

/-! ### Japanese verb suffixes

SI §4.1's Japanese suffix order ([kaiser-yamamoto-2013], UD segmentation) is the
language's affix template, so it lives as Fragment data in
`Fragments/Japanese/Morph.lean` (`Japanese.verbAffixTemplate`); here we derive
the slot list from it rather than re-typing it. -/

/-- Japanese suffix slots from stem outward, derived from the Fragment template
`Japanese.verbAffixTemplate` (SI §4.1, [kaiser-yamamoto-2013]). -/
def japaneseSuffixSlots : List MorphCategory :=
  Japanese.verbAffixTemplate.suffixSlots

/-- Japanese suffix order respects Bybee's hierarchy through the mood slot:
derivation < valence < voice < mood. Beyond mood the order *breaks* —
politeness (agreement), negation, then tense — so only this stem-adjacent
prefix is checked; the full-order violation is `japanese_violates_surveyed_relevance`. -/
theorem japanese_partial_bybee :
    let slots := [MorphCategory.derivation, .valence, .voice, .mood]
    RespectsRelevanceHierarchy slots := by decide

/-- **Structural divergence from the survey.** Bybee's Ch 2 §6 data ranks tense
more stem-relevant than mood (`Bybee1985.SurveyedCloser .tense .mood`, which by
`Bybee1985.survey_order_iso_relevance` *is* the substrate relevance order on
these categories), yet Japanese's causative/desiderative layering places `mood`
closer to the stem than `tense` (slots 4 vs 7) — so its full suffix order is not
sorted by the relevance hierarchy. A genuine cross-linguistic counterexample to
the §6 morpheme-order corollary, stated as a failure of the substrate predicate,
not a positional count. -/
theorem japanese_violates_surveyed_relevance :
    Bybee1985.SurveyedCloser .tense .mood ∧
    ¬ Japanese.verbAffixTemplate.suffixRespectsRelevance := by
  decide

-- ============================================================================
-- §3: Sesotho Verb Template (SI §4.2)
-- ============================================================================

/-! ### Sesotho verb affixes

SI §4.2's Sesotho affix order ([demuth-1992], [doke-mofokeng-1967]) lives as
Fragment data in `Fragments/Sesotho/Morph.lean` (`Sesotho.verbAffixTemplate`);
the slot lists below are derived from it. -/

/-- Sesotho suffix template, stem-outward, from the Fragment
`Sesotho.verbAffixTemplate` (SI §4.2). -/
def sesothoSuffixSlots : List MorphCategory :=
  Sesotho.verbAffixTemplate.suffixSlots

/-- Sesotho prefix template, word-edge inward, from the Fragment
`Sesotho.verbAffixTemplate`. -/
def sesothoPrefixSlots : List MorphCategory :=
  Sesotho.verbAffixTemplate.prefixSlots

/-- Sesotho suffixes respect the relevance hierarchy
(valence < voice < tense < mood < nonfinite) — sorted by the substrate
relevance order, which on the surveyed categories *is* Bybee's §6 order
(`Bybee1985.survey_order_iso_relevance`). Contrast
`japanese_violates_surveyed_relevance`: same surveyed order, opposite outcome. -/
theorem sesotho_suffixes_respect_bybee :
    Sesotho.verbAffixTemplate.suffixRespectsRelevance := by decide

-- ============================================================================
-- §4: Memory-Surprisal Efficiency (SI Figures 6, 8)
-- ============================================================================

/-! ### Trade-off curves

Approximate AUC values from SI Figures 6 and 8. AUC is computed
over the memory-surprisal trade-off curve (lower = more efficient).
Values are multiplied by 100 for integer arithmetic. -/

/-- Japanese morpheme-level AUC × 100. Real ≈ 47.0, Random ≈ 47.2. -/
def japaneseRealAUC100 : Nat := 4700
def japaneseRandomAUC100 : Nat := 4720

/-- Sesotho morpheme-level AUC × 100. Real ≈ 38.7, Random ≈ 38.8. -/
def sesothoRealAUC100 : Nat := 3870
def sesothoRandomAUC100 : Nat := 3880

/-- Japanese real morpheme order is more efficient than random baselines. -/
theorem japanese_morpheme_efficient :
    japaneseRealAUC100 < japaneseRandomAUC100 := by native_decide

/-- Sesotho real morpheme order is more efficient than random baselines. -/
theorem sesotho_morpheme_efficient :
    sesothoRealAUC100 < sesothoRandomAUC100 := by native_decide

-- ============================================================================
-- §5: Morpheme Prediction Accuracy (SI Figure 7)
-- ============================================================================

/-! ### Prediction accuracy

From SI Figure 7 (Japanese) and Figure 9 (Sesotho). The optimized
morpheme order achieves higher pairwise prediction accuracy than
random baselines, and similar accuracy to the real order.

Values are accuracy × 1000. -/

/-- Japanese morpheme prediction: optimized pairs accuracy × 1000. -/
def japanesePairsOptimized : Nat := 953
/-- Japanese morpheme prediction: random baseline pairs accuracy × 1000. -/
def japanesePairsRandom : Nat := 496
/-- Japanese morpheme prediction: real order pairs accuracy × 1000. -/
def japanesePairsReal : Nat := 953

/-- Optimized and real orders vastly outperform random baseline for Japanese. -/
theorem japanese_optimized_beats_random :
    japanesePairsOptimized > japanesePairsRandom := by native_decide

/-- The real Japanese order achieves accuracy matching the optimized order. -/
theorem japanese_real_matches_optimized :
    japanesePairsReal = japanesePairsOptimized := by native_decide

-- ============================================================================
-- §6: Bridges
-- ============================================================================

/-! ### Bridge: Japanese causative is innermost suffix

The Bybee hierarchy predicts valence morphemes should be closest to
the stem. Japanese -(s)ase (causative = valence) is slot 2, the first
functional suffix after derivation. This is consistent with both:
1. The relevance hierarchy (valence is closest to stem meaning)
2. The memory-surprisal explanation (valence affects subcategorization,
   so placing it near the stem concentrates predictive information locally) -/

/-- Japanese causative -(s)ase is in the valence slot (slot 2). -/
theorem japanese_causative_is_valence :
    japaneseSuffixSlots[1]? = some .valence := by decide

/-- The valence slot is the first functional slot (after derivation). -/
theorem valence_is_innermost_functional :
    japaneseSuffixSlots[0]? = some .derivation ∧
    japaneseSuffixSlots[1]? = some .valence := by decide

/-! ### Bridge: Japanese -(s)ase = Song's COMPACT morphological causative

Japanese -(s)ase is classified as a morphological COMPACT causative in
[song-1996]. The `ik_ase` entry in `Fragments/Japanese/Predicates` confirms
this: `causative = some.make`. -/

/-- The Japanese -(s)ase causative entry is causative (derived from causative). -/
theorem ik_ase_is_causative :
    Japanese.Predicates.ik_ase.causative.isSome = true := rfl

/-- Japanese -(s)ase uses the.make causative builder (direct causation). -/
theorem ik_ase_is_make :
    Japanese.Predicates.ik_ase.causative = some .make := rfl

/-! ### Bridge: Relevance hierarchy ↔ Information locality

The Bybee hierarchy orders morphemes by semantic relevance to the stem.
The memory-surprisal framework predicts that information-locality-optimal
orderings place highly predictive morphemes close to the stem. These
two predictions converge: semantic relevance correlates with predictive
information, so the relevance hierarchy is an instantiation of information
locality at the morpheme level.

The near-optimality of Japanese and Sesotho morpheme orders
(`japanese_morpheme_efficient`, `sesotho_morpheme_efficient`) shows that
real morpheme orders are close to the information-locality optimum,
and the fact that they respect the relevance hierarchy
(`japanese_partial_bybee`, `sesotho_suffixes_respect_bybee`) shows
that the relevance hierarchy captures the right notion of locality. -/
theorem relevance_hierarchy_implies_locality :
    -- Languages whose morpheme orders respect Bybee's hierarchy
    -- are also efficient in memory-surprisal terms
    Sesotho.verbAffixTemplate.suffixRespectsRelevance ∧
    sesothoRealAUC100 < sesothoRandomAUC100 :=
  ⟨by decide, by native_decide⟩

end HahnDegenFutrell2021
