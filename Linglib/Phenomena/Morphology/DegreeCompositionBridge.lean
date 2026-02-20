import Linglib.Theories.Morphology.Core.Exponence
import Linglib.Theories.Morphology.Core.ScaleFromParadigm
import Linglib.Fragments.English.Modifiers.Adjectives

/-!
# Degree Morphology Composition: Phenomena

Empirical tests for the degree morphology pipeline, verifying that
adjective stems produce correct comparative and superlative forms
and that Horn scale generation works correctly.

## Coverage

1. **Regular comparatives**: tall → taller, tallest
2. **Irregular comparatives**: good → better, best
3. **Periphrastic**: expensive → "more expensive", "most expensive"
4. **Non-gradable**: dead, pregnant — empty degree paradigms
5. **Scale generation**: tall produces 3-point scale [tall, taller, tallest]
6. **Morphological alternatives**: correct alternatives for each form
7. **Bybee bridge**: `.degree` has correct relevance rank
8. **Vacuity**: all degree rules are semantically vacuous

## References

- Kennedy, C. (2007). Vagueness and grammar.
- Horn, L. R. (1972). On the Semantic Properties of Logical Operators in English.
- Bybee, J. L. (1985). Morphology.
-/

namespace Phenomena.Morphology.DegreeCompositionBridge

open Core.Morphology
open Core.Morphology.Degree
open Core.Morphology.ScaleFromParadigm
open Fragments.English.Modifiers.Adjectives

-- ============================================================================
-- §1: Regular Comparatives
-- ============================================================================

private def tallStem := tall.toStem Unit
private def hotStem := hot.toStem Unit
private def coldStem := cold.toStem Unit

/-- Regular comparative: "tall" → "taller" -/
theorem tall_comparative_form :
    tallStem.paradigm.head?.map (·.formRule tallStem.lemma_)
    = some "taller" := rfl

/-- Regular superlative: "tall" → "tallest" -/
theorem tall_superlative_form :
    (tallStem.paradigm.tail.head?.map (·.formRule tallStem.lemma_))
    = some "tallest" := rfl

/-- Regular comparative: "hot" → "hotter" -/
theorem hot_comparative_form :
    hotStem.paradigm.head?.map (·.formRule hotStem.lemma_)
    = some "hotter" := rfl

/-- Regular comparative: "cold" → "colder" -/
theorem cold_comparative_form :
    coldStem.paradigm.head?.map (·.formRule coldStem.lemma_)
    = some "colder" := rfl

-- ============================================================================
-- §2: Irregular Comparatives
-- ============================================================================

private def goodStem := good.toStem Unit
private def badStem := bad.toStem Unit

/-- Irregular comparative: "good" → "better" (not *"gooder") -/
theorem good_comparative_form :
    goodStem.paradigm.head?.map (·.formRule goodStem.lemma_)
    = some "better" := rfl

/-- Irregular superlative: "good" → "best" (not *"goodest") -/
theorem good_superlative_form :
    (goodStem.paradigm.tail.head?.map (·.formRule goodStem.lemma_))
    = some "best" := rfl

/-- Irregular comparative: "bad" → "worse" -/
theorem bad_comparative_form :
    badStem.paradigm.head?.map (·.formRule badStem.lemma_)
    = some "worse" := rfl

/-- Irregular superlative: "bad" → "worst" -/
theorem bad_superlative_form :
    (badStem.paradigm.tail.head?.map (·.formRule badStem.lemma_))
    = some "worst" := rfl

-- ============================================================================
-- §3: Periphrastic Comparatives
-- ============================================================================

private def expensiveStem := expensive.toStem Unit

/-- Periphrastic comparative: "expensive" → "more expensive" -/
theorem expensive_comparative_form :
    expensiveStem.paradigm.head?.map (·.formRule expensiveStem.lemma_)
    = some "more expensive" := rfl

/-- Periphrastic superlative: "expensive" → "most expensive" -/
theorem expensive_superlative_form :
    (expensiveStem.paradigm.tail.head?.map (·.formRule expensiveStem.lemma_))
    = some "most expensive" := rfl

-- ============================================================================
-- §4: Non-Gradable Adjectives — Empty Degree Paradigms
-- ============================================================================

private def deadStem := dead.toStem Unit
private def pregnantStem := pregnant.toStem Unit

/-- "dead" has no comparative/superlative paradigm. -/
theorem dead_no_degree_paradigm : deadStem.paradigm.length = 0 := rfl

/-- "pregnant" has no comparative/superlative paradigm. -/
theorem pregnant_no_degree_paradigm : pregnantStem.paradigm.length = 0 := rfl

-- ============================================================================
-- §5: Scale Generation
-- ============================================================================

/-- Scale generation produces a 3-point scale for "tall". -/
theorem tall_scale_exists :
    (adjectiveScale tallStem).isSome = true := rfl

/-- The tall scale has the correct members: [tall, taller, tallest]. -/
theorem tall_scale_members :
    (adjectiveScale tallStem).map (·.toHornScale.members)
    = some ["tall", "taller", "tallest"] := rfl

/-- The good scale has the correct irregular members: [good, better, best]. -/
theorem good_scale_members :
    (adjectiveScale goodStem).map (·.toHornScale.members)
    = some ["good", "better", "best"] := rfl

/-- The expensive scale has periphrastic forms. -/
theorem expensive_scale_members :
    (adjectiveScale expensiveStem).map (·.toHornScale.members)
    = some ["expensive", "more expensive", "most expensive"] := rfl

/-- Non-gradable adjectives produce no scale. -/
theorem dead_no_scale :
    (adjectiveScale deadStem).isNone = true := rfl

theorem pregnant_no_scale :
    (adjectiveScale pregnantStem).isNone = true := rfl

-- ============================================================================
-- §6: Morphological Alternatives
-- ============================================================================

/-- "tall" has alternatives ["taller", "tallest"]. -/
theorem tall_alternatives :
    morphologicalAlternatives tallStem "tall"
    = ["taller", "tallest"] := rfl

/-- "taller" has alternatives ["tall", "tallest"]. -/
theorem taller_alternatives :
    morphologicalAlternatives tallStem "taller"
    = ["tall", "tallest"] := rfl

/-- "tallest" has alternatives ["tall", "taller"]. -/
theorem tallest_alternatives :
    morphologicalAlternatives tallStem "tallest"
    = ["tall", "taller"] := rfl

/-- "dead" has no alternatives (no degree paradigm). -/
theorem dead_no_alternatives :
    morphologicalAlternatives deadStem "dead" = [] := rfl

-- ============================================================================
-- §7: Bridge to Bybee (1985) Relevance Hierarchy
-- ============================================================================

/-- `.degree` has relevance rank 5, same as `.tense`. -/
theorem degree_relevance_rank :
    MorphCategory.degree.relevanceRank = 5 := rfl

/-- `.degree` shares rank with `.tense`: both compositionally modify
    their head's interpretation (degree on adjectives, tense on verbs). -/
theorem degree_same_rank_as_tense :
    MorphCategory.degree.relevanceRank = MorphCategory.tense.relevanceRank := rfl

/-- `.degree` is more relevant (lower rank) than `.agreement`. -/
theorem degree_more_relevant_than_agreement :
    MorphCategory.degree.relevanceRank < MorphCategory.agreement.relevanceRank := by
  native_decide

-- ============================================================================
-- §8: Semantic Vacuity of Degree Morphology
-- ============================================================================

/-- All degree rules in the tall paradigm are semantically vacuous. -/
theorem tall_all_vacuous :
    tallStem.paradigm.all (·.isVacuous) = true := rfl

/-- All degree rules in the good paradigm are semantically vacuous. -/
theorem good_all_vacuous :
    goodStem.paradigm.all (·.isVacuous) = true := rfl

/-- All degree rules in the expensive paradigm are semantically vacuous. -/
theorem expensive_all_vacuous :
    expensiveStem.paradigm.all (·.isVacuous) = true := rfl

/-- The vacuity theorem generalizes: all adjective entries with degree
    paradigms have vacuous rules. -/
theorem allAdjs_degree_vacuous :
    allEntries.all
      (λ a => (a.toStem Unit).paradigm.all (·.isVacuous))
    = true := by native_decide

-- ============================================================================
-- §9: Paradigm Size
-- ============================================================================

/-- Gradable adjectives with both comp and super get exactly 2 rules. -/
theorem tall_two_rules : tallStem.paradigm.length = 2 := rfl

/-- Gradable adjectives with both comp and super get exactly 2 rules. -/
theorem good_two_rules : goodStem.paradigm.length = 2 := rfl

-- ============================================================================
-- §10: All Adjective Entries Produce Valid Stems
-- ============================================================================

/-- Every adjective entry can be converted to a stem. -/
theorem allEntries_toStem_lemma :
    allEntries.map (λ a => (a.toStem Unit).lemma_)
    = allEntries.map (·.form) := rfl

/-- Degree paradigm rules all have `category = .degree`. -/
theorem tall_all_degree_category :
    tallStem.paradigm.all (·.category == .degree) = true := rfl

theorem good_all_degree_category :
    goodStem.paradigm.all (·.category == .degree) = true := rfl

end Phenomena.Morphology.DegreeCompositionBridge
