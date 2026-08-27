import Linglib.Studies.AlexandropoulouGotzner2024a
import Linglib.Data.Examples.AlexandropoulouGotzner2024b

/-!
# Alexandropoulou and Gotzner (2024b): adjective interpretation and competition

Re-runs the rating experiments of [alexandropoulou-gotzner-2024a] with one
statement per trial, removing the overt competition among the eight forms of an
item. The polarity asymmetry of weak relative antonyms persists and is larger
without competition, absolute antonyms stay symmetric in both modes, and negated
weak absolutes (*not dirty*, *not clean*) are nonetheless rated differently from
their truth-conditionally equivalent simple antonyms (*clean*, *dirty*).

The relative pattern is Horn's: R-strengthening of *not large* needs no
competitor, while the middling reading of *not small* rides on the semantic gap.
For absolutes the paper proposes that competition among equivalent forms invites
a precision-level reasoning: *clean* is read at a high precision, opening a gap
the complex forms fill. On a two-threshold scale this is exactly the observed
profile — both negated weak forms come apart from their simple antonyms
(`relative_like`) yet the residues are mirror images (`residues_symmetric`),
whereas at a single threshold neither distinction exists
(`Degree.contradictoryDenot_synonymy`).

## References

* [alexandropoulou-gotzner-2024b]
* [alexandropoulou-gotzner-2024a]
* [horn-1989]
* [kennedy-2007]
-/

namespace AlexandropoulouGotzner2024b

open Degree AlexandropoulouGotzner2024a

/-! ### Precision-level gap -/

variable {max : ℕ} (tp : ThresholdPair max)

/-- Under a precision-opened gap, *not dirty* is not *clean* and *not clean* is not
    *dirty*: the relative-like distinctions of the single-statement data. -/
theorem relative_like (h : (tp.neg : Bounded max) < tp.pos) :
    (∃ d, AntonymForm.strengthenedDenot tp .notNegative d ∧
      ¬ AntonymForm.strengthenedDenot tp .positive d) ∧
    ∃ d, AntonymForm.strengthenedDenot tp .notPositive d ∧
      ¬ AntonymForm.strengthenedDenot tp .negative d := by
  refine ⟨Degree.strengthenedDenot_breaks_synonymy tp h, ↑tp.neg, ?_, ?_⟩
  · simpa [Degree.positiveMeaning, Core.Order.Comparison.mem_over, Core.Order.Comparison.rel]
      using le_of_lt h
  · simp [Degree.negativeMeaning, Core.Order.Comparison.mem_over, Core.Order.Comparison.rel]

/-- The two residues are the same region — the gap — so the distinctions are
    symmetric across polarity. -/
theorem residues_symmetric (d : Bounded max) :
    (AntonymForm.strengthenedDenot tp .notNegative d ∧
      ¬ AntonymForm.strengthenedDenot tp .positive d) ↔
    (AntonymForm.strengthenedDenot tp .notPositive d ∧
      ¬ AntonymForm.strengthenedDenot tp .negative d) := by
  simp only [AntonymForm.strengthenedDenot, Degree.positiveMeaning', Degree.contraryNegMeaning,
    Degree.notContraryNegMeaning, Degree.contradictoryNeg, Degree.positiveMeaning,
    Degree.negativeMeaning, Degree.notPositiveMeaning, Core.Order.Comparison.mem_over,
    Core.Order.Comparison.rel, id_eq, not_lt]
  exact and_comm

/-! ### Rows -/

/-- An unmodified negated adjective entails its antonym exactly when the Fragment
    classifies the pair as contradictory. -/
theorem entails_iff_contradictory :
    ∀ row ∈ Examples.all, row.feature? "modifier" = none →
      row.feature? "negation" = some "negated" →
      ∀ e ∈ (row.feature? "adjective").bind entryOf,
        (row.feature? "relation" = some "entails" ↔
          e.antonymRelation = some .contradictory) := by
  decide

/-- The paper's two pragmatic readings are Horn's ranges: negative strengthening
    lands *not large* on the antonym, the middling reading lands *not small* on
    the gap. -/
theorem readings_are_horn_ranges :
    ∀ row ∈ Examples.all, ∀ f ∈ formOf row, ∀ i ∈ row.feature? "inference",
      (i = "negative_strengthening" ↔ hornRanges f = {.negative}) ∧
      (i = "middling" ↔ hornRanges f = {.plateauLow, .plateauHigh}) := by
  decide

end AlexandropoulouGotzner2024b
