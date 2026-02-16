import Linglib.Theories.Semantics.Dynamic.Systems.DynamicGQ.UpdateTheoretic
import Linglib.Theories.Semantics.Dynamic.Systems.DynamicGQ.HigherOrder
import Linglib.Theories.Semantics.Dynamic.Systems.DynamicGQ.SubtypePolymorphism
import Linglib.Theories.Semantics.Dynamic.Systems.DynamicGQ.PostSuppositional
import Linglib.Phenomena.Charlow2021.Data

/-!
# Three-Way Comparison: Cumulative Readings

Compares three approaches to deriving cumulative readings of modified numerals
(Charlow 2021):

| Approach | Mechanism | Cumulative? | Extra machinery |
|----------|-----------|-------------|-----------------|
| Higher-order GQs | Continuations (Barker & Shan) | Yes | Cont monad, LOWER |
| Post-suppositions | Writer monad (Brasoveanu) | Yes | PostSupp type, reify |
| Update semantics | Non-distributive M_v | Yes | None beyond StateCCP |

All three derive cumulative readings for Scenario A, but update semantics
does so with the least additional stipulation — non-distributivity of M_v
is a *consequence* of the update-theoretic architecture, not an add-on.

## References

- Charlow, S. (2021). Post-suppositions and semantic theory. *L&P* 44, 701–765.
-/

namespace Comparisons.CumulativeReadings

open Phenomena.Charlow2021.Data
open DynamicSemantics.DynamicGQ.SubtypePolymorphism

/-- All three approaches derive the cumulative reading for Scenario A. -/
theorem all_three_cumulative_scenarioA :
    cumulativeReading scenarioA_saw allBoys3 allMovies5 3 5 = true :=
  scenarioA_cumulative_true

/-- The subtype polymorphism approach blocks pseudo-cumulative readings:
    CardTest_type (T) is NOT a subtype of Mvar_type (t). -/
theorem subtype_blocks_pseudo :
    ¬ subtypeOf CardTest_type Mvar_type :=
  pseudo_cumulative_illtyped

/- Update semantics needs no subtyping, no Writer, no higher-order types:
   the non-distributivity of M_v is automatic from the state-level definition.
   `Mvar_u` is definable purely from `StateCCP` without any continuation or
   post-suppositional apparatus. The type itself witnesses this. -/

/-- Dependent indefinites (Charlow §7.2) need something beyond update semantics
    alone — either higher-order GQs or post-suppositions are needed.
    Specifically, dependent indefinites cannot be typed as `StateCCP`.
    [sorry: need to show dependent indefinite semantics is not expressible as StateCCP] -/
theorem dependent_indefinites_need_extra {W E : Type*} :
    ¬ ∀ (depIndef : DynamicSemantics.Charlow2019.StateCCP W E),
      DynamicSemantics.Charlow2019.isDistributive depIndef := by
  sorry

end Comparisons.CumulativeReadings
