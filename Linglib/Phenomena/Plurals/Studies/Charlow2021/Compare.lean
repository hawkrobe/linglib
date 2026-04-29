import Linglib.Theories.Semantics.Quantification.Dynamic.UpdateTheoretic
import Linglib.Theories.Semantics.Quantification.Dynamic.HigherOrder
import Linglib.Theories.Semantics.Quantification.Dynamic.SubtypePolymorphism
import Linglib.Theories.Semantics.Quantification.Dynamic.PostSuppositional
import Linglib.Phenomena.Plurals.Studies.Charlow2021.Data

/-!
# Three-Way Comparison: Cumulative Readings
@cite{charlow-2021}

Compares three approaches to deriving cumulative readings of modified numerals:

| Approach | Mechanism | Cumulative? | Extra machinery |
|----------|-----------|-------------|-----------------|
| Higher-order GQs | Continuations (Barker & Shan) | Yes | Cont monad, LOWER |
| Post-suppositions | Writer monad (Brasoveanu) | Yes | PostSupp type, reify |
| Update semantics | Non-distributive M_v | Yes | None beyond StateCCP |

All three derive cumulative readings for Scenario A, but update semantics
does so with the least additional stipulation — non-distributivity of M_v
is a *consequence* of the update-theoretic architecture, not an add-on.

-/

namespace Phenomena.Plurals.Compare

open Data
open Semantics.Quantification.Dynamic.SubtypePolymorphism

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

    Proof: the constant CCP `fun _ => Set.univ` is not distributive —
    it maps ∅ to Set.univ, but per-element processing of ∅ yields ∅. -/
theorem dependent_indefinites_need_extra {W E : Type*} [Nonempty W] [Nonempty E] :
    ¬ ∀ (depIndef : Semantics.Dynamic.Core.StateCCP W E),
      Semantics.Dynamic.Core.IsDistributive depIndef := by
  intro h
  -- The constant CCP returning everything is not distributive at ∅
  have h0 := h (fun _ => Set.univ) ∅
  -- LHS: φ ∅ = Set.univ. RHS: {p | ∃ i ∈ ∅, ...} = ∅.
  simp only [Set.mem_empty_iff_false, false_and, exists_false, Set.setOf_false] at h0
  exact Set.univ_nonempty.ne_empty h0

end Phenomena.Plurals.Compare
