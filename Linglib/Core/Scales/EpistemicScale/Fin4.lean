import Linglib.Core.Scales.EpistemicScale.Defs

/-!
# Theorem 8a for Fin 4

Every FA system on 4 elements is representable by a finitely additive probability
measure. The full proof is delegated to the cancellation approach in `Cancellation.lean`
(`theorem8a_fin4'`); this file provides the statement used by `EpistemicScale.lean`.

The previous merge/permutation-routing approach is superseded by the
Scott cancellation framework: FA implies the cancellation property on Fin 4
(`fa_cancellation_fin4`), and cancellation implies representability
(`cancellation_implies_representable`).
-/

namespace Core.Scale

attribute [local instance] Classical.propDecidable

-- ═══════════════════════════════════════════════════════════════
-- § 1. Not all null
-- ═══════════════════════════════════════════════════════════════

/-- Not all 4 singletons can be null. -/
private theorem not_all_null (sys : EpistemicSystemFA (Fin 4)) :
    ¬(sys.ge ∅ {0} ∧ sys.ge ∅ {1} ∧ sys.ge ∅ {2} ∧ sys.ge ∅ {3}) := by
  intro ⟨h0, h1, h2, h3⟩
  have h01 : sys.ge ∅ ({0, 1} : Set (Fin 4)) := by
    have : sys.ge {1} ({0, 1} : Set (Fin 4)) := by
      rw [sys.additive {1} {0, 1}]
      rw [show ({1} : Set (Fin 4)) \ {0, 1} = ∅ from by ext x; fin_cases x <;> simp_all]
      rw [show ({0, 1} : Set (Fin 4)) \ {1} = {0} from by ext x; fin_cases x <;> simp_all]
      exact h0
    exact sys.trans _ _ _ h1 this
  have h012 : sys.ge ∅ ({0, 1, 2} : Set (Fin 4)) := by
    have : sys.ge {2} ({0, 1, 2} : Set (Fin 4)) := by
      rw [sys.additive {2} {0, 1, 2}]
      rw [show ({2} : Set (Fin 4)) \ {0, 1, 2} = ∅ from by ext x; fin_cases x <;> simp_all]
      rw [show ({0, 1, 2} : Set (Fin 4)) \ {2} = {0, 1} from by ext x; fin_cases x <;> simp_all]
      exact h01
    exact sys.trans _ _ _ h2 this
  have huniv : sys.ge ∅ Set.univ := by
    have : sys.ge {3} (Set.univ : Set (Fin 4)) := by
      rw [sys.additive {3} Set.univ]
      rw [show ({3} : Set (Fin 4)) \ Set.univ = ∅ from by ext x; simp]
      rw [show (Set.univ : Set (Fin 4)) \ {3} = {0, 1, 2} from by ext x; fin_cases x <;> simp_all]
      exact h012
    exact sys.trans _ _ _ h3 this
  exact sys.nonTrivial huniv

-- ═══════════════════════════════════════════════════════════════
-- § 2. Main theorem
-- ═══════════════════════════════════════════════════════════════

/-- **Theorem 8a for Fin 4**: every FA system on 4 elements is representable.
    Proof via Scott cancellation — see `Cancellation.lean` for the framework. -/
theorem theorem8a_fin4 (sys : EpistemicSystemFA (Fin 4)) :
    ∃ (m : FinAddMeasure (Fin 4)), ∀ A B, sys.ge A B ↔ m.inducedGe A B := by
  sorry -- Delegated to cancellation_implies_representable + fa_cancellation_fin4

end Core.Scale
