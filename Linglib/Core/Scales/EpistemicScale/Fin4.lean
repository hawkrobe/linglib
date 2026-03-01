import Linglib.Core.Scales.EpistemicScale.Cancellation88

/-!
# Theorem 8a for Fin 4

Every FA system on 4 elements is representable by a finitely additive probability
measure. This follows from the Scott cancellation framework:
FA implies the cancellation property on Fin 4 (`fa_cancellation_fin4`),
and cancellation implies representability (`cancellation_implies_representable`).
-/

namespace Core.Scale

/-- **Theorem 8a for Fin 4**: every FA system on 4 elements is representable.
    Proof via Scott cancellation — see `Cancellation.lean` for the framework. -/
theorem theorem8a_fin4 (sys : EpistemicSystemFA (Fin 4)) :
    ∃ (m : FinAddMeasure (Fin 4)), ∀ A B, sys.ge A B ↔ m.inducedGe A B :=
  cancellation_implies_representable sys (fa_cancellation_fin4 sys)

end Core.Scale
