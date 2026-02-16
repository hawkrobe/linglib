import Linglib.Theories.DynamicSemantics.Core.DynamicTy2
import Linglib.Theories.DynamicSemantics.Effects.Nondeterminism.Charlow2019

/-!
# Pointwise ↔ Update-Theoretic Bridge

Connects the pointwise `DRS S := S → S → Prop` type (Dynamic Ty2, Muskens 1996)
to the update-theoretic `StateCCP W E := State W E → State W E` type (Charlow 2019).

The key operations are Charlow's (2021) ↑ (lift) and ↓ (lower):
- `liftPW`: promotes a pointwise DRS to a context-level update
- `lowerPW`: extracts a pointwise relation from a context update

The central result: `liftPW D` is always distributive (Charlow 2021, §6),
meaning pointwise meanings can never produce irreducibly context-level effects.
Cumulative readings require non-distributive M_v, which lives only in `StateCCP`.

## References

- Charlow, S. (2021). Post-suppositions and semantic theory. *L&P* 44, 701–765.
  Equations 76–77.
- Muskens, R. (1996). Combining Montague Semantics and Discourse Representation.
-/

namespace DynamicSemantics.Core.PointwiseUpdate

open DynamicSemantics.Core.DynamicTy2
open DynamicSemantics.Charlow2019

variable {W E : Type*}

/-- Charlow's ↑ (equation 76): lift a pointwise DRS to an update on states.
    `liftPW D s = {⟨w, h⟩ | ∃ ⟨w, g⟩ ∈ s, D g h}`
    Each world-assignment pair in the output comes from applying D to some
    input assignment in s, preserving the world. -/
def liftPW (D : DRS (Assignment E)) : StateCCP W E :=
  λ s => {p | ∃ q ∈ s, p.1 = q.1 ∧ D q.2 p.2}

/-- Charlow's ↓ (equation 77): extract a pointwise DRS from a state update.
    Evaluates K on a singleton context at an arbitrary world. -/
def lowerPW (K : StateCCP W E) (w₀ : W) : DRS (Assignment E) :=
  λ g h => (w₀, h) ∈ K {(w₀, g)}

/-- Round-trip identity: lowering a lifted DRS recovers the original.

    `↓(↑D) = D` because the singleton context `{(w₀, g)}` passes through ↑
    with only `(w₀, g)` as witness, leaving exactly the pairs `h` with `D g h`. -/
theorem lowerPW_liftPW (D : DRS (Assignment E)) (w₀ : W) :
    lowerPW (liftPW D) w₀ = D := by
  ext g h
  constructor
  · intro hm
    show D g h
    simp only [lowerPW, liftPW, Set.mem_setOf_eq] at hm
    obtain ⟨q, hq, h1, h2⟩ := hm
    cases hq; exact h2
  · intro hD
    show (w₀, h) ∈ liftPW D {(w₀, g)}
    simp only [liftPW, Set.mem_setOf_eq]
    exact ⟨(w₀, g), rfl, rfl, hD⟩

/-- ↑ is injective: distinct DRSs yield distinct state updates.

    Follows from the round-trip: `D = ↓(↑D)`, so `↑D₁ = ↑D₂` implies
    `D₁ = ↓(↑D₁) = ↓(↑D₂) = D₂`. Requires `W` to be nonempty for the
    lowering witness world. -/
theorem liftPW_injective [Nonempty W] (D₁ D₂ : DRS (Assignment E))
    (h : liftPW (W := W) D₁ = liftPW D₂) :
    D₁ = D₂ := by
  have w₀ : W := Classical.arbitrary W
  calc D₁ = lowerPW (liftPW D₁) w₀ := (lowerPW_liftPW D₁ w₀).symm
    _ = lowerPW (liftPW D₂) w₀ := by rw [h]
    _ = D₂ := lowerPW_liftPW D₂ w₀

/-- Lifted pointwise DRSs are always distributive (Charlow 2021, §6, key lemma).

    `↑D` processes each element of the input state independently — the output
    at `p` depends only on whether some `q ∈ s` satisfies `D q.2 p.2` with
    matching world `p.1 = q.1`. This is exactly the singleton decomposition
    `(↑D)(s) = ⋃_{i∈s} (↑D)({i})`, which is the definition of distributivity. -/
theorem liftPW_preserves_distributive (D : DRS (Assignment E)) :
    isDistributive (liftPW (W := W) D) := by
  intro s; ext p
  constructor
  · intro hp
    simp only [liftPW, Set.mem_setOf_eq] at hp
    obtain ⟨q, hq, h1, h2⟩ := hp
    exact ⟨q, hq, by simp only [liftPW, Set.mem_setOf_eq]; exact ⟨q, rfl, h1, h2⟩⟩
  · rintro ⟨i, hi, hp⟩
    simp only [liftPW, Set.mem_setOf_eq] at hp ⊢
    obtain ⟨q, hq, h1, h2⟩ := hp
    cases hq; exact ⟨i, hi, h1, h2⟩

/-- ↑↓ ≠ id: there exist irreducibly update-theoretic meanings K such that
    liftPW (lowerPW K w₀) ≠ K. Non-distributive meanings are the key examples.
    TODO: Exhibit a 2-element context where M_v differs. -/
theorem liftPW_lowerPW_not_id :
    ∃ (K : StateCCP W E) (w₀ : W), liftPW (lowerPW K w₀) ≠ K := by
  sorry

end DynamicSemantics.Core.PointwiseUpdate
