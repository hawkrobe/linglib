import Mathlib.Data.Set.Piecewise

/-!
# Piecewise interpolation between functions

Two functions agree on `s ∩ t` iff the piecewise combination — or some
function — interpolates between them, agreeing with the first on `s`
and with the second on `t`. Companion to mathlib's `Set.eqOn_union`.
-/

namespace Set

variable {α β : Type*}

/-- Two functions agree on `s ∩ t` iff some function agrees with the
first on `s` and with the second on `t` — the piecewise combination
interpolates. -/
theorem eqOn_inter {f f' : α → β} {s t : Set α} :
    EqOn f f' (s ∩ t) ↔ ∃ g, EqOn f g s ∧ EqOn g f' t := by
  refine ⟨fun hf => ?_, fun ⟨g, h₁, h₂⟩ x hx => (h₁ hx.1).trans (h₂ hx.2)⟩
  classical
  exact ⟨s.piecewise f f', (s.piecewise_eqOn f f').symm,
    s.eqOn_piecewise.mpr ⟨fun x hx => hf ⟨hx.2, hx.1⟩, fun _ _ => rfl⟩⟩

end Set
