import Mathlib.Data.Set.Piecewise

/-!
# Interpolation between functions agreeing on an intersection

Two functions agree on `s ∩ t` iff some function agrees with the first
on `s` and with the second on `t` — the witness is the piecewise
combination along `s`. Companion to mathlib's `Set.eqOn_union`;
`[UPSTREAM]` candidate for `Mathlib.Data.Set.Piecewise`.
-/

namespace Set

variable {α β : Type*} {f h : α → β} {s t : Set α}

/-- Two functions agree on `s ∩ t` iff some function agrees with the
first on `s` and with the second on `t`. -/
theorem eqOn_inter_iff_exists :
    EqOn f h (s ∩ t) ↔ ∃ g, EqOn f g s ∧ EqOn g h t := by
  refine ⟨λ hfh => ?_, λ ⟨g, hs, ht⟩ v hv => (hs hv.1).trans (ht hv.2)⟩
  classical
  refine ⟨s.piecewise f h, (s.piecewise_eqOn f h).symm, λ v hv => ?_⟩
  by_cases hvs : v ∈ s
  · exact (piecewise_eq_of_mem _ _ _ hvs).trans (hfh ⟨hvs, hv⟩)
  · exact piecewise_eq_of_notMem _ _ _ hvs

end Set
