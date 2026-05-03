import Linglib.Core.Logic.Team.Closure

/-!
# Team-semantic properties of formulas (Anttila 2021 §2.2) — re-exports

@cite{anttila-2021}

This file is now a **re-export shim**. The substrate moved to
`Core/Logic/Team/Closure.lean`, which states the four canonical Anttila
Definition 2.2.1 properties as facts about `TeamPred α := Finset α → Prop`
using mathlib's `IsLowerSet` and `SupClosed`:

| Anttila property      | `TeamPred` predicate          |
|-----------------------|-------------------------------|
| Downward closure      | `TeamPred.IsDownward`         |
| Union closure         | `TeamPred.IsSupClosed`        |
| Empty team property   | `TeamPred.HasEmpty`           |
| Flatness              | `TeamPred.IsFlat`             |

The central technical theorem (Anttila Proposition 2.2.2) is
`Core.Logic.Team.TeamPred.isFlat_iff` — flatness ↔ all three closure
properties.

## Migration from the old parametric API

Pre-0.230.653 this file held parametric definitions
`downwardClosed (support : Model → Form → Finset W → Prop) (φ : Form)`
that decorated a per-(M, φ) team-predicate with the Form/Model wrapping.
The decoration was unused — every theorem reduced to a fact about the
team-predicate `support M φ : Finset W → Prop`. Consumers now invoke
`(support M φ).IsDownward` etc. directly.

The audit-flagged "decorative parameters" objection (mathlib-reviewer +
linglib-integration-auditor, May 2026) is closed by this re-export.

## Deprecated aliases

For backward compatibility during the transition, deprecated aliases
preserve the parametric shape:
`downwardClosed support φ ≡ ∀ M, (support M φ).IsDownward` (etc.).
Consumers should prefer the `TeamPred` form.
-/

namespace Core.Logic.Team

variable {W : Type*} [DecidableEq W]
variable {Form : Type*}
variable {Model : Type*}

-- ============================================================================
-- §1 Deprecated parametric aliases
-- ============================================================================

/-- **Deprecated**: use `(support M φ).IsDownward` (per `TeamPred`) directly.
    Kept as a wrapper around the universal-over-models form. -/
def downwardClosed (support : Model → Form → Finset W → Prop) (φ : Form) : Prop :=
  ∀ M : Model, TeamPred.IsDownward (support M φ)

/-- **Deprecated**: use `(support M φ).IsSupClosed` directly. -/
def unionClosed (support : Model → Form → Finset W → Prop) (φ : Form) : Prop :=
  ∀ M : Model, TeamPred.IsSupClosed (support M φ)

/-- **Deprecated**: use `(support M φ).HasEmpty` directly. -/
def emptyTeam (support : Model → Form → Finset W → Prop) (φ : Form) : Prop :=
  ∀ M : Model, TeamPred.HasEmpty (support M φ)

/-- **Deprecated**: use `(support M φ).IsFlat` directly. -/
def flat (support : Model → Form → Finset W → Prop) (φ : Form) : Prop :=
  ∀ M : Model, TeamPred.IsFlat (support M φ)

-- ============================================================================
-- §2 Anttila Proposition 2.2.2 — wrapped form (delegates to TeamPred level)
-- ============================================================================

/-- **Anttila Proposition 2.2.2** in parametric form: a formula is flat iff
    it is downward-closed, sup-closed, and has the empty team property.
    Delegates per-`M` to `TeamPred.isFlat_iff`.

    Prefer `Core.Logic.Team.TeamPred.isFlat_iff` for new code (no Form/Model
    wrapping). -/
theorem flat_iff_downwardClosed_unionClosed_emptyTeam
    (support : Model → Form → Finset W → Prop) (φ : Form) :
    flat support φ ↔
      downwardClosed support φ ∧ unionClosed support φ ∧ emptyTeam support φ := by
  unfold flat downwardClosed unionClosed emptyTeam
  refine ⟨fun h => ⟨fun M => (TeamPred.isFlat_iff _).mp (h M) |>.1,
                    fun M => (TeamPred.isFlat_iff _).mp (h M) |>.2.1,
                    fun M => (TeamPred.isFlat_iff _).mp (h M) |>.2.2⟩,
          fun ⟨hd, hu, he⟩ M =>
            (TeamPred.isFlat_iff _).mpr ⟨hd M, hu M, he M⟩⟩

/-- Constructive form: combine the three to get flatness. -/
theorem flat_of_downwardClosed_unionClosed_emptyTeam
    {support : Model → Form → Finset W → Prop} {φ : Form}
    (hd : downwardClosed support φ) (hu : unionClosed support φ)
    (he : emptyTeam support φ) : flat support φ :=
  (flat_iff_downwardClosed_unionClosed_emptyTeam support φ).mpr ⟨hd, hu, he⟩

/-- Forward extraction. -/
theorem downwardClosed_of_flat
    {support : Model → Form → Finset W → Prop} {φ : Form}
    (h : flat support φ) : downwardClosed support φ :=
  ((flat_iff_downwardClosed_unionClosed_emptyTeam support φ).mp h).1

theorem unionClosed_of_flat
    {support : Model → Form → Finset W → Prop} {φ : Form}
    (h : flat support φ) : unionClosed support φ :=
  ((flat_iff_downwardClosed_unionClosed_emptyTeam support φ).mp h).2.1

theorem emptyTeam_of_flat
    {support : Model → Form → Finset W → Prop} {φ : Form}
    (h : flat support φ) : emptyTeam support φ :=
  ((flat_iff_downwardClosed_unionClosed_emptyTeam support φ).mp h).2.2

end Core.Logic.Team
