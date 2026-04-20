import Linglib.Core.Order.Normality
import Mathlib.Data.Set.Basic

/-!
# Plausibility Orderings and Preferential Consequence

@cite{kraus-magidor-1990} @cite{halpern-2003}

Plausibility orderings and preferential consequence relations are the
general mathematical structures underlying default reasoning. This file
extracts them from the AGM-specific machinery in `BeliefRevision.lean`,
placing them in `Core/Order/` alongside `NormalityOrder`.

## Key definitions

- `PlausibilityOrder W`: `NormalityOrder` + smoothness (every satisfiable
  proposition has minimal elements)
- `PreferentialConsequence W`: System P axioms for `φ |~ ψ`
- `rationalMonotonicity`: the stronger property satisfied by ranked models
- `PlausibilityOrder.toPreferential`: the sound construction

## Architecture

```
Core/Order/Normality.lean      — NormalityOrder (preorder on worlds)
    ↓ extends
Core/Order/Plausibility.lean   — PlausibilityOrder + System P
    ↑ uses                         ↑ uses
Core/Logic/RankingFunction.lean    Core/Logic/BeliefRevision.lean (AGM)
Core/Logic/SystemZ.lean
```
-/

namespace Core.Order

-- ══════════════════════════════════════════════════════════════════════
-- § 1. Preferential Consequence (System P)
-- ══════════════════════════════════════════════════════════════════════

/-- A preferential consequence relation: `φ |~ ψ` reads "normally, if φ then ψ".

    System P axiomatizes the minimal
    properties of default reasoning. @cite{halpern-2003} shows that
    System P is sound and complete for preferential models — structures
    where worlds are ordered by plausibility, and `φ |~ ψ` iff ψ holds
    at all most-plausible φ-worlds. -/
structure PreferentialConsequence (W : Type*) where
  /-- The default consequence relation: `default φ ψ` means φ |~ ψ -/
  default : Set W → Set W → Prop

  /-- Reflexivity: φ |~ φ -/
  refl : ∀ φ, default φ φ

  /-- Left Logical Equivalence: if φ ↔ ψ then (φ |~ χ ↔ ψ |~ χ) -/
  leftEquiv : ∀ φ ψ χ,
    (∀ w, φ w ↔ ψ w) → (default φ χ ↔ default ψ χ)

  /-- Right Weakening: if φ |~ ψ and ψ → χ, then φ |~ χ -/
  rightWeaken : ∀ φ ψ χ,
    default φ ψ → (∀ w, ψ w → χ w) → default φ χ

  /-- And: if φ |~ ψ and φ |~ χ, then φ |~ (ψ ∧ χ) -/
  and_ : ∀ φ ψ χ,
    default φ ψ → default φ χ → default φ (fun w => ψ w ∧ χ w)

  /-- Or: if φ |~ χ and ψ |~ χ, then (φ ∨ ψ) |~ χ -/
  or_ : ∀ φ ψ χ,
    default φ χ → default ψ χ →
    default (fun w => φ w ∨ ψ w) χ

  /-- Cautious Monotonicity: if φ |~ ψ and φ |~ χ, then (φ ∧ ψ) |~ χ -/
  cautiousMono : ∀ φ ψ χ,
    default φ ψ → default φ χ →
    default (fun w => φ w ∧ ψ w) χ

/-- Rational Monotonicity: if φ |~ χ and ¬(φ |~ ¬ψ), then (φ ∧ ψ) |~ χ.

    This is strictly stronger than System P. @cite{halpern-2003} shows
    it corresponds to ranked (well-ordered) plausibility models, not
    merely preferential ones. -/
def rationalMonotonicity {W : Type*} (pc : PreferentialConsequence W) : Prop :=
  ∀ φ ψ χ : Set W,
    pc.default φ χ → ¬pc.default φ (fun w => ¬ψ w) →
    pc.default (fun w => φ w ∧ ψ w) χ

-- ══════════════════════════════════════════════════════════════════════
-- § 2. Plausibility Orderings
-- ══════════════════════════════════════════════════════════════════════

/-- A plausibility ordering on worlds: w₁ ≤ w₂ means w₁ is at least
    as plausible as w₂. The minimal elements of a proposition A are
    the most plausible A-worlds.

    Extends `NormalityOrder` with the **smoothness condition** (also
    called "limit assumption"): every satisfiable proposition has
    minimal elements. This is automatic for finite W; for infinite W
    it rules out infinite descending chains. @cite{kraus-magidor-1990} call this
    "stopperedness". -/
structure PlausibilityOrder (W : Type*) extends NormalityOrder W where
  /-- Smoothness: every satisfiable φ has a minimal element -/
  smooth : ∀ (φ : Set W) (w : W), φ w →
    ∃ v, φ v ∧ le v w ∧ ∀ u, φ u → le u v → le v u

/-- The most plausible worlds satisfying φ: those with no strictly
    more plausible φ-world.

    This is the same as `NormalityOrder.optimal` applied to the set
    `{w | φ w}`, but stated with `Prop'` for the System P interface. -/
def PlausibilityOrder.minimal {W : Type*} (po : PlausibilityOrder W)
    (φ : Set W) : Set W :=
  fun w => φ w ∧ ∀ v, φ v → po.le v w → po.le w v

/-- A plausibility ordering induces a preferential consequence relation:
    φ |~ ψ iff all minimal φ-worlds satisfy ψ.

    @cite{halpern-2003}, Theorem 8.1.1: System P is sound and complete for
    this semantics. -/
def PlausibilityOrder.toPreferential {W : Type*}
    (po : PlausibilityOrder W) : PreferentialConsequence W where
  default := fun φ ψ => ∀ w, po.minimal φ w → ψ w
  refl := fun φ w ⟨hφ, _⟩ => hφ
  leftEquiv := fun φ ψ χ hEquiv => by
    constructor
    · intro h w ⟨hψ, hmin⟩
      exact h w ⟨(hEquiv w).mpr hψ, fun v hv hle => hmin v ((hEquiv v).mp hv) hle⟩
    · intro h w ⟨hφ, hmin⟩
      exact h w ⟨(hEquiv w).mp hφ, fun v hv hle => hmin v ((hEquiv v).mpr hv) hle⟩
  rightWeaken := fun φ ψ χ hdef hent w hmin => hent w (hdef w hmin)
  and_ := fun φ ψ χ hψ hχ w hmin => ⟨hψ w hmin, hχ w hmin⟩
  or_ := fun φ ψ χ hφχ hψχ w ⟨hφψ, hmin⟩ =>
    hφψ.elim
      (fun hφ => hφχ w ⟨hφ, fun v hv hle => hmin v (Or.inl hv) hle⟩)
      (fun hψ => hψχ w ⟨hψ, fun v hv hle => hmin v (Or.inr hv) hle⟩)
  cautiousMono := fun φ ψ χ hψ hχ w ⟨⟨hφ, hψw⟩, hmin⟩ => by
    obtain ⟨v, hφv, hvw, hmin_v⟩ := po.smooth φ w hφ
    have hψv : ψ v := hψ v ⟨hφv, hmin_v⟩
    have hwv := hmin v ⟨hφv, hψv⟩ hvw
    have hmin_w : ∀ u, φ u → po.le u w → po.le w u := by
      intro u hφu huw
      have huv := po.le_trans u w v huw hwv
      have hvu := hmin_v u hφu huv
      exact po.le_trans w v u hwv hvu
    exact hχ w ⟨hφ, hmin_w⟩

end Core.Order
