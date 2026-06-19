import Linglib.Core.Order.Normality
import Mathlib.Data.Set.Basic

/-!
# Plausibility orderings and preferential consequence

[kraus-magidor-1990] [halpern-2003]

A *plausibility ordering* is a `Preorder` on worlds together with a
**smoothness** (stopperedness) property: every satisfiable proposition has a
minimal element below any witness. The most-plausible φ-worlds are mathlib's
`Minimal` (= `Normality.optimal`). This replaces the former
`PlausibilityOrder extends NormalityOrder` hand-rolled structure.

## Main definitions

- `Smooth p` — [kraus-magidor-1990]'s stopperedness for a `Preorder`.
- `PlausibilityOrder W` — a `Preorder W` bundled with `Smooth`.
- `PreferentialConsequence W` — System P for `φ |~ ψ`.
- `PlausibilityOrder.toPreferential` — soundness for System P.
-/

namespace Core.Order

/-! ### Preferential consequence (System P) -/

/-- A preferential consequence relation: `φ |~ ψ` reads "normally, if φ then ψ".
    System P axiomatizes the minimal properties of default reasoning;
    [halpern-2003] shows soundness and completeness for preferential models. -/
structure PreferentialConsequence (W : Type*) where
  /-- The default consequence relation: `default φ ψ` means φ |~ ψ -/
  default : Set W → Set W → Prop
  /-- Reflexivity: φ |~ φ -/
  refl : ∀ φ, default φ φ
  /-- Left Logical Equivalence: if φ ↔ ψ then (φ |~ χ ↔ ψ |~ χ) -/
  leftEquiv : ∀ φ ψ χ, (∀ w, φ w ↔ ψ w) → (default φ χ ↔ default ψ χ)
  /-- Right Weakening: if φ |~ ψ and ψ → χ, then φ |~ χ -/
  rightWeaken : ∀ φ ψ χ, default φ ψ → (∀ w, ψ w → χ w) → default φ χ
  /-- And: if φ |~ ψ and φ |~ χ, then φ |~ (ψ ∧ χ) -/
  and_ : ∀ φ ψ χ, default φ ψ → default φ χ → default φ (fun w => ψ w ∧ χ w)
  /-- Or: if φ |~ χ and ψ |~ χ, then (φ ∨ ψ) |~ χ -/
  or_ : ∀ φ ψ χ, default φ χ → default ψ χ → default (fun w => φ w ∨ ψ w) χ
  /-- Cautious Monotonicity: if φ |~ ψ and φ |~ χ, then (φ ∧ ψ) |~ χ -/
  cautiousMono : ∀ φ ψ χ, default φ ψ → default φ χ → default (fun w => φ w ∧ ψ w) χ

/-- Rational Monotonicity: if φ |~ χ and ¬(φ |~ ¬ψ), then (φ ∧ ψ) |~ χ.
    Strictly stronger than System P; [halpern-2003] ties it to ranked models. -/
def rationalMonotonicity {W : Type*} (pc : PreferentialConsequence W) : Prop :=
  ∀ φ ψ χ : Set W,
    pc.default φ χ → ¬pc.default φ (fun w => ¬ψ w) →
    pc.default (fun w => φ w ∧ ψ w) χ

/-! ### Plausibility orderings -/

/-- **Smoothness** ([kraus-magidor-1990] stopperedness): every satisfiable φ
    has a minimal element below any witness. Automatic for finite `W`; for
    infinite `W` it is the well-foundedness condition ruling out infinite
    descending chains. -/
def Smooth {W : Type*} (p : Preorder W) : Prop :=
  ∀ (φ : Set W) (w : W), φ w →
    ∃ v, φ v ∧ p.le v w ∧ ∀ u, φ u → p.le u v → p.le v u

/-- A plausibility ordering: a `Preorder` with the smoothness property.
    `toPreorder.le w v` means `w` is at least as plausible as `v`. -/
structure PlausibilityOrder (W : Type*) where
  /-- The underlying plausibility preorder. -/
  toPreorder : Preorder W
  /-- Smoothness / stopperedness. -/
  smooth : Smooth toPreorder

/-- The most plausible φ-worlds: those with no strictly more plausible
    φ-world. The same as `Normality.optimal toPreorder φ`. -/
def PlausibilityOrder.minimal {W : Type*} (po : PlausibilityOrder W)
    (φ : Set W) : Set W :=
  fun w => φ w ∧ ∀ v, φ v → po.toPreorder.le v w → po.toPreorder.le w v

/-- A plausibility ordering induces a preferential consequence relation:
    φ |~ ψ iff all minimal φ-worlds satisfy ψ. [halpern-2003]: System P is
    sound and complete for this semantics. -/
def PlausibilityOrder.toPreferential {W : Type*}
    (po : PlausibilityOrder W) : PreferentialConsequence W where
  default := fun φ ψ => ∀ w, po.minimal φ w → ψ w
  refl := fun _ _ ⟨hφ, _⟩ => hφ
  leftEquiv := fun φ ψ χ hEquiv => by
    constructor
    · intro h w ⟨hψ, hmin⟩
      exact h w ⟨(hEquiv w).mpr hψ, fun v hv hle => hmin v ((hEquiv v).mp hv) hle⟩
    · intro h w ⟨hφ, hmin⟩
      exact h w ⟨(hEquiv w).mp hφ, fun v hv hle => hmin v ((hEquiv v).mpr hv) hle⟩
  rightWeaken := fun _ _ _ hdef hent w hmin => hent w (hdef w hmin)
  and_ := fun _ _ _ hψ hχ w hmin => ⟨hψ w hmin, hχ w hmin⟩
  or_ := fun _ _ _ hφχ hψχ w ⟨hφψ, hmin⟩ =>
    hφψ.elim
      (fun hφ => hφχ w ⟨hφ, fun v hv hle => hmin v (Or.inl hv) hle⟩)
      (fun hψ => hψχ w ⟨hψ, fun v hv hle => hmin v (Or.inr hv) hle⟩)
  cautiousMono := fun φ ψ χ hψ hχ w ⟨⟨hφ, _⟩, hmin⟩ => by
    obtain ⟨v, hφv, hvw, hmin_v⟩ := po.smooth φ w hφ
    have hψv : ψ v := hψ v ⟨hφv, hmin_v⟩
    have hwv := hmin v ⟨hφv, hψv⟩ hvw
    have hmin_w : ∀ u, φ u → po.toPreorder.le u w → po.toPreorder.le w u := by
      intro u hφu huw
      have huv := po.toPreorder.le_trans u w v huw hwv
      have hvu := hmin_v u hφu huv
      exact po.toPreorder.le_trans w v u hwv hvu
    exact hχ w ⟨hφ, hmin_w⟩

end Core.Order
