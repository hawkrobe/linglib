import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Data.Set.Basic

/-!
# Anti-additivity
[zwarts-1998] [icard-2012]

The Zwarts function classes the polarity literature quantifies over: `IsAntiAdditive`
(`f (p ⊔ q) = f p ⊓ f q`), `IsAntiMultiplicative` (meets to joins), and `IsAntiMorphic`
(both) — the semantic content of the DE strength hierarchy (`Polarity.DEStrength.HoldsFor`)
and of the anti- signature rows (`Signature.Property.HoldsFor` in `Soundness.lean`). Each
implies antitonicity, and complementation realizes the full anti-morphism. The dual UE-side
properties (preserving joins or meets) have no named classes — consumers state the equations
directly, with `monotone_of_map_sup` and `monotone_of_map_inf` supplying monotonicity.
-/

namespace NaturalLogic

/-! ### The anti- classes -/

section PropertyFamily

variable {α β : Type*}

/-- Anti-additive: `f (p ⊔ q) = f p ⊓ f q`, polymorphic in domain and
codomain. -/
def IsAntiAdditive [SemilatticeSup α] [SemilatticeInf β] (f : α → β) : Prop :=
  ∀ p q, f (p ⊔ q) = f p ⊓ f q

/-- Anti-multiplicative: `f (p ⊓ q) = f p ⊔ f q`. -/
def IsAntiMultiplicative [SemilatticeInf α] [SemilatticeSup β] (f : α → β) : Prop :=
  ∀ p q, f (p ⊓ q) = f p ⊔ f q

/-- Anti-morphic: anti-additive and anti-multiplicative. -/
def IsAntiMorphic [Lattice α] [Lattice β] (f : α → β) : Prop :=
  IsAntiAdditive f ∧ IsAntiMultiplicative f

/-- A join-preserving function is monotone. -/
theorem monotone_of_map_sup [SemilatticeSup α] [SemilatticeSup β]
    {f : α → β} (h : ∀ p q, f (p ⊔ q) = f p ⊔ f q) : Monotone f := by
  intro p q hpq
  calc f p ≤ f p ⊔ f q := le_sup_left
    _ = f (p ⊔ q) := (h p q).symm
    _ = f q := by rw [sup_eq_right.mpr hpq]

/-- A meet-preserving function is monotone. -/
theorem monotone_of_map_inf [SemilatticeInf α] [SemilatticeInf β]
    {f : α → β} (h : ∀ p q, f (p ⊓ q) = f p ⊓ f q) : Monotone f := by
  intro p q hpq
  calc f p = f (p ⊓ q) := by rw [inf_eq_left.mpr hpq]
    _ = f p ⊓ f q := h p q
    _ ≤ f q := inf_le_right

/-- Anti-additive implies antitone. -/
theorem IsAntiAdditive.antitone [SemilatticeSup α] [SemilatticeInf β]
    {f : α → β} (h : IsAntiAdditive f) : Antitone f := by
  intro p q hpq
  calc f q = f (p ⊔ q) := by rw [sup_eq_right.mpr hpq]
    _ = f p ⊓ f q := h p q
    _ ≤ f p := inf_le_left

/-- Anti-multiplicative implies antitone. -/
theorem IsAntiMultiplicative.antitone [SemilatticeInf α] [SemilatticeSup β]
    {f : α → β} (h : IsAntiMultiplicative f) : Antitone f := by
  intro p q hpq
  calc f q ≤ f p ⊔ f q := le_sup_right
    _ = f (p ⊓ q) := (h p q).symm
    _ = f p := by rw [inf_eq_left.mpr hpq]

/-- Anti-morphic implies anti-additive. -/
theorem IsAntiMorphic.antiAdditive [Lattice α] [Lattice β]
    {f : α → β} (h : IsAntiMorphic f) : IsAntiAdditive f := h.1

/-- Anti-morphic implies anti-multiplicative. -/
theorem IsAntiMorphic.antiMultiplicative [Lattice α] [Lattice β]
    {f : α → β} (h : IsAntiMorphic f) : IsAntiMultiplicative f := h.2

/-- Anti-morphic implies antitone. -/
theorem IsAntiMorphic.antitone [Lattice α] [Lattice β]
    {f : α → β} (h : IsAntiMorphic f) : Antitone f :=
  h.1.antitone

end PropertyFamily

/-! ### Complementation -/

section BooleanAlgebra

variable {α : Type*} [BooleanAlgebra α]

theorem isAntiAdditive_compl : IsAntiAdditive (compl : α → α) :=
  fun _ _ => compl_sup

theorem isAntiMultiplicative_compl : IsAntiMultiplicative (compl : α → α) :=
  fun _ _ => compl_inf

theorem isAntiMorphic_compl : IsAntiMorphic (compl : α → α) :=
  ⟨isAntiAdditive_compl, isAntiMultiplicative_compl⟩

theorem antitone_compl : Antitone (compl : α → α) :=
  isAntiAdditive_compl.antitone

end BooleanAlgebra

/-! ### Pointwise bridges

The anti-additivity equation at the `Set`- and `Prop`-valued instances, in the membership
forms consumers destructure. -/

section Bridges

variable {γ δ : Type*}

theorem isAntiAdditive_iff_mem {f : Set γ → Set δ} :
    IsAntiAdditive f ↔ ∀ p q x, x ∈ f (p ∪ q) ↔ x ∈ f p ∧ x ∈ f q := by
  simp only [IsAntiAdditive, Set.sup_eq_union, Set.inf_eq_inter, Set.ext_iff,
    Set.mem_inter_iff]

/-- The `Prop`-valued instance: anti-additivity is `f (p ∪ q) ↔ f p ∧ f q`. -/
theorem isAntiAdditive_iff_gq {f : Set γ → Prop} :
    IsAntiAdditive f ↔ ∀ p q, f (p ∪ q) ↔ f p ∧ f q := by
  simp only [IsAntiAdditive, Set.sup_eq_union, inf_Prop_eq, eq_iff_iff]

/-- Any function of the form `fun X y => ∀ x ∈ X, P x y` is anti-additive
in `X`. -/
theorem isAntiAdditive_forall_mem {α β : Type*} (P : α → β → Prop) :
    IsAntiAdditive (fun (X : Set α) (y : β) => ∀ x ∈ X, P x y) :=
  fun A B => funext fun y =>
    propext (by simp [Set.mem_union, or_imp, forall_and])

end Bridges

end NaturalLogic
