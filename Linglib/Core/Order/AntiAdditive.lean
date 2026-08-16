import Mathlib.Order.Monotone.Defs
import Mathlib.Order.Hom.BoundedLattice
import Mathlib.Data.Set.Basic

/-!
# Additive, multiplicative, and anti- function classes

Unbundled equational classes for maps between (semi)lattices: `IsAdditive`
(`f (p ⊔ q) = f p ⊔ f q`), `IsMultiplicative` (meets to meets),
`IsAntiAdditive` (joins to meets), `IsAntiMultiplicative` (meets to
joins), and `IsAntiMorphic` (both anti-properties). Each class implies
monotonicity or antitonicity; the `IsCompletely*` variants add the unit
conditions (`f ⊤ = ⊤`, `f ⊤ = ⊥`, …). The anti-classes are the plain
classes read into the order dual, so an additive function bundles as a
`SupHom` and anti-additivity is additivity composed with `toDual`.

## Main declarations

- `IsAdditive`, `IsMultiplicative`, `IsAntiAdditive`,
  `IsAntiMultiplicative`, `IsAntiMorphic` — the classes, with
  `Monotone`/`Antitone` consequence lemmas.
- `IsCompletely*` — the unit-condition refinements.
- `IsAdditive.toSupHom`, `isAntiAdditive_iff_isAdditive_toDual` — the
  bundled-hom and duality bridges.
- `isAntiAdditive_iff_mem`, `isAntiAdditive_iff_gq` — pointwise forms at
  the `Set`- and `Prop`-valued instances.
-/


/-! ### The property family -/

section PropertyFamily

variable {α β : Type*}

/-- Additive: `f (p ⊔ q) = f p ⊔ f q`. -/
def IsAdditive [SemilatticeSup α] [SemilatticeSup β] (f : α → β) : Prop :=
  ∀ p q, f (p ⊔ q) = f p ⊔ f q

/-- Multiplicative: `f (p ⊓ q) = f p ⊓ f q`. -/
def IsMultiplicative [SemilatticeInf α] [SemilatticeInf β] (f : α → β) : Prop :=
  ∀ p q, f (p ⊓ q) = f p ⊓ f q

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

/-! ### Completely-variants -/

/-- Completely additive: additive and `f ⊤ = ⊤`. -/
def IsCompletelyAdditive [SemilatticeSup α] [OrderTop α]
    [SemilatticeSup β] [OrderTop β] (f : α → β) : Prop :=
  IsAdditive f ∧ f ⊤ = ⊤

/-- Completely multiplicative: multiplicative and `f ⊥ = ⊥`. -/
def IsCompletelyMultiplicative [SemilatticeInf α] [OrderBot α]
    [SemilatticeInf β] [OrderBot β] (f : α → β) : Prop :=
  IsMultiplicative f ∧ f ⊥ = ⊥

/-- Completely anti-additive: anti-additive and `f ⊤ = ⊥`. -/
def IsCompletelyAntiAdditive [SemilatticeSup α] [OrderTop α]
    [SemilatticeInf β] [OrderBot β] (f : α → β) : Prop :=
  IsAntiAdditive f ∧ f ⊤ = ⊥

/-- Completely anti-multiplicative: anti-multiplicative and `f ⊥ = ⊤`. -/
def IsCompletelyAntiMultiplicative [SemilatticeInf α] [OrderBot α]
    [SemilatticeSup β] [OrderTop β] (f : α → β) : Prop :=
  IsAntiMultiplicative f ∧ f ⊥ = ⊤

/-! ### Monotonicity consequences -/

/-- Additive implies monotone. -/
theorem IsAdditive.monotone [SemilatticeSup α] [SemilatticeSup β]
    {f : α → β} (h : IsAdditive f) : Monotone f := by
  intro p q hpq
  calc f p ≤ f p ⊔ f q := le_sup_left
    _ = f (p ⊔ q) := (h p q).symm
    _ = f q := by rw [sup_eq_right.mpr hpq]

/-- Multiplicative implies monotone. -/
theorem IsMultiplicative.monotone [SemilatticeInf α] [SemilatticeInf β]
    {f : α → β} (h : IsMultiplicative f) : Monotone f := by
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

/-! ### mathlib hom-hierarchy bridges

The function classes are the unbundled predicates for mathlib's bundled
lattice homs: an additive function *is* a `SupHom`, a multiplicative one an
`InfHom`. The anti-classes are the same notions read into the order dual —
anti-additivity is additivity composed with `toDual` (De Morgan duality),
so the `.antitone` consequences are the duals of the `.monotone` ones. -/

section HomBridges

variable {α β : Type*}

/-- An additive function bundles as a `SupHom`. -/
def IsAdditive.toSupHom [SemilatticeSup α] [SemilatticeSup β] {f : α → β}
    (h : IsAdditive f) : SupHom α β where
  toFun := f
  map_sup' := h

/-- A multiplicative function bundles as an `InfHom`. -/
def IsMultiplicative.toInfHom [SemilatticeInf α] [SemilatticeInf β] {f : α → β}
    (h : IsMultiplicative f) : InfHom α β where
  toFun := f
  map_inf' := h

/-- **De Morgan duality**: anti-additivity is additivity into the order
dual — `f` sends joins to meets iff `toDual ∘ f` preserves joins. -/
theorem isAntiAdditive_iff_isAdditive_toDual [SemilatticeSup α]
    [SemilatticeInf β] {f : α → β} :
    IsAntiAdditive f ↔ IsAdditive (β := βᵒᵈ) (OrderDual.toDual ∘ f) :=
  Iff.rfl

end HomBridges

/-! ### Pointwise bridges

The equational properties at the `Set` and GQ instances, in the membership
forms consumers destructure. -/

section Bridges

variable {γ δ : Type*}

theorem isAntiAdditive_iff_mem {f : Set γ → Set δ} :
    IsAntiAdditive f ↔ ∀ p q x, x ∈ f (p ∪ q) ↔ x ∈ f p ∧ x ∈ f q := by
  constructor
  · intro h p q x
    have hpq : f (p ∪ q) = f p ∩ f q := h p q
    rw [hpq]
    exact Set.mem_inter_iff x (f p) (f q)
  · intro h p q
    show f (p ∪ q) = f p ∩ f q
    ext x
    exact (h p q x).trans (Set.mem_inter_iff x (f p) (f q)).symm

theorem isAntiMultiplicative_iff_mem {f : Set γ → Set δ} :
    IsAntiMultiplicative f ↔ ∀ p q x, x ∈ f (p ∩ q) ↔ x ∈ f p ∨ x ∈ f q := by
  constructor
  · intro h p q x
    have hpq : f (p ∩ q) = f p ∪ f q := h p q
    rw [hpq]
    exact Set.mem_union x (f p) (f q)
  · intro h p q
    show f (p ∩ q) = f p ∪ f q
    ext x
    exact (h p q x).trans (Set.mem_union x (f p) (f q)).symm

/-- The `Prop`-valued instance: anti-additivity is
`f (p ∪ q) ↔ f p ∧ f q`. -/
theorem isAntiAdditive_iff_gq {f : Set γ → Prop} :
    IsAntiAdditive f ↔ ∀ p q, f (p ∪ q) ↔ f p ∧ f q := by
  constructor
  · intro h p q
    have hpq : f (p ∪ q) = (f p ∧ f q) := h p q
    exact iff_of_eq hpq
  · intro h p q
    show f (p ∪ q) = (f p ∧ f q)
    exact propext (h p q)

/-- Any function of the form `fun X y => ∀ x ∈ X, P x y` is anti-additive
in `X`. -/
theorem isAntiAdditive_forall_mem {α β : Type*} (P : α → β → Prop) :
    IsAntiAdditive (fun (X : Set α) (y : β) => ∀ x ∈ X, P x y) := by
  refine isAntiAdditive_iff_mem.mpr (fun A B y => ?_)
  refine ⟨fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩, ?_⟩
  rintro ⟨hA, hB⟩ x (hx | hx)
  · exact hA x hx
  · exact hB x hx

end Bridges

