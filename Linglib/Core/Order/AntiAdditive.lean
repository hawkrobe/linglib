import Mathlib.Data.Fintype.Order
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.GaloisConnection.Basic
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
- `GaloisConnection.isAdditive` and friends — adjoints land in the
  classes; `exists_galoisConnection_iff_forall_sSup` — the poset adjoint
  functor theorem (`[UPSTREAM]` candidate), with the finite corollary
  `isAdditive_and_bot_iff_exists_galoisConnection`.
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

theorem isCompletelyAntiAdditive_compl :
    IsCompletelyAntiAdditive (compl : α → α) :=
  ⟨isAntiAdditive_compl, compl_top⟩

theorem isCompletelyAntiMultiplicative_compl :
    IsCompletelyAntiMultiplicative (compl : α → α) :=
  ⟨isAntiMultiplicative_compl, compl_bot⟩

end BooleanAlgebra

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

/-! ### Galois connections

Adjoints land in the function classes: a left adjoint is additive, a
right adjoint multiplicative, and the anti-classes are adjoints into the
order dual. A single adjunction yields `⊥`- (resp. `⊤`-) preservation,
never the opposite unit, so only *bi*-adjoints reach the `IsCompletely*`
classes. `exists_galoisConnection_iff_forall_sSup` is the poset adjoint
functor theorem, an `[UPSTREAM]` candidate: mathlib has
`GaloisConnection.l_sSup` but not the converse. -/

section GaloisBridges

variable {α β : Type*}

/-- A left adjoint is additive. -/
theorem GaloisConnection.isAdditive [SemilatticeSup α] [SemilatticeSup β]
    {l : α → β} {u : β → α} (gc : GaloisConnection l u) : IsAdditive l :=
  λ _ _ => gc.l_sup

/-- A right adjoint is multiplicative. -/
theorem GaloisConnection.isMultiplicative [SemilatticeInf α] [SemilatticeInf β]
    {l : β → α} {u : α → β} (gc : GaloisConnection l u) : IsMultiplicative u :=
  λ _ _ => gc.u_inf

/-- An antitone left adjoint — a left adjoint into the order dual — is
anti-additive. -/
theorem GaloisConnection.isAntiAdditive [SemilatticeSup α] [SemilatticeInf β]
    {f : α → β} {u : βᵒᵈ → α}
    (gc : GaloisConnection (OrderDual.toDual ∘ f) u) : IsAntiAdditive f :=
  isAntiAdditive_iff_isAdditive_toDual.mpr gc.isAdditive

/-- An antitone right adjoint — a right adjoint into the order dual — is
anti-multiplicative. -/
theorem GaloisConnection.isAntiMultiplicative [SemilatticeInf α] [SemilatticeSup β]
    {f : α → β} {l : βᵒᵈ → α}
    (gc : GaloisConnection l (OrderDual.toDual ∘ f)) : IsAntiMultiplicative f :=
  λ _ _ => gc.u_inf

/-- A map with adjoints on both sides is completely additive: additivity
from its left adjunction, `f ⊤ = ⊤` from its right one. -/
theorem isCompletelyAdditive_of_galoisConnection
    [SemilatticeSup α] [OrderTop α] [SemilatticeSup β] [OrderTop β]
    {f : α → β} {u : β → α} {l : β → α}
    (gc₁ : GaloisConnection f u) (gc₂ : GaloisConnection l f) :
    IsCompletelyAdditive f :=
  ⟨gc₁.isAdditive, gc₂.u_top⟩

/-- A map with adjoints on both sides is completely multiplicative:
multiplicativity from its right adjunction, `f ⊥ = ⊥` from its left
one. -/
theorem isCompletelyMultiplicative_of_galoisConnection
    [SemilatticeInf α] [OrderBot α] [SemilatticeInf β] [OrderBot β]
    {f : α → β} {u : β → α} {l : β → α}
    (gc₁ : GaloisConnection f u) (gc₂ : GaloisConnection l f) :
    IsCompletelyMultiplicative f :=
  ⟨gc₂.isMultiplicative, gc₁.l_bot⟩

/-- The morphism and anti-morphism unit conditions collide on a
nontrivial codomain. -/
theorem IsCompletelyAdditive.not_isCompletelyAntiAdditive
    [SemilatticeSup α] [OrderTop α] [Lattice β] [BoundedOrder β] [Nontrivial β]
    {f : α → β} (h : IsCompletelyAdditive f) (h' : IsCompletelyAntiAdditive f) :
    False :=
  top_ne_bot (h.2.symm.trans h'.2)

end GaloisBridges

section AdjointFunctorTheorem

variable {α β : Type*} [CompleteLattice α] [CompleteLattice β]

/-- Poset adjoint functor theorem, construction half: a `sSup`-preserving
map between complete lattices is a left adjoint, with right adjoint
`λ b => sSup {a | f a ≤ b}`. -/
theorem galoisConnection_of_forall_sSup {f : α → β}
    (hf : ∀ s : Set α, f (sSup s) = ⨆ a ∈ s, f a) :
    GaloisConnection f λ b => sSup {a | f a ≤ b} := by
  have hmono : Monotone f := λ a b hab => by
    have h := hf {a, b}
    rw [sSup_pair, sup_eq_right.mpr hab, iSup_pair] at h
    exact le_sup_left.trans h.ge
  intro a b
  refine ⟨λ h => le_sSup h, λ h => (hmono h).trans ?_⟩
  rw [hf]
  exact iSup₂_le λ x hx => hx

/-- Poset adjoint functor theorem: a map between complete lattices is a
left adjoint iff it preserves arbitrary suprema. -/
theorem exists_galoisConnection_iff_forall_sSup (f : α → β) :
    (∃ u, GaloisConnection f u) ↔ ∀ s : Set α, f (sSup s) = ⨆ a ∈ s, f a :=
  ⟨λ ⟨_, gc⟩ _ => gc.l_sSup, λ hf => ⟨_, galoisConnection_of_forall_sSup hf⟩⟩

end AdjointFunctorTheorem

/-- On a finite lattice, binary additivity plus `⊥`-preservation is
exactly left-adjointness. -/
theorem isAdditive_and_bot_iff_exists_galoisConnection
    {α β : Type*} [Lattice α] [BoundedOrder α] [Finite α]
    [SemilatticeSup β] [OrderBot β] (f : α → β) :
    IsAdditive f ∧ f ⊥ = ⊥ ↔ ∃ u, GaloisConnection f u := by
  constructor
  · rintro ⟨hadd, hbot⟩
    cases nonempty_fintype α
    let _ : CompleteLattice α := Fintype.toCompleteLattice α
    have key : ∀ s : Set α, ∀ b, (∀ x ∈ s, f x ≤ b) → f (sSup s) ≤ b := by
      intro s
      induction s, (Set.toFinite s) using Set.Finite.induction_on with
      | empty => intro b _; rw [sSup_empty, hbot]; exact bot_le
      | insert _ _ ih =>
          intro b hb
          rw [sSup_insert, hadd]
          exact sup_le (hb _ (Set.mem_insert ..))
            (ih b λ x hx => hb x (Set.mem_insert_of_mem _ hx))
    refine ⟨λ b => sSup {a | f a ≤ b}, λ a b => ⟨λ h => le_sSup h, λ h => ?_⟩⟩
    exact (hadd.monotone h).trans (key _ b λ x hx => hx)
  · rintro ⟨u, gc⟩
    exact ⟨gc.isAdditive, gc.l_bot⟩


