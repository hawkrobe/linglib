import Mathlib.Order.Monotone.Defs
import Mathlib.Order.Hom.BoundedLattice
import Mathlib.Order.Heyting.Hom
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Linglib.Semantics.Entailment.NaturalLogic
import Linglib.Semantics.Entailment.Basic
import Linglib.Semantics.Entailment.Polarity

/-!
# The DE < anti-additive < anti-morphic hierarchy

[icard-2012]'s function classes (his Definition 1.7, after [hoeksema-1983]
and Zwarts; cf. [chierchia-2013] §1.4.3, [ladusaw-1980]): additive,
multiplicative, anti-additive, and anti-multiplicative functions, stated in
equational form over semilattices and instantiated at context functions
(`Set W → Set W'`) and generalized quantifiers (`Set E → Prop`). Following
Icard, the plain properties are the binary equations; the `IsCompletely*`
refinements add his unit conditions (adopted for non-trivial linguistic
domains, his §1.1).

## Main declarations

- `IsAdditive`, `IsMultiplicative`, `IsAntiAdditive`, `IsAntiMultiplicative`:
  the four classes, with `Monotone`/`Antitone` consequence lemmas;
- `IsAntiMorphic`: anti-additive and anti-multiplicative (Zwarts's class for
  superstrong NPIs);
- `IsCompletely*`: Icard's "completely P" refinements (unit conditions);
- `isAntiAdditive_iff_mem`, `isAntiAdditive_iff_gq`: pointwise bridges for
  the `Set`- and GQ-typed instances;
- `licensesWeakNPI`, `licensesStrongNPI`, `licensesSuperstrongNPI`: the
  Zwarts licensing thresholds ([icard-2012] §4);
- toy-`World` witnesses: `pnot` (anti-morphic), `no_student` (anti-additive),
  `atMost1_student` (DE but not anti-additive — the strictness witness).
-/

namespace Entailment

open NaturalLogic (DEStrength UEStrength strengthSufficient)
open Entailment
open List (Sublist)

/-! ### The property family ([icard-2012] Definition 1.7) -/

section PropertyFamily

variable {α β : Type*}

/-- Additive: `f (p ⊔ q) = f p ⊔ f q`. -/
def IsAdditive [SemilatticeSup α] [SemilatticeSup β] (f : α → β) : Prop :=
  ∀ p q, f (p ⊔ q) = f p ⊔ f q

/-- Multiplicative: `f (p ⊓ q) = f p ⊓ f q`. -/
def IsMultiplicative [SemilatticeInf α] [SemilatticeInf β] (f : α → β) : Prop :=
  ∀ p q, f (p ⊓ q) = f p ⊓ f q

/-- Anti-additive: `f (p ⊔ q) = f p ⊓ f q`. Polymorphic in domain and
codomain — needed e.g. for [hoeksema-1983]'s S-comparative, anti-additive as
a function `Set Degree → Set Individual`. -/
def IsAntiAdditive [SemilatticeSup α] [SemilatticeInf β] (f : α → β) : Prop :=
  ∀ p q, f (p ⊔ q) = f p ⊓ f q

/-- Anti-multiplicative: `f (p ⊓ q) = f p ⊔ f q`. -/
def IsAntiMultiplicative [SemilatticeInf α] [SemilatticeSup β] (f : α → β) : Prop :=
  ∀ p q, f (p ⊓ q) = f p ⊔ f q

/-- Anti-morphic: anti-additive and anti-multiplicative — Zwarts's class of
sentential negation, the superstrong-NPI licensors. -/
def IsAntiMorphic [Lattice α] [Lattice β] (f : α → β) : Prop :=
  IsAntiAdditive f ∧ IsAntiMultiplicative f

/-! ### Completely-variants ([icard-2012] Definition 1.7)

Icard: "by P we mean completely P" for linguistic application — the unit
conditions amount to assuming non-trivial domains. -/

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

/-! ### Monotonicity consequences

Each class refines monotonicity or antitonicity ([icard-2012] Def. 1.7's
closing remark). -/

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

/-- Anti-additive implies antitone ([hoeksema-1983] Fact 4). -/
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

/-- The GQ-typed instance (`f : Set γ → Prop`, `Prop` as a complete
lattice): anti-additivity is the familiar `f (p ∪ q) ↔ f p ∧ f q`. -/
theorem isAntiAdditive_iff_gq {f : Set γ → Prop} :
    IsAntiAdditive f ↔ ∀ p q, f (p ∪ q) ↔ f p ∧ f q := by
  constructor
  · intro h p q
    have hpq : f (p ∪ q) = (f p ∧ f q) := h p q
    exact iff_of_eq hpq
  · intro h p q
    show f (p ∪ q) = (f p ∧ f q)
    exact propext (h p q)

end Bridges

/-! ### Toy-`World` witnesses and NPI licensing thresholds -/

section ToyWitnesses

/-- Any function of the form `fun X y => ∀ x ∈ X, P x y` is anti-additive in
`X`. `npComparative` and `Comparison.gt.overSet` ([hoeksema-1983]) instantiate this
with `P x y := μ x < μ y` and `P d y := d < μ y` respectively. -/
theorem isAntiAdditive_forall_mem {α β : Type*} (P : α → β → Prop) :
    IsAntiAdditive (fun (X : Set α) (y : β) => ∀ x ∈ X, P x y) := by
  refine isAntiAdditive_iff_mem.mpr (fun A B y => ?_)
  refine ⟨fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩, ?_⟩
  rintro ⟨hA, hB⟩ x (hx | hx)
  · exact hA x hx
  · exact hB x hx

/-- Negation is anti-additive. -/
theorem pnot_isAntiAdditive : IsAntiAdditive pnot := fun p q => by
  show (p ∪ q)ᶜ = pᶜ ∩ qᶜ
  exact Set.compl_union p q

/-- Negation is anti-multiplicative. -/
theorem pnot_isAntiMultiplicative : IsAntiMultiplicative pnot := fun p q => by
  show (p ∩ q)ᶜ = pᶜ ∪ qᶜ
  exact Set.compl_inter p q

/-- Negation is anti-morphic. -/
theorem pnot_isAntiMorphic : IsAntiMorphic pnot :=
  ⟨pnot_isAntiAdditive, pnot_isAntiMultiplicative⟩

/-- "No A is B" = ∀x. A(x) → ¬B(x). -/
def no' (restr : Set World) (scope : Set World) : Set World :=
  λ _ => ∀ x ∈ allWorlds, ¬ (restr x ∧ scope x)

/-- "No student ___" with fixed restrictor. -/
def no_student : Set World → Set World := no' p01

/-- "No" is anti-additive in scope. -/
theorem no_isAntiAdditive_scope : IsAntiAdditive no_student := by
  refine isAntiAdditive_iff_mem.mpr (fun p q _w => ?_)
  show (∀ x ∈ allWorlds, ¬ (p01 x ∧ (p ∪ q) x)) ↔
       (∀ x ∈ allWorlds, ¬ (p01 x ∧ p x)) ∧
       (∀ x ∈ allWorlds, ¬ (p01 x ∧ q x))
  constructor
  · intro h
    refine ⟨?_, ?_⟩ <;> intro x hx ⟨hr, hpx⟩
    · exact h x hx ⟨hr, Or.inl hpx⟩
    · exact h x hx ⟨hr, Or.inr hpx⟩
  · rintro ⟨h1, h2⟩ x hx ⟨hr, hor⟩
    cases hor with
    | inl hp => exact h1 x hx ⟨hr, hp⟩
    | inr hq => exact h2 x hx ⟨hr, hq⟩

/-- "No" is DE in scope. -/
theorem no_isDE_scope : IsDE no_student :=
  no_isAntiAdditive_scope.antitone

/-- "At most n A's are B" - true if at most n worlds satisfy both.
    Uses an existential over a sublist witness so the def is decidable
    only when the predicates are decidable, but stays in `Prop`. -/
def atMost (n : Nat) (restr scope : Set World) : Prop :=
  ∀ ws : List World, ws.Nodup →
    (∀ w ∈ ws, restr w ∧ scope w) →
    ws.length ≤ n

/-- Monotonicity: if `p ⊆ q` (entailment) and `q` has at most `n` witnesses,
    so does `p`. -/
theorem atMost_mono (n : Nat) (restr p q : Set World)
    (hpq : ∀ w, p w → q w) (h : atMost n restr q) :
    atMost n restr p := by
  intro ws hnd hall
  apply h ws hnd
  intro w hw
  exact ⟨(hall w hw).1, hpq w (hall w hw).2⟩

/-- "At most 2 students ___" with fixed restrictor. -/
def atMost2_student : Set World → Set World :=
  λ scope => λ _ => atMost 2 p01 scope

/-- "At most n" is DE in scope. -/
theorem atMost_isDE_scope : IsDE atMost2_student := by
  intro p q hpq _w h
  exact atMost_mono 2 p01 p q (fun _ hp => hpq hp) h

/-- "At most 1 student ___" with fixed restrictor. -/
def atMost1_student : Set World → Set World :=
  λ scope => λ _ => atMost 1 p01 scope

/-- "At most 1" is still DE. -/
theorem atMost1_isDE_scope : IsDE atMost1_student := by
  intro p q hpq _w h
  exact atMost_mono 1 p01 p q (fun _ hp => hpq hp) h

/-- "At most n" is not anti-additive (counterexample): the strictness
witness for DE ⊊ anti-additive. -/
theorem atMost_not_antiAdditive :
    ¬IsAntiAdditive atMost1_student := by
  intro hAA
  have h := isAntiAdditive_iff_mem.mp hAA
  let qProp : Set World := λ w => w = .w1
  have key : atMost1_student (por p0 qProp) .w0 ↔
             atMost1_student p0 .w0 ∧ atMost1_student qProp .w0 :=
    h p0 qProp World.w0
  -- p0 has just w0 as a witness; ≤ 1 ✓
  have hp : atMost1_student p0 .w0 := by
    intro ws hnd hall
    -- Every element of ws satisfies p01 ∧ p0, hence equals w0
    have hall_w0 : ∀ w ∈ ws, w = .w0 := by
      intro w hw
      have := (hall w hw).2
      exact this
    -- A nodup list whose every element is w0 has length ≤ 1
    rcases ws with _ | ⟨a, t⟩
    · simp
    · rcases t with _ | ⟨b, t'⟩
      · simp
      · exfalso
        have ha : a = .w0 := hall_w0 a (List.mem_cons_self ..)
        have hb : b = .w0 := hall_w0 b (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        have : a ≠ b := List.ne_of_not_mem_cons (List.Nodup.notMem hnd)
        exact this (ha.trans hb.symm)
  -- qProp has just w1 as a witness; ≤ 1 ✓
  have hq : atMost1_student qProp .w0 := by
    intro ws hnd hall
    have hall_w1 : ∀ w ∈ ws, w = .w1 := by
      intro w hw
      have := (hall w hw).2
      simpa [qProp] using this
    rcases ws with _ | ⟨a, t⟩
    · simp
    · rcases t with _ | ⟨b, t'⟩
      · simp
      · exfalso
        have ha : a = .w1 := hall_w1 a (List.mem_cons_self ..)
        have hb : b = .w1 := hall_w1 b (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        have : a ≠ b := List.ne_of_not_mem_cons (List.Nodup.notMem hnd)
        exact this (ha.trans hb.symm)
  -- por p0 qProp has both w0 and w1 as witnesses; not ≤ 1
  have hcontr : ¬ atMost1_student (por p0 qProp) .w0 := by
    intro hle
    have : ([World.w0, World.w1]).length ≤ 1 := by
      apply hle [.w0, .w1]
      · decide
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw'
        · exact ⟨Or.inl rfl, by left; rfl⟩
        · rcases List.mem_singleton.mp hw' with rfl
          exact ⟨Or.inr rfl, by right; rfl⟩
    simp at this
  exact hcontr (key.mpr ⟨hp, hq⟩)

/-- Weak NPI licensing: requires DE. -/
def licensesWeakNPI (f : Set World → Set World) : Prop := IsDownwardEntailing f

/-- Strong NPI licensing: requires anti-additivity. -/
def licensesStrongNPI (f : Set World → Set World) : Prop := IsAntiAdditive f

/-- Superstrong NPI licensing ([icard-2012] §4, after Zwarts): requires
anti-morphicity — *a tad bit* under *not* but not under *no*. -/
def licensesSuperstrongNPI (f : Set World → Set World) : Prop := IsAntiMorphic f

example : licensesWeakNPI pnot := pnot_isDownwardEntailing
example : licensesStrongNPI pnot := pnot_isAntiAdditive
example : licensesSuperstrongNPI pnot := pnot_isAntiMorphic

example : licensesWeakNPI no_student := no_isDE_scope
example : licensesStrongNPI no_student := no_isAntiAdditive_scope

example : licensesWeakNPI atMost2_student := atMost_isDE_scope

/-!
### `DEStrength` ↔ proof hierarchy ([icard-2012] §4)

| `DEStrength` | Proof predicate | Example licensor |
|--------------|-----------------|------------------|
| `.weak` | `IsDE` | few, at most n |
| `.antiAdditive` | `IsAntiAdditive` | no, nobody, without |
| `.antiMorphic` | `IsAntiMorphic` | not, never |
-/

end ToyWitnesses

end Entailment
