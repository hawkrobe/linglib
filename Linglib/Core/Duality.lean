import Mathlib.Order.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic

/-!
# Duality

Universal vs existential operators formalized as a Galois connection.

## Main definitions

- `DualityType`: existential vs universal classification
- `Truth3`: three-valued truth (Kleene strong)
- `aggregate`: aggregate list by duality type

## References

- Barwise & Cooper (1981). Generalized Quantifiers and Natural Language.
- Keenan & Stavi (1986). A Semantic Characterization of Natural Language Determiners.
-/

namespace Core.Duality

/-- Existential vs universal classification. -/
inductive DualityType where
  | existential
  | universal
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Existential is robust: one witness suffices. -/
def DualityType.isRobust : DualityType → Bool
  | .existential => true
  | .universal => false

/-- Universal is fragile: one counterexample breaks. -/
def DualityType.isFragile : DualityType → Bool
  | .existential => false
  | .universal => true

/-- Swap existential and universal. -/
def DualityType.dual : DualityType → DualityType
  | .existential => .universal
  | .universal => .existential

theorem dual_involutive (d : DualityType) : d.dual.dual = d := by
  cases d <;> rfl

/-- Three-valued truth. -/
inductive Truth3 where
  | true
  | false
  | indet
  deriving Repr, DecidableEq, BEq, Inhabited

namespace Truth3

/-- Kleene strong negation. -/
def neg : Truth3 → Truth3
  | .true => .false
  | .false => .true
  | .indet => .indet

/-- Existential aggregation. -/
def join : Truth3 → Truth3 → Truth3
  | .true, _ => .true
  | _, .true => .true
  | .false, .false => .false
  | _, _ => .indet

/-- Universal aggregation. -/
def meet : Truth3 → Truth3 → Truth3
  | .false, _ => .false
  | _, .false => .false
  | .true, .true => .true
  | _, _ => .indet

/-- Lattice ordering: false < indet < true. -/
def le : Truth3 → Truth3 → Bool
  | .false, _ => Bool.true
  | .indet, .indet => Bool.true
  | .indet, .true => Bool.true
  | .true, .true => Bool.true
  | _, _ => Bool.false

instance : LE Truth3 where
  le a b := le a b = Bool.true


instance : Preorder Truth3 where
  le a b := le a b = Bool.true
  le_refl a := by cases a <;> rfl
  le_trans a b c hab hbc := by cases a <;> cases b <;> cases c <;> trivial

instance : PartialOrder Truth3 where
  le_antisymm a b hab hba := by cases a <;> cases b <;> trivial

instance : SemilatticeSup Truth3 where
  sup := join
  le_sup_left a b := by cases a <;> cases b <;> rfl
  le_sup_right a b := by cases a <;> cases b <;> rfl
  sup_le a b c hac hbc := by cases a <;> cases b <;> cases c <;> trivial

instance : SemilatticeInf Truth3 where
  inf := meet
  inf_le_left a b := by cases a <;> cases b <;> rfl
  inf_le_right a b := by cases a <;> cases b <;> rfl
  le_inf a b c hab hac := by cases a <;> cases b <;> cases c <;> trivial

instance : Lattice Truth3 where
  __ := inferInstanceAs (SemilatticeSup Truth3)
  __ := inferInstanceAs (SemilatticeInf Truth3)

instance : Bot Truth3 := ⟨.false⟩
instance : Top Truth3 := ⟨.true⟩

instance : OrderBot Truth3 where
  bot_le a := by cases a <;> rfl

instance : OrderTop Truth3 where
  le_top a := by cases a <;> rfl

instance : BoundedOrder Truth3 where
  __ := inferInstanceAs (OrderBot Truth3)
  __ := inferInstanceAs (OrderTop Truth3)

end Truth3

/-- Aggregate a list according to duality type. -/
def aggregate (d : DualityType) (l : List Truth3) : Truth3 :=
  match d with
  | .existential => l.foldl (· ⊔ ·) ⊥  -- sup = ∃-like
  | .universal => l.foldl (· ⊓ ·) ⊤    -- inf = ∀-like

/-- Existential aggregation: true if ANY true. -/
def existsAny (l : List Truth3) : Truth3 := aggregate .existential l

/-- Universal aggregation: true only if ALL true. -/
def forallAll (l : List Truth3) : Truth3 := aggregate .universal l

@[simp] theorem Truth3.sup_true (a : Truth3) : a ⊔ .true = .true := by cases a <;> rfl
@[simp] theorem Truth3.true_sup (a : Truth3) : Truth3.true ⊔ a = .true := by cases a <;> rfl
@[simp] theorem Truth3.inf_false (a : Truth3) : a ⊓ .false = .false := by cases a <;> rfl
@[simp] theorem Truth3.false_inf (a : Truth3) : Truth3.false ⊓ a = .false := by cases a <;> rfl

theorem foldl_sup_of_true (l : List Truth3) : l.foldl (· ⊔ ·) Truth3.true = .true := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons, Truth3.true_sup, ih]

theorem foldl_inf_of_false (l : List Truth3) : l.foldl (· ⊓ ·) Truth3.false = .false := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons, Truth3.false_inf, ih]

theorem foldl_sup_mem_true (l : List Truth3) (acc : Truth3) (h : Truth3.true ∈ l) :
    l.foldl (· ⊔ ·) acc = .true := by
  induction l generalizing acc with
  | nil => simp at h
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    simp only [List.mem_cons] at h
    cases h with
    | inl heq =>
      subst heq
      simp only [Truth3.sup_true, foldl_sup_of_true]
    | inr hmem =>
      exact ih (acc ⊔ hd) hmem

theorem foldl_inf_mem_false (l : List Truth3) (acc : Truth3) (h : Truth3.false ∈ l) :
    l.foldl (· ⊓ ·) acc = .false := by
  induction l generalizing acc with
  | nil => simp at h
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    simp only [List.mem_cons] at h
    cases h with
    | inl heq =>
      subst heq
      simp only [Truth3.inf_false, foldl_inf_of_false]
    | inr hmem =>
      exact ih (acc ⊓ hd) hmem

theorem existential_robust (l : List Truth3) (h : l.any (· == .true)) :
    existsAny l = .true := by
  simp only [existsAny, aggregate, List.any_eq_true] at *
  obtain ⟨x, hx_mem, hx_eq⟩ := h
  cases x with
  | true => exact foldl_sup_mem_true l ⊥ hx_mem
  | false => exact absurd hx_eq (by decide)
  | indet => exact absurd hx_eq (by decide)

theorem universal_fragile (l : List Truth3) (h : l.any (· == .false)) :
    forallAll l = .false := by
  simp only [forallAll, aggregate, List.any_eq_true] at *
  obtain ⟨x, hx_mem, hx_eq⟩ := h
  cases x with
  | false => exact foldl_inf_mem_false l ⊤ hx_mem
  | true => exact absurd hx_eq (by decide)
  | indet => exact absurd hx_eq (by decide)

/-- Standard quantifiers. -/
inductive Quantifier where
  | every | some | no | notEvery | most | few
  deriving Repr, DecidableEq, BEq

/-- Quantifier duality classification. -/
def Quantifier.duality : Quantifier → DualityType
  | .every => .universal
  | .no => .universal
  | .some => .existential
  | .notEvery => .existential
  | .most => .universal
  | .few => .existential

/-- Universal-like quantifiers are "strong". -/
def Quantifier.isStrong (q : Quantifier) : Bool :=
  q.duality == .universal

theorem strength_is_duality (q : Quantifier) :
    q.isStrong = true ↔ q.duality = .universal := by
  cases q <;> decide

def const {α : Type*} (t : Truth3) : α → Truth3 := λ _ => t

def exists' {α : Type*} (P : α → Truth3) (l : List α) : Truth3 :=
  existsAny (l.map P)

def forall' {α : Type*} (P : α → Truth3) (l : List α) : Truth3 :=
  forallAll (l.map P)

end Core.Duality
