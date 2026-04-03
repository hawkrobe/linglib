import Linglib.Core.Logic.Truth3

/-!
# Duality
@cite{barwise-cooper-1981}

Universal vs existential operators formalized as a Galois connection.

## Main definitions

- `DualityType`: existential vs universal classification
- `aggregate`: aggregate list by duality type

For GQ-level duality operations (outer negation, inner negation, dual) see
`Core.Quantification.outerNeg` / `innerNeg` / `dualQ`.

-/

namespace Core.Duality

/-- Existential vs universal classification. -/
inductive DualityType where
  | existential
  | universal
  deriving Repr, DecidableEq, Inhabited

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

/-- Aggregate a list according to duality type. -/
def aggregate (d : DualityType) (l : List Truth3) : Truth3 :=
  match d with
  | .existential => l.foldl (· ⊔ ·) ⊥  -- sup = ∃-like
  | .universal => l.foldl (· ⊓ ·) ⊤    -- inf = ∀-like

/-- Existential aggregation: true if ANY true. -/
def existsAny (l : List Truth3) : Truth3 := aggregate .existential l

/-- Universal aggregation: true only if ALL true. -/
def forallAll (l : List Truth3) : Truth3 := aggregate .universal l

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

def const {α : Type*} (t : Truth3) : α → Truth3 := λ _ => t

def exists' {α : Type*} (P : α → Truth3) (l : List α) : Truth3 :=
  existsAny (l.map P)

def forall' {α : Type*} (P : α → Truth3) (l : List α) : Truth3 :=
  forallAll (l.map P)

end Core.Duality
