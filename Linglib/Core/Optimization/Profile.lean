import Mathlib.Order.PiLex
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Max

/-!
# Score profiles and their lexicographic order

A `Profile β n` is a length-`n` vector of `β`-valued evaluations
(`Fin n → β`), and `LexProfile β n` is `Lex (Fin n → β)` carrying
`Pi.Lex`'s lexicographic order. Choices of `β` cover the standard
numerical codomains: `Nat`, `ℚ`, `ℝ`, `Bool`.

## Why a separate file?

Mathlib's `Pi.Lex` deliberately strips algebraic instances
(`assert_not_exists Monoid`) — adding a `Monoid` to `Lex` would create
diamonds with `Pi.instMonoid`. This file lifts the algebraic structure
back through `Lex` *only* under the lexicographic order, where the
compatibility is sound, and in maximum generality so that downstream
modules can specialize to whatever value type they need.
-/

namespace Core.Optimization

-- ============================================================================
-- § 1: Profile and LexProfile
-- ============================================================================

/-- A length-`n` vector of `β`-valued entries. Carries no order
    — downstream aggregators decide. -/
abbrev Profile (β : Type*) (n : Nat) : Type _ := Fin n → β

/-- A lexicographically ordered profile: `Pi.Lex` of `Fin n → β`.

    With `[LinearOrder β]`, `LexProfile β n` is itself a `LinearOrder`
    (inherited from `Pi.Lex`). With `[AddCommMonoid β]` and the right
    monotonicity hypotheses on `β`, it carries `IsOrderedAddMonoid` and
    `IsOrderedCancelAddMonoid` (proved below). -/
abbrev LexProfile (β : Type*) (n : Nat) : Type _ := Lex (Fin n → β)

namespace LexProfile

variable {β : Type*} {n : Nat}

/-- Extensionality: two `LexProfile`s are equal iff pointwise equal.
    `Lex` carries no `@[ext]` instance, so this is the local helper. -/
private theorem ext {a b : LexProfile β n} (h : ∀ i, a i = b i) : a = b :=
  show toLex (ofLex a) = toLex (ofLex b) from congrArg toLex (funext h)

-- `Add` and `Zero` are inherited from `instAddLex` / `instZeroLex` (which
-- lift `Pi.instAdd` / `Pi.instZero` through the `Lex` synonym), so the
-- pointwise semantics hold definitionally:
example [Add β] (a b : LexProfile β n) (i : Fin n) : (a + b) i = a i + b i := rfl
example [Zero β] (i : Fin n) : (0 : LexProfile β n) i = 0 := rfl

/-- Componentwise additive monoid structure. The axioms hold pointwise
    so the proofs reduce to pointwise applications of the corresponding
    `β` axioms. -/
instance [AddCommMonoid β] : AddCommMonoid (LexProfile β n) where
  add_assoc a b c := ext fun _ => add_assoc ..
  zero_add a := ext fun _ => zero_add ..
  add_zero a := ext fun _ => add_zero ..
  add_comm a b := ext fun _ => add_comm ..
  nsmul := nsmulRec

/-- Riggle's distributivity for general `β`: adding the same vector to
    both sides preserves lexicographic order. The witness `i` (first
    differing position) survives because right-translation by `c i`
    preserves strict inequality (`AddRightStrictMono`).

    Note on naming: mathlib's `add_lt_add_left` proves `a + c < b + c`
    (the *left* operand changes — `c` is the constant added on the right)
    and is the additive analog of `mul_lt_mul_left`. -/
instance [AddCommMonoid β] [PartialOrder β] [AddRightStrictMono β] :
    IsOrderedAddMonoid (LexProfile β n) where
  add_le_add_left a b hab c := by
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_refl _
    · apply le_of_lt
      obtain ⟨i, hpre, hi⟩ := hlt
      exact ⟨i,
        fun j hj => show a j + c j = b j + c j by rw [hpre j hj],
        add_lt_add_left hi (c i)⟩

/-- Left cancellation: if `a + b ≤ a + c` then `b ≤ c`. Promotes the
    ordered monoid to an ordered cancel monoid, which downstream is what
    licenses the tropical semiring derivation. -/
instance [AddCommMonoid β] [PartialOrder β] [AddRightStrictMono β]
    [IsLeftCancelAdd β] [AddLeftReflectLT β] :
    IsOrderedCancelAddMonoid (LexProfile β n) where
  le_of_add_le_add_left a b c hab := by
    rcases eq_or_lt_of_le hab with heq | hlt
    · exact le_of_eq (ext fun i => add_left_cancel (congrFun heq i))
    · apply le_of_lt
      obtain ⟨i, hpre, hi⟩ := hlt
      exact ⟨i,
        fun j hj => add_left_cancel (hpre j hj),
        lt_of_add_lt_add_left hi⟩

end LexProfile

-- ============================================================================
-- § 2: Compatibility with ViolationProfile
-- ============================================================================

/-- The existing `ViolationProfile n := Lex (Fin n → Nat)` from
    `Core.Optimization.Evaluation` is definitionally `LexProfile Nat n`.
    This `rfl` is the load-bearing claim that no downstream code needs
    to change when the `Nat`-specific instances are replaced by the
    generic ones above. -/
example (n : Nat) : Lex (Fin n → Nat) = LexProfile Nat n := rfl

/-- The four key instances are inferable for `β = Nat`. The `LinearOrder`
    is `noncomputable` (inherited from `Pi.Lex`); the others compute. -/
noncomputable example (n : Nat) : LinearOrder (LexProfile Nat n) := inferInstance
example (n : Nat) : AddCommMonoid (LexProfile Nat n) := inferInstance
example (n : Nat) : IsOrderedAddMonoid (LexProfile Nat n) := inferInstance
example (n : Nat) : IsOrderedCancelAddMonoid (LexProfile Nat n) := inferInstance

end Core.Optimization
