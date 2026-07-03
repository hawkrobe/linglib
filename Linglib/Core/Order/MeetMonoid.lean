import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.BoundedOrder.Lattice
import Mathlib.Algebra.Group.Defs

/-!
# The meet monoid of a semilattice

`MeetMonoid α` is a type synonym equipping a meet-semilattice with top
with its monoid structure: `* = ⊓`, `1 = ⊤` (the `Multiplicative` /
`OrderDual` pattern). The synonym is non-reducible, so the instance is
global and never leaks onto `α` itself — in particular it cannot collide
with the scoped `Pointwise` algebra on `Set`.

Deliberately not upstream material: mathlib serves this role unbundled —
`Std.Commutative` / `Std.Associative` / `Std.IdempotentOp` instances for
`⊓` in `Order/Lattice.lean` plus native aggregation (`Finset.inf`,
`sInf`, `List.foldr`). The wrapper exists here to give discourse-update
dynamics bundled `MonoidHom` / `MulActionHom` vocabulary, which the
unbundled route does not provide.
-/

/-- Type synonym: `α` with `⊓` as multiplication and `⊤` as unit. -/
def MeetMonoid (α : Type*) := α

namespace MeetMonoid

variable {α : Type*}

/-- Wrap an element of `α` as an element of its meet monoid. -/
def of (a : α) : MeetMonoid α := a

/-- Unwrap an element of the meet monoid. -/
def val (a : MeetMonoid α) : α := a

@[simp] theorem of_val (a : MeetMonoid α) : of (val a) = a := rfl

@[simp] theorem val_of (a : α) : val (of a) = a := rfl

theorem of_injective : Function.Injective (of : α → MeetMonoid α) :=
  fun _ _ h => h

instance [SemilatticeInf α] [OrderTop α] : CommMonoid (MeetMonoid α) where
  mul a b := of (val a ⊓ val b)
  one := of ⊤
  mul_assoc a b c :=
    show val a ⊓ val b ⊓ val c = val a ⊓ (val b ⊓ val c) from inf_assoc ..
  mul_comm a b := show val a ⊓ val b = val b ⊓ val a from inf_comm ..
  one_mul a := show (⊤ : α) ⊓ val a = val a from top_inf_eq _
  mul_one a := show val a ⊓ (⊤ : α) = val a from inf_top_eq _

section Lattice

variable [SemilatticeInf α] [OrderTop α]

@[simp] theorem val_mul (a b : MeetMonoid α) : val (a * b) = val a ⊓ val b :=
  rfl

@[simp] theorem val_one : val (1 : MeetMonoid α) = (⊤ : α) := rfl

theorem of_inf (a b : α) : of (a ⊓ b) = of a * of b := rfl

theorem of_top : of (⊤ : α) = 1 := rfl

/-- Meet is idempotent, so every element of the meet monoid is. -/
@[simp] theorem mul_idem (a : MeetMonoid α) : a * a = a :=
  show val a ⊓ val a = val a from inf_idem _

end Lattice

end MeetMonoid
