import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Order.Defs.PartialOrder

/-!
# Prototypes — Graded Category Membership

A prototype attaches a typicality grade (`ℚ`) to each member of a category.
Higher values are more prototypical. Used wherever graded membership is
needed (e.g. color-term typicality @cite{westerbeek-koolen-maes-2015}).

The `TypicalityOrder` wrapper carries the `Preorder` instance derived from
typicality: `(a : TypicalityOrder p) ≤ b ↔ p.typicality a ≤ p.typicality b`.
The wrapper pattern (cf. `Core.Inheritance.IsAOrder`) is needed because a
single `α` may carry multiple unrelated prototype gradings.
-/

set_option autoImplicit false

namespace Core

/-- A prototype: a category with graded typicality over instances.
Higher values = more prototypical. -/
structure Prototype (α : Type) where
  category : α
  typicality : α → ℚ

namespace Prototype

variable {α : Type}

/-- `a` is at least as typical as `b` in `proto`. -/
def AtLeastAsTypical (proto : Prototype α) (a b : α) : Prop :=
  proto.typicality b ≤ proto.typicality a

instance (proto : Prototype α) : DecidableRel proto.AtLeastAsTypical :=
  fun _ _ => inferInstanceAs (Decidable (_ ≤ _))

/-- `a` is strictly more typical than `b` in `proto`. -/
def MoreTypical (proto : Prototype α) (a b : α) : Prop :=
  proto.typicality b < proto.typicality a

instance (proto : Prototype α) : DecidableRel proto.MoreTypical :=
  fun _ _ => inferInstanceAs (Decidable (_ < _))

theorem atLeastAsTypical_refl (proto : Prototype α) (a : α) :
    proto.AtLeastAsTypical a a :=
  show proto.typicality a ≤ proto.typicality a from le_refl _

theorem atLeastAsTypical_trans (proto : Prototype α) {a b c : α}
    (hab : proto.AtLeastAsTypical a b) (hbc : proto.AtLeastAsTypical b c) :
    proto.AtLeastAsTypical a c :=
  show proto.typicality c ≤ proto.typicality a from le_trans hbc hab

end Prototype

/-- A node type viewed as preordered by typicality under a particular
prototype. Definitionally equal to `α`, but carries the `Preorder`
instance. Mirrors `Core.Inheritance.IsAOrder`. -/
def TypicalityOrder {α : Type} (_ : Prototype α) : Type := α

namespace TypicalityOrder

variable {α : Type}

/-- Tag a value as inhabiting the typicality preorder of `proto`. The
function-call wrapper avoids the elaboration pitfall where
`(a : TypicalityOrder proto)` ascription gets unfolded to `α` during
instance search. -/
def mk (proto : Prototype α) (a : α) : TypicalityOrder proto := a

/-- Forget the typicality view, returning the underlying value. -/
def val {proto : Prototype α} (a : TypicalityOrder proto) : α := a

/-- Preorder by typicality: `a ≤ b` iff `b` is at least as typical as `a`. -/
instance preorder (proto : Prototype α) : Preorder (TypicalityOrder proto) where
  le a b := proto.AtLeastAsTypical b a
  le_refl a := proto.atLeastAsTypical_refl a
  le_trans _ _ _ hab hbc := proto.atLeastAsTypical_trans hbc hab

@[simp] theorem le_def (proto : Prototype α) (a b : TypicalityOrder proto) :
    a ≤ b ↔ proto.AtLeastAsTypical b a := Iff.rfl

@[simp] theorem val_mk (proto : Prototype α) (a : α) : val (mk proto a) = a := rfl

end TypicalityOrder

end Core
