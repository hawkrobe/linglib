import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Word order

The order of a head relative to one of its dependents, and the linear arrangement of a finite
set of constituents, in particular of the subject, object and verb of a clause.

`HeadDirection` is the two-valued order of a head and a dependent, head-initial when the head
precedes; `HeadDirection.swap` is the opposite direction and `HeadDirection.ofLT` the direction
read off two positions. `WordOrder.Arrangement α n` is a linear arrangement of the elements of
`α` over `n` ranks, a bijection onto `Fin n`, so that precedence, the head direction of any
pair and the mirror image are read off the ranks. `Arrangement Constituent 3` arranges the
three clausal constituents, and its six values are the basic word orders of the typological
literature ([greenberg-1963], [dryer-2013-wals]), `Arrangement.sov` and its siblings.

## Main declarations

* `HeadDirection`, `HeadDirection.swap`, `HeadDirection.ofLT`: the two directions, the
  involution exchanging them, and the direction of a head and a dependent at given positions.
* `WordOrder.Arrangement`, `Arrangement.Precedes`, `Arrangement.headDirection`,
  `Arrangement.mirror`: an arrangement of a finite type over ranks, precedence of two elements,
  the head direction of a pair, and the reversed arrangement, which reverses every precedence
  and every head direction.
* `WordOrder.Constituent`, `Arrangement.sov` and its siblings: the subject, object and verb,
  and their six arrangements.

## Implementation notes

The WALS classification of a language's dominant orders, with its "no dominant order" value, is
data (`Data/WALS/Features/F81A` and its siblings). A fragment records the arrangements a
language admits as a `Finset (Arrangement Constituent 3)`; the pairwise orders the language
fixes are the ones every member agrees on, so no separate consistency invariant is needed. The
rank count is a parameter rather than `Fintype.card α`, so that numerals and `decide` reduce.

## References

* [dryer-1992]
* [dryer-2013-wals]
* [greenberg-1963]
-/

/-- The order of a head and one of its dependents, head-initial when the head precedes, as a
verb precedes its object in VO order and a preposition its noun phrase, head-final otherwise. -/
inductive HeadDirection where
  | headInitial
  | headFinal
  deriving DecidableEq, Repr, Fintype

namespace HeadDirection

/-- The opposite direction. -/
def swap : HeadDirection → HeadDirection
  | headInitial => headFinal
  | headFinal => headInitial

@[simp] theorem swap_headInitial : headInitial.swap = headFinal := rfl

@[simp] theorem swap_headFinal : headFinal.swap = headInitial := rfl

@[simp] theorem swap_swap : ∀ d : HeadDirection, d.swap.swap = d := by decide

theorem swap_involutive : Function.Involutive swap := swap_swap

theorem swap_injective : Function.Injective swap := swap_involutive.injective

theorem swap_ne_self : ∀ d : HeadDirection, d.swap ≠ d := by decide

theorem swap_eq_iff_eq_swap {d e : HeadDirection} : d.swap = e ↔ d = e.swap :=
  swap_involutive.eq_iff

/-- A direction is a given one or its opposite. -/
theorem eq_or_eq_swap : ∀ d e : HeadDirection, e = d ∨ e = d.swap := by decide

section ofLT

variable {α : Type*} [LT α] [DecidableLT α] {head dep : α}

/-- The direction of a head at position `head` with a dependent at position `dep`. -/
def ofLT (head dep : α) : HeadDirection := if head < dep then headInitial else headFinal

@[simp] theorem ofLT_eq_headInitial : ofLT head dep = headInitial ↔ head < dep := by
  unfold ofLT; split <;> simp [*]

@[simp] theorem ofLT_eq_headFinal : ofLT head dep = headFinal ↔ ¬ head < dep := by
  unfold ofLT; split <;> simp [*]

end ofLT

/-- Exchanging the positions of a head and a dependent reverses the direction. -/
theorem ofLT_swap {α : Type*} [LinearOrder α] {head dep : α} (h : head ≠ dep) :
    ofLT dep head = (ofLT head dep).swap := by
  rcases lt_or_gt_of_ne h with hlt | hlt <;> simp [ofLT, hlt, lt_asymm hlt]

end HeadDirection

namespace WordOrder

/-- A linear arrangement of the elements of `α` over `n` ranks, each element sent to its
rank. -/
abbrev Arrangement (α : Type*) (n : ℕ) := α ≃ Fin n

namespace Arrangement

variable {α : Type*} {n : ℕ} (a : Arrangement α n) (x y : α)

/-- `x` precedes `y`. -/
def Precedes : Prop := a x < a y

instance : Decidable (a.Precedes x y) := inferInstanceAs (Decidable (_ < _))

/-- The direction of the head `x` with respect to its dependent `y`. -/
def headDirection : HeadDirection := .ofLT (a x) (a y)

/-- The mirror image, every rank reversed. -/
def mirror : Arrangement α n := a.trans Fin.revPerm

variable {a x y}

theorem headDirection_eq_headInitial :
    a.headDirection x y = .headInitial ↔ a.Precedes x y :=
  HeadDirection.ofLT_eq_headInitial

theorem headDirection_eq_headFinal : a.headDirection x y = .headFinal ↔ ¬ a.Precedes x y :=
  HeadDirection.ofLT_eq_headFinal

@[simp] theorem mirror_mirror (a : Arrangement α n) : a.mirror.mirror = a := by
  ext c; simp [mirror]

theorem mirror_involutive : Function.Involutive (mirror (α := α) (n := n)) := mirror_mirror

/-- The mirror image reverses every precedence. -/
theorem precedes_mirror : a.mirror.Precedes x y ↔ a.Precedes y x := by
  simp [mirror, Precedes]

/-- The mirror image reverses the direction of every head with respect to a distinct
dependent. -/
theorem headDirection_mirror (h : x ≠ y) :
    a.mirror.headDirection x y = (a.headDirection x y).swap := by
  unfold headDirection
  rw [← HeadDirection.ofLT_swap (a.injective.ne h)]
  simp [mirror, HeadDirection.ofLT]

end Arrangement

/-- The three constituents of a transitive clause. -/
inductive Constituent where
  | subject
  | object
  | verb
  deriving DecidableEq, Repr, Fintype

namespace Arrangement

/-- Subject, object, verb. -/
def sov : Arrangement Constituent 3 :=
  ⟨fun | .subject => 0 | .object => 1 | .verb => 2,
    fun | 0 => .subject | 1 => .object | 2 => .verb, by decide, by decide⟩

/-- Subject, verb, object. -/
def svo : Arrangement Constituent 3 :=
  ⟨fun | .subject => 0 | .verb => 1 | .object => 2,
    fun | 0 => .subject | 1 => .verb | 2 => .object, by decide, by decide⟩

/-- Verb, subject, object. -/
def vso : Arrangement Constituent 3 :=
  ⟨fun | .verb => 0 | .subject => 1 | .object => 2,
    fun | 0 => .verb | 1 => .subject | 2 => .object, by decide, by decide⟩

/-- Verb, object, subject. -/
def vos : Arrangement Constituent 3 :=
  ⟨fun | .verb => 0 | .object => 1 | .subject => 2,
    fun | 0 => .verb | 1 => .object | 2 => .subject, by decide, by decide⟩

/-- Object, verb, subject. -/
def ovs : Arrangement Constituent 3 :=
  ⟨fun | .object => 0 | .verb => 1 | .subject => 2,
    fun | 0 => .object | 1 => .verb | 2 => .subject, by decide, by decide⟩

/-- Object, subject, verb. -/
def osv : Arrangement Constituent 3 :=
  ⟨fun | .object => 0 | .subject => 1 | .verb => 2,
    fun | 0 => .object | 1 => .subject | 2 => .verb, by decide, by decide⟩

end Arrangement

end WordOrder
