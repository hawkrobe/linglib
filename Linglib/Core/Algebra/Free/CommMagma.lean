import Mathlib.Algebra.Free
import Mathlib.Data.Quot

set_option autoImplicit false

/-!
# Free commutative magma

The **free commutative magma** on a type `α`: planar binary trees with
leaves in `α` (i.e., `FreeMagma α`) modulo the smallest congruence
containing the swap relation `a * b ~ b * a`.

This is the non-associative, commutative analogue of `FreeMonoid` /
`FreeCommMonoid`. The corresponding typeclass `CommMagma`
(in `Mathlib.Algebra.Group.Defs`) is satisfied by `FreeCommMagma α`,
giving us the universal property: any function `α → β` to a
`CommMagma`-equipped type extends uniquely to a magma homomorphism
`FreeCommMagma α →ₙ* β`.

## Mathlib precedents

- `Multiset α := Quotient (List.isSetoid α)`
  (`Mathlib/Data/Multiset/Defs.lean`)
- `Sym2 α := Quot (Sym2.Rel α)` (`Mathlib/Data/Sym/Sym2.lean:100`)
- `FreeAbelianGroup α := Additive (Abelianization (FreeGroup α))`
  (`Mathlib/GroupTheory/FreeAbelianGroup.lean`) — closest analogue:
  take a free non-commutative thing, commutativize via quotient.

The recursor / lift API mirrors `Mathlib/Data/Sym/Sym2.lean` lines
123–235 verbatim.

## Why a quotient and not a `Sym2`-style inductive

A direct inductive `inductive FreeCommMagma | of | mul : Sym2 _ → _`
is rejected by Lean's positivity check (`Sym2` is a `Quot`, and Lean
does not allow recursive occurrences under an arbitrary `Quot`). The
quotient construction here is the only viable shape.

## Linglib usage

Linglib's `SyntacticObject` is `FreeCommMagma (LIToken ⊕ Nat)`, with
`Sum.inl a` representing real lexical leaves and `Sum.inr n`
representing trace markers (synthesized by Internal Merge). The
`SyntacticObject.leaf` and `SyntacticObject.trace` shims preserve
the constructor-name distinction at use sites.

## Out of scope (deferred)

- `DecidableEq` and `Repr` via canonicalization (next file in this
  Phase 0 sequence; requires `[LinearOrder α]`).
- `Functor` / `Monad` instances.
- `length` (number of leaves).
-/

universe u v

namespace FreeMagma

variable {α : Type u}

/-- The smallest commutativity congruence on `FreeMagma α`: swap, plus
    push through both arguments of `*`. The transitive symmetric
    closure (computed by `Quot`) is the actual equivalence relation
    we quotient by.

    Three constructors: `swap` is the substantive content; `mul_left`
    and `mul_right` push the relation through nested multiplications
    so that, e.g., `(a * b) * c ~ (b * a) * c` is derivable. Without
    these congruence rules, `Quot CommRel` would only quotient
    top-level swaps, missing nested commutativity. -/
inductive CommRel : FreeMagma α → FreeMagma α → Prop
  | swap (a b : FreeMagma α) : CommRel (a * b) (b * a)
  | mul_left {a b : FreeMagma α} (h : CommRel a b) (c : FreeMagma α) :
      CommRel (a * c) (b * c)
  | mul_right (a : FreeMagma α) {b c : FreeMagma α} (h : CommRel b c) :
      CommRel (a * b) (a * c)

end FreeMagma

/-- **Free commutative magma** on `α`: planar binary trees with leaves
    in `α` modulo the smallest congruence containing the swap relation.

    Single type parameter, matching mathlib's `FreeMagma α` shape.
    The non-associative, commutative analogue of `FreeMonoid` /
    `FreeCommMonoid`.

    Universal property: any `α → β` to a `CommMagma`-equipped `β`
    extends uniquely to `FreeCommMagma α →ₙ* β` (the `lift` below). -/
def FreeCommMagma (α : Type u) : Type u :=
  Quot (@FreeMagma.CommRel α)

namespace FreeCommMagma

variable {α : Type u} {β : Type v}

/-- Embed a leaf as a `FreeCommMagma`. Mirrors `FreeMagma.of`. -/
def of (a : α) : FreeCommMagma α := Quot.mk _ (FreeMagma.of a)

/-- Multiplication on `FreeCommMagma α` lifted from `FreeMagma.mul`
    via `Quot.lift₂`. The swap-respect proofs are exactly the
    `mul_left` and `mul_right` constructors of `CommRel` (which is
    why we need the congruence rules in `CommRel`). -/
def mul : FreeCommMagma α → FreeCommMagma α → FreeCommMagma α :=
  Quot.lift₂ (fun a b => Quot.mk _ (a * b))
    (fun _ _ _ h => Quot.sound (.mul_right _ h))
    (fun _ _ _ h => Quot.sound (.mul_left h _))

instance : Mul (FreeCommMagma α) := ⟨mul⟩

@[simp] theorem of_mul_of (a b : α) :
    (of a : FreeCommMagma α) * of b
      = Quot.mk _ (FreeMagma.of a * FreeMagma.of b) := rfl

/-- **Headline**: multiplication is commutative. The reason this
    type was constructed. Private — use `mul_comm` from the
    `CommMagma` typeclass instance below. -/
private theorem mul_comm_aux (a b : FreeCommMagma α) : a * b = b * a := by
  induction a using Quot.ind with
  | _ a =>
    induction b using Quot.ind with
    | _ b => exact Quot.sound (.swap a b)

/-- `CommMagma` typeclass instance: external `_root_.mul_comm`
    just works. -/
instance : CommMagma (FreeCommMagma α) where
  mul_comm := mul_comm_aux

/-- Lift a `FreeMagma α → β` function that respects `CommRel` to a
    `FreeCommMagma α → β` function. Mirrors `Quot.lift`. -/
def lift (f : FreeMagma α → β)
    (h : ∀ a b, FreeMagma.CommRel a b → f a = f b) :
    FreeCommMagma α → β :=
  Quot.lift f h

@[simp] theorem lift_mk (f : FreeMagma α → β)
    (h : ∀ a b, FreeMagma.CommRel a b → f a = f b) (a : FreeMagma α) :
    lift f h (Quot.mk _ a) = f a := rfl

/-- Induction principle for `FreeCommMagma α`: to prove `motive t`
    for all `t : FreeCommMagma α`, it suffices to prove it for every
    `Quot.mk _ a` with `a : FreeMagma α`. (Quot's `ind` propagates
    through the equivalence automatically since `motive` is a `Prop`.) -/
@[elab_as_elim, induction_eliminator]
protected theorem ind {motive : FreeCommMagma α → Prop}
    (h : ∀ a : FreeMagma α, motive (Quot.mk _ a))
    (t : FreeCommMagma α) : motive t :=
  Quot.ind h t

/-- `recOn`-style elimination for `Sort`-valued motives. Requires the
    `respect` hypothesis explicitly (Quot.recOn obligation). -/
@[elab_as_elim]
protected def recOn {motive : FreeCommMagma α → Sort*}
    (t : FreeCommMagma α) (h : ∀ a : FreeMagma α, motive (Quot.mk _ a))
    (respect : ∀ a b (r : FreeMagma.CommRel a b),
        (Quot.sound r : (Quot.mk _ a : FreeCommMagma α) = Quot.mk _ b) ▸ h a = h b) :
    motive t :=
  Quot.recOn t h respect

/-! ### Basic operations

`size` is the canonical "number of constructors" measure. Lifts via
`lift` since the underlying `FreeMagma.size`-equivalent respects swap
(addition is commutative). -/

/-- Underlying `size` on `FreeMagma α` (counts both branches +1). -/
private def sizeAux : FreeMagma α → Nat
  | .of _ => 1
  | .mul l r => 1 + sizeAux l + sizeAux r

@[simp] private theorem sizeAux_of (a : α) : sizeAux (FreeMagma.of a) = 1 := rfl

@[simp] private theorem sizeAux_mul (a b : FreeMagma α) :
    sizeAux (a * b) = 1 + sizeAux a + sizeAux b := rfl

private theorem sizeAux_respects_commRel
    (a b : FreeMagma α) (h : FreeMagma.CommRel a b) : sizeAux a = sizeAux b := by
  induction h with
  | swap a b => simp only [sizeAux_mul]; omega
  | mul_left _ _ ih => simp only [sizeAux_mul]; omega
  | mul_right _ _ ih => simp only [sizeAux_mul]; omega

/-- `size t` counts the constructors of any planar representative of
    `t : FreeCommMagma α`. Well-defined because addition is
    commutative (the swap-respecting underlying function). -/
def size : FreeCommMagma α → Nat :=
  lift sizeAux sizeAux_respects_commRel

@[simp] theorem size_of (a : α) : size (of a : FreeCommMagma α) = 1 := rfl

@[simp] theorem size_mul (a b : FreeCommMagma α) :
    size (a * b) = 1 + size a + size b := by
  induction a using Quot.ind with
  | _ a => induction b using Quot.ind with | _ b => rfl

/-! ### Universal property (CommMagma adjunction)

Any function `α → β` to a `CommMagma`-equipped `β` extends uniquely
to a magma homomorphism `FreeCommMagma α →ₙ* β`. The key step is
that `FreeMagma.lift f` already respects `CommRel`-swap when `β`
is a `CommMagma`.

Stated in `MulHom`-shape (`→ₙ*`) per the mathlib convention for
non-unital homomorphisms. -/

variable [CommMagma β]

/-- Lift a function `f : α → β` to a non-unital magma homomorphism
    `FreeCommMagma α →ₙ* β`, when `β` is a `CommMagma`. The underlying
    function is `FreeMagma.liftAux f` (already non-commutative-aware);
    we just need to show it respects `CommRel`. -/
private theorem liftAux_respects_commRel (f : α → β)
    (a b : FreeMagma α) (h : FreeMagma.CommRel a b) :
    FreeMagma.liftAux f a = FreeMagma.liftAux f b := by
  induction h with
  | swap a b =>
    show FreeMagma.liftAux f a * FreeMagma.liftAux f b
        = FreeMagma.liftAux f b * FreeMagma.liftAux f a
    exact CommMagma.mul_comm _ _
  | mul_left _ c ih =>
    show FreeMagma.liftAux f _ * FreeMagma.liftAux f c
        = FreeMagma.liftAux f _ * FreeMagma.liftAux f c
    rw [ih]
  | mul_right c _ ih =>
    show FreeMagma.liftAux f c * FreeMagma.liftAux f _
        = FreeMagma.liftAux f c * FreeMagma.liftAux f _
    rw [ih]

/-- **Universal property**: lift `f : α → β` to a magma homomorphism
    `FreeCommMagma α →ₙ* β`. Mirrors `FreeMagma.lift` (line ~110 of
    `Mathlib/Algebra/Free.lean`). -/
def liftHom (f : α → β) : FreeCommMagma α →ₙ* β where
  toFun := lift (FreeMagma.liftAux f) (liftAux_respects_commRel f)
  map_mul' := by
    intro x y
    induction x using Quot.ind with
    | _ x => induction y using Quot.ind with | _ y => rfl

@[simp] theorem liftHom_of (f : α → β) (a : α) :
    liftHom f (of a) = f a := rfl

end FreeCommMagma
