import Mathlib.Algebra.Free
import Mathlib.Data.Quot
import Mathlib.Logic.Relation
import Mathlib.Order.Defs.LinearOrder

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

    Declared as `abbrev` (not `def`) so that `Quot`-aware lemmas
    (`Quot.eq`, `Quot.exists_rep`, `Quot.recOnSubsingleton`, …) fire
    on `FreeCommMagma α` without needing an unfold. Mirrors
    `Sym2 α := Quot _` (`Mathlib/Data/Sym/Sym2.lean:100`).

    Universal property: any `α → β` to a `CommMagma`-equipped `β`
    extends uniquely to `FreeCommMagma α →ₙ* β` (the `lift` below). -/
abbrev FreeCommMagma (α : Type u) : Type u :=
  Quot (@FreeMagma.CommRel α)

namespace FreeCommMagma

variable {α : Type u} {β : Type v}

/-- Public alias for `Quot.mk _` on `FreeCommMagma α`. Use this instead
    of writing `(Quot.mk _ a : FreeCommMagma α)` at call sites — the
    type ascription is inferred. Mirrors `Sym2.mk` (`Sym2.lean:103`). -/
protected abbrev mk (a : FreeMagma α) : FreeCommMagma α := Quot.mk _ a

/-- Embed a leaf as a `FreeCommMagma`. Mirrors `FreeMagma.of`. -/
protected abbrev of (a : α) : FreeCommMagma α :=
  FreeCommMagma.mk (FreeMagma.of a)

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
    (FreeCommMagma.of a : FreeCommMagma α) * FreeCommMagma.of b
      = FreeCommMagma.mk (FreeMagma.of a * FreeMagma.of b) := rfl

/-- **Headline**: multiplication is commutative. The reason this
    type was constructed. -/
instance : CommMagma (FreeCommMagma α) where
  mul_comm a b := by
    induction a using Quot.ind with
    | _ a =>
      induction b using Quot.ind with
      | _ b => exact Quot.sound (.swap a b)

/-- Lift a `FreeMagma α → β` function that respects `CommRel` to a
    `FreeCommMagma α → β` function. Mirrors `Quot.lift`. -/
def lift (f : FreeMagma α → β)
    (h : ∀ a b, FreeMagma.CommRel a b → f a = f b) :
    FreeCommMagma α → β :=
  Quot.lift f h

@[simp] theorem lift_mk (f : FreeMagma α → β)
    (h : ∀ a b, FreeMagma.CommRel a b → f a = f b) (a : FreeMagma α) :
    lift f h (FreeCommMagma.mk a) = f a := rfl

/-- Lemma form of `Quot.sound` specialized to `FreeCommMagma`. -/
protected theorem sound {a b : FreeMagma α} (h : FreeMagma.CommRel a b) :
    (FreeCommMagma.mk a : FreeCommMagma α) = FreeCommMagma.mk b := Quot.sound h

/-- Specialized `swap`: `mk (a * b) = mk (b * a)` as a named lemma.
    Mirrors `mul_comm` on the quotient but stated at the `FreeMagma`
    level to spare consumers an `induction`. -/
protected theorem swap (a b : FreeMagma α) :
    (FreeCommMagma.mk (a * b) : FreeCommMagma α) = FreeCommMagma.mk (b * a) :=
  FreeCommMagma.sound (.swap a b)

/-- The eqv-gen-soundness companion to `sound`: equality on the quotient
    extracts a `EqvGen CommRel` proof. Mirrors `Sym2.exact`-style API. -/
protected theorem exact {a b : FreeMagma α}
    (h : (FreeCommMagma.mk a : FreeCommMagma α) = FreeCommMagma.mk b) :
    Relation.EqvGen FreeMagma.CommRel a b := Quot.eqvGen_exact h

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
    (t : FreeCommMagma α) (h : ∀ a : FreeMagma α, motive (FreeCommMagma.mk a))
    (respect : ∀ a b (r : FreeMagma.CommRel a b),
        (FreeCommMagma.sound r) ▸ h a = h b) :
    motive t :=
  Quot.recOn t h respect

/-- Subsingleton elimination — the typical shape for `Decidable`,
    `DecidablePred`, and other proof-irrelevant `Sort`-valued motives.
    Mirrors `Sym2.recOnSubsingleton` (`Sym2.lean:168`). Saves consumers
    from writing `Quot.recOnSubsingleton` raw and ascribing the type. -/
@[elab_as_elim]
protected abbrev recOnSubsingleton {motive : FreeCommMagma α → Sort*}
    [∀ a : FreeMagma α, Subsingleton (motive (FreeCommMagma.mk a))]
    (t : FreeCommMagma α) (h : ∀ a : FreeMagma α, motive (FreeCommMagma.mk a)) :
    motive t :=
  Quot.recOnSubsingleton t h

/-- `lift₂`: lift a binary `FreeMagma α → FreeMagma α → β` function
    that respects `CommRel` on each argument. Mirrors `Quot.lift₂`. -/
def lift₂ (f : FreeMagma α → FreeMagma α → β)
    (hr : ∀ a b₁ b₂, FreeMagma.CommRel b₁ b₂ → f a b₁ = f a b₂)
    (hs : ∀ a₁ a₂ b, FreeMagma.CommRel a₁ a₂ → f a₁ b = f a₂ b) :
    FreeCommMagma α → FreeCommMagma α → β :=
  Quot.lift₂ f hr hs

@[simp] theorem lift₂_mk (f : FreeMagma α → FreeMagma α → β) (hr) (hs)
    (a b : FreeMagma α) :
    lift₂ f hr hs (FreeCommMagma.mk a) (FreeCommMagma.mk b) = f a b := rfl

/-- Two-argument induction: useful for binary operations. The `t`-then-`s`
    argument order mirrors `Sym2.inductionOn₂` so callers can pass binary
    SOs in their natural left-then-right order. -/
@[elab_as_elim]
protected theorem inductionOn₂ {motive : FreeCommMagma α → FreeCommMagma α → Prop}
    (t s : FreeCommMagma α)
    (h : ∀ a b : FreeMagma α, motive (FreeCommMagma.mk a) (FreeCommMagma.mk b)) :
    motive t s := by
  induction t using Quot.ind with
  | _ a => induction s using Quot.ind with | _ b => exact h a b

/-- Surjectivity of `Quot.mk`: every `FreeCommMagma α` element has
    *some* `FreeMagma α` representative. Useful with `obtain`. -/
theorem exists_rep (t : FreeCommMagma α) :
    ∃ a : FreeMagma α, FreeCommMagma.mk a = t :=
  Quot.exists_rep t

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
  induction h <;> simp only [sizeAux_mul] <;> omega

/-- `size t` counts the constructors of any planar representative of
    `t : FreeCommMagma α`. Well-defined because addition is
    commutative (the swap-respecting underlying function). -/
def size : FreeCommMagma α → Nat :=
  lift sizeAux sizeAux_respects_commRel

@[simp] theorem size_of (a : α) :
    size (FreeCommMagma.of a : FreeCommMagma α) = 1 := rfl

@[simp] theorem size_mul (a b : FreeCommMagma α) :
    size (a * b) = 1 + size a + size b := by
  induction a, b using FreeCommMagma.inductionOn₂ with | _ a b => rfl

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
    liftHom f (FreeCommMagma.of a) = f a := rfl

end FreeCommMagma

/-! ### Functoriality: `map`

`FreeCommMagma` is a functor in `α`. `map f` is the lift of `of ∘ f` to a
magma homomorphism — the universal property gives uniqueness. -/

namespace FreeCommMagma

variable {α : Type u} {β : Type v}

/-- Functorial map: `map f` lifts `f : α → β` to
    `FreeCommMagma α →ₙ* FreeCommMagma β`. The codomain `FreeCommMagma β`
    is itself a `CommMagma` (instance above), so this is just `liftHom`
    applied to the `of`-composed function. -/
def map (f : α → β) : FreeCommMagma α →ₙ* FreeCommMagma β :=
  liftHom (FreeCommMagma.of ∘ f)

@[simp] theorem map_of (f : α → β) (a : α) :
    map f (FreeCommMagma.of a) = FreeCommMagma.of (f a) := rfl

@[simp] theorem map_mul (f : α → β) (l r : FreeCommMagma α) :
    map f (l * r) = map f l * map f r := MulHom.map_mul (map f) l r

end FreeCommMagma

/-! ### Canonicalization → DecidableEq

`FreeCommMagma α := Quot CommRel` doesn't have a generic `DecidableEq`
instance. The standard mathlib idiom (see `Multiset.decidableEq`) is
to canonicalize: pick a unique representative per equivalence class
and reduce equality on the quotient to equality of canonical forms.

For `[LinearOrder α]` we sort the children of each `.mul` node by lex
order on the underlying `FreeMagma` trees.

`Sym2` gets to enumerate representatives because there are only two,
but `FreeCommMagma`'s equivalence classes are exponentially large
(n! for n internal nodes), so canonicalization is the only viable
route. -/

namespace FreeMagma

variable {α : Type u}

section LexCompare

variable [LinearOrder α]

/-- Lex comparison on `FreeMagma α`: leaves sort by α-order, leaves
    sort before mul nodes, mul nodes recursively (left then right). -/
def lexCompare : FreeMagma α → FreeMagma α → Ordering
  | .of a, .of b => compare a b
  | .of _, .mul _ _ => .lt
  | .mul _ _, .of _ => .gt
  | .mul l₁ r₁, .mul l₂ r₂ => (lexCompare l₁ l₂).then (lexCompare r₁ r₂)

private theorem compare_self_eq (x : α) : compare x x = .eq :=
  compare_eq_iff_eq.mpr rfl

private theorem compare_swap_eq (x y : α) : compare x y = (compare y x).swap := by
  cases h : compare y x with
  | lt =>
    rw [compare_lt_iff_lt] at h
    exact compare_gt_iff_gt.mpr h
  | eq =>
    rw [compare_eq_iff_eq] at h; subst h
    exact compare_self_eq _
  | gt =>
    rw [compare_gt_iff_gt] at h
    exact compare_lt_iff_lt.mpr h

theorem lexCompare_self (a : FreeMagma α) : lexCompare a a = .eq := by
  induction a with
  | ih1 x => exact compare_self_eq x
  | ih2 l r ihl ihr =>
    show (lexCompare l l).then (lexCompare r r) = .eq
    rw [ihl, ihr]; rfl

theorem lexCompare_eq_iff (a b : FreeMagma α) : lexCompare a b = .eq ↔ a = b := by
  induction a generalizing b with
  | ih1 x =>
    match b with
    | .of y =>
      constructor
      · intro h
        show FreeMagma.of x = FreeMagma.of y
        have : compare x y = .eq := h
        rw [compare_eq_iff_eq] at this; exact congrArg _ this
      · intro h; injection h with h'; subst h'; exact compare_self_eq _
    | .mul _ _ => exact ⟨nofun, nofun⟩
  | ih2 l r ihl ihr =>
    match b with
    | .of _ => exact ⟨nofun, nofun⟩
    | .mul l' r' =>
      show (lexCompare l l').then (lexCompare r r') = .eq ↔ _
      constructor
      · intro h
        rw [Ordering.then_eq_eq] at h
        obtain ⟨hl, hr⟩ := h
        rw [ihl] at hl; rw [ihr] at hr
        subst hl; subst hr; rfl
      · intro h
        injection h with h1 h2
        subst h1; subst h2
        rw [Ordering.then_eq_eq]
        exact ⟨lexCompare_self _, lexCompare_self _⟩

theorem lexCompare_swap (a b : FreeMagma α) :
    lexCompare a b = (lexCompare b a).swap := by
  induction a generalizing b with
  | ih1 x =>
    match b with
    | .of y => exact compare_swap_eq x y
    | .mul _ _ => rfl
  | ih2 l r ihl ihr =>
    match b with
    | .of _ => rfl
    | .mul l' r' =>
      show (lexCompare l l').then (lexCompare r r')
        = ((lexCompare l' l).then (lexCompare r' r)).swap
      rw [ihl l', ihr r']
      cases lexCompare l' l <;> cases lexCompare r' r <;> rfl

end LexCompare

section Normalize

variable [LinearOrder α]

/-- Canonical form: recursively sort children at each `.mul` node by
    lex order. `normalize a` is the unique representative of the
    `CommRel`-equivalence class of `a`. -/
def normalize : FreeMagma α → FreeMagma α
  | .of a => .of a
  | .mul l r =>
    let l' := normalize l
    let r' := normalize r
    match lexCompare l' r' with
    | .gt => r' * l'
    | _   => l' * r'

@[simp] theorem normalize_of (a : α) :
    normalize (.of a : FreeMagma α) = .of a := rfl

theorem normalize_mul (l r : FreeMagma α) :
    normalize (l * r)
      = (match lexCompare (normalize l) (normalize r) with
         | .gt => normalize r * normalize l
         | _   => normalize l * normalize r) := rfl

/-- `normalize` produces a sorted-children form: at each `.mul` node
    of `normalize a`, the left child does NOT lex-compare-greater than
    the right child. -/
theorem normalize_swap_mul (a b : FreeMagma α) :
    normalize (a * b) = normalize (b * a) := by
  show (match lexCompare (normalize a) (normalize b) with
        | .gt => normalize b * normalize a
        | _   => normalize a * normalize b)
     = (match lexCompare (normalize b) (normalize a) with
        | .gt => normalize a * normalize b
        | _   => normalize b * normalize a)
  rw [lexCompare_swap (normalize b) (normalize a)]
  cases hcmp : lexCompare (normalize a) (normalize b) with
  | lt => rfl
  | eq =>
    have hab : normalize a = normalize b := (lexCompare_eq_iff _ _).mp hcmp
    rw [hab]; rfl
  | gt => rfl

theorem normalize_mul_left (l₁ l₂ r : FreeMagma α) (h : normalize l₁ = normalize l₂) :
    normalize (l₁ * r) = normalize (l₂ * r) := by
  simp only [normalize_mul, h]

theorem normalize_mul_right (l r₁ r₂ : FreeMagma α) (h : normalize r₁ = normalize r₂) :
    normalize (l * r₁) = normalize (l * r₂) := by
  simp only [normalize_mul, h]

/-- `normalize` is constant on `CommRel`-related elements. The headline
    of canonicalization. -/
theorem commRel_normalize_eq (a b : FreeMagma α) (h : CommRel a b) :
    normalize a = normalize b := by
  induction h with
  | swap a b => exact normalize_swap_mul a b
  | mul_left _ c ih => exact normalize_mul_left _ _ c ih
  | mul_right c _ ih => exact normalize_mul_right c _ _ ih

end Normalize

end FreeMagma

namespace FreeCommMagma

variable {α : Type u}

section DecidableEq

variable [LinearOrder α]

/-- Lift `normalize` to `FreeCommMagma α`: the normal form of any
    representative is itself a representative, and equal representatives
    have equal normal forms. -/
def normalize : FreeCommMagma α → FreeMagma α :=
  lift FreeMagma.normalize FreeMagma.commRel_normalize_eq

@[simp] theorem normalize_mk (a : FreeMagma α) :
    normalize (Quot.mk _ a : FreeCommMagma α) = FreeMagma.normalize a := rfl

/-- Lifting `EqvGen` through `mul_left` congruence. -/
private theorem _root_.FreeMagma.eqvGen_mul_left {α : Type u} {a b : FreeMagma α}
    (h : Relation.EqvGen FreeMagma.CommRel a b) (c : FreeMagma α) :
    Relation.EqvGen FreeMagma.CommRel (a * c) (b * c) := by
  induction h with
  | rel _ _ h => exact .rel _ _ (.mul_left h _)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

/-- Lifting `EqvGen` through `mul_right` congruence. -/
private theorem _root_.FreeMagma.eqvGen_mul_right {α : Type u} (a : FreeMagma α)
    {b c : FreeMagma α} (h : Relation.EqvGen FreeMagma.CommRel b c) :
    Relation.EqvGen FreeMagma.CommRel (a * b) (a * c) := by
  induction h with
  | rel _ _ h => exact .rel _ _ (.mul_right _ h)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

/-- Every `FreeMagma α` element is `EqvGen CommRel`-related to its
    normal form. Proven by induction on the tree structure: the leaf
    case is reflexivity; for `.mul l r`, lift `IH(l)` and `IH(r)`
    through congruence (mul_left + mul_right), then apply swap if the
    normalizer reordered. -/
theorem _root_.FreeMagma.eqvGen_normalize (a : FreeMagma α) :
    Relation.EqvGen FreeMagma.CommRel a (FreeMagma.normalize a) := by
  induction a with
  | ih1 x => exact .refl _
  | ih2 l r ihl ihr =>
    have step1 : Relation.EqvGen FreeMagma.CommRel (l * r) (FreeMagma.normalize l * r) :=
      FreeMagma.eqvGen_mul_left ihl r
    have step2 : Relation.EqvGen FreeMagma.CommRel
        (FreeMagma.normalize l * r)
        (FreeMagma.normalize l * FreeMagma.normalize r) :=
      FreeMagma.eqvGen_mul_right _ ihr
    have step12 : Relation.EqvGen FreeMagma.CommRel (l * r)
        (FreeMagma.normalize l * FreeMagma.normalize r) := .trans _ _ _ step1 step2
    show Relation.EqvGen FreeMagma.CommRel (l * r) (FreeMagma.normalize (l * r))
    rw [FreeMagma.normalize_mul]
    cases FreeMagma.lexCompare (FreeMagma.normalize l) (FreeMagma.normalize r) with
    | lt => exact step12
    | eq => exact step12
    | gt =>
      have step3 : Relation.EqvGen FreeMagma.CommRel
          (FreeMagma.normalize l * FreeMagma.normalize r)
          (FreeMagma.normalize r * FreeMagma.normalize l) :=
        .rel _ _ (.swap _ _)
      exact .trans _ _ _ step12 step3

/-- `EqvGen CommRel` collapses to equality after `normalize`. Proven by
    induction on `EqvGen` — the `rel` case uses `commRel_normalize_eq`,
    other cases are reflexivity / symm / trans of plain equality. -/
private theorem eqvGen_implies_normalize_eq {a b : FreeMagma α}
    (h : Relation.EqvGen FreeMagma.CommRel a b) :
    FreeMagma.normalize a = FreeMagma.normalize b := by
  induction h with
  | rel _ _ h => exact FreeMagma.commRel_normalize_eq _ _ h
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Bridge lemma: `Quot.mk` equality on `FreeCommMagma α` corresponds
    exactly to `normalize`-equality on `FreeMagma α`. -/
theorem mk_eq_iff_normalize_eq (a b : FreeMagma α) :
    (Quot.mk _ a : FreeCommMagma α) = Quot.mk _ b
      ↔ FreeMagma.normalize a = FreeMagma.normalize b := by
  constructor
  · intro h
    have hab : Relation.EqvGen FreeMagma.CommRel a b := Quot.eqvGen_exact h
    exact eqvGen_implies_normalize_eq hab
  · intro h
    have h₁ : Relation.EqvGen FreeMagma.CommRel a (FreeMagma.normalize a) :=
      FreeMagma.eqvGen_normalize a
    have h₂ : Relation.EqvGen FreeMagma.CommRel b (FreeMagma.normalize b) :=
      FreeMagma.eqvGen_normalize b
    have hab : Relation.EqvGen FreeMagma.CommRel a b :=
      .trans _ _ _ h₁ (h ▸ .symm _ _ h₂)
    exact Quot.eqvGen_sound hab

end DecidableEq

end FreeCommMagma

/-! ### DecidableEq via direct recursion (the mathlib idiom)

`Multiset.decidableEq` requires only `[DecidableEq α]` because
`List.Perm` has a clever direct decision procedure (count each element
on both sides). For `FreeCommMagma`, the analogous fact: each `.mul`
node has exactly 2 children, so `(l₁*r₁) ~ (l₂*r₂)` iff
`{l₁, r₁} = {l₂, r₂}` as a 2-element multiset, which decomposes to
`(l₁~l₂ ∧ r₁~r₂) ∨ (l₁~r₂ ∧ r₁~l₂)`. Recursive and decidable from
`[DecidableEq α]` alone — no `[LinearOrder α]` needed.

Crucially this works because `FreeMagma` is non-associative —
`((a*b)*c)` and `(a*(b*c))` are NOT `CommRel`-equivalent. The
equivalence preserves tree structure modulo per-node swap.

This is the mathlib-canonical answer: don't canonicalize when a direct
`DecidableRel` on the equivalence works. The LinearOrder-based
canonicalization above is still useful when a normal form is wanted
(e.g., `Repr`), but `DecidableEq` doesn't need it. -/

namespace FreeMagma

variable {α : Type u}

/-- Constructor count, used as a recursion measure for `CommEqv.trans`.
    Public so termination proofs in this namespace can reference it. -/
def nodeCount : FreeMagma α → Nat
  | .of _ => 1
  | .mul l r => 1 + nodeCount l + nodeCount r

@[simp] theorem nodeCount_of (a : α) : nodeCount (FreeMagma.of a) = 1 := rfl
@[simp] theorem nodeCount_mul (l r : FreeMagma α) :
    nodeCount (l * r) = 1 + nodeCount l + nodeCount r := rfl

/-- Recursive equivalence relation matching `EqvGen CommRel`. At each
    `.mul` node, try both pairings of children. -/
def CommEqv : FreeMagma α → FreeMagma α → Prop
  | .of a, .of b => a = b
  | .of _, .mul _ _ => False
  | .mul _ _, .of _ => False
  | .mul l₁ r₁, .mul l₂ r₂ =>
      (CommEqv l₁ l₂ ∧ CommEqv r₁ r₂) ∨ (CommEqv l₁ r₂ ∧ CommEqv r₁ l₂)

instance instDecidableCommEqv [DecidableEq α] :
    (a b : FreeMagma α) → Decidable (CommEqv a b)
  | .of a, .of b => inferInstanceAs (Decidable (a = b))
  | .of _, .mul _ _ => isFalse id
  | .mul _ _, .of _ => isFalse id
  | .mul l₁ r₁, .mul l₂ r₂ =>
    have : Decidable (CommEqv l₁ l₂) := instDecidableCommEqv l₁ l₂
    have : Decidable (CommEqv r₁ r₂) := instDecidableCommEqv r₁ r₂
    have : Decidable (CommEqv l₁ r₂) := instDecidableCommEqv l₁ r₂
    have : Decidable (CommEqv r₁ l₂) := instDecidableCommEqv r₁ l₂
    inferInstanceAs (Decidable (_ ∨ _))

theorem CommEqv.refl (a : FreeMagma α) : CommEqv a a := by
  induction a with
  | ih1 _ => rfl
  | ih2 l r ihl ihr => exact .inl ⟨ihl, ihr⟩

theorem CommEqv.symm {a b : FreeMagma α} : CommEqv a b → CommEqv b a := by
  induction a generalizing b with
  | ih1 x =>
    match b with
    | .of y => exact Eq.symm
    | .mul _ _ => exact id
  | ih2 l r ihl ihr =>
    match b with
    | .of _ => exact id
    | .mul l' r' =>
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact .inl ⟨ihl h1, ihr h2⟩
      · exact .inr ⟨ihr h2, ihl h1⟩

theorem CommEqv.trans : ∀ {a b c : FreeMagma α},
    CommEqv a b → CommEqv b c → CommEqv a c
  | .of x, .of y, .of z, hab, hbc => by
    show x = z; exact (show x = y from hab).trans (show y = z from hbc)
  | .of _, .of _, .mul _ _, _, h => h.elim
  | .of _, .mul _ _, _, h, _ => h.elim
  | .mul _ _, .of _, _, h, _ => h.elim
  | .mul _ _, .mul _ _, .of _, _, h => h.elim
  | .mul l r, .mul l' r', .mul l'' r'', hab, hbc => by
    rcases hab with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ <;>
      rcases hbc with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩
    · exact .inl ⟨CommEqv.trans ha1 hb1, CommEqv.trans ha2 hb2⟩
    · exact .inr ⟨CommEqv.trans ha1 hb1, CommEqv.trans ha2 hb2⟩
    · exact .inr ⟨CommEqv.trans ha1 hb2, CommEqv.trans ha2 hb1⟩
    · exact .inl ⟨CommEqv.trans ha1 hb2, CommEqv.trans ha2 hb1⟩
termination_by a b c _ _ => nodeCount a + nodeCount b + nodeCount c

theorem CommEqv.of_commRel {a b : FreeMagma α} (h : CommRel a b) : CommEqv a b := by
  induction h with
  | swap a b => exact .inr ⟨.refl _, .refl _⟩
  | mul_left _ c ih => exact .inl ⟨ih, .refl _⟩
  | mul_right c _ ih => exact .inl ⟨.refl _, ih⟩

/-- The headline correspondence: `CommEqv` is exactly the equivalence
    closure of `CommRel`. Forward: induction on `EqvGen` using refl,
    symm, trans, and `of_commRel`. Reverse: induction on the recursive
    structure of `CommEqv`, lifting through congruence rules. -/
theorem commEqv_iff_eqvGen (a b : FreeMagma α) :
    CommEqv a b ↔ Relation.EqvGen CommRel a b := by
  refine ⟨?_, ?_⟩
  · -- CommEqv → EqvGen CommRel
    induction a generalizing b with
    | ih1 x =>
      match b with
      | .of y => intro h; cases h; exact .refl _
      | .mul _ _ => intro h; exact h.elim
    | ih2 l r ihl ihr =>
      match b with
      | .of _ => intro h; exact h.elim
      | .mul l' r' =>
        rintro (⟨hl, hr⟩ | ⟨hl, hr⟩)
        · exact .trans _ _ _ (eqvGen_mul_left (ihl _ hl) r) (eqvGen_mul_right l' (ihr _ hr))
        · -- (l*r) ~ (r*l) by swap, then (r*l) ~ (l'*l) ~ (l'*r')
          have step1 : Relation.EqvGen CommRel (l * r) (r * l) := .rel _ _ (.swap _ _)
          have step2 : Relation.EqvGen CommRel (r * l) (l' * l) :=
            eqvGen_mul_left (ihr _ hr) l
          have step3 : Relation.EqvGen CommRel (l' * l) (l' * r') :=
            eqvGen_mul_right l' (ihl _ hl)
          exact .trans _ _ _ step1 (.trans _ _ _ step2 step3)
  · -- EqvGen CommRel → CommEqv
    intro h
    induction h with
    | rel _ _ h => exact CommEqv.of_commRel h
    | refl a => exact CommEqv.refl a
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end FreeMagma

namespace FreeCommMagma

variable {α : Type u}

/-- Bridge: `Quot.mk` equality on `FreeCommMagma α` corresponds exactly
    to `CommEqv`-equivalence on `FreeMagma α`. -/
theorem mk_eq_iff_commEqv (a b : FreeMagma α) :
    (Quot.mk _ a : FreeCommMagma α) = Quot.mk _ b ↔ FreeMagma.CommEqv a b := by
  rw [Quot.eq, ← FreeMagma.commEqv_iff_eqvGen]

variable [DecidableEq α]

/-- `DecidableEq` from `[DecidableEq α]` alone, mirroring
    `Multiset.decidableEq`. The `LinearOrder`-based `normalize` exists
    above for cases that need a canonical form (e.g., `Repr`), but
    `DecidableEq` doesn't go through it. -/
instance : DecidableEq (FreeCommMagma α) := fun x y =>
  Quot.recOnSubsingleton₂ x y fun a b =>
    decidable_of_iff _ (mk_eq_iff_commEqv a b).symm

end FreeCommMagma

/-! ### `Repr` — placeholder

`FreeCommMagma α` doesn't have a canonical printable form without
canonicalization (`[LinearOrder α]` + `normalize`); printing an
arbitrary representative is `unsafe` (Multiset's strategy at
`Mathlib/Data/Multiset/Sort.lean:106`) and propagates `unsafe` to every
consumer that wants `deriving Repr`.

This **placeholder** instance returns the string `"<FreeCommMagma>"`
so that downstream `deriving Repr` on structures containing
`FreeCommMagma α` fields (e.g., linglib's `Derivation { initial : SO }`)
synthesizes safely. The output is uninformative; substantive printing
needs a `[LinearOrder α]`-based `normalize`-canonicalized variant in a
follow-up. -/

namespace FreeCommMagma

variable {α : Type u}

instance : Repr (FreeCommMagma α) where
  reprPrec _ _ := "<FreeCommMagma>"

end FreeCommMagma

/-! ### Sections of the quotient projection `Quot.mk : FreeMagma → FreeCommMagma`

A **section** of the projection picks a planar representative (a `FreeMagma α`)
for each nonplanar tree (a `FreeCommMagma α`). This is the natural primitive
for the **Externalization** models of [marcolli-chomsky-berwick-2025] §1.12.1
(book pp. 105-108): the section σ_L assigns to each abstract syntactic object
T ∈ 𝔗_{SO_0} a planar embedding σ_L(T) ∈ 𝔗^{pl}_{SO_0}, language-dependently.

**Key properties** (MCB §1.12.1):
- The section is a **map of sets, NOT a morphism of magmas**. Per MCB Lemma 1.13.1
  (book p. 124), no morphism of magmas exists from `FreeCommMagma α` to
  `FreeMagma α` — a commutative submagma argument rules it out.
- The section is **noncanonical**: it depends on choices (e.g., language-specific
  word-order parameters in linguistics).

**Mathlib shape**: a section is captured exactly by `Function.LeftInverse mk σ`
on the standard quotient projection. We bundle it into a `Section` structure for
ergonomic field access (downstream `HeadFunction` etc. embed `section_ : Section _`
as a single field rather than two).

**Downstream uses** (forward references):
- `Linglib/Syntax/Minimalist/HeadFunction.lean` uses `Section (LIToken ⊕ Nat)`
  as the substrate for MCB head functions
- The `Section.σ_of` keystone lemma absorbs ~13 sites of singleton-class
  case-analysis into a single application
- Per MCB §1.12.3, σ_L can be lifted to a linear map of vector spaces
  `V(𝔗_{SO_0}) → V(𝔗^{pl}_{SO_0})` — this lift is straightforward via
  `Quot.lift` once the algebra-side substrate is in place; Section captures
  the underlying set-level fact

This abstraction generalizes any future MCB-style "section of a quotient
projection" need (e.g. Π_L of MCB eq 1.12.4, second projection).
-/

namespace FreeCommMagma

variable {α : Type u}

/-- A **section** of the quotient projection `Quot.mk : FreeMagma α → FreeCommMagma α`,
    per [marcolli-chomsky-berwick-2025] §1.12.1.

    The section σ : `FreeCommMagma α → FreeMagma α` picks a planar representative
    for each nonplanar tree. The `isSection` field witnesses
    `Function.LeftInverse mk σ`, i.e. `∀ T, FreeCommMagma.mk (σ T) = T`.

    Per MCB Lemma 1.13.1, σ is **not** a morphism of magmas (no such morphism
    exists from `FreeCommMagma α` to `FreeMagma α`). It is a map of sets only.
    Constructing σ is **noncanonical**: distinct sections correspond to distinct
    planar embedding choices.

    Equivalent to a (noncomputable) bare `(σ, isSection)` pair, but bundled for
    ergonomic field access in downstream structures (e.g. `HeadFunction`). -/
structure Section (α : Type u) where
  /-- The underlying section function: assigns a planar representative to each
      nonplanar tree. -/
  σ : FreeCommMagma α → FreeMagma α
  /-- Section equation: `mk` is a left inverse of `σ`, i.e. composing yields id. -/
  isSection : Function.LeftInverse (FreeCommMagma.mk : FreeMagma α → FreeCommMagma α) σ

namespace Section

variable {α : Type u}

/-- A section is injective: distinct quotient elements have distinct planar
    representatives. Derived via mathlib's `Function.LeftInverse.injective`. -/
theorem injective (s : Section α) : Function.Injective s.σ :=
  s.isSection.injective

/-- The trivial section via `Quot.out`: noncomputable (classical choice).
    Useful as a default when no language-specific section is supplied. -/
noncomputable def out : Section α where
  σ := Quot.out
  isSection := Quot.out_eq

/-- **The keystone helper for singleton-class proofs.**

    For any `a : α`, the section's image of `FreeCommMagma.of a` has the
    `FreeMagma.of a` shape: `s.σ (of a) = of a`.

    **Why this lemma exists**: downstream consumers (e.g. `HeadFunction.head_leaf`,
    `outerCat_leaf`, `checkedSel_leaf`, `toNonplanar_leaf`, ...) repeatedly need to prove
    `f (s.σ (of a)) = expected` by case-analysis on `s.σ (of a)`'s `FreeMagma`
    shape — leveraging that the equivalence class of `of a` under `CommRel` is a
    singleton (no swap fires on `.of _`). Without this lemma, every consumer
    repeats the same 5-line scaffold:
    ```
    have hSec := s.isSection (of a)
    rw [mk_eq_iff_commEqv] at hSec
    match hext : s.σ (of a) with
    | .of x => exact ...
    | .mul _ _ => exact absurd hSec ...
    ```
    With this lemma, the consumer just rewrites `s.σ (of a)` to `of a` and
    continues structurally.

    Proof: composing `mk` with `s.σ` recovers the input (`isSection`); since
    the equivalence class of `of a` is a singleton modulo `CommRel`, `s.σ (of a)`
    must itself be `of a`. -/
theorem σ_of (s : Section α) (a : α) :
    s.σ (FreeCommMagma.of a) = FreeMagma.of a := by
  have hSec : FreeCommMagma.mk (s.σ (FreeCommMagma.of a))
      = (FreeCommMagma.of a : FreeCommMagma α) := s.isSection _
  rw [FreeCommMagma.mk_eq_iff_commEqv] at hSec
  -- hSec : FreeMagma.CommEqv (s.σ (of a)) (of a)
  match hext : s.σ (FreeCommMagma.of a) with
  | .of x =>
    rw [hext] at hSec
    -- hSec : x = a (CommEqv on .of cells reduces to equality)
    exact congrArg FreeMagma.of hSec
  | .mul _ _ =>
    rw [hext] at hSec
    -- absurd: CommEqv (mul _ _) (of a) is False by definition
    exact absurd hSec (by simp [FreeMagma.CommEqv])

end Section

end FreeCommMagma
