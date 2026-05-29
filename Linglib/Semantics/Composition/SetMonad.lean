import Mathlib.Data.Set.Functor
import Linglib.Semantics.Composition.Applicative
import Linglib.Semantics.Composition.TypeShifting

/-!
# The Set Monad: Indeterminacy and Scope
@cite{charlow-2020}

Alternative-denoting expressions (indefinites, *wh*-words, focused elements)
interact with their semantic context by **taking scope**. @cite{charlow-2020}
shows that this can be accomplished by decomposing Partee's LIFT into two
freely-applying type-shifters — `η` (unit, = IDENT generalized) and `⫝̸`
(bind, = a polymorphic scope-taker) — that together form a **monad** over
sets.

The set monad `(S, η, ⫝̸)` is the "indeterminacy" effect from
@cite{bumford-charlow-2024}'s effect taxonomy. Its key property is
**ASSOCIATIVITY**: because `⫝̸` is
associative (monad law), indefinites can iteratively take scope out of
nested islands via scopal pied-piping, without any island-violating
movement.

## Organization

- **§1** Set monad operations: `η` (pure/unit), `⫝̸` (bind), `map`
- **§2** Monad laws: left identity, right identity, ASSOCIATIVITY
- **§3** Closure operators: `∃̣` (existential closure), `if` (conditional)
- **§4** Bridge to Applicative.lean: `setAp` derives from `setBind` + `setPure`
- **§5** LIFT decomposition: `lift = A ∘ η` (Partee's triangle, eq. 28)
- **§6** Exceptional scope: ASSOCIATIVITY derives island-escaping readings
-/

set_option autoImplicit false

namespace Semantics.Composition.SetMonad

open Semantics.Composition.Applicative (setPure setAp)

-- ════════════════════════════════════════════════════════════════
-- §1 Set Monad Operations
-- ════════════════════════════════════════════════════════════════

/-! ### §1 Set monad operations

The set monad `S a := a → Prop` with:
- `η x := {x}` (singleton set)
- `m ⫝̸ f := ⋃_{x ∈ m} f(x)` (flatmap / bind)

These are eqs (16) and (27), generalized to
arbitrary types (the paper uses `S` as abbreviation for `Set`). -/

section Operations

variable {A B C : Type}

attribute [local instance] Set.monad

/-- **η** (unit): inject a value into a singleton set.

    eq. (16): `η := λp. {p}`. This is mathlib's `Set`-monad `pure` (the
    singleton `{x}`); the monad is not re-implemented here. -/
def eta (x : A) : Set A := pure x

/-- **⫝̸** (bind): monadic bind for sets.

    eq. (27): `m ⫝̸ f := ⋃_{x ∈ m} f(x)`. This is mathlib's `Set`-monad
    bind (`Mathlib.Data.Set.Functor`'s `Set.monad`). -/
def setBind (m : Set A) (f : A → Set B) : Set B := m >>= f

/-- `map` for the set functor: mathlib's `Functor.map` (`Set.image`). -/
def setMap (f : A → B) (m : Set A) : Set B := f <$> m

@[simp] theorem mem_eta (x y : A) : y ∈ eta x ↔ y = x := Iff.rfl

@[simp] theorem mem_setBind (m : Set A) (f : A → Set B) (b : B) :
    b ∈ setBind m f ↔ ∃ a, a ∈ m ∧ b ∈ f a := by
  simp only [setBind, Set.bind_def, Set.mem_iUnion, exists_prop]

/-- Application-form characterisation of `eta` (for consumers that treat
    `Set A = A → Prop` and apply `eta x` as a function). -/
@[simp] theorem eta_apply (x y : A) : eta x y ↔ y = x := Iff.rfl

/-- Application-form characterisation of `setBind` (for consumers that apply
    `setBind m f` as a function `B → Prop`). -/
@[simp] theorem setBind_apply (m : Set A) (f : A → Set B) (b : B) :
    setBind m f b ↔ ∃ a, m a ∧ f a b := mem_setBind m f b

end Operations

-- ════════════════════════════════════════════════════════════════
-- §2 Monad Laws
-- ════════════════════════════════════════════════════════════════

/-! ### §2 Monad laws

The three monad laws for `(S, η, ⫝̸)`. ASSOCIATIVITY (the third law)
is the key property: it guarantees that an indefinite can iteratively
scope out of nested islands, and that the result is the same as if it
had directly taken wide scope (§4.2, eq. 34). -/

section MonadLaws

variable {A B C : Type}

attribute [local instance] Set.monad

/-- **LEFT IDENTITY**: `η x ⫝̸ f = f x`. mathlib's `pure_bind` for `Set`.
    eq. (42), first law. -/
theorem set_left_identity (x : A) (f : A → Set B) :
    setBind (eta x) f = f x := pure_bind x f

/-- **RIGHT IDENTITY**: `m ⫝̸ η = m`. mathlib's `bind_pure` for `Set`.
    eq. (42), second law. -/
theorem set_right_identity (m : Set A) :
    setBind m eta = m := bind_pure m

/-- **ASSOCIATIVITY**: `(m ⫝̸ f) ⫝̸ g = m ⫝̸ (λx. f x ⫝̸ g)`. mathlib's
    `bind_assoc` for `Set`.

    The central theorem of §4.2: because `⫝̸` is associative (a monad law
    `Set` already satisfies via `LawfulMonad Set`), taking scope at the edge
    of an island and then taking scope again equals taking scope directly out
    of the island — generating exceptional scope without island-violating
    movement (eq. 34, Figure 7). -/
theorem set_associativity (m : Set A) (f : A → Set B) (g : B → Set C) :
    setBind (setBind m f) g = setBind m (fun a => setBind (f a) g) :=
  bind_assoc m f g

end MonadLaws

-- ════════════════════════════════════════════════════════════════
-- §3 Closure Operators
-- ════════════════════════════════════════════════════════════════

/-! ### §3 Closure operators

Operations that **discharge** sets of alternatives, turning them into
propositions or combining them with other sets.

- `∃̣` (existential closure): turns a set of truth values into a single
  truth value — true iff the set contains a true member. -/

section Closure

variable {A : Type}

/-- **∃̣** (existential closure): a set of propositions is "true" iff
    it contains a true member.

    eq. (19): `m^∃̣ := T ∈ m`. In classical set
    theory this checks whether `True` is literally in the set. In Lean's
    type theory, we use `∃ p, m p ∧ p` (there exists a true member),
    which avoids `propext` issues when propositions are logically but
    not definitionally equal to `True`. -/
def existsClosure (m : Prop → Prop) : Prop := ∃ p, m p ∧ p

end Closure

-- ════════════════════════════════════════════════════════════════
-- §4 Bridge to Applicative.lean
-- ════════════════════════════════════════════════════════════════

/-! ### §4 Bridge to Applicative.lean

The set applicative (`setPure`, `setAp`) from `Applicative.lean` is a
consequence of the set monad. This section proves that:

1. `eta` = `setPure` (same operation, same type)
2. `setAp` derives from `setBind` + `eta` (the standard monad→applicative
   derivation)

This makes precise observation that the
pointwise composition of alternative semantics (the applicative `⊛`)
is strictly weaker than scope-taking composition (the monadic `⫝̸`):
the former is derivable from the latter, but not vice versa. -/

section ApplicativeBridge

variable {A B : Type}

/-- `eta` and `setPure` are the same operation. -/
theorem eta_eq_setPure (x : A) : eta x = setPure x := rfl

/-- The standard monad-to-applicative derivation:
    `m ⊛ n = m ⫝̸ λf. n ⫝̸ λx. η(f x)`.

    The set applicative `setAp` from Applicative.lean agrees with the
    derived applicative from the set monad. -/
theorem setAp_from_setBind (m : (A → B) → Prop) (n : A → Prop) :
    setAp m n = setBind m (fun f => setBind n (fun x => eta (f x))) := by
  funext b
  apply propext
  show (∃ f, m f ∧ ∃ x, n x ∧ f x = b)
      ↔ b ∈ setBind m (fun f => setBind n (fun x => eta (f x)))
  simp only [mem_setBind, mem_eta]
  constructor
  · rintro ⟨f, hf, x, hx, rfl⟩; exact ⟨f, hf, x, hx, rfl⟩
  · rintro ⟨f, hf, x, hx, rfl⟩; exact ⟨f, hf, x, hx, rfl⟩

end ApplicativeBridge

-- ════════════════════════════════════════════════════════════════
-- §5 LIFT Decomposition
-- ════════════════════════════════════════════════════════════════

/-! ### §5 LIFT decomposition

§3.2 (eq. 28): Partee's LIFT operation —
which maps an individual to a generalized quantifier — decomposes
as `⫝̸ ∘ η`. Starting from the predicative (set) meaning of an
indefinite, `η` injects it into a singleton set, and `⫝̸` produces
a scope-taking function.

More precisely: for an entity `j`, `lift(j) = A(η(j))` where `A`
is Partee's existential type-shifter (TypeShifting.lean) and `η`
is the set monad's unit.

The key insight: LIFT need not be a primitive. It falls out of the
monad structure. This means we need only `η` and `⫝̸` — not the
full suite of Partee's type-shifters (`η`, `A`, `+wh`) — to handle
indefinites compositionally. -/

section LiftDecomposition

open Semantics.Composition.TypeShifting (lift A ident A_ident_eq_lift)
open Core.Logic.Intensional (Frame Ty)

variable {F : Frame}

/-- **LIFT = A ∘ η** on the domain.

    eq. (28): `(η x)^⫝̸ = λf. ⋃_{y ∈ {x}} f y = λf. f x = lift(x)`.

    In linglib's formulation using `A` (which takes an explicit domain):
    `A(domain)(ident(j))(P) = (∃ x ∈ domain, j = x ∧ P x)`.
    When `j ∈ domain`, this reduces to `P(j) = lift(j)(P)`.

    This is exactly `A_ident_eq_lift` from TypeShifting.lean, re-exported
    here in the set monad context. -/
theorem lift_eq_A_eta (domain : List F.Entity) (j : F.Entity)
    (hj : j ∈ domain) (_hnd : domain.Nodup) :
    ∀ P : F.Denot Ty.et, A domain (ident j) P = lift j P := by
  intro P; exact congrFun (A_ident_eq_lift domain j hj) P

end LiftDecomposition

-- ════════════════════════════════════════════════════════════════
-- §6 Higher-Order Alternative Sets
-- ════════════════════════════════════════════════════════════════

/-! ### §6 Higher-order alternative sets

§5.2, eq. (48): when a scope argument `f` is itself
a function into sets, `⫝̸` with an extra `η` produces **higher-order
alternative sets** of type `S(S b)`. These preserve the identity of
distinct sources of alternatives, enabling selective exceptional scope
when multiple indefinites occur on an island.

See `Studies/Charlow2020.lean` for worked derivations
of exceptional scope, selectivity, and the Binder Roof Constraint. -/

section HigherOrder

/-- Applying `η` inside a `⫝̸` computation produces higher-order
    alternative sets: the result is of type `S(S b)`, a set of sets.

    §5.2, eq. (48): if `m : S a` and `f : a → b`,
    then `m ⫝̸ (λx. η(η(f x)))` has type `S(S b)`. Each member of the
    outer set is a singleton containing one alternative. -/
theorem higher_order_from_eta {A B : Type} (m : A → Prop) (f : A → B) :
    setBind m (fun x => eta (eta (f x))) =
    (fun (s : B → Prop) => ∃ a, m a ∧ s = eta (f a)) := by
  ext s; simp only [mem_setBind, mem_eta]; rfl

end HigherOrder

end Semantics.Composition.SetMonad
