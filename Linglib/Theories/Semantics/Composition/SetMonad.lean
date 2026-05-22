import Linglib.Theories.Semantics.Composition.Applicative
import Linglib.Theories.Semantics.Composition.TypeShifting

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

/-- **η** (unit): inject a value into a singleton set.

    eq. (16): `η := λp. {p}`. Equivalent to
    `setPure` from `Applicative.lean` (shown in `eta_eq_setPure`). -/
def eta (x : A) : A → Prop := fun y => y = x

/-- **⫝̸** (bind): monadic bind for sets.

    eq. (27): `m ⫝̸ f := ⋃_{x ∈ m} f(x)`.
    For each element `a` in the set `m`, apply `f` to get a new set,
    then take the union of all results. -/
def setBind (m : A → Prop) (f : A → B → Prop) : B → Prop :=
  fun b => ∃ a, m a ∧ f a b

/-- `map` for the set functor, derived from `η` and `⫝̸`. -/
def setMap (f : A → B) (m : A → Prop) : B → Prop :=
  setBind m (fun a => eta (f a))

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

/-- **LEFT IDENTITY**: `η x ⫝̸ f = f x`.

    Applying the singleton `{x}` to a function `f` yields exactly `f x`.
    eq. (42), first law. -/
theorem set_left_identity (x : A) (f : A → B → Prop) :
    setBind (eta x) f = f x := by
  funext b; apply propext; simp only [setBind, eta]; constructor
  · rintro ⟨a, rfl, h⟩; exact h
  · intro h; exact ⟨x, rfl, h⟩

/-- **RIGHT IDENTITY**: `m ⫝̸ η = m`.

    Binding a set with the singleton constructor recovers the original set.
    eq. (42), second law. -/
theorem set_right_identity (m : A → Prop) :
    setBind m eta = m := by
  funext a; apply propext; simp only [setBind, eta]; constructor
  · rintro ⟨_, hm, rfl⟩; exact hm
  · intro h; exact ⟨a, h, rfl⟩

/-- **ASSOCIATIVITY**: `(m ⫝̸ f) ⫝̸ g = m ⫝̸ (λx. f x ⫝̸ g)`.

    The central theorem of §4.2. Because `⫝̸` is
    associative, taking scope at the edge of an island (one application
    of `⫝̸`) and then taking scope at the next level (another `⫝̸`) is
    equivalent to taking scope directly out of the island. This is what
    generates exceptional scope readings without island-violating movement.

    Concretely (eq. 34): `(m ⫝̸ λx. f x) ⫝̸ g = m ⫝̸ (λx. f x ⫝̸ g)`
    guarantees that the tree on the left of Figure 7 (local scope at the
    island edge, then further scope) equals the tree on the right (direct
    wide scope). -/
theorem set_associativity (m : A → Prop) (f : A → B → Prop) (g : B → C → Prop) :
    setBind (setBind m f) g = setBind m (fun a => setBind (f a) g) := by
  funext c; apply propext; simp only [setBind]; constructor
  · rintro ⟨b, ⟨a, hma, hfab⟩, hgbc⟩; exact ⟨a, hma, b, hfab, hgbc⟩
  · rintro ⟨a, hma, b, hfab, hgbc⟩; exact ⟨b, ⟨a, hma, hfab⟩, hgbc⟩

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
  funext b; apply propext
  -- setAp: ∃ f, m f ∧ ∃ x, n x ∧ f x = b
  -- setBind: ∃ f, m f ∧ ∃ x, n x ∧ b = f x  (eta reverses eq order)
  exact ⟨fun ⟨f, hf, x, hx, h⟩ => ⟨f, hf, x, hx, h.symm⟩,
         fun ⟨f, hf, x, hx, h⟩ => ⟨f, hf, x, hx, h.symm⟩⟩

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
    (fun (s : B → Prop) => ∃ a, m a ∧ s = eta (f a)) := rfl

end HigherOrder

end Semantics.Composition.SetMonad
