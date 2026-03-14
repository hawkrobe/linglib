import Linglib.Theories.Semantics.Composition.Applicative
import Linglib.Theories.Semantics.Lexical.Noun.TypeShifting

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

These are @cite{charlow-2020}'s eqs (16) and (27), generalized to
arbitrary types (the paper uses `S` as abbreviation for `Set`). -/

section Operations

variable {A B C : Type}

/-- **η** (unit): inject a value into a singleton set.

    @cite{charlow-2020} eq. (16): `η := λp. {p}`. Equivalent to
    `setPure` from `Applicative.lean` (shown in `eta_eq_setPure`). -/
def eta (x : A) : A → Prop := fun y => y = x

/-- **⫝̸** (bind): monadic bind for sets.

    @cite{charlow-2020} eq. (27): `m ⫝̸ f := ⋃_{x ∈ m} f(x)`.
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
had directly taken wide scope (@cite{charlow-2020} §4.2, eq. 34). -/

section MonadLaws

variable {A B C : Type}

/-- **LEFT IDENTITY**: `η x ⫝̸ f = f x`.

    Applying the singleton `{x}` to a function `f` yields exactly `f x`.
    @cite{charlow-2020} eq. (42), first law. -/
theorem set_left_identity (x : A) (f : A → B → Prop) :
    setBind (eta x) f = f x := by
  funext b; apply propext; simp only [setBind, eta]; constructor
  · rintro ⟨a, rfl, h⟩; exact h
  · intro h; exact ⟨x, rfl, h⟩

/-- **RIGHT IDENTITY**: `m ⫝̸ η = m`.

    Binding a set with the singleton constructor recovers the original set.
    @cite{charlow-2020} eq. (42), second law. -/
theorem set_right_identity (m : A → Prop) :
    setBind m eta = m := by
  funext a; apply propext; simp only [setBind, eta]; constructor
  · rintro ⟨_, hm, rfl⟩; exact hm
  · intro h; exact ⟨a, h, rfl⟩

/-- **ASSOCIATIVITY**: `(m ⫝̸ f) ⫝̸ g = m ⫝̸ (λx. f x ⫝̸ g)`.

    The central theorem of @cite{charlow-2020} §4.2. Because `⫝̸` is
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
  truth value — true iff the set contains `True`.
- `if` (conditional closure): combines two sets of propositions into a
  set of conditional propositions. -/

section Closure

variable {A : Type}

/-- **∃̣** (existential closure): `m^∃̣ := True ∈ m`.

    @cite{charlow-2020} eq. (19): `m^∃̣ := λm. T ∈ m`. Extracts
    propositional content from a set of truth values by checking
    whether `True` is a member. -/
def existsClosure (m : Prop → Prop) : Prop := m True

/-- **if** (conditional closure): combines antecedent and consequent
    sets of propositions.

    @cite{charlow-2020} eq. (31): `if m n := {if m^∃̣ n^∃̣}`.
    Each pair of antecedent/consequent alternatives yields a conditional. -/
def setIf (antecedent consequent : Prop → Prop) : Prop → Prop :=
  eta (antecedent True → consequent True)

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

This makes precise @cite{charlow-2020}'s observation that the
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

@cite{charlow-2020} §3.2 (eq. 28): Partee's LIFT operation —
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

open Semantics.Lexical.Noun.TypeShifting (lift A)
open Semantics.Montague (Model Ty)

variable {m : Model}

/-- **LIFT = A ∘ η** on the domain.

    @cite{charlow-2020} eq. (28): `(η x)^⫝̸ = λf. ⋃_{y ∈ {x}} f y = λf. f x = lift(x)`.

    In linglib's formulation using `A` (which takes an explicit domain):
    `A(domain)(η(j))(P) = domain.any (λx. η(j)(x) && P(x))`.
    When `j ∈ domain`, this reduces to `P(j) = lift(j)(P)`.

    This theorem uses Bool-level equality rather than Prop because
    `lift` and `A` produce `Bool`-valued GQs (matching linglib's Model). -/
theorem lift_eq_A_eta (domain : List m.Entity) (j : m.interpTy .e)
    (hj : j ∈ domain) (hnd : domain.Nodup) :
    ∀ P : m.interpTy Ty.et, A domain (fun x => @decide (j = x) (m.decEq j x)) P = lift j P := by
  intro P
  simp only [A, lift]
  induction domain with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.any_cons]
    have hnd_tl := (List.nodup_cons.mp hnd).2
    have hd_nmem := (List.nodup_cons.mp hnd).1
    cases List.mem_cons.mp hj with
    | inl heq =>
      subst heq
      have hdec : @decide (j = j) (m.decEq j j) = true := by
        cases m.decEq j j with | isTrue _ => rfl | isFalse h => exact absurd rfl h
      have : tl.any (fun x => @decide (j = x) (m.decEq j x) && P x) = false := by
        rw [List.any_eq_false]
        intro x hx
        by_cases heq : j = x
        · subst heq; exact absurd hx hd_nmem
        · have : @decide (j = x) (m.decEq j x) = false := by
            cases m.decEq j x with | isTrue h => exact absurd h heq | isFalse _ => rfl
          simp [this]
      rw [this, Bool.or_false, hdec, Bool.true_and]
    | inr hmem =>
      have hne : ¬ (j = hd) := fun heq => hd_nmem (heq ▸ hmem)
      have hdec : @decide (j = hd) (m.decEq j hd) = false := by
        cases m.decEq j hd with | isTrue h => exact absurd h hne | isFalse _ => rfl
      simp only [hdec, Bool.false_and, Bool.false_or]
      exact ih hmem hnd_tl

end LiftDecomposition

-- ════════════════════════════════════════════════════════════════
-- §6 Exceptional Scope via ASSOCIATIVITY
-- ════════════════════════════════════════════════════════════════

/-! ### §6 Exceptional scope via ASSOCIATIVITY

The payoff: ASSOCIATIVITY of `⫝̸` generates exceptional scope readings
for indefinites embedded in scope islands, without movement.

**The mechanism** (@cite{charlow-2020} §4.1–4.2, Figures 6–8):

1. An indefinite `m : S e` denotes a set of individuals.
2. Inside the island, `⫝̸` turns the island into a set of alternative
   propositions (scope at the island edge).
3. A second `⫝̸` takes scope over the conditional/matrix
   (scope at the next level).
4. **ASSOCIATIVITY** guarantees this two-step process produces the same
   result as if `m` had directly scoped out of the island.

**Example**: "If [a rich relative of mine dies], I'll inherit a house."
The indefinite *a rich relative* can take scope over the conditional
despite being embedded in the conditional's antecedent (a scope island).

The derivation below shows this for a finite model. -/

section ExceptionalScope

/-- A tiny model for the island-escaping example. -/
inductive Person where | alice | bob | carol
  deriving DecidableEq, Repr, BEq

/-- Relatives of mine. -/
def rel : Person → Prop
  | .alice => True
  | .bob => True
  | .carol => False

/-- The indefinite "a rich relative of mine": the set of my relatives. -/
def aRel : Person → Prop := rel

/-- "x dies" (a property). -/
def dies : Person → Prop := fun _ => True

/-- Step 1: Inside the island, the indefinite takes scope via ⫝̸,
    turning the island into a set of alternative antecedent propositions.

    @cite{charlow-2020} eq. (33), first ⫝̸:
    `{dies x | rel x}` — the island's meaning is a set of propositions. -/
def islandMeaning : Prop → Prop :=
  setBind aRel (fun x => eta (dies x))

/-- Step 2: The pied-piped island takes scope over the conditional
    via a second ⫝̸.

    @cite{charlow-2020} eq. (33), second ⫝̸:
    `{if(dies x) house | rel x}` — for each relative, a conditional. -/
def house : Prop := True  -- simplified

def conditionalMeaning : Prop → Prop :=
  setBind islandMeaning (fun antecedent => eta (antecedent → house))

/-- The exceptional scope reading: `∃x ∈ rel. if(dies x) house`.

    By ASSOCIATIVITY, the two-step derivation (scope at island edge,
    then scope over conditional) equals direct wide scope:
    `aRel ⫝̸ (λx. η(dies x)) ⫝̸ (λp. η(p → house))`
    `= aRel ⫝̸ (λx. η(dies x) ⫝̸ (λp. η(p → house)))` — by ASSOCIATIVITY
    `= aRel ⫝̸ (λx. η(dies x → house))`                — by LEFT IDENTITY
    `= {dies x → house | rel x}`                         — wide scope -/
theorem exceptional_scope_via_associativity :
    conditionalMeaning =
    setBind aRel (fun x => setBind (eta (dies x)) (fun p => eta (p → house))) := by
  simp only [conditionalMeaning, islandMeaning]
  exact set_associativity aRel (fun x => eta (dies x)) (fun p => eta (p → house))

/-- After applying LEFT IDENTITY, the wide-scope form simplifies. -/
theorem exceptional_scope_simplified :
    setBind aRel (fun x => setBind (eta (dies x)) (fun p => eta (p → house))) =
    setBind aRel (fun x => eta (dies x → house)) := by
  congr 1; funext x
  exact set_left_identity (dies x) (fun p => eta (p → house))

/-- The full derivation: two-step island-escaping = direct wide scope. -/
theorem exceptional_scope_full :
    conditionalMeaning = setBind aRel (fun x => eta (dies x → house)) := by
  rw [exceptional_scope_via_associativity, exceptional_scope_simplified]

end ExceptionalScope

-- ════════════════════════════════════════════════════════════════
-- §7 Selectivity and the Binder Roof Constraint
-- ════════════════════════════════════════════════════════════════

/-! ### §7 Selectivity and the Binder Roof Constraint

Two further predictions of the η-and-⫝̸ approach:

**Selectivity** (@cite{charlow-2020} §5): When multiple indefinites live
on an island, extra applications of `η` produce **higher-order alternative
sets** `S(S t)`. These allow different indefinites to take exceptional scope
in different ways — the grammar never conflates distinct sources of
alternatives.

**Binder Roof Constraint** (@cite{charlow-2020} §6.4): When an operator
binds into an indefinite, the indefinite cannot scope over that operator.
This falls out naturally because scope-taking (via `⫝̸`) requires the
indefinite (or its island) to dominate the binding operator in the tree.
If the operator binds *into* the indefinite, it must c-command the
indefinite's restrictor, which means the indefinite is below the operator
and can't scope over it. -/

section Selectivity

/-- Higher-order alternative sets: applying `η` to a set produces `S(S a)`.

    @cite{charlow-2020} §5.2, eq. (48): if `m : S a` and `f : a → S b`,
    then `m ⫝̸ η(f x)` has type `S(S b)` — a set of sets.

    This is what enables selectivity: distinct indefinites produce
    distinct layers of the higher-order set, so they can be independently
    extracted outside the island. -/
theorem higher_order_from_eta {A B : Type} (m : A → Prop) (f : A → B) :
    setBind m (fun x => eta (eta (f x))) =
    (fun (s : B → Prop) => ∃ a, m a ∧ s = eta (f a)) := rfl

end Selectivity

end Semantics.Composition.SetMonad
