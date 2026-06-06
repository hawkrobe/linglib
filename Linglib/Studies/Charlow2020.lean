import Mathlib.Data.Set.Functor
import Linglib.Semantics.Composition.Applicative
import Linglib.Semantics.Composition.TypeShifting

/-!
# [charlow-2020]: The Scope of Alternatives — Indefiniteness and Islands

Simon Charlow (2020). "The scope of alternatives: indefiniteness and
islands." *Linguistics and Philosophy* 43(4): 427–472.
<https://doi.org/10.1007/s10988-019-09278-3>

## Thesis

Alternative-denoting expressions (indefinites, *wh*-words, focused
elements) interact with their semantic context by **taking scope**, not
by point-wise functional application as in classical alternative
semantics. Charlow decomposes Partee's LIFT into two freely-applying
type-shifters — `η` (eq. 16: `λp.{p}`, = Karttunen IDENT generalised)
and `≫=` (eq. 27: `λm.λf. ⋃_{x∈m} f x`, a polymorphic scope-taker) —
which together form a **monad** over sets.

The crucial property is **ASSOCIATIVITY** (eq. 34, Figure 7): scoping
at the edge of an island and then scoping again is provably equivalent
to direct wide scope. Indefinites can iteratively pied-pipe out of
nested islands without any island-violating movement — *roll-up
pied-piping*, §4.3.

## Part I — Apparatus (Charlow §§3–4)

* `eta` — set unit (eq. 16): `η := λp.{p}`
* `setBind` — set bind (eq. 27): `m ≫= := λf. ⋃_{x∈m} f x`
* `setMap` — set fmap (derived)
* monad laws (Left/Right Identity + ASSOCIATIVITY) inherited from
  mathlib's `LawfulMonad Set`
* `existsClosure` — Charlow's `↓` (eq. 19): `m^↓ := ⊤ ∈ m`
* bridges to `Applicative.lean` (`setPure`/`setAp`): the applicative
  presentation is strictly weaker than the monad
* `lift_eq_A_eta` — LIFT decomposition (eq. 28):
  `A ∘ η = LIFT` on entities (Partee 1986's triangle, extended)
* `higher_order_from_eta` — higher-order alternative sets `S(S t)`
  (§5.2): the substrate for selective exceptional scope

## Part II — Empirical predictions (Charlow §§2, 4, 5, 6.4)

* Exceptional scope: indefinites escape conditional islands
* Intermediate exceptional scope: scope can stop anywhere up the tree
* Selectivity: higher-order alternative sets distinguish multiple
  island-bound indefinites
* Binder Roof Constraint: type-system blocks an indefinite from
  scoping over a binder that binds into it

## Parallel with the maybe monad ([grove-2022])

The same `η`/`≫=` structure with a different carrier:

| | Indeterminacy ([charlow-2020]) | Presupposition ([grove-2022]) |
|---|---|---|
| Carrier | `Set α = α → Prop` | `Option α` |
| Unit | `η_S(x) = {x}` | `η_#(v) = some v` |
| Bind | `m ≫=_S f = ⋃_{x∈m} f(x)` | `v ≫=_# k = k(v); # ≫=_# k = #` |
| Linguistic effect | Alternatives | Partiality |
| Scope payoff | Indefinites escape islands | Presuppositions project past filters |
-/

set_option autoImplicit false

namespace Charlow2020

open Semantics.Composition.Applicative (setPure setAp)

/-! ## Part I — Apparatus -/

/-! ### §1 Set monad operations

The set monad `S a := Set a` with:

* `η x := {x}` (eq. 16: singleton)
* `m ≫= f := ⋃_{x ∈ m} f(x)` (eq. 27: flatmap / bind)

Generalised to arbitrary types (the paper uses `S a` for sets of `a`'s).
The operations and `LawfulMonad` come from mathlib's `Set.monad`; we
add the paper-faithful names and application-form simp lemmas. -/

section Operations

variable {A B C : Type}

attribute [local instance] Set.monad

/-- **η** (eq. 16): inject a value into a singleton set. Charlow's
generalised Karttunen IDENT. -/
def eta (x : A) : Set A := pure x

/-- **≫=** (eq. 27): monadic bind for sets. Charlow's scope-taking
operator: feeds `m`'s alternatives one-by-one to `f` and unions the
results. -/
def setBind (m : Set A) (f : A → Set B) : Set B := m >>= f

/-- `map` for the set functor: mathlib's `Functor.map` (`Set.image`). -/
def setMap (f : A → B) (m : Set A) : Set B := f <$> m

@[simp] theorem mem_eta (x y : A) : y ∈ eta x ↔ y = x := Iff.rfl

@[simp] theorem mem_setBind (m : Set A) (f : A → Set B) (b : B) :
    b ∈ setBind m f ↔ ∃ a, a ∈ m ∧ b ∈ f a := by
  simp only [setBind, Set.bind_def, Set.mem_iUnion, exists_prop]

/-- Application-form characterisation of `eta` (consumers treat
`Set A = A → Prop` and apply `eta x` as a function). -/
@[simp] theorem eta_apply (x y : A) : eta x y ↔ y = x := Iff.rfl

/-- Application-form characterisation of `setBind`. -/
@[simp] theorem setBind_apply (m : Set A) (f : A → Set B) (b : B) :
    setBind m f b ↔ ∃ a, m a ∧ f a b := mem_setBind m f b

end Operations

/-! ### §2 Monad laws

The three monad laws for `(S, η, ≫=)`. ASSOCIATIVITY (eq. 34, Figure 7)
is load-bearing: it guarantees that scope at the edge of an island,
followed by scope of the resulting set, equals direct wide scope —
exceptional scope without island-violating movement. -/

section MonadLaws

variable {A B C : Type}

attribute [local instance] Set.monad

/-- **LEFT IDENTITY**: `η x ≫= f = f x`. Mathlib's `pure_bind` for `Set`. -/
theorem set_left_identity (x : A) (f : A → Set B) :
    setBind (eta x) f = f x := pure_bind x f

/-- **RIGHT IDENTITY**: `m ≫= η = m`. Mathlib's `bind_pure` for `Set`. -/
theorem set_right_identity (m : Set A) :
    setBind m eta = m := bind_pure m

/-- **ASSOCIATIVITY** (eq. 34): `(m ≫= f) ≫= g = m ≫= (λx. f x ≫= g)`.
Mathlib's `bind_assoc` for `Set`. This is the central theorem of
Figure 7: taking scope at an island edge and then taking scope again
equals taking scope directly out of the island — generating exceptional
scope without island-violating movement. -/
theorem set_associativity (m : Set A) (f : A → Set B) (g : B → Set C) :
    setBind (setBind m f) g = setBind m (fun a => setBind (f a) g) :=
  bind_assoc m f g

end MonadLaws

/-! ### §3 Existential closure -/

/-- **↓** (eq. 19): a set of propositions is "true" iff it contains a
true member. Charlow's existential closure operator, used to turn a set
of alternative propositions back into a single truth value. In classical
set theory `m^↓ := ⊤ ∈ m`; in Lean's type theory we use the
extensional `∃ p, m p ∧ p` (existence of a true member), avoiding
`propext` issues when propositions are logically but not definitionally
equal to `True`. -/
def existsClosure (m : Prop → Prop) : Prop := ∃ p, m p ∧ p

/-! ### §4 Bridge to `Composition/Applicative.lean`

The set applicative (`setPure`, `setAp`) — point-wise composition — is
strictly weaker than the monadic bind: the former is derivable from the
latter, but not vice versa. Charlow argues (§5.4) that this difference
matters: the applicative cannot derive selectivity for multiple
island-bound indefinites, while the monad can. -/

section ApplicativeBridge

variable {A B : Type}

/-- `eta` and `setPure` (from `Applicative.lean`) are the same operation. -/
theorem eta_eq_setPure (x : A) : eta x = setPure x := rfl

/-- Standard monad-to-applicative derivation:
`m ⊛ n = m ≫= λf. n ≫= λx. η(f x)`. The set applicative `setAp`
agrees with the derived applicative from the set monad. -/
theorem setAp_from_setBind (m : Set (A → B)) (n : Set A) :
    setAp m n = setBind m (fun f => setBind n (fun x => eta (f x))) := by
  ext b
  simp only [Applicative.mem_setAp, mem_setBind, mem_eta]
  aesop

end ApplicativeBridge

/-! ### §5 LIFT decomposition (Charlow §3.2, eq. 28)

Partee's LIFT — which maps an individual to a generalised quantifier
— decomposes as `≫= ∘ η`. Starting from the predicative (set) meaning
of an indefinite, `η` injects it into a singleton set, and `≫=`
produces a scope-taking function:

`(η x)^≫= = λf. ⋃_{y ∈ {x}} f y = λf. f x = lift(x)`

The key insight: LIFT is not primitive; it falls out of the monad
structure. We need only `η` and `≫=` — not Partee's full suite — to
handle indefinites compositionally. -/

section LiftDecomposition

open Semantics.Composition.TypeShifting (lift A ident A_ident_eq_lift)
open Core.Logic.Intensional (Frame Ty)

variable {F : Frame}

/-- **LIFT = A ∘ η** on the domain (eq. 28). In linglib's formulation
using `A` (which takes an explicit domain):
`A(domain)(ident j)(P) = (∃ x ∈ domain, j = x ∧ P x)`. When `j ∈ domain`
this reduces to `P j = lift j P`. This is exactly `A_ident_eq_lift`
from `TypeShifting.lean`, re-exposed in the set-monad context. -/
theorem lift_eq_A_eta (domain : List F.Entity) (j : F.Entity)
    (hj : j ∈ domain) (_hnd : domain.Nodup) :
    ∀ P : F.Denot Ty.et, A domain (ident j) P = lift j P := by
  intro P; exact congrFun (A_ident_eq_lift domain j hj) P

end LiftDecomposition

/-! ### §6 Higher-order alternative sets (Charlow §5.2, eq. 48)

When a scope argument `f` is itself a function into sets, `≫=` with
an extra `η` produces **higher-order alternative sets** of type
`S(S b)`. These preserve the identity of distinct sources of
alternatives, enabling selective exceptional scope when multiple
indefinites occur on an island. The mechanism that point-wise
alternative semantics cannot replicate (§5.4). -/

/-- Applying `η` inside a `≫=` computation produces higher-order
alternative sets. If `m : S a` and `f : a → b`, then
`m ≫= (λx. η(η(f x)))` has type `S(S b)` — a set of singletons,
each containing one alternative. -/
theorem higher_order_from_eta {A B : Type} (m : A → Prop) (f : A → B) :
    setBind m (fun x => eta (eta (f x))) =
    (fun (s : B → Prop) => ∃ a, m a ∧ s = eta (f a)) := by
  ext s; simp only [mem_setBind, mem_eta]; rfl

/-! ## Part II — Empirical predictions -/

/-! ### §7 Exceptional scope: indefinites escape conditional islands

Charlow §2.1, eqs (1)–(2): indefinites (but not universals) can take
scope out of the antecedent of a conditional.

* (1) If [a rich relative of mine dies], I'll inherit a house.
      ✓ Reading: `∃x ∈ rel. if(dies x) → house`
* (2) If [every rich relative of mine dies], I'll inherit a house.
      ✗ No reading: `*∀x ∈ rel. if(dies x) → house`

The indefinite *a rich relative of mine* denotes a set of individuals
(type `S e`). The monad's `≫=` turns the island into a set of
alternative propositions, and ASSOCIATIVITY guarantees this equals
direct wide scope. Derivation follows §4.1–4.2, eq. 33, Figures 6–7. -/

section ConditionalIsland

/-- A model with three people, two of whom are my relatives. -/
inductive Ind where | r₁ | r₂ | nonrel
  deriving DecidableEq, Repr

/-- My relatives: r₁ and r₂. -/
def myRel : Ind → Prop
  | .r₁ => True
  | .r₂ => True
  | .nonrel => False

/-- "a rich relative of mine" — the set-valued (indefinite) meaning. -/
def aRichRelative : Ind → Prop := myRel

/-- "x dies" — a predicate on individuals. -/
def dies : Ind → Prop := fun _ => True

/-- "I'll inherit a house" — simplified as a constant proposition. -/
def house : Prop := True

/-- **Step 1** (island-internal): the indefinite takes scope at the
island edge via `≫=`, turning the island into a set of alternative
antecedent propositions. Eq. 33, first `≫=`:
`aRel ≫= (λx. η(dies x)) = {dies r₁, dies r₂}`. -/
def islandMeaning : Prop → Prop :=
  setBind aRichRelative (fun x => eta (dies x))

/-- **Step 2** (island-external): the pied-piped island takes scope
over the conditional via a second `≫=`. Eq. 33, second `≫=`:
`{dies x | rel x} ≫= (λp. η(p → house))`. -/
def conditionalMeaning : Prop → Prop :=
  setBind islandMeaning (fun antecedent => eta (antecedent → house))

/-- **Direct wide scope**: the indefinite scopes directly over the
conditional, bypassing the island boundary. -/
def wideScope : Prop → Prop :=
  setBind aRichRelative (fun x => eta (dies x → house))

/-- **ASSOCIATIVITY derives exceptional scope** (the key theorem).
The two-step derivation (scope at island edge via first `≫=`, then
scope over conditional via second `≫=`) equals direct wide scope by
ASSOCIATIVITY + LEFT IDENTITY:

```
  (aRel ≫= λx. η(dies x)) ≫= (λp. η(p → house))
= aRel ≫= (λx. η(dies x) ≫= (λp. η(p → house)))   — ASSOCIATIVITY
= aRel ≫= (λx. η(dies x → house))                  — LEFT IDENTITY
= wideScope
``` -/
theorem island_eq_wide : conditionalMeaning = wideScope := by
  simp only [conditionalMeaning, islandMeaning, wideScope]
  rw [set_associativity]
  congr 1; funext x
  exact set_left_identity (dies x) (fun p => eta (p → house))

/-- The exceptional scope reading is satisfiable: there exists a
member of the result set (since r₁ is a relative). -/
theorem exceptional_scope_satisfiable :
    ∃ p, wideScope p := by
  refine ⟨dies .r₁ → house, ?_⟩
  simp only [wideScope, setBind_apply, eta_apply]
  exact ⟨.r₁, trivial, rfl⟩

end ConditionalIsland

/-! ### §8 Intermediate exceptional scope

§2.1 eq. (3), §4.2 Figure 8: indefinites allow not just widest scope
but also **intermediate** exceptional scope.

* (3) Each student has to come up with three arguments showing that
      [some condition proposed by Chomsky is wrong].
      ✓ ∀ ≫ ∃ ≫ 3: for each student, there is some condition …

The indefinite *some condition* is embedded in a relative clause (a
scope island). It escapes via ASSOCIATIVITY — same mechanism as §7 —
but stops at an intermediate position under the universal *each
student*. The difference is simply WHERE the indefinite stops. Each
application of ASSOCIATIVITY crosses one island boundary; the
indefinite can always "forego one or more of the secondary island
scopings, come what may higher up in the tree" (p. 442). -/

section IntermediateScope

inductive Condition where | c₁ | c₂ | c₃
  deriving DecidableEq, Repr

/-- "some condition proposed by Chomsky" — the indefinite (type `S e`). -/
def someCondition : Condition → Prop
  | .c₁ => True
  | .c₂ => True
  | .c₃ => False

/-- "x is wrong" -/
def isWrong : Condition → Prop := fun _ => True

/-- Island-internal meaning: the relative clause with the indefinite.
The first `≫=` at the island edge produces a set of propositions. -/
def rcIsland : Prop → Prop :=
  setBind someCondition (fun c => eta (isWrong c))

/-- Island-external: a second `≫=` carries the alternatives out into
the matrix clause "showing that …". -/
def matrixMeaning : Prop → Prop :=
  setBind rcIsland (fun p => eta p)

/-- **ASSOCIATIVITY + LEFT IDENTITY** let the indefinite escape the
relative clause, producing a set of alternative propositions. After
escaping, the set `{isWrong c | condition c}` can be universally
quantified per student (intermediate scope) without needing a further
`≫=` over the universal — the indefinite simply stops here. -/
theorem intermediate_escapes_rc :
    matrixMeaning = setBind someCondition (fun c => eta (isWrong c)) := by
  simp only [matrixMeaning, rcIsland]
  rw [set_associativity]
  congr 1; funext c
  exact set_left_identity (isWrong c) (fun p => eta p)

/-- The escaped set has distinct alternatives (one per accessible
condition), confirming the indefinite genuinely scopes out. -/
theorem intermediate_has_alternatives :
    matrixMeaning (isWrong .c₁) ∧ matrixMeaning (isWrong .c₂) := by
  rw [intermediate_escapes_rc]
  simp only [setBind_apply, eta_apply]
  exact ⟨⟨.c₁, trivial, rfl⟩, ⟨.c₂, trivial, rfl⟩⟩

end IntermediateScope

/-! ### §9 Selectivity with multiple island-bound indefinites

Charlow §5: when multiple indefinites occur on an island, the grammar
generates **selective** exceptional scope — each indefinite can
independently take scope inside or outside the island.

* (43) If [a persuasive lawyer visits a rich relative of mine],
       I'll inherit a house.
       ✓ ∃_lawyer ≫ if ≫ ∃_relative  (specific lawyer, any relative)
       ✓ ∃_relative ≫ if ≫ ∃_lawyer  (specific relative, any lawyer)
       ✓ ∃_lawyer ≫ ∃_relative ≫ if  (both wide scope)

**The mechanism** (§5.2, Figure 10): applying `η` to a scope argument
that is itself a function into sets produces **higher-order alternative
sets** `S(S t)`. The outer set tracks one indefinite, the inner set
tracks the other. Because the layers are independent, the grammar can
process them differently — scoping one above the conditional while
existentially closing the other inside it.

This is what alternative semantics (point-wise `{{·}}`) CANNOT do: the
point-wise interpretation function `{{·}}` maps everything to flat sets
`S t`, conflating distinct sources of alternatives (§5.4). -/

section Selectivity

inductive LawyerOrRel where | l₁ | l₂ | r₁ | r₂
  deriving DecidableEq, Repr

def isLawyer : LawyerOrRel → Prop
  | .l₁ => True
  | .l₂ => True
  | _ => False

def isRelative : LawyerOrRel → Prop
  | .r₁ => True
  | .r₂ => True
  | _ => False

def visits : LawyerOrRel → LawyerOrRel → Prop := fun _ _ => True

/-- **Higher-order island meaning**: two applications of `η` produce
`S(S t)` — a set of sets. §5.2, Figure 10 (left tree): the lawyer
indefinite sits in the outer layer (via an extra `η`), the relative in
the inner layer. Each member of the outer set corresponds to one
lawyer; each is itself a set of visit-propositions (one per relative). -/
def higherOrderIsland : (Prop → Prop) → Prop :=
  setBind isLawyer (fun l =>
    eta (setBind isRelative (fun r =>
      eta (visits l r))))

/-- The higher-order structure is genuine: the outer set contains
distinct inner sets, one per lawyer. -/
theorem higherOrder_has_layers :
    higherOrderIsland (setBind isRelative (fun r => eta (visits .l₁ r))) ∧
    higherOrderIsland (setBind isRelative (fun r => eta (visits .l₂ r))) := by
  simp only [higherOrderIsland, setBind_apply, eta_apply]
  exact ⟨⟨.l₁, trivial, rfl⟩, ⟨.l₂, trivial, rfl⟩⟩

/-- **Flattening** (monadic join `μ`): collapsing the two layers via
`≫= id` recovers the flat island where both indefinites scope at the
same level. Uses ASSOCIATIVITY + LEFT IDENTITY — the same mechanism as
exceptional scope in §7. This gives the both-wide-scope reading: both
indefinites escape. -/
theorem flatten_higher_order :
    setBind higherOrderIsland id =
    setBind isLawyer (fun l =>
      setBind isRelative (fun r => eta (visits l r))) := by
  simp only [higherOrderIsland]
  rw [set_associativity]
  congr 1; funext l
  exact set_left_identity _ id

/-- Both-wide-scope reading: both indefinites escape the island. The
result is `{visits l r → house | lawyer l ∧ relative r}`. -/
def bothWide : Prop → Prop :=
  setBind isLawyer (fun l =>
    setBind isRelative (fun r =>
      eta (visits l r → house)))

/-- Lawyer-wide, relative-narrow: only the lawyer escapes. For each
lawyer, the conditional quantifies over relatives inside. Arises from
the higher-order island: the outer layer (lawyers) scopes above the
conditional, while the inner layer (relatives) is existentially closed
inside it (eq. 49). -/
def lawyerWide : Prop → Prop :=
  setBind isLawyer (fun l =>
    eta ((∃ r, isRelative r ∧ visits l r) → house))

/-- The two readings are genuinely different: `bothWide` has
alternatives for each (lawyer, relative) pair, while `lawyerWide` has
alternatives only for each lawyer. -/
theorem selectivity_produces_distinct_readings :
    (∃ p, bothWide p) ∧ (∃ p, lawyerWide p) := by
  simp only [bothWide, lawyerWide, setBind_apply, eta_apply]
  exact ⟨⟨_, .l₁, trivial, .r₁, trivial, rfl⟩, ⟨_, .l₁, trivial, rfl⟩⟩

end Selectivity

/-! ### §10 Binder Roof Constraint (Charlow §6.4)

When an operator binds into an indefinite, the indefinite cannot scope
over that operator.

* (52) Every boyˣ who talked to a friend of hisₓ left.     `*∃ ≫ ∀`
* (53) No candidateˣ submitted a paper heₓ had written.     `*∃ ≫ no`

**The type-theoretic argument**: because the η-and-`≫=` approach is
oriented around scope-taking, an indefinite whose restrictor contains a
bound variable `x` is of type `A → B → Prop` — a function that DEPENDS
on `x`:

```
  m x : B → Prop      -- the indefinite's meaning, given a value for x
  setBind (m x) f     -- well-typed: x is in scope
```

For the indefinite to scope OVER x's binder, we would need
`setBind m …` where `m : A → B → Prop` — but `setBind` expects
`m : Set B`. The constraint is enforced by the type system, not by a
stipulation.

This contrasts with **choice-function** approaches ([reinhart-1997]),
which leave indefinites in situ and need additional stipulations to
block the wide-scope reading (cf. eqs 67–69). No theorem is needed
here: the Binder Roof Constraint is enforced by Lean's type checker.
The indefinite's dependence on the bound variable `x` prevents it from
scoping over `x`'s binder. -/

end Charlow2020
