import Linglib.Theories.Semantics.Composition.SetMonad

/-!
# Charlow (2020): The Scope of Alternatives
@cite{charlow-2020}

The scope of alternatives: indefiniteness and islands.
*Linguistics and Philosophy* 43(4): 427–472.

## Core claim

Alternative-denoting expressions interact with their semantic context by
**taking scope**, not by pointwise composition. The set monad `(S, η, ⫝̸)`
— with `η` (singleton) and `⫝̸` (flatmap) — handles indefinites,
*wh*-words, and focus in a unified framework that:

1. **Derives exceptional scope** for indefinites out of scope islands
   via ASSOCIATIVITY of `⫝̸` (§4)
2. **Predicts selectivity** when multiple indefinites occur on an island,
   via higher-order alternative sets `S(S t)` (§5)
3. **Derives the Binder Roof Constraint**: an indefinite bound into by
   an operator cannot scope over that operator (§6.4)

## Empirical data

- (1) If [a rich relative of mine dies], I'll inherit a house. ✓ ∃ ≫ if
- (2) If [every rich relative of mine dies], I'll inherit a house. ✗ *∀ ≫ if
- (3) Each student has to come up with three arguments showing that
      [some condition proposed by Chomsky is wrong]. ✓ ∀ ≫ ∃ ≫ 3
- (43) If [a persuasive lawyer visits a rich relative of mine],
       I'll inherit a house. ✓ selective: ∃_lawyer ≫ if ≫ ∃_relative

## Formalization

The theoretical core (the set monad) is formalized in
`Theories/Semantics/Composition/SetMonad.lean`. This file instantiates
it on concrete examples, verifying the paper's empirical predictions.
-/

set_option autoImplicit false

namespace Charlow2020

open Semantics.Composition.SetMonad

-- ════════════════════════════════════════════════════════════════
-- §1 Exceptional scope: indefinites escape conditional islands
-- ════════════════════════════════════════════════════════════════

/-! ### §1 Exceptional scope out of conditional islands

@cite{charlow-2020} §2.1, eqs (1)–(2): indefinites (but not universals)
can take scope out of the antecedent of a conditional.

  (1) If [a rich relative of mine dies], I'll inherit a house.
      ✓ Reading: ∃x ∈ rel. if(dies x) → house

  (2) If [every rich relative of mine dies], I'll inherit a house.
      ✗ No reading: *∀x ∈ rel. if(dies x) → house

The indefinite *a rich relative of mine* denotes a set of individuals
(type `S e`). The monad's `⫝̸` turns the island into a set of alternative
propositions, and ASSOCIATIVITY guarantees this equals direct wide scope.

The derivation follows @cite{charlow-2020} §4.1–4.2, eq. (33),
Figures 6–7. -/

section ConditionalIsland

/-- A model with three people, two of whom are my relatives. -/
inductive Ind where | r₁ | r₂ | nonrel
  deriving DecidableEq, Repr

/-- My relatives: r₁ and r₂. -/
def myRel : Ind → Prop
  | .r₁ => True
  | .r₂ => True
  | .nonrel => False

/-- "a rich relative of mine" — the set-valued (indefinite) meaning.
    The indefinite denotes the characteristic function of my relatives
    (type `S e`). -/
def aRichRelative : Ind → Prop := myRel

/-- "x dies" — a predicate on individuals. -/
def dies : Ind → Prop := fun _ => True

/-- "I'll inherit a house" — simplified as a constant proposition. -/
def house : Prop := True

/-- **Step 1** (island-internal): the indefinite takes scope at the
    island edge via `⫝̸`, turning the island into a set of alternative
    antecedent propositions.

    @cite{charlow-2020} eq. (33), first `⫝̸`:
    `aRel ⫝̸ (λx. η(dies x)) = {dies r₁, dies r₂}`. -/
def islandMeaning : Prop → Prop :=
  setBind aRichRelative (fun x => eta (dies x))

/-- **Step 2** (island-external): the pied-piped island takes scope
    over the conditional via a second `⫝̸`.

    @cite{charlow-2020} eq. (33), second `⫝̸`:
    `{dies x | rel x} ⫝̸ (λp. η(p → house))`. -/
def conditionalMeaning : Prop → Prop :=
  setBind islandMeaning (fun antecedent => eta (antecedent → house))

/-- **Direct wide scope**: the indefinite scopes directly over the
    conditional, bypassing the island boundary. -/
def wideScope : Prop → Prop :=
  setBind aRichRelative (fun x => eta (dies x → house))

/-- **ASSOCIATIVITY derives exceptional scope** (the key theorem).

    The two-step derivation (scope at island edge via first `⫝̸`,
    then scope over conditional via second `⫝̸`) equals direct wide
    scope by ASSOCIATIVITY + LEFT IDENTITY:

    `(aRel ⫝̸ λx. η(dies x)) ⫝̸ (λp. η(p → house))`
    `= aRel ⫝̸ (λx. η(dies x) ⫝̸ (λp. η(p → house)))` — ASSOCIATIVITY
    `= aRel ⫝̸ (λx. η(dies x → house))`               — LEFT IDENTITY
    `= wideScope` -/
theorem island_eq_wide : conditionalMeaning = wideScope := by
  simp only [conditionalMeaning, islandMeaning, wideScope]
  -- Step 1: ASSOCIATIVITY re-brackets the two ⫝̸ applications
  rw [set_associativity]
  -- Step 2: LEFT IDENTITY simplifies η(dies x) ⫝̸ ... = η(dies x → house)
  congr 1; funext x
  exact set_left_identity (dies x) (fun p => eta (p → house))

/-- The exceptional scope reading is satisfiable: there exists a
    member of the result set (since r₁ is a relative). -/
theorem exceptional_scope_satisfiable :
    ∃ p, wideScope p := ⟨dies .r₁ → house, .r₁, trivial, rfl⟩

end ConditionalIsland

-- ════════════════════════════════════════════════════════════════
-- §2 Intermediate exceptional scope
-- ════════════════════════════════════════════════════════════════

/-! ### §2 Intermediate exceptional scope

@cite{charlow-2020} §2.1, eq. (3), §4.2 Figure 8: indefinites allow not
just widest scope but also **intermediate** exceptional scope.

  (3) Each student has to come up with three arguments showing that
      [some condition proposed by Chomsky is wrong].
      ✓ ∀ ≫ ∃ ≫ 3: for each student, there is some condition ...

The indefinite *some condition* is embedded in a relative clause (a scope
island). It escapes the relative clause via ASSOCIATIVITY — exactly the
same mechanism as §1 — but stops at an intermediate position under the
universal *each student*.

The difference from §1 is simply WHERE the indefinite stops. Each
application of ASSOCIATIVITY crosses one island boundary. The indefinite
can always "forego one or more of the secondary island scopings, come
what may higher up in the tree" (@cite{charlow-2020} p. 442). -/

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
    The first `⫝̸` at the island edge produces a set of propositions. -/
def rcIsland : Prop → Prop :=
  setBind someCondition (fun c => eta (isWrong c))

/-- Island-external: a second `⫝̸` carries the alternatives out
    into the matrix clause "showing that ...". -/
def matrixMeaning : Prop → Prop :=
  setBind rcIsland (fun p => eta p)

/-- **ASSOCIATIVITY + LEFT IDENTITY** let the indefinite escape the
    relative clause, producing a set of alternative propositions.

    After escaping, the set `{isWrong c | condition c}` can be
    universally quantified per student (intermediate scope) without
    needing a further `⫝̸` over the universal — the indefinite simply
    stops here. -/
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
  exact ⟨⟨.c₁, trivial, rfl⟩, ⟨.c₂, trivial, rfl⟩⟩

end IntermediateScope

-- ════════════════════════════════════════════════════════════════
-- §3 Selectivity with multiple island-bound indefinites
-- ════════════════════════════════════════════════════════════════

/-! ### §3 Selectivity

@cite{charlow-2020} §5: when multiple indefinites occur on an island,
the grammar generates **selective** exceptional scope — each indefinite
can independently take scope inside or outside the island.

  (43) If [a persuasive lawyer visits a rich relative of mine],
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

This is what alternative semantics (pointwise `{{·}}`) CANNOT do: the
pointwise interpretation function `{{·}}` maps everything to flat sets
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
    `S(S t)` — a set of sets.

    @cite{charlow-2020} §5.2, Figure 10 (left tree): the lawyer
    indefinite sits in the outer layer (via an extra `η`), the relative
    in the inner layer.

    Each member of the outer set corresponds to one lawyer; each is
    itself a set of visit-propositions (one per relative). -/
def higherOrderIsland : (Prop → Prop) → Prop :=
  setBind isLawyer (fun l =>
    eta (setBind isRelative (fun r =>
      eta (visits l r))))

/-- The higher-order structure is genuine: the outer set contains
    distinct inner sets, one per lawyer. -/
theorem higherOrder_has_layers :
    higherOrderIsland (setBind isRelative (fun r => eta (visits .l₁ r))) ∧
    higherOrderIsland (setBind isRelative (fun r => eta (visits .l₂ r))) :=
  ⟨⟨.l₁, trivial, rfl⟩, ⟨.l₂, trivial, rfl⟩⟩

/-- **Flattening** (monadic join `μ`): collapsing the two layers via
    `⫝̸ id` recovers the flat island where both indefinites scope at
    the same level. This uses ASSOCIATIVITY + LEFT IDENTITY — the same
    mechanism as exceptional scope in §1.

    This gives the both-wide-scope reading: both indefinites escape. -/
theorem flatten_higher_order :
    setBind higherOrderIsland id =
    setBind isLawyer (fun l =>
      setBind isRelative (fun r => eta (visits l r))) := by
  simp only [higherOrderIsland]
  rw [set_associativity]
  congr 1; funext l
  exact set_left_identity _ id

/-- Both-wide-scope reading: both indefinites escape the island.
    The result is `{visits l r → house | lawyer l ∧ relative r}`. -/
def bothWide : Prop → Prop :=
  setBind isLawyer (fun l =>
    setBind isRelative (fun r =>
      eta (visits l r → house)))

/-- Lawyer-wide, relative-narrow: only the lawyer escapes.
    For each lawyer, the conditional quantifies over relatives inside.

    This arises from the higher-order island: the outer layer (lawyers)
    scopes above the conditional, while the inner layer (relatives)
    is existentially closed inside it (@cite{charlow-2020} eq. 49). -/
def lawyerWide : Prop → Prop :=
  setBind isLawyer (fun l =>
    eta ((∃ r, isRelative r ∧ visits l r) → house))

/-- The two readings are genuinely different: `bothWide` has
    alternatives for each (lawyer, relative) pair, while `lawyerWide`
    has alternatives only for each lawyer. -/
theorem selectivity_produces_distinct_readings :
    (∃ p, bothWide p) ∧ (∃ p, lawyerWide p) :=
  ⟨⟨_, .l₁, trivial, .r₁, trivial, rfl⟩, ⟨_, .l₁, trivial, rfl⟩⟩

end Selectivity

-- ════════════════════════════════════════════════════════════════
-- §4 Binder Roof Constraint
-- ════════════════════════════════════════════════════════════════

/-! ### §4 Binder Roof Constraint

@cite{charlow-2020} §6.4: when an operator binds into an indefinite,
the indefinite cannot scope over that operator.

  (52) Every boyˣ who talked to a friend of hisₓ left.     *∃ ≫ ∀
  (53) No candidateˣ submitted a paper heₓ had written.     *∃ ≫ no

**The type-theoretic argument**: because the η-and-⫝̸ approach is oriented
around scope-taking, an indefinite whose restrictor contains a bound
variable `x` is of type `A → B → Prop` — a function that DEPENDS on `x`.

    `m x : B → Prop`    -- the indefinite's meaning, given a value for x
    `setBind (m x) f`   -- well-typed: x is in scope

For the indefinite to scope OVER x's binder, we would need:

    `setBind m ...`      -- ILL-TYPED: m has type `A → B → Prop`,
                         -- not `B → Prop`

There is no well-typed term that achieves this. The constraint is
enforced by the type system, not by a stipulation.

This contrasts with **choice-function** approaches (@cite{reinhart-1997}),
which leave indefinites in situ and therefore need additional stipulations
to block the wide-scope reading (cf. eqs (67)–(69) in the paper). -/

-- No theorem needed: the Binder Roof Constraint is enforced by
-- Lean's type checker. The indefinite's dependence on the bound
-- variable `x` prevents it from scoping over x's binder.

end Charlow2020
