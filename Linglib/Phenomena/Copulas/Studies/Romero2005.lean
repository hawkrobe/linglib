import Linglib.Core.Semantics.Intension
import Linglib.Core.Semantics.Proposition
import Linglib.Theories.Semantics.Attitudes.Intensional
import Linglib.Theories.Semantics.Attitudes.Doxastic

/-!
# Romero (2005): Concealed Questions and Specificational Subjects
@cite{romero-2005}

Concealed Questions and Specificational Subjects.
*Linguistics and Philosophy* 28(6):687–737.

## Core Claims

1. **Epistemic `know` is intensional** w.r.t. its object position. The semantic
   argument of `know` is an intensional object obtained from either the
   *extension* (Reading A) or the *intension* (Reading B) of the complement NP.

2. **Specificational `be` is intensional** w.r.t. its subject position.
   The same extension/intension choice applies to the subject NP of
   specificational copular sentences, yielding the same A/B ambiguity.

3. Three purely extensional accounts (evaluation world, trace type ambiguity,
   pragmatic) are refuted for both concealed questions and specificational
   subjects.

## The A/B Ambiguity (@cite{heim-1979})

"John knows the price that Fred knows."

- **Reading A**: John knows the same price question Fred knows —
  e.g., both know how much the milk costs.
- **Reading B**: John knows *which* price question Fred knows —
  e.g., John knows that the question Fred knows the answer to is
  "How much does the milk cost?", but John need not know the answer himself.

## Lexical Entries

Two crosscategorial variants of `know` (Romero (29b,c)):

- `know₁ : ⟨⟨s,e⟩, ⟨e, ⟨s,t⟩⟩⟩` — for ⟨s,e⟩ (individual concept) arguments
- `know₂ : ⟨⟨s,⟨s,e⟩⟩, ⟨e, ⟨s,t⟩⟩⟩` — for ⟨s,⟨s,e⟩⟩ (concept of concepts) arguments

Parallel entries for specificational `be` (Romero (67a,b)):

- `be₁_spec : ⟨e, ⟨⟨s,e⟩, ⟨s,t⟩⟩⟩` — Reading A (extension of SS NP)
- `be₂_spec : ⟨⟨s,e⟩, ⟨⟨s,⟨s,e⟩⟩, ⟨s,t⟩⟩⟩` — Reading B (intension of SS NP)

## Relation to Modern Frameworks

@cite{uegaki-2019} argues for a *question-oriented* semantics where all
complement-taking predicates select for propositional concepts `⟨s,⟨s,t⟩⟩`.
Under that view, `know₁`/`know₂` are subcases of a single entry taking a
question meaning. Romero's A/B data remains the key empirical test for any
such unification. See also @cite{ciardelli-groenendijk-roelofsen-2018} for
an inquisitive-semantics approach to the same unification.
-/

namespace Phenomena.Copulas.Studies.Romero2005

open Core.Proposition (World4)
open Core (Intension)
open Semantics.Attitudes.Doxastic (AccessRel boxAt)

/-! ## World and Entity Setup -/

abbrev W := World4
abbrev E := Fin 4

instance : DecidableEq E := inferInstance
instance : BEq E := inferInstance

/-- All worlds in the model. -/
def worlds : List W := [.w0, .w1, .w2, .w3]

/-- All entities in the model (prices / question-answers). -/
def entities : List E := [0, 1, 2, 3]

/-! ## Doxastic Accessibility

Accessibility relations for two agents (John = 0, Fred = 1). -/

/-- Agent identifiers. -/
abbrev john : E := 0
abbrev fred : E := 1

/-- Doxastic accessibility: `Dox agent w w'` means `w'` is compatible with
    what `agent` believes/knows in `w`. -/
def Dox : E → W → W → Bool
  -- John's beliefs: in w0, John's doxastic alternatives are {w0}
  -- (he knows everything relevant)
  | 0, .w0, .w0 => true
  | 0, .w0, _   => false
  -- In w1, John's doxastic alternatives are {w1}
  | 0, .w1, .w1 => true
  | 0, .w1, _   => false
  -- In w2, John's doxastic alternatives are {w2, w3}
  -- (he doesn't distinguish w2 from w3)
  | 0, .w2, .w2 => true
  | 0, .w2, .w3 => true
  | 0, .w2, _   => false
  | 0, .w3, .w2 => true
  | 0, .w3, .w3 => true
  | 0, .w3, _   => false
  -- Fred's beliefs: partition worlds by milk price.
  -- At each w, Fred's alternatives are exactly those w' where priceMilk agrees.
  -- w0,w2 → price 0; w1 → price 1; w3 → price 2.
  | 1, .w0, .w0 => true
  | 1, .w0, .w2 => true
  | 1, .w0, _   => false
  | 1, .w1, .w1 => true
  | 1, .w1, _   => false
  | 1, .w2, .w0 => true
  | 1, .w2, .w2 => true
  | 1, .w2, _   => false
  | 1, .w3, .w3 => true
  | 1, .w3, _   => false
  -- Other agents: trivial
  | _, w, w'  => w == w'

/-- `Dox` is an `AccessRel` — connecting to the theory-layer doxastic
    infrastructure in `Semantics.Attitudes.Doxastic`. -/
abbrev DoxRel : AccessRel W E := Dox

/-! ## Individual Concepts (Price Functions)

A "price" is an individual concept: a function from worlds to entities.
"The price of milk" maps each world to the price of milk in that world.
"The price of oil" maps each world to the price of oil in that world. -/

/-- Price of milk: varies across worlds. -/
def priceMilk : Intension W E
  | .w0 => 0  -- $1.79
  | .w1 => 1  -- $2.49
  | .w2 => 0  -- $1.79
  | .w3 => 2  -- $3.00

/-- Price of oil: constant across all worlds. -/
def priceOil : Intension W E
  | _ => 3  -- $4.99

instance : BEq (Intension W E) where
  beq f g := worlds.all λ w => f w == g w

/-! ## Romero's Lexical Entries

### `know₁` and `know₂` (Romero (29b,c))

These are crosscategorial variants: they perform the same doxastic-universal
operation but differ in the type of their first argument.

- `know₁` takes an individual concept `y : ⟨s,e⟩` and checks that its value
  is correctly identified across all doxastic alternatives.
- `know₂` takes a concept of individual concepts `y : ⟨s,⟨s,e⟩⟩` and checks
  that the *meta-question* answer is correctly identified. -/

/-- ⟦know₁⟧(y_{⟨s,e⟩})(x_e)(w_s) = 1 iff ∀w' ∈ Dox_x(w). y(w') = y(w)

    The agent `x` knows the value of individual concept `y`:
    in all doxastic alternatives, `y` yields the same value as in actuality. -/
def know₁ (y : W → E) (x : E) (w : W) : Bool :=
  worlds.all λ w' => !Dox x w w' || y w' == y w

/-- ⟦know₂⟧(y_{⟨s,⟨s,e⟩⟩})(x_e)(w_s) = 1 iff ∀w' ∈ Dox_x(w). y(w') = y(w)

    The agent `x` knows the value of a *concept of individual concepts* `y`:
    in all doxastic alternatives, the meta-question `y` yields the same
    individual concept as in actuality. Same operation, higher type. -/
def know₂ (y : W → (W → E)) (x : E) (w : W) : Bool :=
  worlds.all λ w' => !Dox x w w' || y w' == y w

/-! ### Connection to Doxastic Theory Layer

`know₁` is a specialization of `Doxastic.boxAt`: universal quantification
over doxastic alternatives with a specific proposition `y(w') = y(w)`. -/

/-- `know₁` is `boxAt` applied to the identity proposition `y(w') = y(w)`. -/
theorem know₁_eq_boxAt (y : W → E) (x : E) (w : W) :
    know₁ y x w = boxAt DoxRel x w worlds (λ w' => y w' == y w) := rfl

/-! ### `be₁_spec` and `be₂_spec` (Romero (67a,b))

Specificational `be` is an intensional verb w.r.t. its subject position.

- `be₁_spec` takes the NP's extension (an individual concept) and a
  post-copular entity, and checks identity at the evaluation world.
- `be₂_spec` takes the NP's intension (a concept of concepts) and a
  post-copular individual concept, and checks identity at the evaluation world. -/

/-- ⟦be₁_spec⟧(x_e)(y_{⟨s,e⟩})(w_s) = 1 iff y(w) = x

    Reading A: the individual concept `y` (extension of the SS NP) has
    value `x` at the actual world `w`. -/
def be₁_spec (x : E) (y : W → E) (w : W) : Bool :=
  y w == x

/-- ⟦be₂_spec⟧(x_{⟨s,e⟩})(y_{⟨s,⟨s,e⟩⟩})(w_s) = 1 iff y(w) = x

    Reading B: the concept-of-concepts `y` (intension of the SS NP) has
    value `x` (an individual concept) at the actual world `w`. -/
def be₂_spec (x : W → E) (y : W → (W → E)) (w : W) : Bool :=
  y w == x

/-! ## The A/B Ambiguity: "John knows the price that Fred knows"

The CQ NP "the price that Fred knows" has:
- **Extension** at `w`: the unique price concept whose value Fred knows at `w`.
- **Intension**: the function mapping each world to that extension.

In our model, Fred knows `priceMilk` (his Dox-alternatives all agree on milk
prices). So the NP's extension is `priceMilk` at every world. -/

/-- Extension of "the price that Fred knows" at world `w`:
    the unique price individual concept `y` such that Fred knows `y` at `w`.
    In our model, Fred knows `priceMilk` at every world (`fred_knows_milk`),
    so this is constant. -/
def thePriceFredKnows (_w : W) : W → E := priceMilk

/-- Fred knows the price of milk at all worlds. -/
theorem fred_knows_milk : ∀ w : W, know₁ priceMilk fred w = true := by
  intro w; simp only [know₁, Dox, worlds]; cases w <;> native_decide

/-- Reading A: ⟦know₁⟧ + extension of NP.

    "John knows the same price as Fred" — both know how much the milk costs.
    At w0, John's Dox = {w0}, and priceMilk w0 = 0 = priceMilk w0. -/
theorem readingA_w0 :
    know₁ (thePriceFredKnows .w0) john .w0 = true := by native_decide

/-- Reading A fails at w2: John doesn't know the milk price (his Dox
    alternatives w2 and w3 assign different milk prices). -/
theorem readingA_w2 :
    know₁ (thePriceFredKnows .w2) john .w2 = false := by native_decide

/-- The intension of "the price that Fred knows": maps each world to the
    individual concept that Fred knows at that world. In our model this is
    constant (Fred always knows priceMilk). -/
def thePriceFredKnows_intension : W → (W → E) :=
  λ _ => priceMilk

/-- Reading B: ⟦know₂⟧ + intension of NP.

    "John knows which price question Fred knows the answer to."
    At w2, John's Dox = {w2, w3}. The intension maps both to `priceMilk`.
    So `know₂` checks: ∀w' ∈ Dox(john, w2). thePriceFredKnows_intension w' =
    thePriceFredKnows_intension w2. Both map to priceMilk.

    Note: Reading B is true at w2 even though Reading A is false — John knows
    *which* question Fred knows (the milk price question) without knowing the
    actual milk price. This is the key empirical difference. -/
theorem readingB_w2 :
    know₂ thePriceFredKnows_intension john .w2 = true := by native_decide

/-- The two readings genuinely differ: A is false but B is true at w2. -/
theorem readings_differ :
    know₁ (thePriceFredKnows .w2) john .w2 = false ∧
    know₂ thePriceFredKnows_intension john .w2 = true := by
  exact ⟨readingA_w2, readingB_w2⟩

/-! ## Refutation of Account 1: Evaluation World

Romero §2.4.1: Can the A/B ambiguity be derived by evaluating the NP's
extension at different world variables? The answer is no.

The formula has only two possible world binders: `λw` (top) and `∀w'`
(from `know`). Binding by `λw` gives Reading A. Binding by `∀w'` gives
a formula that is NOT Reading B — it requires John to also know the answer
to the price question, which Reading B does not require. -/

/-- Account 1's "Reading B" candidate (Romero (37)): evaluate the NP at the
    bound doxastic variable `w'` instead of the matrix `w`.

    ∀w' ∈ Dox(john, w). [the price Fred knows at w'](w') =
                         [the price Fred knows at w'](w)

    The NP extension is computed at `w'`, yielding a single IC, which is then
    compared at worlds `w'` and `w`. But this is NOT Reading B because it
    still requires John to track the actual price.

    Note: in our model, `thePriceFredKnows` is constant, so the second argument
    `(thePriceFredKnows w') w` equals `priceMilk w` regardless. For non-constant
    NP extensions, this formula and the paper's (37) would further diverge. -/
def account1_readingB (w : W) : Bool :=
  worlds.all λ w' =>
    !Dox john w w' || (thePriceFredKnows w') w' == (thePriceFredKnows w') w

/-- Account 1 collapses: its "Reading B" candidate equals Reading A.

    Because `thePriceFredKnows` is constant (`priceMilk` at every world),
    both `(thePriceFredKnows w') w'` and `(thePriceFredKnows w') w` reduce to
    `priceMilk w'` and `priceMilk w` respectively. The formula reduces to
    `∀w' ∈ Dox(john, w). priceMilk w' = priceMilk w` — which is exactly
    `know₁ priceMilk john w`. The evaluation world trick doesn't help. -/
theorem account1_equals_readingA :
    ∀ w : W, account1_readingB w = know₁ (thePriceFredKnows w) john w := by
  intro w; cases w <;> native_decide

/-! ## Specificational Subjects: Parallel Ambiguity

"The price that Fred thought was $1.29 was (actually) $1.79."

Reading A: The question whose answer Fred thought was $1.29 has actual
answer $1.79 (e.g., Fred thought milk costs $1.29; it actually costs $1.79).

Reading B: The *question* Fred thought had answer $1.29 was the milk-price
question (and milk actually costs $1.79).

The same extension/intension mechanism applies to `be`. -/

/-- Specificational `be` Reading A: extension of SS NP + `be₁_spec`. -/
theorem spec_readingA :
    be₁_spec (priceMilk .w0) priceMilk .w0 = true := by native_decide

/-- Specificational `be` Reading B: intension of SS NP + `be₂_spec`. -/
theorem spec_readingB :
    be₂_spec priceMilk thePriceFredKnows_intension .w0 = true := by native_decide

/-! ## Crosscategorial Uniformity

`know₁` and `know₂` perform the same operation — doxastic universal
quantification with identity check — at different types. They are
crosscategorial variants in the sense of @cite{partee-rooth-1983}. -/

/-- Generic doxastic knowledge template: ∀w' ∈ Dox(x,w). y(w') = y(w).
    Both `know₁` (at type `E`) and `know₂` (at type `W → E`) instantiate
    this template — same operation, different type parameter. -/
def knowGeneric {α : Type} [BEq α] (y : W → α) (x : E) (w : W) : Bool :=
  worlds.all λ w' => !Dox x w w' || y w' == y w

/-- `know₁` is `knowGeneric` at type `E`. -/
theorem know₁_is_knowGeneric (y : W → E) (x : E) (w : W) :
    know₁ y x w = knowGeneric y x w := rfl

/-- `know₂` is `knowGeneric` at type `W → E`. -/
theorem know₂_is_knowGeneric (y : W → (W → E)) (x : E) (w : W) :
    know₂ y x w = knowGeneric y x w := rfl

/-- Similarly, `be₁_spec` and `be₂_spec` share a template at different types. -/
def beGeneric {α : Type} [BEq α] (x : α) (y : W → α) (w : W) : Bool := y w == x

theorem be₁_is_beGeneric (x : E) (y : W → E) (w : W) :
    be₁_spec x y w = beGeneric x y w := rfl

theorem be₂_is_beGeneric (x : W → E) (y : W → (W → E)) (w : W) :
    be₂_spec x y w = beGeneric x y w := rfl

/-! ## Individual Concepts Are Not Rigid

The A/B ambiguity only arises when the individual concept is non-rigid
(varies across worlds). For rigid designators (proper names), extension =
intension (up to type), so the two readings collapse. -/

/-- Oil price is rigid — the two readings of "John knows the price of oil"
    would be equivalent. -/
theorem oil_rigid : Core.Intension.IsRigid (W := W) priceOil :=
  λ _ _ => rfl

/-- Milk price is NOT rigid — the two readings genuinely differ. -/
theorem milk_not_rigid : ¬ Core.Intension.IsRigid (W := W) priceMilk := by
  intro h; exact absurd (h .w0 .w1) (by decide)

/-- When the IC is rigid, Reading A is trivially true — the agent knows the
    value because it never varies. This is why the A/B distinction only
    matters for non-rigid ICs. -/
theorem rigid_trivializes_readingA :
    ∀ w : W, know₁ priceOil john w = true := by
  intro w; cases w <;> native_decide

/-! ## Predicational vs Specificational `be`

@cite{partee-1987} analyzes the **predicational** copula as an extensional
type-shift `BE : ⟨⟨e,t⟩,t⟩ → ⟨e,t⟩`. This applies to sentences like
"The number of planets is large" (predicational: a property is predicated
of the subject).

Romero's `be₁_spec`/`be₂_spec` are for **specificational** copular sentences
like "The number of planets is nine" — the subject determines a question
and the post-copular phrase gives the answer. The key difference:

- Partee's `BE` is **extensional**: both arguments are evaluated at the
  same world. No intensional mechanism.
- Romero's specificational `be` is **intensional** w.r.t. its subject: the
  subject NP contributes an intensional object (an individual concept or
  a concept of concepts), not a simple entity.

This is Romero's novel contribution: specificational `be` is an intensional
verb, paralleling `know` and `look for`, not a variant of the predicational
copula.

See `Phenomena.Copulas.Studies.Partee1987` for the predicational analysis. -/

/-! ## Refutation of Account 2: Trace Type Ambiguity (§2.4.2)

Account 2 varies the type τ of the trace in [NP the price that Fred knows t_τ]:
- τ = ⟨s,e⟩ → Reading A (using `know₁` throughout)
- τ = ⟨s,⟨s,e⟩⟩ → Reading B (using `know₂` for matrix, `know₃` for embedded)

This requires a third lexical entry `know₃` (Romero (43c)), which evaluates
the concept-of-concepts at the matrix world before checking doxastic identity.

The problem: once `know₂` and `know₃` are both in the lexicon, nothing
prevents them from swapping positions (know₃ for matrix, know₂ for embedded),
generating the unavailable Reading B' — the inverse of B. -/

/-- ⟦know₃⟧(y_{⟨s,⟨s,e⟩⟩})(x_e)(w_s) = 1 iff ∀w' ∈ Dox_x(w). y(w)(w') = y(w)(w)

    Account 2's additional lexical entry (Romero (43c)). Takes a
    concept-of-concepts y but evaluates it at the matrix world w first,
    then checks that the resulting IC's value is stable across
    dox-alternatives. Unlike `know₂`, this is NOT a crosscategorial
    variant — it introduces an extra layer of world evaluation. -/
def know₃ (y : W → (W → E)) (x : E) (w : W) : Bool :=
  worlds.all λ w' => !Dox x w w' || (y w) w' == (y w) w

/-- `know₃` structurally collapses to `know₁`: evaluating the
    concept-of-concepts at w yields an individual concept, which is then
    processed identically to `know₁`. The extra intension layer is
    absorbed by evaluation. -/
theorem know₃_reduces_to_know₁ (y : W → (W → E)) (x : E) (w : W) :
    know₃ y x w = know₁ (y w) x w := rfl

/-- Reading B': the unavailable inverse reading overgenerated by Account 2.
    Uses `know₃` for the matrix verb (John) — meaning John knows the actual
    value of the IC that Fred meta-knows — rather than `know₂`.

    Since `know₃` reduces to `know₁`, B' = `know₁ priceMilk john w` =
    Reading A. -/
def readingBprime (w : W) : Bool :=
  know₃ thePriceFredKnows_intension john w

/-- B' reduces to Reading A (since `thePriceFredKnows_intension` is constant
    at `priceMilk`). -/
theorem readingBprime_eq_readingA :
    ∀ w : W, readingBprime w = know₁ (thePriceFredKnows w) john w := by
  intro w; rfl

/-- Account 2 overgenerates: B' ≠ B at w2 (B' is false, B is true).
    The spurious Reading B' is predicted to be available but isn't. -/
theorem account2_overgenerates :
    readingBprime .w2 = false ∧
    know₂ thePriceFredKnows_intension john .w2 = true :=
  ⟨by native_decide, readingB_w2⟩

/-! ## Refutation of Account 3: Pragmatic Account (§2.4.3)

@cite{heim-1979}'s pragmatic account: `know` takes two internal arguments:
- an entity x_e provided by the NP's extension
- a free property P_{⟨e,⟨s,t⟩⟩} contextually supplied

Formula: `know(agent, ιx_e[price(x,w) ∧ know(f,x,Q,w)], P, w)`

The argument is type e (an entity), NOT ⟨s,e⟩ (an individual concept).
Since the NP's extension and the trace co-refer (same variable x), the
formula can only track entity-level knowledge. Reading B requires
question-level knowledge (which IC Fred knows), which cannot be encoded
as a property P of an entity. -/

/-- Account 3's pragmatic `know`: the agent knows entity x under property P.
    ∀w' ∈ Dox(agent, w). P(x)(w') -/
def knowPragmatic (agent : E) (x : E) (P : E → W → Bool) (w : W) : Bool :=
  worlds.all λ w' => !Dox agent w w' || P x w'

/-- The most natural property P for "the price that Fred knows":
    being the price of milk. Under @cite{heim-1979}'s pragmatic bias,
    the property mentioned in the NP is the most salient one. -/
def priceMilkProperty : E → W → Bool := λ x w => x == priceMilk w

/-- The structural limitation of Account 3: the entity argument is evaluated
    and frozen at the matrix world w. Across dox-alternatives w', P is
    always applied to the SAME entity `priceMilk w`, never to different
    entities. This is why the formula can only track whether John knows
    the entity-level value, not which IC Fred knows. -/
theorem account3_entity_frozen (P : E → W → Bool) (w : W) :
    knowPragmatic john (priceMilk w) P w =
    worlds.all λ w' => !Dox john w w' || P (priceMilk w) w' := rfl

/-- With the salient P, Account 3 gives Reading A (not B).
    The formula checks whether John knows the entity-level value of
    `priceMilk`, which is exactly what Reading A checks. -/
theorem account3_gives_readingA :
    ∀ w : W, knowPragmatic john (priceMilk w) priceMilkProperty w =
              know₁ priceMilk john w := by
  intro w; cases w <;> native_decide

/-- Account 3 cannot derive Reading B: the salient-P formula is false at w2
    (= Reading A), but Reading B is true. Since the argument is type e,
    no property P can capture question-level knowledge. -/
theorem account3_fails_at_w2 :
    knowPragmatic john (priceMilk .w2) priceMilkProperty .w2 = false ∧
    know₂ thePriceFredKnows_intension john .w2 = true :=
  ⟨by native_decide, readingB_w2⟩

/-! ## Refutation of Accounts 1-3 for Specificational Subjects (§3.3)

The same three extensional accounts fail for specificational `be`.

- **Account 1** (§3.3.1): Inapplicable for SSs — the formula has only one
  operator (λw) that could bind the world variable. Unlike the CQ case,
  there is no lower ∀w' binder from `know`, so the ambiguity cannot stem
  from world variable choice.

- **Account 2** (§3.3.2): Requires `be₃_spec` below, which collapses to
  `be₁_spec` (Reading A). Overgenerates Reading B' for SSs, just as
  `know₃` does for CQs.

- **Account 3** (§3.3.3): The entity-level limitation from §2.4.3 applies
  equally: property P on entities cannot capture which IC the SS NP
  denotes. Structurally identical to the CQ case. -/

/-- ⟦be₃_spec⟧(x_e)(y_{⟨s,⟨s,e⟩⟩})(w_s) = 1 iff y(w)(w) = x

    Account 2's additional entry for specificational `be` (Romero (71c)).
    Evaluates the concept-of-concepts y at the matrix world w to get an IC,
    then evaluates that IC at w to get an entity, then checks identity with x.
    Parallel to `know₃` — adds an extra layer of world evaluation. -/
def be₃_spec (x : E) (y : W → (W → E)) (w : W) : Bool :=
  (y w) w == x

/-- `be₃_spec` collapses to `be₁_spec`: double world evaluation reduces to
    single entity comparison. Parallel to `know₃_reduces_to_know₁`. -/
theorem be₃_reduces_to_be₁ (x : E) (y : W → (W → E)) (w : W) :
    be₃_spec x y w = be₁_spec x (y w) w := rfl

/-! ## Mention-Some Readings and Exhaustivity (§4.1)

CQs and SSs share a property that distinguishes them from regular NPs:
they allow mention-some (existential-like) readings in contexts where
regular NPs require exhaustive answers.

Spanish `saber` 'know' + CQ *lo que también llevaba* "what he was also
wearing" has a mention-some reading: knowing *something* Carlos was wearing
suffices (Romero (91)). SSs pattern identically (Romero (93)).

Two degrees of exhaustivity:
- **Strongly exhaustive** (= `know₁` / `be₁_spec`): agent identifies the
  complete answer / the IC's value equals the entity exactly.
- **Mention-some**: agent identifies at least one correct part /
  the entity is a part of the IC's value.

The part-of relation ≤ is @cite{link-1983}'s mereological ≤ for plural
individuals. For atomic entities, ≤ reduces to equality and mention-some
collapses to strongly exhaustive. -/

/-- Exhaustivity degree for CQ/SS interpretations (Romero §4.1). -/
inductive ExhaustivityDegree where
  | stronglyExhaustive  -- know/identify the COMPLETE answer
  | mentionSome         -- know/identify SOME correct part
  deriving DecidableEq, BEq, Repr

/-- Mention-some `know` (Romero (101)):
    ∃z. z ≤ y(w) ∧ ∀w' ∈ Dox(x,w). z ≤ y(w')

    The agent identifies at least one entity z that is a part of the IC's
    actual value y(w), and z is also a part of y(w') in all dox-alternatives.
    Parametric over a part-of relation `leq` (@cite{link-1983}'s ≤). -/
def know_CQ_SOME (leq : E → E → Bool) (y : W → E) (x : E) (w : W) : Bool :=
  entities.any λ z => leq z (y w) &&
    worlds.all λ w' => !Dox x w w' || leq z (y w')

/-- Mention-some `be` (Romero (105)):
    x ≤ y(w)

    The post-copular entity x is a part of the IC's value at w. -/
def be_SS_SOME (leq : E → E → Bool) (x : E) (y : W → E) (w : W) : Bool :=
  leq x (y w)

/-- `know₁` is the strongly exhaustive variant `know_CQ_STR` (Romero (100)).
    The definitions are identical. -/
theorem know₁_is_strongly_exhaustive :
    ∀ (y : W → E) (x : E) (w : W),
      know₁ y x w = knowGeneric (α := E) y x w := fun _ _ _ => rfl

/-- `be₁_spec` is the strongly exhaustive variant `be_SS_STR` (Romero (104)).
    The definitions are identical. -/
theorem be₁_spec_is_strongly_exhaustive :
    ∀ (x : E) (y : W → E) (w : W),
      be₁_spec x y w = beGeneric (α := E) x y w := fun _ _ _ => rfl

/-! ## CQ/SS Unification (§4–5)

The paper's core contribution: concealed questions (with `know`) and
specificational subjects (with `be`) are **the same semantic phenomenon**.
Both involve an NP in a configuration with an intensional verb where
the NP can contribute either its extension (Reading A) or its intension
(Reading B). The formal parallel:

| Feature                | CQs (`know`)       | SSs (`be`)           |
|------------------------|---------------------|----------------------|
| Extension → Reading A  | `know₁` + ext NP   | `be₁_spec` + ext NP |
| Intension → Reading B  | `know₂` + int NP   | `be₂_spec` + int NP |
| Generic schema         | `knowGeneric`       | `beGeneric`          |
| Account 2 refutation   | `know₃` collapses   | `be₃_spec` collapses |
| Mention-some variant   | `know_CQ_SOME`      | `be_SS_SOME`         |

Both `know` and `be` are crosscategorial variants at different types of
the SAME doxastic/identity operation — captured by `knowGeneric` and
`beGeneric` sharing the same type-parametric template.

Furthermore, CQs and SSs share two grammatical properties that set them
apart from regular NPs in predicational sentences:

1. **Neuter pronominalization**: pronouns referring to CQs/SSs must be
   neuter *it* (English) / *se* (Finnish), not gendered *she*/*he* / *hän*.
   Regular NPs select gender based on the referent (Romero (84)–(89)).

2. **Mention-some readings**: CQs/SSs allow existential-like readings
   (Spanish *saber* + *también* data, (91)–(93)). Regular NPs in
   predicational sentences do not readily allow this.

These shared properties support the unified analysis: CQs and SSs are
not different constructions but the same type of NP in a configuration
with an intensional verb. -/

/-! ## Extensional Verb Limitation (Appendix)

Intensional verbs (`know`, `look for`, specificational `be`) allow the NP
complement/subject to contribute either its extension or its intension.
Extensional verbs (`kill`) only allow the extension.

This is a type-level constraint: extensional verbs take arguments of type e,
which forces evaluation at the local world. The NP's intension (type ⟨s,e⟩)
cannot serve as the argument. Intensional verbs take arguments of intensional
type (⟨s,e⟩ or ⟨s,⟨s,e⟩⟩), so both the extension (NP evaluated at w) and the
intension (NP unevaluated) can provide the right type.

Example: "#John killed (yesterday) what Alexander the Great was looking for
in his conquests" (Romero (117)). If `kill` could take the NP's extension
at a non-local situation s, the sentence would wrongly predict a de dicto
reading where the killed individual and Alexander's search target might be
different physical objects. This reading is unavailable — `kill` is extensional. -/

/-- Classification of verbs by whether they allow the NP's intension as
    argument, per the appendix. -/
inductive VerbIntensionality where
  | intensional  -- know, look for, be_spec: NP contributes ext or int
  | extensional  -- kill, see: NP contributes only its extension
  deriving DecidableEq, BEq, Repr

end Phenomena.Copulas.Studies.Romero2005
