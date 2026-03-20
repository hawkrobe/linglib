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

/-! ## TODO: Additional Refutation Arguments

The paper refutes three purely extensional accounts of the A/B ambiguity
(§2.4.1–2.4.3 for CQs, §3.3.1–3.3.3 for SSs). We formalize only Account 1.

- **Account 2** (trace type ambiguity, §2.4.2): Varying the type of the
  trace τ in `[NP the price that Fred knows t_τ]` between `⟨s,e⟩` and
  `⟨s,⟨s,e⟩⟩` generates both readings but also the unavailable Reading B'
  (inverse of B). The overgeneration argument: once `know₂` and `know₃`
  are in the lexicon, nothing prevents them from swapping positions.

- **Account 3** (pragmatic account, §2.4.3): Adding a free property variable
  P to `know` (Heim 1979's suggestion) can derive Reading A but not
  Reading B — the formula forces `ιx_e[...]` and the trace `x` to
  co-refer, preventing the needed separation.

- **Mention-some readings** (§4.1): CQs and SSs allow existential-like
  readings (Spanish `saber` / `también` data). Romero gives `know_CQ_SOME`
  and `be_SS_SOME` entries with `∃z ≥ ... ` semantics. -/

end Phenomena.Copulas.Studies.Romero2005
