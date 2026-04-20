import Linglib.Core.IntensionalLogic.Rigidity
import Linglib.Theories.Semantics.Attitudes.Intensional
import Linglib.Theories.Semantics.Attitudes.Doxastic
import Linglib.Theories.Semantics.Questions.Answerhood.MentionSome

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

namespace Romero2005

open Core (Intension)
open Semantics.Attitudes.Doxastic (AccessRel boxAt)

/-! ## World and Entity Setup -/

/-- A simple 4-world type for the Romero examples. -/
inductive W where
  | w0 | w1 | w2 | w3
  deriving DecidableEq, Repr, Inhabited

abbrev E := Fin 4

/-- All worlds in the model. -/
def worlds : List W := [.w0, .w1, .w2, .w3]

/-- All entities in the model (prices / question-answers). -/
def entities : List E := [0, 1, 2, 3]

/-- `worlds` covers all of `World4`. Needed for soundness of `List.all`
    as universal quantification. -/
theorem worlds_complete : ∀ w : W, w ∈ worlds := by
  intro w; cases w <;> simp [worlds]

/-- `entities` covers all of `Fin 4`. -/
theorem entities_complete : ∀ e : E, e ∈ entities := by decide

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

/-- `Dox` lifted to a Prop-valued `AccessRel` — connecting to the theory-layer
    doxastic infrastructure in `Semantics.Attitudes.Doxastic`. -/
def DoxRel : AccessRel W E := fun a w w' => Dox a w w' = true

instance : ∀ a w w', Decidable (DoxRel a w w') := by
  intro a w w'; unfold DoxRel; infer_instance

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

/-- A rigid IC with value 0 at all worlds. Used to demonstrate that
    extensional mechanisms (Account 3, extensional verbs) cannot distinguish
    ICs that agree at the evaluation world. -/
def rigidZero : W → E := λ _ => 0

scoped instance : BEq (Intension W E) where
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
    in all doxastic alternatives, `y` yields the same value as in actuality.
    Romero (29b); also (100) `know_{CQ,STR}` (strongly exhaustive CQ `know`). -/
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
    know₁ y x w = true ↔
    boxAt DoxRel x w worlds (λ w' => y w' = y w) := by
  simp only [know₁, boxAt, DoxRel, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq]
  constructor
  · intro h w' hw' hR
    have := h w' hw'
    rcases this with hd | heq
    · exact absurd hR (by simp [hd])
    · exact heq
  · intro h w' hw'
    by_cases hd : Dox x w w' = true
    · exact Or.inr (h w' hw' hd)
    · exact Or.inl (by simp [hd])

/-! ### `be₁_spec` and `be₂_spec` (Romero (67a,b))

Specificational `be` is an intensional verb w.r.t. its subject position.

- `be₁_spec` takes the NP's extension (an individual concept) and a
  post-copular entity, and checks identity at the evaluation world.
- `be₂_spec` takes the NP's intension (a concept of concepts) and a
  post-copular individual concept, and checks identity at the evaluation world. -/

/-- ⟦be₁_spec⟧(x_e)(y_{⟨s,e⟩})(w_s) = 1 iff y(w) = x

    Reading A: the individual concept `y` (extension of the SS NP) has
    value `x` at the actual world `w`. Romero (67a); also (104) `be_{SS,STR}`. -/
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

See `Partee1987` for the predicational analysis. -/

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

/-- `know₃` breaks crosscategorial uniformity: unlike `know₁` and `know₂`,
    it is NOT an instance of `knowGeneric`. It pre-evaluates the
    concept-of-concepts `y` at `w` before applying the generic schema, so
    `know₃ y x w = knowGeneric (y w) x w` rather than `knowGeneric y x w`.

    This is the structural economy argument (§2.5): the proposed analysis
    uses only `know₁`/`know₂` (both crosscategorial), while Account 2
    requires the non-uniform `know₃` which breaks the pattern. -/
theorem know₃_not_crosscategorial :
    ∃ (y : W → (W → E)) (x : E) (w : W),
      know₃ y x w ≠ @knowGeneric (W → E) _ y x w := by
  -- Witness: y varies across John's doxastic alternatives at w2 ({w2, w3}).
  -- know₃ evaluates y at w first (getting rigidZero, which is constant) → true.
  -- knowGeneric compares y w2 (rigidZero) vs y w3 (priceMilk) as functions → false.
  refine ⟨fun w => match w with | .w3 => priceMilk | _ => rigidZero, john, .w2, ?_⟩
  native_decide

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

/-- **Type-level expressiveness limitation**: Account 3's entity-type argument
    makes `knowPragmatic` extensional in the IC — it depends on `y` only
    through `y w`, discarding cross-world behavior. For ANY property P, two
    ICs that agree at `w` produce identical results. -/
theorem account3_extensional_in_ic (y y' : W → E) (agent : E)
    (P : E → W → Bool) (w : W) (h : y w = y' w) :
    knowPragmatic agent (y w) P w = knowPragmatic agent (y' w) P w := by
  simp only [h]

/-- The structural refutation: Account 3 cannot distinguish ICs that agree
    at the evaluation world, for ANY choice of P. But `know₁` can, because
    it checks the IC's values across doxastic alternatives.

    `priceMilk` and `rigidZero` both yield 0 at w2. No property P makes
    `knowPragmatic` tell them apart. Yet `know₁` gives different results
    (false vs true) because milk prices vary at w3 but rigidZero doesn't. -/
theorem account3_type_limitation :
    priceMilk .w2 = rigidZero .w2 ∧
    (∀ P : E → W → Bool,
      knowPragmatic john (priceMilk .w2) P .w2 =
      knowPragmatic john (rigidZero .w2) P .w2) ∧
    know₁ priceMilk john .w2 ≠ know₁ rigidZero john .w2 := by
  refine ⟨rfl, fun P => ?_, ?_⟩
  · exact account3_extensional_in_ic priceMilk rigidZero john P .w2 rfl
  · native_decide

/-! ## SS Account Refutations (§3.3)

Parallel to §2.4 for CQs. Account 2 requires `be₃_spec` which collapses
to `be₁_spec`. -/

/-- Account 2's `be` entry (Romero (71c)). Evaluates concept-of-concepts
    at w twice, collapsing to entity comparison. Parallel to `know₃`. -/
def be₃_spec (x : E) (y : W → (W → E)) (w : W) : Bool :=
  (y w) w == x

/-- `be₃_spec` collapses to `be₁_spec`. -/
theorem be₃_reduces_to_be₁ (x : E) (y : W → (W → E)) (w : W) :
    be₃_spec x y w = be₁_spec x (y w) w := rfl

/-! ## CQ Knowledge as Partition-Cell Inclusion

@cite{groenendijk-stokhof-1984} partition semantics: a question denotes an
equivalence relation on worlds. `know₁ y x w` checks that all doxastic
alternatives of x at w fall within the same partition cell as w — the cell
induced by the individual concept y. -/

/-- The CQ question induced by individual concept y: "what is y's value?"
    Two worlds are equivalent iff y assigns them the same entity. -/
def cqQuestion (y : W → E) : QUD W := QUD.ofProject y

/-- `know₁ y x w` = all dox-alternatives of x at w lie in the same
    partition cell as w under the CQ question induced by y.

    This is the formal bridge between Romero's individual-concept semantics
    and @cite{groenendijk-stokhof-1984}'s partition semantics for questions:
    knowing a CQ IS having one's epistemic state contained in a single
    partition cell. -/
theorem know₁_eq_doxInCell (y : W → E) (x : E) (w : W) :
    know₁ y x w =
    worlds.all fun w' => !Dox x w w' || (cqQuestion y).sameAnswer w w' := by
  simp only [know₁, cqQuestion, QUD.ofProject_sameAnswer, Bool.beq_comm]

/-- Rigid IC → trivially known by all agents.

    When an IC is rigid (constant), the induced CQ partition is trivial — the
    question has only one possible answer. Every agent's doxastic state is
    vacuously contained in the single cell. This is why the A/B distinction
    only matters for non-rigid ICs like `priceMilk`. -/
theorem rigid_trivial_question (y : W → E) (hrig : Core.Intension.IsRigid y) :
    ∀ x w, know₁ y x w = true := by
  intro x w
  simp only [know₁, List.all_eq_true]
  intro w' _
  simp only [Bool.or_eq_true, Bool.not_eq_true']
  right; exact beq_iff_eq.mpr (hrig w' w)

/-! ## Mention-Some Readings (§4.1) -/

/-- Mention-some `know` (Romero (101)): ∃z. z ≤ y(w) ∧ ∀w' ∈ Dox(x,w). z ≤ y(w').
    Parametric over `leq` (@cite{link-1983}'s ≤). -/
def know_CQ_SOME (leq : E → E → Bool) (y : W → E) (x : E) (w : W) : Bool :=
  entities.any fun z => leq z (y w) &&
    worlds.all fun w' => !Dox x w w' || leq z (y w')

/-- Mention-some `be` (Romero (105)): x ≤ y(w). -/
def be_SS_SOME (leq : E → E → Bool) (x : E) (y : W → E) (w : W) : Bool :=
  leq x (y w)

/-- For atomic ≤ (= equality), mention-some entails strongly exhaustive.
    With no proper parts, any witness z with z = y(w) yields `know₁`.
    This is the converse of @cite{groenendijk-stokhof-1984}'s
    `mentionAll_implies_mentionSome`. -/
theorem mentionSome_atomic_entails_str (y : W → E) (x : E) (w : W)
    (h : know_CQ_SOME (· == ·) y x w = true) :
    know₁ y x w = true := by
  simp only [know_CQ_SOME, know₁] at *
  rcases List.any_eq_true.mp h with ⟨z, _, hz⟩
  simp only [Bool.and_eq_true] at hz
  have hzeq : z = y w := eq_of_beq hz.1
  exact List.all_eq_true.mpr fun w' hw' => by
    have := (List.all_eq_true.mp hz.2) w' hw'
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at this ⊢
    rcases this with h | h
    · left; exact h
    · right; rw [hzeq] at h; rw [Bool.beq_comm]; exact h

/-! ## Connection to G&S Mention-Some Framework

Romero's `know_CQ_SOME` is an instance of @cite{groenendijk-stokhof-1984}'s
`knowMentionSome`: the CQ under `leq` induces a mention-some interrogative
where `abstract(w, z) = leq(z, y(w))`, and doxastic universal quantification
supplies the knowledge operator. -/

open Semantics.Questions.MentionSome (MentionSomeInterrogative knowMentionSome)

/-- The mention-some interrogative induced by a CQ under part-of ≤.
    "Which part z of y's value holds?" -/
def cqMSI (leq : E → E → Bool) (y : W → E) : MentionSomeInterrogative W E :=
  ⟨entities, fun w z => leq z (y w)⟩

/-- Doxastic universal quantification as a knowledge operator. -/
def doxKnows (agent : E) (w : W) (prop : W → Bool) : Bool :=
  worlds.all fun w' => !Dox agent w w' || prop w'

/-- Romero's `know_CQ_SOME` IS @cite{groenendijk-stokhof-1984}'s
    `knowMentionSome` applied to the CQ-induced mention-some interrogative
    with doxastic knowledge. Definitional equality (rfl). -/
theorem know_CQ_SOME_eq_knowMentionSome (leq : E → E → Bool) (y : W → E)
    (x : E) (w : W) :
    know_CQ_SOME leq y x w =
    knowMentionSome (cqMSI leq y) (fun w agent prop => doxKnows agent w prop) x w :=
  rfl

/-! ## Extensional Verb Limitation (Appendix)

Romero's Appendix argues that the freedom to combine with extension or
intension is a property of *intensional* verbs (`know`, `look for`, spec. `be`)
only. Extensional verbs like `kill` take type-`e` arguments, so the NP's
contribution is always evaluated at the local world — no room for IC-level
interpretation. This is why CQ/SS readings don't arise with extensional verbs.

We formalize this by defining an extensional verb template and proving that
it collapses the A/B distinction: it can only access the entity `y(w)`, not
the IC `y` itself, making it impossible to distinguish worlds where `y`
varies. -/

/-- An extensional verb takes an entity argument (type e) and checks a
    world-relative property. The IC `y` is always evaluated at `w` before
    being passed to the verb. -/
def extensionalVerb (verb : E → E → W → Bool) (y : W → E) (x : E) (w : W) : Bool :=
  verb (y w) x w

/-- For extensional verbs, the IC `y` and any IC `y'` that agrees at `w`
    produce identical results. The verb cannot "see" the IC's behavior at
    other worlds. This is why CQ readings (which require cross-world IC
    comparison) are unavailable with extensional verbs. -/
theorem extensional_collapses (verb : E → E → W → Bool)
    (y y' : W → E) (x : E) (w : W) (h : y w = y' w) :
    extensionalVerb verb y x w = extensionalVerb verb y' x w := by
  simp only [extensionalVerb, h]

/-- The key contrast: `priceMilk` and `rigidZero` agree at w2 (both yield 0).
    An extensional verb CANNOT distinguish them (it only sees the entity at w),
    but intensional `know₁` CAN (it checks doxastic alternatives where they
    diverge). This is why CQ readings require intensional verbs. -/
theorem extensional_vs_intensional :
    -- Both ICs agree at w2: priceMilk w2 = rigidZero w2 = 0
    priceMilk .w2 = rigidZero .w2 ∧
    -- An extensional verb cannot distinguish them at w2
    (∀ verb : E → E → W → Bool,
      extensionalVerb verb priceMilk john .w2 =
      extensionalVerb verb rigidZero john .w2) ∧
    -- But know₁ CAN distinguish them at w2
    know₁ priceMilk john .w2 ≠ know₁ rigidZero john .w2 := by
  refine ⟨rfl, fun verb => ?_, ?_⟩
  · exact extensional_collapses verb priceMilk rigidZero john .w2 rfl
  · native_decide

/-! ## CQ/SS Unification

The paper's main contribution: CQs (with `know`) and SSs (with `be`) share
the same semantic mechanism — the complement/subject NP contributes either
its extension (Reading A) or its intension (Reading B) as an intensional
object. The A/B ambiguity is derived from the two interpretive dimensions of
the NP, NOT from lexical ambiguity of the verb.

The crosscategorial templates `knowGeneric` and `beGeneric` witness this
unification: both are parameterized by the same type variable α, with
α = E for Reading A and α = (W → E) for Reading B. -/

/-- CQ/SS unification: `know₁`/`be₁_spec` (Reading A) and `know₂`/`be₂_spec`
    (Reading B) are instances of the SAME crosscategorial templates at
    different types. The A/B ambiguity is type-driven, not lexicon-driven. -/
theorem cq_ss_unified :
    -- CQ Reading A = knowGeneric at type E
    (∀ y x w, know₁ y x w = @knowGeneric E _ y x w) ∧
    -- CQ Reading B = knowGeneric at type (W → E)
    (∀ y x w, know₂ y x w = @knowGeneric (W → E) _ y x w) ∧
    -- SS Reading A = beGeneric at type E
    (∀ x y w, be₁_spec x y w = @beGeneric E _ x y w) ∧
    -- SS Reading B = beGeneric at type (W → E)
    (∀ x y w, be₂_spec x y w = @beGeneric (W → E) _ x y w) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

end Romero2005
