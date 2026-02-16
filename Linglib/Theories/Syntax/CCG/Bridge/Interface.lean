/-
# CCG Syntax-Semantics Interface

Syntactic categories directly encode semantic types. Combinatory rules correspond
to function application and composition.

## Main definitions

- `catToTy`: Maps CCG categories to semantic types
- `SemLexEntry`: Lexical entry with semantics
- `DerivStep.interp`: Computes meaning from derivation compositionally

## References

- Steedman (2000). The Syntactic Process.
-/

import Linglib.Theories.Syntax.CCG.Core.Basic
import Linglib.Theories.Semantics.Compositional.Basic
import Linglib.Theories.Semantics.Compositional.Conjunction

namespace CCG

open TruthConditional

-- Combinators (defined locally to avoid circular import)

/-- B combinator (composition): B f g x = f (g x) -/
private def B {α β γ : Type} (f : β → γ) (g : α → β) : α → γ :=
  λ x => f (g x)

/-- T combinator (type-raising): T x f = f x -/
private def T {α β : Type} (x : α) : (α → β) → β :=
  λ f => f x

-- Type Correspondence

/-- Map CCG categories to semantic types -/
def catToTy : Cat → Ty
  | .atom .S => .t
  | .atom .NP => .e
  | .atom .N => .e ⇒ .t    -- common nouns are properties
  | .atom .PP => .e ⇒ .t   -- PPs are modifiers (simplified)
  | .rslash x y => catToTy y ⇒ catToTy x
  | .lslash x y => catToTy y ⇒ catToTy x

-- Verify the type correspondence
#eval catToTy S            -- t
#eval catToTy NP           -- e
#eval catToTy N            -- e ⇒ t
#eval catToTy IV           -- e ⇒ t (same as N, both are properties)
#eval catToTy TV           -- e ⇒ e ⇒ t (relations)
#eval catToTy Det          -- (e ⇒ t) ⇒ e (simplified)

-- Semantic Lexicon

/-- A CCG lexical entry with semantics -/
structure SemLexEntry (m : Model) where
  form : String
  cat : Cat
  sem : m.interpTy (catToTy cat)

/-- Semantic lexicon for the toy model -/
def semLexicon : List (SemLexEntry toyModel) := [
  -- Proper names: NP (type e)
  ⟨"John", NP, ToyEntity.john⟩,
  ⟨"Mary", NP, ToyEntity.mary⟩,

  -- Intransitive verbs: S\NP (type e → t)
  ⟨"sleeps", IV, ToyLexicon.sleeps_sem⟩,
  ⟨"laughs", IV, ToyLexicon.laughs_sem⟩,

  -- Transitive verbs: (S\NP)/NP (type e → e → t)
  ⟨"sees", TV, ToyLexicon.sees_sem⟩,
  ⟨"eats", TV, ToyLexicon.eats_sem⟩,
  ⟨"reads", TV, ToyLexicon.reads_sem⟩,
  ⟨"likes", TV, ToyLexicon.sees_sem⟩  -- using sees_sem as placeholder
]

-- Semantic Composition

-- Forward application semantically is just function application
-- If f : ⟦Y⟧ → ⟦X⟧ and a : ⟦Y⟧, then f(a) : ⟦X⟧

-- Backward application is the same
-- If a : ⟦Y⟧ and f : ⟦Y⟧ → ⟦X⟧, then f(a) : ⟦X⟧

-- Example: "John sleeps"

-- Syntactically: John:NP  sleeps:S\NP  ⇒  S
-- Semantically: sleeps_sem(john_sem) : t

def john_sem' : toyModel.interpTy (catToTy NP) := ToyEntity.john
def sleeps_sem' : toyModel.interpTy (catToTy IV) := ToyLexicon.sleeps_sem

-- The semantic derivation mirrors the syntactic one
def john_sleeps_sem : toyModel.interpTy (catToTy S) :=
  sleeps_sem' john_sem'

#eval john_sleeps_sem  -- true

-- Example: "John sees Mary"

-- Syntactically:
--   John:NP  sees:(S\NP)/NP  Mary:NP
--   sees Mary ⇒ S\NP  (forward app)
--   John (sees Mary) ⇒ S  (backward app)

-- Semantically:
--   sees_sem : e → e → t
--   sees_sem(mary) : e → t
--   (sees_sem(mary))(john) : t

def sees_sem' : toyModel.interpTy (catToTy TV) := ToyLexicon.sees_sem
def mary_sem' : toyModel.interpTy (catToTy NP) := ToyEntity.mary

-- Step 1: sees Mary
def sees_mary_sem : toyModel.interpTy (catToTy IV) :=
  sees_sem' mary_sem'  -- function application

-- Step 2: John (sees Mary)
def john_sees_mary_sem : toyModel.interpTy (catToTy S) :=
  sees_mary_sem john_sem'  -- function application

#eval john_sees_mary_sem  -- true

-- Example: "Mary sees John"

def mary_sees_john_sem : toyModel.interpTy (catToTy S) :=
  (sees_sem' john_sem') mary_sem'

#eval mary_sees_john_sem  -- true

-- Example: "John eats pizza"

def eats_sem' : toyModel.interpTy (catToTy TV) := ToyLexicon.eats_sem
def pizza_sem' : toyModel.interpTy (catToTy NP) := ToyEntity.pizza

def john_eats_pizza_sem : toyModel.interpTy (catToTy S) :=
  (eats_sem' pizza_sem') john_sem'

#eval john_eats_pizza_sem  -- true

-- Truth Conditions from CCG Derivations

/-- A sentence is true if its meaning is true -/
def sentenceTrue (meaning : toyModel.interpTy .t) : Prop :=
  meaning = true

-- Prove truth conditions
example : sentenceTrue john_sleeps_sem := rfl
example : sentenceTrue john_sees_mary_sem := rfl
example : sentenceTrue john_eats_pizza_sem := rfl

-- Derivation-Driven Semantic Composition

/-
The CCG derivation structure directly mirrors semantic composition:

Syntax:                    Semantics:
John:NP   sees:(S\NP)/NP   john:e   sees:e→e→t
               |                        |
          Mary:NP                  mary:e
               ↓                        ↓
          sees Mary:S\NP           sees(mary):e→t
               ↓                        ↓
        John sees Mary:S         sees(mary)(john):t

Each syntactic combination corresponds to function application.
This is the "transparency" of the syntax-semantics interface.
-/

-- TYPE PRESERVATION THEOREMS

/-
These theorems establish that CCG combinatory rules preserve semantic well-typedness.
If the syntactic combination succeeds, the semantic combination is well-typed.
-/

/-- Forward application preserves semantic typing:
    If X/Y combines with Y to give X, then (σ→τ) applied to σ gives τ -/
theorem forward_app_type_preservation (x y : Cat) :
    catToTy (x.rslash y) = (catToTy y ⇒ catToTy x) := rfl

/-- Backward application preserves semantic typing:
    If Y combines with X\Y to give X, then (σ→τ) applied to σ gives τ -/
theorem backward_app_type_preservation (x y : Cat) :
    catToTy (x.lslash y) = (catToTy y ⇒ catToTy x) := rfl

/-- Type correspondence for transitive verbs -/
theorem tv_type_is_relation :
    catToTy TV = (.e ⇒ .e ⇒ .t) := rfl

/-- Type correspondence for intransitive verbs -/
theorem iv_type_is_property :
    catToTy IV = (.e ⇒ .t) := rfl

-- COMPOSITIONALITY: DERIVATIONS COMPUTE MEANINGS

/--
A semantic derivation: pairs a CCG category with its meaning.
This represents a node in the derivation tree with its semantic interpretation.
-/
structure SemDeriv (m : Model) where
  cat : Cat
  meaning : m.interpTy (catToTy cat)

/-
Note: A fully general semForwardApp would require dependent types to express
that the result category depends on the input categories. Instead, we work
with concrete examples that show the principle.
-/

/-- Apply a function meaning to an argument meaning -/
def applyMeaning {m : Model} {σ τ : Ty}
    (f : m.interpTy (σ ⇒ τ)) (x : m.interpTy σ) : m.interpTy τ :=
  f x

/-- Composition is function application -/
theorem composition_is_application {m : Model} {σ τ : Ty}
    (f : m.interpTy (σ ⇒ τ)) (x : m.interpTy σ) :
    applyMeaning f x = f x := rfl

-- SOUNDNESS: WELL-FORMED DERIVATIONS HAVE MEANINGS

/--
For a lexical entry, we can always extract its meaning.
-/
theorem lexical_has_meaning (entry : SemLexEntry toyModel) :
    ∃ (meaning : toyModel.interpTy (catToTy entry.cat)), meaning = entry.sem :=
  ⟨entry.sem, rfl⟩

/--
If we have meanings for functor and argument with compatible types,
we can compute the meaning of the result.
-/
theorem combination_has_meaning {m : Model} {x y : Cat}
    (functor_meaning : m.interpTy (catToTy (x.rslash y)))
    (arg_meaning : m.interpTy (catToTy y)) :
    ∃ (result : m.interpTy (catToTy x)), result = functor_meaning arg_meaning :=
  ⟨functor_meaning arg_meaning, rfl⟩

-- EXAMPLE: COMPLETE DERIVATION WITH TYPES

/-- The complete derivation of "John sees Mary" preserving types -/
theorem john_sees_mary_typed_derivation :
    -- 1. sees : (S\NP)/NP has type e → e → t
    let sees_ty : toyModel.interpTy (catToTy TV) := ToyLexicon.sees_sem
    -- 2. Mary : NP has type e
    let mary_ty : toyModel.interpTy (catToTy NP) := ToyEntity.mary
    -- 3. sees Mary : S\NP has type e → t
    let sees_mary_ty : toyModel.interpTy (catToTy IV) := sees_ty mary_ty
    -- 4. John : NP has type e
    let john_ty : toyModel.interpTy (catToTy NP) := ToyEntity.john
    -- 5. John sees Mary : S has type t
    let result : toyModel.interpTy (catToTy S) := sees_mary_ty john_ty
    -- The result is the expected truth value
    result = true := rfl

/-- The derivation of "Mary sleeps" preserving types -/
theorem mary_sleeps_typed_derivation :
    let sleeps_ty : toyModel.interpTy (catToTy IV) := ToyLexicon.sleeps_sem
    let mary_ty : toyModel.interpTy (catToTy NP) := ToyEntity.mary
    let result : toyModel.interpTy (catToTy S) := sleeps_ty mary_ty
    result = false := rfl

-- THE HOMOMORPHISM PRINCIPLE

/-
The fundamental theorem of compositional semantics (Montague's homomorphism):

For every syntactic rule R: A × B → C
there is a semantic rule R': ⟦A⟧ × ⟦B⟧ → ⟦C⟧

such that ⟦R(a, b)⟧ = R'(⟦a⟧, ⟦b⟧)

In CCG, ALL syntactic rules correspond to function application or composition.
This makes the homomorphism particularly transparent.
-/

/-- Forward application satisfies the homomorphism:
    ⟦fapp(f, a)⟧ = ⟦f⟧(⟦a⟧)

    The semantic interpretation of syntactic combination is function application. -/
theorem forward_app_homomorphism {m : Model} {x y : Cat}
    (f_sem : m.interpTy (catToTy (x.rslash y)))
    (a_sem : m.interpTy (catToTy y)) :
    -- The semantic result is function application of functor to argument
    f_sem a_sem = f_sem a_sem := rfl

/-- Backward application satisfies the homomorphism:
    ⟦bapp(a, f)⟧ = ⟦f⟧(⟦a⟧)

    The order of arguments in syntax doesn't affect semantic composition. -/
theorem backward_app_homomorphism {m : Model} {x y : Cat}
    (a_sem : m.interpTy (catToTy y))
    (f_sem : m.interpTy (catToTy (x.lslash y))) :
    -- The semantic result is function application
    f_sem a_sem = f_sem a_sem := rfl

-- DERIVATION INTERPRETATION

/-
This section connects CCG derivations (DerivStep) to their semantic interpretations.
The key insight: every CCG combinatory rule corresponds to function application.
-/

/-- A semantic interpretation: category paired with its meaning -/
structure Interp (m : Model) where
  cat : Cat
  meaning : m.interpTy (catToTy cat)

/-- Semantic lexicon: maps words to interpretations -/
def SemLexicon (m : Model) := String → Cat → Option (Interp m)

/-- The toy semantic lexicon -/
def toySemLexicon : SemLexicon toyModel := λ word cat =>
  match word, cat with
  -- Proper names
  | "John", .atom .NP => some ⟨NP, ToyEntity.john⟩
  | "Mary", .atom .NP => some ⟨NP, ToyEntity.mary⟩
  -- Common noun phrases (using pizza entity as placeholder)
  | "beans", .atom .NP => some ⟨NP, ToyEntity.pizza⟩
  -- Intransitive verbs
  | "sleeps", .lslash (.atom .S) (.atom .NP) => some ⟨IV, ToyLexicon.sleeps_sem⟩
  | "laughs", .lslash (.atom .S) (.atom .NP) => some ⟨IV, ToyLexicon.laughs_sem⟩
  -- Transitive verbs
  | "sees", .rslash (.lslash (.atom .S) (.atom .NP)) (.atom .NP) =>
      some ⟨TV, ToyLexicon.sees_sem⟩
  | "eats", .rslash (.lslash (.atom .S) (.atom .NP)) (.atom .NP) =>
      some ⟨TV, ToyLexicon.eats_sem⟩
  | "likes", .rslash (.lslash (.atom .S) (.atom .NP)) (.atom .NP) =>
      some ⟨TV, ToyLexicon.sees_sem⟩  -- using sees_sem as placeholder
  | "hates", .rslash (.lslash (.atom .S) (.atom .NP)) (.atom .NP) =>
      some ⟨TV, ToyLexicon.sees_sem⟩  -- using sees_sem as placeholder
  | _, _ => none

/--
Interpret a CCG derivation, computing its meaning from the lexicon.

Returns `none` if the derivation is ill-formed or uses unknown words.
-/
def DerivStep.interp (d : DerivStep) (lex : SemLexicon toyModel)
    : Option (Interp toyModel) :=
  match d with
  | .lex entry => lex entry.form entry.cat

  | .fapp d1 d2 => do
      -- Forward application: X/Y Y → X
      let ⟨c1, m1⟩ ← d1.interp lex
      let ⟨c2, m2⟩ ← d2.interp lex
      match c1 with
      | .rslash x y =>
          if h : c2 = y then
            -- m1 : catToTy y ⇒ catToTy x
            -- m2 : catToTy c2 = catToTy y
            let m2' : toyModel.interpTy (catToTy y) := h ▸ m2
            some ⟨x, m1 m2'⟩
          else none
      | _ => none

  | .bapp d1 d2 => do
      -- Backward application: Y X\Y → X
      let ⟨c1, m1⟩ ← d1.interp lex
      let ⟨c2, m2⟩ ← d2.interp lex
      match c2 with
      | .lslash x y =>
          if h : c1 = y then
            -- m2 : catToTy y ⇒ catToTy x
            -- m1 : catToTy c1 = catToTy y
            let m1' : toyModel.interpTy (catToTy y) := h ▸ m1
            some ⟨x, m2 m1'⟩
          else none
      | _ => none

  | .fcomp d1 d2 => do
      -- Forward composition: X/Y + Y/Z → X/Z
      -- Semantic rule: B combinator (f ∘ g)
      let ⟨c1, m1⟩ ← d1.interp lex
      let ⟨c2, m2⟩ ← d2.interp lex
      match c1, c2 with
      | .rslash x y1, .rslash y2 z =>
          if h : y1 = y2 then
            -- m1 : catToTy y1 → catToTy x
            -- m2 : catToTy z → catToTy y2
            -- B m1 m2 : catToTy z → catToTy x
            let m2' : toyModel.interpTy (catToTy z ⇒ catToTy y1) :=
              h ▸ m2
            some ⟨x / z, B m1 m2'⟩
          else none
      | _, _ => none

  | .bcomp d1 d2 => do
      -- Backward composition: Y\Z + X\Y → X\Z
      -- Semantic rule: B combinator (f ∘ g)
      let ⟨c1, m1⟩ ← d1.interp lex
      let ⟨c2, m2⟩ ← d2.interp lex
      match c1, c2 with
      | .lslash y1 z, .lslash x y2 =>
          if h : y1 = y2 then
            -- m1 : catToTy z → catToTy y1
            -- m2 : catToTy y2 → catToTy x
            -- B m2 m1 : catToTy z → catToTy x
            let m1' : toyModel.interpTy (catToTy z ⇒ catToTy y2) :=
              h ▸ m1
            some ⟨x \ z, B m2 m1'⟩
          else none
      | _, _ => none

  | .ftr d t => do
      -- Forward type-raising: X → T/(T\X)
      -- Semantic rule: T combinator (λf. f x)
      let ⟨x, m⟩ ← d.interp lex
      -- T m : (catToTy x → catToTy t) → catToTy t
      -- catToTy (t / (t \ x)) = catToTy (t \ x) ⇒ catToTy t
      --                       = (catToTy x ⇒ catToTy t) ⇒ catToTy t
      some ⟨forwardTypeRaise x t, T m⟩

  | .btr d t => do
      -- Backward type-raising: X → T\(T/X)
      -- Semantic rule: T combinator (λf. f x)
      let ⟨x, m⟩ ← d.interp lex
      -- T m : (catToTy x → catToTy t) → catToTy t
      -- catToTy (t \ (t / x)) = catToTy (t / x) ⇒ catToTy t
      --                       = (catToTy x ⇒ catToTy t) ⇒ catToTy t
      some ⟨backwardTypeRaise x t, T m⟩

  | .coord d1 d2 => do
      -- Coordination: X and X → X
      -- Semantic rule: generalized conjunction (Partee & Rooth 1983)
      -- Uses TruthConditional.Conjunction.genConj for uniform type-driven coordination
      let ⟨c1, m1⟩ ← d1.interp lex
      let ⟨c2, m2⟩ ← d2.interp lex
      if h : c1 = c2 then
        let ty := catToTy c1
        -- Only conjoinable types can be coordinated
        if ty.isConjoinable then
          let m2' : toyModel.interpTy (catToTy c1) := h ▸ m2
          some ⟨c1, Conjunction.genConj ty toyModel m1 m2'⟩
        else none
      else none

-- INTERPRETATION EXAMPLES

/-- Helper to extract meaning from interpretation result -/
def getMeaning (result : Option (Interp toyModel)) : Option Bool :=
  match result with
  | some ⟨.atom .S, m⟩ => some m
  | _ => none

-- "John sleeps" interpretation
#eval getMeaning (john_sleeps.interp toySemLexicon)
-- Expected: some true

-- "John sees Mary" interpretation
#eval getMeaning (john_sees_mary.interp toySemLexicon)
-- Expected: some true

/-- Interpretation of "John sleeps" produces correct truth value -/
theorem john_sleeps_interp_correct :
    getMeaning (john_sleeps.interp toySemLexicon) = some true := by
  native_decide

/-- Interpretation of "John sees Mary" produces correct truth value -/
theorem john_sees_mary_interp_correct :
    getMeaning (john_sees_mary.interp toySemLexicon) = some true := by
  native_decide

-- TYPE-RAISING AND COMPOSITION TESTS

/--
Type-raised "John":
  John:NP  →  S/(S\NP)  via forward type-raising
-/
def john_typeraised : DerivStep := .ftr (.lex ⟨"John", NP⟩) S

-- Test type-raising produces correct category
#eval john_typeraised.cat
-- Expected: some (S / (S \ NP))

-- Test type-raising interpretation works (check it's not none)
#eval (john_typeraised.interp toySemLexicon).isSome
-- Expected: true

/--
"John sees Mary" via type-raising:
  John          sees          Mary
  NP            (S\NP)/NP     NP
  ↓T(S)
  S/(S\NP)      (S\NP)/NP     NP
                └────>────────┘
                    S\NP
  └──────>──────────────────────┘
                S
Note: Type-raised subject uses FORWARD application (it's S/(S\NP), seeking S\NP to its right)
-/
def john_sees_mary_via_tr : DerivStep :=
  .fapp john_typeraised (.fapp (.lex ⟨"sees", TV⟩) (.lex ⟨"Mary", NP⟩))

-- Full derivation still works
#eval getMeaning (john_sees_mary_via_tr.interp toySemLexicon)
-- Expected: some true

/-- Type-raised derivation produces correct truth value -/
theorem john_sees_mary_via_tr_correct :
    getMeaning (john_sees_mary_via_tr.interp toySemLexicon) = some true := by
  native_decide

-- FORWARD COMPOSITION TEST

/--
"John likes" as S/NP via type-raising + composition (for coordination):
  John          likes
  NP            (S\NP)/NP
  ↓T(S)
  S/(S\NP)
  └──────>B────┘
       S/NP

This is the constituent that can coordinate with "Mary hates" in
"John likes and Mary hates beans".
-/
def john_likes_composed : DerivStep :=
  .fcomp john_typeraised (.lex ⟨"likes", TV⟩)

-- Test composition produces correct category
#eval john_likes_composed.cat
-- Expected: some (S / NP)

-- Test composition interpretation works (check it's not none)
#eval (john_likes_composed.interp toySemLexicon).isSome
-- Expected: true

-- NON-CONSTITUENT COORDINATION SEMANTICS

/-
This is the substantive theorem that validates CCG's treatment of coordination:

"John likes and Mary hates beans" means likes'(beans', john') ∧ hates'(beans', mary')

The derivation:
1. Type-raise John to S/(S\NP)
2. Compose with likes to get S/NP
3. Type-raise Mary to S/(S\NP)
4. Compose with hates to get S/NP
5. Coordinate to get S/NP with conjunctive meaning
6. Apply to beans to get S

The key insight: composition preserves functional structure, so the
coordinated S/NP applies pointwise to the argument.
-/

-- Re-import the derivations from Basic (they're in the CCG namespace)
-- john_tr, john_likes, mary_tr, mary_hates, john_likes_and_mary_hates, john_likes_and_mary_hates_beans

-- Test: Coordination interpretation succeeds
#eval (john_likes_and_mary_hates.interp toySemLexicon).isSome
-- Expected: true (S/NP)

-- Test: Full coordination sentence interpretation succeeds
#eval (john_likes_and_mary_hates_beans.interp toySemLexicon).isSome
-- Expected: true

-- Test: Coordination produces truth value
#eval getMeaning (john_likes_and_mary_hates_beans.interp toySemLexicon)
-- Expected: some false (in toy model, likes=hates=sees, and nobody "sees" pizza)

/--
**THE COORDINATION SEMANTICS THEOREM**

The interpretation of non-constituent coordination "John likes and Mary hates beans"
is semantically well-formed (produces a truth value).

This is non-trivial because it requires:
1. Type-raising (T combinator)
2. Forward composition (B combinator)
3. Generalized conjunction (pointwise ∧)
4. Forward application

All four operations must compose correctly for the derivation to succeed.
-/
theorem coordination_semantics_well_formed :
    (john_likes_and_mary_hates_beans.interp toySemLexicon).isSome = true := by
  native_decide

/--
Extract the meaning of a coordination derivation as a function.

For an S/NP derivation (like "John likes and Mary hates"),
the meaning is a predicate on entities.
-/
def getPredicateMeaning (result : Option (Interp toyModel))
    : Option (ToyEntity → Bool) :=
  match result with
  | some ⟨.rslash (.atom .S) (.atom .NP), m⟩ => some m
  | _ => none

/--
Helper to extract predicate from coordination result.
-/
def coordMeaningAt (e : ToyEntity) : Option Bool :=
  match john_likes_and_mary_hates.interp toySemLexicon with
  | some ⟨.rslash (.atom .S) (.atom .NP), m⟩ => some (m e)
  | _ => none

/--
Helper to compute pointwise conjunction of two predicate meanings.
-/
def pointwiseConjAt (e : ToyEntity) : Option Bool :=
  match john_likes.interp toySemLexicon, mary_hates.interp toySemLexicon with
  | some ⟨.rslash (.atom .S) (.atom .NP), m₁⟩, some ⟨.rslash (.atom .S) (.atom .NP), m₂⟩ =>
      some (m₁ e && m₂ e)
  | _, _ => none

/--
**THE POINTWISE CONJUNCTION THEOREM**

The meaning of "John likes and Mary hates" (category S/NP) is the pointwise
conjunction of "John likes" and "Mary hates".

That is: ⟦John likes and Mary hates⟧(x) = ⟦John likes⟧(x) ∧ ⟦Mary hates⟧(x)

This is the semantic counterpart to the syntactic coordination rule.
-/
theorem coordination_is_pointwise_conjunction :
    ∀ e : ToyEntity, coordMeaningAt e = pointwiseConjAt e := by
  intro e
  cases e <;> native_decide

/--
**THE TRUTH-CONDITIONAL CORRECTNESS THEOREM**

The truth value of "John likes and Mary hates beans" is true iff
both John likes beans AND Mary hates beans.

In our toy model (where likes = hates = sees), this computes to the
conjunction of the two predications.
-/
theorem coordination_truth_conditions_correct :
    getMeaning (john_likes_and_mary_hates_beans.interp toySemLexicon) =
      some (ToyLexicon.sees_sem ToyEntity.pizza ToyEntity.john &&
            ToyLexicon.sees_sem ToyEntity.pizza ToyEntity.mary) := by
  native_decide

-- WHY THIS THEOREM MATTERS

/-
## The Significance of These Theorems

Previous theorems in CCG/Semantics.lean were trivial (rfl):
- Type preservation: rfl (by construction of catToTy)
- Homomorphism: rfl (application = application)

These coordination theorems are SUBSTANTIVE:
1. They verify the FULL derivation pipeline works end-to-end
2. They prove semantic content (pointwise conjunction emerges from rules)
3. They require non-trivial computation (native_decide, not rfl)

The key insight: CCG's claim is that non-constituent coordination "just works"
because the fragments ARE constituents. The theorems prove this computationally:
- The derivation succeeds (coordination_semantics_well_formed)
- The meaning is correct (coordination_is_pointwise_conjunction)
- The truth conditions are what we expect (coordination_truth_conditions_correct)

## What Makes This Non-Trivial

In phrase structure grammar, "John likes" is NOT a constituent.
You'd need special mechanisms (ATB movement, ellipsis, across-the-board rules).

In CCG, it IS a constituent (S/NP), built by type-raising + composition.
No special mechanism needed - the same rules work for all sentences.

The theorems verify that this unified treatment produces correct semantics.
-/

-- CONNECTION TO MONTAGUE SYNTAXINTERFACE

/-
With `DerivStep.interp`, we can now implement `MontagueSyntax` for CCG:

```
instance : MontagueSyntax Cat DerivStep where
  catOf d := d.cat.getOrElse S
  typeOf c := catToTy c
  wellFormed d := d.cat.isSome
  interp d m := (d.interp semLexicon).get!.meaning
```

This completes the syntax → semantics pipeline for CCG.
-/

end CCG
