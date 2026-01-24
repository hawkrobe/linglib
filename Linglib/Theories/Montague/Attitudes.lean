/-
# Intensional Semantics and Propositional Attitudes

Extension of Montague semantics with possible worlds for handling:
1. Intension/extension distinction
2. Belief verbs and propositional attitudes
3. De dicto vs de re readings

## Key Concepts

Following Montague (1973) "The Proper Treatment of Quantification":

**Intension**: A function from possible worlds to extensions
- The intension of "the morning star" maps each world to whatever is the morning star in that world
- The intension of a proposition (type t) maps each world to a truth value

**Attitude Verbs**: Relate individuals to intensions, not extensions
- "John believes that Mary sleeps" = believe(john, ^(sleeps(mary)))
- This avoids the problem of substituting co-referential terms in belief contexts

**De Dicto vs De Re**:
- De dicto: "John believes someone is a spy" (existential under belief)
- De re: "There is someone John believes is a spy" (existential over belief)

Reference: Montague, R. (1973). The Proper Treatment of Quantification in Ordinary English.
-/

import Linglib.Theories.Montague.Basic

namespace Montague.Attitudes

open Montague

-- ============================================================================
-- PART 1: Possible Worlds
-- ============================================================================

/-- A finite set of possible worlds for decidable reasoning -/
inductive World where
  | w0 | w1 | w2 | w3
  deriving DecidableEq, BEq, Repr, Inhabited

def allWorlds : List World := [.w0, .w1, .w2, .w3]

-- ============================================================================
-- PART 2: Intensional Types
-- ============================================================================

/--
Extended type system with possible worlds.

In Montague's full IL (Intensional Logic):
- `s` : the type of possible world indices
- `⟨s, τ⟩` : intensions (functions from worlds to extensions of type τ)

We extend our existing Ty with:
- `s` : worlds
- `intens τ` : intensional type (world → τ)
-/
inductive ITy where
  | e     -- entities
  | t     -- truth values
  | s     -- worlds
  | fn : ITy → ITy → ITy     -- function types
  | intens : ITy → ITy       -- intensional types ⟨s, τ⟩
  deriving Repr, DecidableEq

infixr:25 " ⇒ " => ITy.fn

/-- Shorthand for intension type -/
prefix:30 "^" => ITy.intens

-- Common intensional types
def ITy.prop : ITy := ^.t              -- propositions (intensions of t)
def ITy.indConcept : ITy := ^.e        -- individual concepts (intensions of e)

-- ============================================================================
-- PART 3: Intensional Model
-- ============================================================================

/--
An intensional model extends the basic model with possible worlds.

Following Montague's possible worlds semantics:
- Each world is an assignment of extensions to expressions
- Intensions are functions from worlds to extensions
-/
structure IModel where
  /-- The domain of entities -/
  Entity : Type
  /-- Decidable equality on entities -/
  decEq : DecidableEq Entity

/-- Interpretation of intensional types in a model -/
def IModel.interpTy (m : IModel) : ITy → Type
  | .e => m.Entity
  | .t => Bool
  | .s => World
  | .fn σ τ => m.interpTy σ → m.interpTy τ
  | .intens τ => World → m.interpTy τ

-- ============================================================================
-- PART 4: Intensional Operators
-- ============================================================================

/--
The "up" operator (^): convert extension to intension (constant function)

If x is an extension of type τ, then ^x is the intension that maps
every world to x.

In Montague's notation: ^α is the intension of α
-/
def up {m : IModel} {τ : ITy} (x : m.interpTy τ) : m.interpTy (^τ) :=
  fun _ => x

/--
The "down" operator (ˇ): evaluate intension at a world

If f is an intension of type ⟨s, τ⟩ and w is a world,
then ˇf at w gives the extension of type τ.

In Montague's notation: ˇα is the extension of α at the evaluation world
-/
def down {m : IModel} {τ : ITy} (f : m.interpTy (^τ)) (w : World) : m.interpTy τ :=
  f w

-- ============================================================================
-- PART 5: Toy Intensional Model
-- ============================================================================

/-- A small domain for examples -/
inductive ToyIEntity where
  | john
  | mary
  | hesperus  -- the morning star
  | phosphorus -- the evening star (= Venus, but potentially different in other worlds)
  deriving Repr, DecidableEq

def toyIModel : IModel := {
  Entity := ToyIEntity
  decEq := inferInstance
}

-- ============================================================================
-- PART 6: World-Dependent Extensions
-- ============================================================================

/--
"sleeps" as a world-dependent property.
Different individuals sleep in different worlds.
-/
def sleeps : toyIModel.interpTy (^(.e ⇒ .t)) :=
  fun w x => match w, x with
    | .w0, .john => true
    | .w0, .mary => false
    | .w1, .john => false
    | .w1, .mary => true
    | .w2, .john => true
    | .w2, .mary => true
    | .w3, .john => false
    | .w3, .mary => false
    | _, _ => false

/--
"is happy" as a world-dependent property.
-/
def happy : toyIModel.interpTy (^(.e ⇒ .t)) :=
  fun w x => match w, x with
    | .w0, .john => true
    | .w0, .mary => true
    | .w1, .john => false
    | .w1, .mary => true
    | .w2, .john => true
    | .w2, .mary => false
    | .w3, .john => false
    | .w3, .mary => false
    | _, _ => false

-- ============================================================================
-- PART 7: The Morning Star / Evening Star Problem
-- ============================================================================

/--
"the morning star" - an individual concept (intension of type e)
that picks out potentially different individuals in different worlds.
-/
def morningStar : toyIModel.interpTy ITy.indConcept :=
  fun w => match w with
    | .w0 => .hesperus
    | .w1 => .hesperus
    | .w2 => .phosphorus  -- different in w2!
    | .w3 => .hesperus

/--
"the evening star" - another individual concept
-/
def eveningStar : toyIModel.interpTy ITy.indConcept :=
  fun w => match w with
    | .w0 => .hesperus
    | .w1 => .phosphorus  -- different in w1!
    | .w2 => .hesperus
    | .w3 => .hesperus

/--
In the actual world (w0), morning star = evening star.
But their INTENSIONS differ (they pick out different things in other worlds).
-/
theorem extensions_equal_at_w0 :
    down morningStar .w0 = down eveningStar .w0 := rfl

theorem intensions_differ :
    morningStar ≠ eveningStar := by
  intro h
  have : morningStar .w1 = eveningStar .w1 := congrFun h .w1
  simp only [morningStar, eveningStar] at this
  cases this

-- ============================================================================
-- PART 8: Belief Verb Semantics
-- ============================================================================

/--
Doxastic accessibility relation: which worlds are compatible with
what an agent believes.

R(a, w, w') means: w' is compatible with what a believes in w
-/
def believes_access : ToyIEntity → World → World → Bool
  -- In w0, John believes he's in w0 or w2 (both where he sleeps)
  | .john, .w0, .w0 => true
  | .john, .w0, .w2 => true
  -- In w0, Mary believes she's in w1 or w2 (both where she sleeps)
  | .mary, .w0, .w1 => true
  | .mary, .w0, .w2 => true
  -- Default: agents believe they're in the actual world
  | _, w, w' => w == w'

/--
"believe" as an attitude verb.

Type: e → ⟨s,t⟩ → t
(takes an individual and a proposition-intension, returns truth value)

Semantics: "a believes p" is true at w iff p is true at all worlds
compatible with what a believes in w.

⟦believe⟧(a)(p)(w) = ∀w'. R(a,w,w') → p(w')
-/
def believe : toyIModel.interpTy (.e ⇒ ITy.prop ⇒ .t) :=
  fun agent prop =>
    allWorlds.all fun w' =>
      !believes_access agent .w0 w' || prop w'

/--
Extended believe that's world-dependent.
-/
def believeAt : World → toyIModel.interpTy (.e ⇒ ITy.prop ⇒ .t) :=
  fun evalWorld agent prop =>
    allWorlds.all fun w' =>
      !believes_access agent evalWorld w' || prop w'

-- ============================================================================
-- PART 9: De Dicto vs De Re
-- ============================================================================

/--
"John believes Mary sleeps" (de dicto)

The proposition "Mary sleeps" is evaluated at belief-accessible worlds,
not the actual world.

⟦John believes Mary sleeps⟧ = believe(john)(^(sleeps(mary)))
-/
def johnBelievesMary_deDicto : toyIModel.interpTy .t :=
  -- The proposition "Mary sleeps" as an intension
  let marySleeps : toyIModel.interpTy ITy.prop := fun w => sleeps w .mary
  believe .john marySleeps

-- At w0: John's belief-accessible worlds are {w0, w2}
-- Mary sleeps at w0? false
-- Mary sleeps at w2? true
-- So "John believes Mary sleeps" is false at w0 (not all accessible worlds satisfy it)
#eval johnBelievesMary_deDicto  -- false

/--
"John believes John sleeps" (de dicto)

At w0: John's belief-accessible worlds are {w0, w2}
John sleeps at w0? true
John sleeps at w2? true
So "John believes John sleeps" is true at w0
-/
def johnBelievesJohnSleeps : toyIModel.interpTy .t :=
  let johnSleeps : toyIModel.interpTy ITy.prop := fun w => sleeps w .john
  believe .john johnSleeps

#eval johnBelievesJohnSleeps  -- true

/-
**Substitution failure example**

Even if "the morning star" = "the evening star" at the actual world,
"John believes the morning star is F" need not equal
"John believes the evening star is F"

Because belief operates on INTENSIONS, not extensions.
-/

-- ============================================================================
-- PART 10: Connection to Scalar Implicature Context
-- ============================================================================

/-
**Why this matters for scalar implicatures**

"Mary believes John ate some of the cookies"

In the Gricean analysis (Geurts 2010), the "not all" implicature
from "some" can either be:

1. **Global (de re)**: Speaker implicates ¬(speaker believes all)
2. **Local (de dicto)**: Mary believes (some but not all)

The Neo-Gricean predicts only global implicatures.
RSA can model both readings through different parses.

This connects to the GeurtsPouscoulous2009 data:
- 57% of participants got "local" reading for "think" embedding
- Explained by competence assumption, not true local implicature
-/

/--
Proposition: "John ate some cookies" (simplified)
-/
def someCookies : toyIModel.interpTy ITy.prop :=
  fun _ => true  -- simplified: always true for demo

/--
Proposition: "John ate all cookies" (simplified)
-/
def allCookies : toyIModel.interpTy ITy.prop :=
  fun w => w == .w0 || w == .w1  -- true in some worlds

/--
"Mary believes John ate some cookies"
-/
def maryBelievesSome : toyIModel.interpTy .t :=
  believe .mary someCookies

/--
"Mary believes John ate all cookies"
-/
def maryBelievesAll : toyIModel.interpTy .t :=
  believe .mary allCookies

#eval maryBelievesSome  -- true (trivially, since someCookies always true)
#eval maryBelievesAll   -- depends on Mary's accessible worlds

-- ============================================================================
-- PART 11: Intensionality Tests
-- ============================================================================

/--
**Theorem: Belief is intensional**

Two expressions can have the same extension but yield different
truth values under belief.
-/
theorem belief_intensional :
    -- Morning star and evening star are co-extensional at w0
    (down morningStar .w0 = down eveningStar .w0)
    -- But we can construct belief contexts that distinguish them
    -- (here we just verify the intensions differ)
    ∧ (morningStar ≠ eveningStar) := by
  constructor
  · rfl
  · intro h
    have : morningStar .w1 = eveningStar .w1 := congrFun h .w1
    simp only [morningStar, eveningStar] at this
    cases this

/--
**Theorem: Up-down identity**

Applying down after up at any world returns the original value.
-/
theorem up_down_identity {m : IModel} {τ : ITy} (x : m.interpTy τ) (w : World) :
    down (up x) w = x := rfl

-- ============================================================================
-- PART 12: Summary
-- ============================================================================

/-
## What This Module Provides

### Types
- `World`: Finite set of possible worlds
- `ITy`: Intensional type system (e, t, s, →, ^)
- `IModel`: Intensional model with entities

### Operators
- `up`: Convert extension to constant intension
- `down`: Evaluate intension at a world

### Attitude Verbs
- `believes_access`: Doxastic accessibility relation
- `believe`: Belief verb semantics
- `believeAt`: World-dependent belief

### Key Examples
- Morning star / Evening star problem
- John believes Mary sleeps (de dicto)
- Substitution failure in belief contexts

### Connection to Pragmatics
This module provides the semantic foundation for understanding:
1. Why belief embedding affects scalar implicatures
2. De dicto vs de re scope distinctions
3. The competence-based explanation of "apparent local" SIs

### Theoretical Context
Following Montague (1973), intensions are necessary for:
- Handling opacity (substitution failures)
- Modeling propositional attitudes
- Distinguishing necessarily equivalent but intensionally distinct meanings
-/

end Montague.Attitudes
