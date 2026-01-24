/-
# Kratzer-Style Modal Semantics

Extension of Montague intensional semantics with Kratzer's (1977, 1981, 1991)
framework for context-dependent modality.

## Key Innovation: Conversational Backgrounds

Kratzer's insight: Modal domains aren't fixed - they're determined by context
through two parameters:

1. **Modal Base** `f`: world → set of propositions (the relevant "facts")
2. **Ordering Source** `g`: world → set of propositions (ideals/norms for ranking)

The accessibility relation is DERIVED from these:
- `R(w,w')` = w' is compatible with all propositions in f(w)

## Modal Flavors

Different conversational backgrounds yield different modal "flavors":
- **Epistemic**: f = what is known, g = ∅
- **Deontic**: f = circumstances, g = what the law requires
- **Teleological**: f = circumstances, g = goals
- **Bouletic**: f = circumstances, g = desires

## Attitudes as Modals

Attitude verbs can be analyzed as modals:
- "John believes P" = epistemic necessity relative to John's belief state
- "John wants P" = bouletic necessity relative to John's desires

References:
- Kratzer, A. (1977). What 'Must' and 'Can' Must and Can Mean.
- Kratzer, A. (1981). The Notional Category of Modality.
- Kratzer, A. (1991). Modality. In Semantics: An International Handbook.
- Heim, I. & Kratzer, A. (1998). Semantics in Generative Grammar.
-/

import Linglib.Theories.Montague.Attitudes

namespace Montague.Modality

open Montague.Attitudes

-- ============================================================================
-- PART 1: Propositions as Sets of Worlds
-- ============================================================================

/-- A proposition is a set of worlds (equivalently, World → Bool) -/
abbrev Proposition := World → Bool

/-- The set of all worlds where a proposition holds -/
def truthSet (p : Proposition) : List World :=
  allWorlds.filter p

/-- Check if world w satisfies proposition p -/
def satisfies (w : World) (p : Proposition) : Bool := p w

/-- Check if world w satisfies ALL propositions in a set -/
def satisfiesAll (w : World) (ps : List Proposition) : Bool :=
  ps.all (satisfies w)

-- ============================================================================
-- PART 2: Conversational Backgrounds
-- ============================================================================

/--
A conversational background maps worlds to sets of propositions.

Examples:
- "What is known": maps w to the set of propositions known at w
- "What the law requires": maps w to legal requirements at w
- "What John believes": maps w to John's beliefs at w
-/
def ConversationalBackground := World → List Proposition

/--
The modal base determines which worlds are "accessible" -
those compatible with the relevant facts.
-/
abbrev ModalBase := ConversationalBackground

/--
The ordering source ranks accessible worlds by how well they
satisfy certain ideals (laws, goals, desires, etc.).
-/
abbrev OrderingSource := ConversationalBackground

-- ============================================================================
-- PART 3: Derived Accessibility
-- ============================================================================

/--
Accessibility derived from modal base.

w' is accessible from w iff w' satisfies all propositions in f(w).
-/
def accessibleFrom (f : ModalBase) (w w' : World) : Bool :=
  satisfiesAll w' (f w)

/--
The set of worlds accessible from w given modal base f.
-/
def accessibleWorlds (f : ModalBase) (w : World) : List World :=
  allWorlds.filter (accessibleFrom f w)

-- ============================================================================
-- PART 4: Ordering on Worlds
-- ============================================================================

/--
Count how many propositions from the ordering source a world satisfies.
Higher count = "better" world according to the ideals.
-/
def idealScore (g : OrderingSource) (w : World) (w' : World) : Nat :=
  (g w).filter (satisfies w') |>.length

/--
`candidate` is at least as good as `other` (according to ordering source g at world w)
iff `candidate` satisfies at least as many ideal-propositions as `other`.

This is Kratzer's "ordering" on worlds.
-/
def atLeastAsGood (g : OrderingSource) (w : World) (candidate other : World) : Bool :=
  idealScore g w candidate ≥ idealScore g w other

/--
The "best" worlds: accessible worlds that are maximal according to ordering.

In the limit case (empty ordering source), all accessible worlds are "best".
-/
def bestWorlds (f : ModalBase) (g : OrderingSource) (w : World) : List World :=
  let accessible := accessibleWorlds f w
  if g w |>.isEmpty then
    accessible
  else
    -- Keep worlds that are at least as good as all others
    accessible.filter fun w' =>
      accessible.all fun w'' => atLeastAsGood g w w' w''

-- ============================================================================
-- PART 5: Modal Operators
-- ============================================================================

/--
Necessity (must/have to): proposition is true at ALL best accessible worlds.

⟦must⟧^{f,g}(p)(w) = ∀w' ∈ Best(f,g,w). p(w')
-/
def must (f : ModalBase) (g : OrderingSource) (p : Proposition) (w : World) : Bool :=
  (bestWorlds f g w).all p

/--
Possibility (can/may): proposition is true at SOME best accessible world.

⟦can⟧^{f,g}(p)(w) = ∃w' ∈ Best(f,g,w). p(w')
-/
def can (f : ModalBase) (g : OrderingSource) (p : Proposition) (w : World) : Bool :=
  (bestWorlds f g w).any p

/--
Simple necessity (no ordering): true at all accessible worlds.
This is what you get with empty ordering source.
-/
def mustSimple (f : ModalBase) (p : Proposition) (w : World) : Bool :=
  (accessibleWorlds f w).all p

/--
Simple possibility (no ordering): true at some accessible world.
-/
def canSimple (f : ModalBase) (p : Proposition) (w : World) : Bool :=
  (accessibleWorlds f w).any p

-- ============================================================================
-- PART 6: Modal Flavors
-- ============================================================================

/--
A modal flavor packages a modal base and ordering source.
Different flavors give different readings of the same modal verb.
-/
structure ModalFlavor where
  name : String
  base : ModalBase
  ordering : OrderingSource

-- Example propositions for building conversational backgrounds
def itIsRaining : Proposition := fun w => w == .w0 || w == .w1
def johnIsHome : Proposition := fun w => w == .w0 || w == .w2
def maryIsHome : Proposition := fun w => w == .w1 || w == .w2
def theGroundIsWet : Proposition := fun w => w == .w0 || w == .w1 || w == .w3

/--
Epistemic modal base: what is known (by the speaker).
Here: we know the ground is wet.
-/
def epistemicBase : ModalBase := fun _ => [theGroundIsWet]

/--
Empty ordering source (for pure epistemic modals).
-/
def emptyOrdering : OrderingSource := fun _ => []

/--
Epistemic flavor: "It must be raining" (given we know the ground is wet)
-/
def epistemicFlavor : ModalFlavor :=
  { name := "epistemic"
  , base := epistemicBase
  , ordering := emptyOrdering
  }

/--
Circumstantial modal base: the relevant circumstances.
Here: John is home.
-/
def circumstantialBase : ModalBase := fun w =>
  if johnIsHome w then [johnIsHome] else []

/--
Deontic ordering source: what the rules require.
Here: people should stay home when it rains.
-/
def deonticOrdering : OrderingSource := fun _ => [johnIsHome, maryIsHome]

/--
Deontic flavor: "John must stay home" (given the rules)
-/
def deonticFlavor : ModalFlavor :=
  { name := "deontic"
  , base := circumstantialBase
  , ordering := deonticOrdering
  }

-- ============================================================================
-- PART 7: Examples and Theorems
-- ============================================================================

/--
Epistemic "must": given the ground is wet, it must be raining.

Accessible worlds (where ground is wet): {w0, w1, w3}
Worlds where it's raining: {w0, w1}
Is it raining at ALL accessible worlds? No (w3 is accessible but not raining)
-/
def epistemicMustRaining : Bool :=
  must epistemicBase emptyOrdering itIsRaining .w0

#eval epistemicMustRaining  -- false (w3 is wet but not raining)

/--
Epistemic "can": given the ground is wet, it can be raining.
-/
def epistemicCanRaining : Bool :=
  can epistemicBase emptyOrdering itIsRaining .w0

#eval epistemicCanRaining  -- true (w0 and w1 are accessible and raining)

/--
If we know MORE (restrict the modal base), necessity becomes easier to satisfy.
-/
def strongerEpistemicBase : ModalBase := fun _ => [theGroundIsWet, itIsRaining]

def epistemicMustRainingStrong : Bool :=
  must strongerEpistemicBase emptyOrdering itIsRaining .w0

#eval epistemicMustRainingStrong  -- true (only raining worlds are accessible now)

/--
**Theorem: Stronger knowledge → easier necessity**

Adding propositions to modal base restricts accessible worlds,
making necessity easier to achieve.
-/
theorem stronger_base_easier_necessity :
    -- With weak base, "must rain" is false
    must epistemicBase emptyOrdering itIsRaining .w0 = false ∧
    -- With stronger base, "must rain" is true
    must strongerEpistemicBase emptyOrdering itIsRaining .w0 = true := by
  native_decide

-- ============================================================================
-- PART 8: Attitudes as Modals
-- ============================================================================

/--
Belief as epistemic modality.

"John believes P" = P is necessary given John's doxastic state.
The modal base is: what John believes.
-/
def johnBelievesBase : ModalBase := fun w =>
  -- What John believes varies by world
  match w with
  | .w0 => [johnIsHome]  -- In w0, John believes he's home
  | .w1 => [itIsRaining] -- In w1, John believes it's raining
  | _ => []

/--
"John believes he is home" at w0
-/
def johnBelievesHome : Bool :=
  must johnBelievesBase emptyOrdering johnIsHome .w0

#eval johnBelievesHome  -- true

/--
Want as bouletic modality.

"John wants P" = P is necessary given John's desires.
Modal base: circumstances, Ordering: John's desires.
-/
def johnsDesiresOrdering : OrderingSource := fun _ => [johnIsHome, maryIsHome]

def johnWantsEveryoneHome : Bool :=
  -- Best worlds according to John's desires are those where everyone is home
  must (fun _ => []) johnsDesiresOrdering (fun w => johnIsHome w && maryIsHome w) .w0

#eval johnWantsEveryoneHome  -- depends on which worlds maximize desires

-- ============================================================================
-- PART 9: Connection to Simple Attitudes
-- ============================================================================

/--
The simple belief from Attitudes.lean is a special case:
- Modal base = agent's belief state (fixed accessibility)
- Ordering source = empty

This shows how Kratzer generalizes Montague's treatment.
-/
def simpleBeliefAsModal (agent : ToyIEntity) (p : Proposition) : Bool :=
  let beliefBase : ModalBase := fun w =>
    -- Convert the accessibility relation to a modal base
    allWorlds.filter (believes_access agent w) |>.map fun w' =>
      (fun w'' => w'' == w' : Proposition)
  must beliefBase emptyOrdering p .w0

/--
**Theorem: Simple belief matches modal belief**

When we use the Attitudes.lean accessibility relation as a modal base,
we get the same truth conditions.
-/
theorem attitudes_belief_is_modal_belief :
    -- John believes John sleeps (from Attitudes.lean style)
    (allWorlds.filter (believes_access .john .w0)).all (fun w => sleeps w .john)
    =
    -- John believes John sleeps (modal style)
    simpleBeliefAsModal .john (fun w => sleeps w .john) := by
  native_decide

-- ============================================================================
-- PART 10: Graded Modality
-- ============================================================================

/--
Kratzer's framework supports GRADED modality through the ordering source.

"It's more likely that P than Q" can be captured by comparing
how P and Q fare across the ordering.
-/
def moreNecessary (f : ModalBase) (g : OrderingSource)
    (p q : Proposition) (w : World) : Bool :=
  -- p is "more necessary" if it holds at more of the best worlds
  let best := bestWorlds f g w
  (best.filter p).length > (best.filter q).length

/--
Comparative possibility: "It's more likely to be raining than snowing"
-/
def itIsSnowing : Proposition := fun w => w == .w3

def rainingMoreLikelyThanSnowing : Bool :=
  moreNecessary epistemicBase emptyOrdering itIsRaining itIsSnowing .w0

#eval rainingMoreLikelyThanSnowing  -- true (2 raining worlds vs 1 snowing in accessible set)

-- ============================================================================
-- PART 11: Summary
-- ============================================================================

/-
## What This Module Provides

### Core Types
- `Proposition`: World → Bool
- `ConversationalBackground`: World → List Proposition
- `ModalBase`: Facts that determine accessibility
- `OrderingSource`: Ideals that rank accessible worlds
- `ModalFlavor`: Packaged modal base + ordering

### Derived Notions
- `accessibleFrom`: Derived accessibility relation
- `accessibleWorlds`: Set of accessible worlds
- `bestWorlds`: Accessible worlds maximal under ordering

### Modal Operators
- `must`: Universal quantification over best worlds
- `can`: Existential quantification over best worlds
- `mustSimple`/`canSimple`: Without ordering (pure accessibility)

### Modal Flavors
- `epistemicFlavor`: Knowledge-based ("It must be raining")
- `deonticFlavor`: Norm-based ("You must stay home")

### Attitudes as Modals
- Belief = epistemic necessity relative to doxastic state
- Want = bouletic necessity relative to desires
- `simpleBeliefAsModal`: Shows Attitudes.lean is a special case

### Key Theorems
- `stronger_base_easier_necessity`: More knowledge → easier necessity
- `attitudes_belief_is_modal_belief`: Unifies with Attitudes.lean

### Relationship to Attitudes.lean
This module EXTENDS Attitudes.lean:
- Reuses: World, intensions, basic proposition type
- Adds: Conversational backgrounds, derived accessibility, ordering
- Shows: Simple attitudes are a special case of Kratzer modality
-/

end Montague.Modality
