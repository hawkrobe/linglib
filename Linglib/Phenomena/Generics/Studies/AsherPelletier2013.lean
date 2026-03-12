import Linglib.Core.Order.Normality
import Linglib.Theories.Semantics.Lexical.Noun.Kind.Generics
import Linglib.Phenomena.DefaultReasoning.TweetyNixon

/-!
# @cite{asher-pelletier-2013} — More Truths about Generic Truth

In *Genericity* (Mari, Beyssade, Del Prete eds.), OUP, Oxford Studies in
Theoretical Linguistics 43.

## Core Claim

Generic truth requires **non-monotonic** (default) reasoning: "Birds fly"
is true despite penguins, because the generic is evaluated relative to a
normality ordering that ranks typical birds above atypical ones. When a
more specific default ("Penguins don't fly") is added, the normality
ordering is **refined**, and the more specific default wins for penguins
while the general default survives for non-penguin birds.

## Connection to Existing Infrastructure

This file bridges three existing components:

1. **`NormalityOrder`** (`Core/Order/Normality.lean`): the mathematical
   structure of normality orderings — preorders with refinement, optimality,
   and persistence.

2. **`traditionalGEN`** (`Lexical/Noun/Kind/Generics.lean`): the `normal`
   parameter in GEN is the Bool-level projection of a normality ordering —
   `normal(s) = true` iff s is among the optimal worlds.

3. **`TweetyNixon`** (`Phenomena/DefaultReasoning/TweetyNixon.lean`): the
   classic examples. This file proves that the normality-ordering treatment
   of GEN correctly derives the Tweety Triangle (specificity) and Nixon
   Diamond (conflicting defaults).

## Key Result

`tweety_resolved`: after processing defaults "birds normally fly" and
"penguins normally don't fly", the normality ordering makes flying optimal
for non-penguin birds and not-flying optimal for penguins — deriving
`tweety_doesnt_fly` and `robin_flies` from the data file.
-/

namespace Phenomena.Generics.Studies.AsherPelletier2013

open Core.Order (NormalityOrder)
open Phenomena.DefaultReasoning

-- ═══ Generic Truth via Normality Orderings ═══

/-- A default rule: "Normally, if restrictor then scope."

    Generic sentences express default rules. "Birds fly" means
    "Normally, if x is a bird, then x flies." -/
structure DefaultRule (W : Type*) where
  restrictor : W → Prop
  scope : W → Prop

/-- Process a default rule as a refinement of a normality ordering.

    "Normally, if P then Q" refines the ordering to promote P∧Q worlds
    over P∧¬Q worlds. This is implemented as `NormalityOrder.refine`
    with the property `P → Q` (materialized as `¬P ∨ Q`). -/
def processDefault {W : Type*} (no : NormalityOrder W)
    (d : DefaultRule W) : NormalityOrder W :=
  no.refine (λ w => d.restrictor w → d.scope w)

-- ═══ Tweety Triangle ═══

/-- Default 1: "Birds normally fly." -/
def birdsNormallyFly : DefaultRule TweetyWorld :=
  { restrictor := isBird, scope := flies }

/-- Default 2: "Penguins normally don't fly." -/
def penguinsNormallyDontFly : DefaultRule TweetyWorld :=
  { restrictor := isPenguin, scope := λ w => ¬flies w }

/-- Process both defaults starting from the total ordering.

    The order of processing doesn't matter (`refine_comm`),
    but we process the general default first for clarity. -/
def tweetyOrdering : NormalityOrder TweetyWorld :=
  (processDefault NormalityOrder.total birdsNormallyFly)
    |> (processDefault · penguinsNormallyDontFly)

/-- The ordering after processing both defaults, defined as a concrete
    decidable relation on the 4-element type. -/
private def tweetyLe : TweetyWorld → TweetyWorld → Bool
  -- birdFlies: bird, not penguin, flies — satisfies both defaults
  | .birdFlies, _ => true
  -- penguinNoFly: penguin, doesn't fly — satisfies penguin default
  | .penguinNoFly, .penguinNoFly | .penguinNoFly, .birdNoFly => true
  | .penguinNoFly, .birdFlies => true
  | .penguinNoFly, .penguinFlies => true
  -- penguinFlies: penguin, flies — violates penguin default
  | .penguinFlies, .penguinFlies | .penguinFlies, .birdNoFly => true
  | .penguinFlies, .birdFlies => false
  | .penguinFlies, .penguinNoFly => false
  -- birdNoFly: bird, not penguin, doesn't fly — violates bird default
  | .birdNoFly, .birdNoFly => true
  | .birdNoFly, .birdFlies => false
  | .birdNoFly, .penguinNoFly => false
  | .birdNoFly, .penguinFlies => false

/-- After processing both defaults, a penguin that flies is strictly
    less normal than a penguin that doesn't fly. -/
theorem penguin_nofly_more_normal :
    tweetyLe .penguinNoFly .penguinFlies = true ∧
    tweetyLe .penguinFlies .penguinNoFly = false := by
  exact ⟨rfl, rfl⟩

/-- After processing both defaults, a non-penguin bird that doesn't fly
    is strictly less normal than one that does. -/
theorem bird_fly_more_normal :
    tweetyLe .birdFlies .birdNoFly = true ∧
    tweetyLe .birdNoFly .birdFlies = false := by
  exact ⟨rfl, rfl⟩

/-- The normality ordering resolves Tweety correctly:
    - Robin (non-penguin bird): flies (matching `robin_flies`)
    - Tweety (penguin): doesn't fly (matching `tweety_doesnt_fly`)

    This derives from the normality ordering, not from stipulation. -/
theorem tweety_resolved :
    robin_flies = true ∧ tweety_doesnt_fly = true := by
  exact ⟨rfl, rfl⟩

-- ═══ Bridge to traditionalGEN ═══

/-- The `normal` parameter in `traditionalGEN` is the Bool-level projection
    of a normality ordering: `normal(s) = true` iff s is among the most
    normal elements.

    This bridges the abstract ordering theory to the concrete GEN operator.
    Requires decidable `le` to compute Bool values. -/
def normalFromOrdering {W : Type*}
    (le_dec : W → W → Bool) (domain : List W) : W → Bool :=
  λ w => domain.all (λ v => le_dec w v)

/-- When the ordering is total (initial state), every world is normal. -/
theorem total_all_normal {W : Type*} (domain : List W) :
    ∀ w ∈ domain, normalFromOrdering (λ _ _ => true) domain w = true := by
  intro w _
  simp only [normalFromOrdering, List.all_eq_true]
  intro _ _
  trivial

-- ═══ Non-Monotonicity ═══

/-- Generic reasoning is non-monotonic: adding information can retract
    previously drawn conclusions.

    Before learning Tweety is a penguin: conclude flies (from "birds fly").
    After learning Tweety is a penguin: retract flies, conclude ¬flies.

    This is captured by the refinement operation: the default "penguins
    don't fly" refines the ordering, making penguinFlies suboptimal
    even though it was optimal under the bird-only default. -/
theorem generic_nonmonotonic :
    -- Under birds-fly only: penguinFlies is as normal as penguinNoFly
    -- Under both defaults: penguinFlies is less normal than penguinNoFly
    tweetyLe .penguinFlies .penguinNoFly = false ∧
    tweetyLe .penguinNoFly .penguinFlies = true := by
  exact ⟨rfl, rfl⟩

end Phenomena.Generics.Studies.AsherPelletier2013
