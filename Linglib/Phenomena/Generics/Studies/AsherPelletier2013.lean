import Linglib.Core.Order.Normality
import Linglib.Theories.Semantics.Lexical.Noun.Kind.Generics
import Linglib.Phenomena.DefaultReasoning.TweetyNixon

/-!
# @cite{asher-pelletier-2012} — More Truths about Generic Truth

Nicholas Asher and Francis Jeffry Pelletier, ch. 12 of
*Genericity* (Mari, Beyssade, Del Prete eds.), OUP, Oxford Studies in
Theoretical Linguistics 43.

## Core Claim

Generics should be analyzed as **modal quantifiers** — ∀x(φ(x) > ψ(x)),
where > is a weak conditional (from Asher & Morreau 1991). The key
innovation is **per-individual evaluation** (§12.3): ψ is evaluated for
each individual *a* only in those worlds where *a* is a normal φ.

"Birds fly" is true because for each bird *a*, the most normal *a*-bird
worlds are ones where *a* flies. For Opus the penguin, the normal
Opus-penguin worlds are NOT normal Opus-bird worlds, so "Penguins don't
fly" correctly overrides "Birds fly" for penguins (exx. 7–8).

## Chapter Sections Covered

- **§12.1–12.2**: Framework and challenges (exx. 1–5)
- **§12.3**: Per-individual normality (exx. 6–9)
- **§12.4**: Arguments against probabilistic alternatives

## Connection to Existing Infrastructure

1. **`NormalityOrder`** (`Core/Order/Normality.lean`): preorder structure
   on worlds. A&P's per-individual normality is a normality ordering
   *per entity and restrictor class*.

2. **`traditionalGEN`** (`Lexical/Noun/Kind/Generics.lean`): GEN's `normal`
   parameter is the Bool-level projection of a normality ordering.

3. **`TweetyNixon`** (`Phenomena/DefaultReasoning/TweetyNixon.lean`):
   the Tweety Triangle data — the classic test case for A&P's system.

## Refinement vs Specificity

`processDefault` below uses `NormalityOrder.refine` (@cite{veltman-1996}'s
operation), which intersects ordering constraints. For the Tweety Triangle,
Veltman's refinement produces **incomparability** between penguinFlies and
penguinNoFly (neither is ≤ the other, since each satisfies one default
and violates the other). A&P's per-individual evaluation resolves this
via **specificity**: the more specific "penguins don't fly" overrides
"birds fly" for penguins. The `tweetyLe` ordering encodes this
specificity-resolved result directly.
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
    over P∧¬Q worlds via `NormalityOrder.refine`. This is
    @cite{veltman-1996}'s monotonic (intersection-based) operation.

    Note: A&P's actual system uses per-individual evaluation with
    specificity, which goes beyond simple refinement. See the module
    docstring caveat about refinement vs specificity. -/
def processDefault {W : Type*} (no : NormalityOrder W)
    (d : DefaultRule W) : NormalityOrder W :=
  no.refine (λ w => d.restrictor w → d.scope w)


-- ═══ Per-Individual Evaluation (§12.3, exx. 7–9) ═══

/-- Per-individual evaluation data from §12.3.

    The chapter's key innovation: for ∀x(φ(x) > ψ(x)), the consequent
    ψ is evaluated per-individual. For individual *a* in the domain,
    we look at normal *a*-φ worlds — worlds where *a* is a normal φ. -/
structure PerIndividualDatum where
  sentence : String
  individual : String
  restrictorClass : String
  normalWorldDesc : String
  scopeHolds : Bool
  exNumber : String
  deriving Repr

/-- Ex. (7): "Penguins don't fly" — evaluated for Opus.
    Normal Opus-PENGUIN worlds: Opus doesn't fly. Scope (¬fly) holds. -/
def opusPenguinsDontFly : PerIndividualDatum :=
  { sentence := "Penguins don't fly"
  , individual := "Opus"
  , restrictorClass := "penguin"
  , normalWorldDesc := "Normal Opus-penguin worlds: Opus doesn't fly"
  , scopeHolds := true
  , exNumber := "(7)" }

/-- Ex. (8): "Birds fly" — evaluated for Opus.
    Normal Opus-BIRD worlds: in those worlds, Opus is "definitely not
    a normal penguin." So Opus flies. Scope (fly) holds.

    Key insight: both "Birds fly" and "Penguins don't fly" are true
    SIMULTANEOUSLY for the same individual — evaluated at different
    normal worlds (normal-bird vs normal-penguin worlds). -/
def opusBirdsFly : PerIndividualDatum :=
  { sentence := "Birds fly"
  , individual := "Opus"
  , restrictorClass := "bird"
  , normalWorldDesc := "Normal Opus-bird worlds: Opus is not a penguin"
  , scopeHolds := true
  , exNumber := "(8)" }

/-- Both generics are simultaneously true for penguins.
    Per-individual evaluation evaluates at DIFFERENT normal worlds
    for each restrictor, so both can hold without contradiction. -/
theorem both_generics_true :
    opusPenguinsDontFly.scopeHolds = true ∧
    opusBirdsFly.scopeHolds = true := ⟨rfl, rfl⟩

/-- Specificity determines which default to apply for inference:
    the more specific "penguins don't fly" overrides "birds fly"
    for penguins. This is a property of defeasible inference with
    the > conditional, not of the per-individual evaluation itself. -/
theorem specificity_selects_penguin_default :
    opusPenguinsDontFly.scopeHolds = true ∧
    tweety_doesnt_fly = true := ⟨rfl, rfl⟩


-- ═══ Context-Dependent Normality (§12.3, ex. 9) ═══

/-- §12.3, ex. (9): "Turtles live to be 100."

    The notion of a "normal φ(a) world" has some "give" to it —
    different construals of normality yield different truth values.
    Under an Aristotelian/teleological conception (natural telos of
    a turtle: if everything goes right), it's true. Under a statistical
    conception (most turtles die within hours of hatching), it's false.

    A&P consider this context-dependence a virtue: discourse and
    contextual factors fix the normality construal. -/
structure NormalityConstrual where
  sentence : String
  construal : String
  genericTrue : Bool
  exNumber : String
  deriving Repr

def turtlesTeleological : NormalityConstrual :=
  { sentence := "Turtles live to be 100"
  , construal := "Aristotelian/teleological: natural telos of a turtle"
  , genericTrue := true
  , exNumber := "(9)" }

def turtlesStatistical : NormalityConstrual :=
  { sentence := "Turtles live to be 100"
  , construal := "Statistical: most turtles die within hours of hatching"
  , genericTrue := false
  , exNumber := "(9)" }

/-- The same generic has different truth values under different
    normality construals — A&P's "slop" in the normality notion. -/
theorem normality_context_dependent :
    turtlesTeleological.genericTrue ≠ turtlesStatistical.genericTrue := by
  decide


-- ═══ Tweety Triangle ═══

/-- Default 1: "Birds normally fly." -/
def birdsNormallyFly : DefaultRule TweetyWorld :=
  { restrictor := isBird, scope := flies }

/-- Default 2: "Penguins normally don't fly." -/
def penguinsNormallyDontFly : DefaultRule TweetyWorld :=
  { restrictor := isPenguin, scope := λ w => ¬flies w }

/-- Veltman-style refinement of both defaults.

    This uses `NormalityOrder.refine` to process both defaults. The
    result makes penguinNoFly and penguinFlies **incomparable** — neither
    is ≤ the other — because the two defaults create crossing constraints.
    (penguinFlies satisfies "birds fly" but violates "penguins don't fly";
    penguinNoFly does the reverse.)

    This matches the Nixon Diamond behavior (conflicting defaults →
    agnosticism), not the Tweety Triangle (specificity resolution).
    A&P's per-individual evaluation resolves this via specificity,
    encoded in `tweetyLe` below.

    The order of processing doesn't matter (`NormalityOrder.refine_comm`). -/
def tweetyOrdering : NormalityOrder TweetyWorld :=
  (processDefault NormalityOrder.total birdsNormallyFly)
    |> (processDefault · penguinsNormallyDontFly)

/-- The **specificity-resolved** normality ordering for the Tweety Triangle.

    This encodes the result of A&P's per-individual evaluation with
    specificity: the more specific penguin default overrides the general
    bird default for penguins. The ordering has two tiers:

    - Top: {birdFlies, penguinNoFly} — each satisfies its most specific default
    - Middle: {penguinFlies} — violates the more specific penguin default
    - Bottom: {birdNoFly} — violates the bird default with no override -/
private def tweetyLe : TweetyWorld → TweetyWorld → Bool
  -- birdFlies: satisfies bird default, not a penguin → top tier
  | .birdFlies, _ => true
  -- penguinNoFly: penguin default overrides bird default → top tier
  | .penguinNoFly, .penguinNoFly | .penguinNoFly, .birdNoFly => true
  | .penguinNoFly, .birdFlies => true
  | .penguinNoFly, .penguinFlies => true
  -- penguinFlies: violates more specific penguin default → middle
  | .penguinFlies, .penguinFlies | .penguinFlies, .birdNoFly => true
  | .penguinFlies, .birdFlies => false
  | .penguinFlies, .penguinNoFly => false
  -- birdNoFly: violates bird default, no override → bottom
  | .birdNoFly, .birdNoFly => true
  | .birdNoFly, .birdFlies => false
  | .birdNoFly, .penguinNoFly => false
  | .birdNoFly, .penguinFlies => false

/-- Specificity resolution: penguinNoFly is strictly more normal than
    penguinFlies (the more specific penguin default wins). -/
theorem penguin_nofly_more_normal :
    tweetyLe .penguinNoFly .penguinFlies = true ∧
    tweetyLe .penguinFlies .penguinNoFly = false := ⟨rfl, rfl⟩

/-- The bird default applies for non-penguin birds: birdFlies is
    strictly more normal than birdNoFly. -/
theorem bird_fly_more_normal :
    tweetyLe .birdFlies .birdNoFly = true ∧
    tweetyLe .birdNoFly .birdFlies = false := ⟨rfl, rfl⟩

/-- The empirical judgments match: Robin flies, Tweety doesn't. -/
theorem tweety_resolved :
    robin_flies = true ∧ tweety_doesnt_fly = true := ⟨rfl, rfl⟩


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

/-- Under the specificity-resolved ordering, the normal TweetyWorlds
    (those in the top tier) are exactly birdFlies and penguinNoFly. -/
theorem tweety_normal_worlds :
    let domain := [TweetyWorld.birdFlies, .birdNoFly, .penguinFlies, .penguinNoFly]
    normalFromOrdering tweetyLe domain .birdFlies = true ∧
    normalFromOrdering tweetyLe domain .penguinNoFly = true ∧
    normalFromOrdering tweetyLe domain .penguinFlies = false ∧
    normalFromOrdering tweetyLe domain .birdNoFly = false := ⟨rfl, rfl, rfl, rfl⟩


-- ═══ Challenges (§12.2, exx. 4–5) ═══

/-- Challenge examples from §12.2 that the simple modal analysis ∀x(φ > ψ)
    appears to predict wrongly. -/
structure ChallengeDatum where
  sentence : String
  challenge : String
  exNumber : String
  deriving Repr

/-- Ex. (4a): "Ducks lay eggs" — the basic analysis predicts normal
    male ducks lay eggs, which is wrong. -/
def ducksLayEggs : ChallengeDatum :=
  { sentence := "Ducks lay eggs"
  , challenge := "Predicts normal male ducks lay eggs"
  , exNumber := "(4a)" }

/-- Ex. (4b): "Cardinals are bright red" — predicts normal female
    cardinals are bright red, which is wrong. -/
def cardinalsRed : ChallengeDatum :=
  { sentence := "Cardinals are bright red"
  , challenge := "Predicts normal female cardinals are bright red"
  , exNumber := "(4b)" }

/-- Ex. (5): "Mosquitoes carry the West Nile Virus" — true despite
    a vanishingly small percentage of normal mosquitoes carrying WNV. -/
def mosquitoesWNV : ChallengeDatum :=
  { sentence := "Mosquitoes carry the West Nile Virus"
  , challenge := "True despite vanishingly small percentage carrying WNV"
  , exNumber := "(5)" }

def challengeData : List ChallengeDatum :=
  [ducksLayEggs, cardinalsRed, mosquitoesWNV]


-- ═══ Against Probabilistic Alternatives (§12.4) ═══

/-- A&P's arguments against @cite{cohen-1999a}'s probabilistic semantics
    for generics.

    Cohen proposes generic truth ↔ Pr(B(a)|A(a)) > 0.5 (the "Cohen
    conditional"). A&P argue this is inadequate for three reasons. -/
inductive AntiProbArgument where
  /-- Too weak: Pr(tails|coin-flip) ≈ 50.05% → "*This coin normally
      comes up tails" should NOT be a true generic. -/
  | tooWeak
  /-- Wrong inference pattern: probabilistic semantics validates Modus
      Ponens (Pr(B|A) > 0.5 and A(a) → B(a) more likely than not) but
      NOT Defeasible Modus Ponens. Generics support the latter ("Birds
      fly, Tweety is a bird, so Tweety flies") but the inference is
      defeasible. -/
  | wrongInference
  /-- Embedded generics ("Dogs chase cats that chase mice") require
      higher-order probabilities, leading to triviality results. -/
  | embeddedGenerics
  deriving DecidableEq, Repr


-- ═══ Non-Monotonicity ═══

/-- Generic reasoning is non-monotonic: the specificity-resolved ordering
    makes penguinNoFly top-tier (equally normal as birdFlies), despite
    penguinNoFly violating the "birds fly" default. The more specific
    penguin default overrides.

    Adding the information "Tweety is a penguin" retracts the conclusion
    "Tweety flies" and replaces it with "Tweety doesn't fly." -/
theorem generic_nonmonotonic :
    -- penguinNoFly is in the top tier (as normal as birdFlies)
    tweetyLe .penguinNoFly .birdFlies = true ∧
    tweetyLe .birdFlies .penguinNoFly = true ∧
    -- penguinFlies is strictly below the top tier
    tweetyLe .penguinFlies .penguinNoFly = false ∧
    tweetyLe .penguinFlies .birdFlies = false := ⟨rfl, rfl, rfl, rfl⟩

end Phenomena.Generics.Studies.AsherPelletier2013
