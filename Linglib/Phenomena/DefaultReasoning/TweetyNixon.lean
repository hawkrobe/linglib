/-!
# Default Reasoning: Classic Examples

Theory-neutral data for two classic default reasoning examples:

1. **Tweety Triangle** (Reiter 1980): Birds normally fly. Tweety is a
   bird. Tweety is a penguin. Penguins are birds. Penguins normally
   don't fly. Conclusion: Tweety presumably doesn't fly (the more
   specific default wins).

2. **Nixon Diamond** (multiple attributions): Quakers are normally
   pacifist. Republicans are normally not pacifist. Nixon is both a
   Quaker and a Republican. Conclusion: agnosticism — neither
   "presumably pacifist" nor "presumably not pacifist" follows.

These examples test *specificity* (Tweety) and *conflicting defaults*
(Nixon). Both require conditional defaults ("if φ then normally ψ")
to formalize properly — unconditional defaults can only express the
degenerate case.
-/

namespace Phenomena.DefaultReasoning

-- ═══ Tweety Triangle ═══

/-- The Tweety world: 4 possible states of an entity. -/
inductive TweetyWorld : Type where
  | birdFlies      -- bird, not penguin, flies
  | birdNoFly      -- bird, not penguin, doesn't fly
  | penguinFlies   -- penguin (hence bird), flies
  | penguinNoFly   -- penguin (hence bird), doesn't fly
  deriving DecidableEq, Repr

open TweetyWorld

def isBird : TweetyWorld → Prop
  | birdFlies => True
  | birdNoFly => True
  | penguinFlies => True
  | penguinNoFly => True

def isPenguin : TweetyWorld → Prop
  | penguinFlies => True
  | penguinNoFly => True
  | _ => False

def flies : TweetyWorld → Prop
  | birdFlies => True
  | penguinFlies => True
  | _ => False

/-- Every penguin is a bird. -/
theorem penguin_is_bird : ∀ w, isPenguin w → isBird w := by
  intro w hw; cases w <;> simp_all [isPenguin, isBird]

/-- Empirical judgment: given "birds normally fly" and "penguins
    normally don't fly", Tweety (a penguin) presumably doesn't fly.
    The more specific default (penguins) overrides the general one
    (birds). -/
def tweety_doesnt_fly : Bool := true

/-- Empirical judgment: non-penguin birds presumably do fly. -/
def robin_flies : Bool := true


-- ═══ Nixon Diamond ═══

/-- The Nixon world: 4 possible states. -/
inductive NixonWorld : Type where
  | quakerPacifist     -- Quaker, pacifist
  | quakerNotPacifist  -- Quaker, not pacifist
  | repPacifist        -- Republican, pacifist
  | repNotPacifist     -- Republican, not pacifist
  deriving DecidableEq, Repr

open NixonWorld

def isQuaker : NixonWorld → Prop
  | quakerPacifist => True
  | quakerNotPacifist => True
  | _ => False

def isRepublican : NixonWorld → Prop
  | repPacifist => True
  | repNotPacifist => True
  | _ => False

def isPacifist : NixonWorld → Prop
  | quakerPacifist => True
  | repPacifist => True
  | _ => False

/-- Empirical judgment: given conflicting defaults ("Quakers normally
    pacifist", "Republicans normally not pacifist"), a Quaker Republican
    is agnostic — neither "presumably pacifist" nor "presumably not
    pacifist" should follow. -/
def nixon_agnostic : Bool := true


end Phenomena.DefaultReasoning
