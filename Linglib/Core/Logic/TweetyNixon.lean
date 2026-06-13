import Mathlib.Data.Fintype.Basic

/-!
# Tweety Triangle and Nixon Diamond
[veltman-1996] [goldszmidt-pearl-1996] [asher-pelletier-2012]

The two classic default-reasoning testbeds, as finite world types shared
by the rival accounts in `Studies/Veltman1996`, `Studies/GoldszmidtPearl1996`,
and `Studies/AsherPelletier2013`:

1. **Tweety Triangle** (specificity): birds normally fly; penguins are
   birds; penguins normally don't fly. The more specific default wins.
2. **Nixon Diamond** (conflicting defaults): Quakers are normally
   pacifist; Republicans are normally not; Nixon is both.

## Main declarations

- `TweetyWorld`, `isBird`, `isPenguin`, `flies`, `penguin_is_bird`
- `NixonWorld`, `isQuaker`, `isRepublican`, `isPacifist`
-/

namespace Core.Logic.TweetyNixon

/-- The Tweety world: 4 possible states of an entity. -/
inductive TweetyWorld : Type where
  | birdFlies      -- bird, not penguin, flies
  | birdNoFly      -- bird, not penguin, doesn't fly
  | penguinFlies   -- penguin (hence bird), flies
  | penguinNoFly   -- penguin (hence bird), doesn't fly
  deriving DecidableEq, Repr

instance : Fintype TweetyWorld :=
  ⟨⟨[TweetyWorld.birdFlies, TweetyWorld.birdNoFly,
     TweetyWorld.penguinFlies, TweetyWorld.penguinNoFly], by decide⟩,
   fun w => by cases w <;> decide⟩

open TweetyWorld

def isBird : TweetyWorld → Prop
  | birdFlies => True
  | birdNoFly => True
  | penguinFlies => True
  | penguinNoFly => True

instance : DecidablePred isBird := fun w => by cases w <;> unfold isBird <;> infer_instance

def isPenguin : TweetyWorld → Prop
  | penguinFlies => True
  | penguinNoFly => True
  | _ => False

instance : DecidablePred isPenguin :=
  fun w => by cases w <;> unfold isPenguin <;> infer_instance

def flies : TweetyWorld → Prop
  | birdFlies => True
  | penguinFlies => True
  | _ => False

instance : DecidablePred flies :=
  fun w => by cases w <;> unfold flies <;> infer_instance

/-- Every penguin is a bird. -/
theorem penguin_is_bird : ∀ w, isPenguin w → isBird w := by
  intro w hw; cases w <;> simp_all [isPenguin, isBird]

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

end Core.Logic.TweetyNixon
