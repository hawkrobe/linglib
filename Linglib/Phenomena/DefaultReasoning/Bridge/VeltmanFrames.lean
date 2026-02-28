import Linglib.Phenomena.DefaultReasoning.TweetyNixon
import Linglib.Theories.Semantics.Dynamic.Effects.Default.Frames

/-!
# Bridge: Veltman (1996) Frames → Tweety/Nixon

@cite{veltman-1996}

Regression tests for `ExpFrame.normal`. The subdomain check is
essential: without it, `penguinFlies_not_normal_in_birds` fails.
-/

namespace Phenomena.DefaultReasoning.Bridge

open Phenomena.DefaultReasoning
open Semantics.Dynamic.Default
open Core.Order (NormalityOrder)
open Classical

-- ═══ Tweety Triangle ═══

section Tweety

open TweetyWorld

def birdDomain : Set TweetyWorld := { w | isBird w }
def penguinDomain : Set TweetyWorld := { w | isPenguin w }

-- Build the orderings as term-level definitions
-- so proofs can rewrite to them directly.

/-- Ordering for the bird domain: promotes flying. -/
private def birdOrd : NormalityOrder TweetyWorld where
  le w v := (flies v → flies w)
  le_refl _ := id
  le_trans _ _ _ huv hvw h := huv (hvw h)

/-- Ordering for the penguin domain: promotes ¬flying. -/
private def penguinOrd : NormalityOrder TweetyWorld where
  le w v := (¬flies v → ¬flies w)
  le_refl _ := id
  le_trans _ _ _ huv hvw h := huv (hvw h)

/-- The Tweety frame: pattern-match on domain to assign orderings. -/
private noncomputable def tweetyPattern (d : Set TweetyWorld) :
    NormalityOrder TweetyWorld :=
  if d = penguinDomain then penguinOrd
  else if d = birdDomain then birdOrd
  else NormalityOrder.total

noncomputable def tweetyFrame : ExpFrame TweetyWorld :=
  ⟨tweetyPattern⟩

-- Key facts about domains
private theorem pen_ne_bird : penguinDomain ≠ birdDomain := by
  intro h
  have : birdFlies ∈ penguinDomain :=
    h ▸ (show birdFlies ∈ birdDomain from True.intro)
  exact this

private theorem penguin_sub_bird : penguinDomain ⊆ birdDomain :=
  fun w hw => penguin_is_bird w hw

-- ─── Pattern evaluation helpers ───

private theorem pat_penguin : tweetyPattern penguinDomain = penguinOrd :=
  if_pos rfl

private theorem pat_bird : tweetyPattern birdDomain = birdOrd := by
  unfold tweetyPattern
  rw [if_neg (Ne.symm pen_ne_bird), if_pos rfl]

private theorem pat_other (d : Set TweetyWorld)
    (hp : d ≠ penguinDomain) (hb : d ≠ birdDomain) :
    tweetyPattern d = NormalityOrder.total := by
  unfold tweetyPattern; rw [if_neg hp, if_neg hb]

-- Helper: d ⊆ penguinDomain → d ≠ birdDomain
private theorem sub_penguin_ne_bird (d : Set TweetyWorld)
    (h : d ⊆ penguinDomain) : d ≠ birdDomain := by
  intro heq; subst heq
  exact pen_ne_bird.symm (Set.Subset.antisymm h penguin_sub_bird)

-- ─── Positive: birdFlies is normal among birds ───

/-- birdFlies is normal among birds: the bird default works for
    non-penguin birds. -/
theorem birdFlies_normal_in_birds :
    birdFlies ∈ tweetyFrame.normal birdDomain := by
  refine ⟨True.intro, fun d' hd' hwd' v _ => ?_⟩
  change (tweetyPattern d').le birdFlies v
  by_cases hp : d' = penguinDomain
  · -- birdFlies ∉ penguinDomain, contradiction
    subst hp; exact absurd hwd' id
  · by_cases hb : d' = birdDomain
    · -- bird ordering: flies v → flies birdFlies, trivially true
      subst hb; rw [pat_bird]; exact fun _ => True.intro
    · -- other domain: total ordering, trivially true
      rw [pat_other d' hp hb]; exact True.intro

-- ─── Negative: penguinFlies is NOT normal among birds ───

/-- penguinFlies is NOT normal among birds — the penguin subdomain
    demotes it. This is the key specificity test: without the
    subdomain check in `ExpFrame.normal`, this theorem would fail. -/
theorem penguinFlies_not_normal_in_birds :
    penguinFlies ∉ tweetyFrame.normal birdDomain := by
  intro ⟨_, hsub⟩
  -- Instantiate at the penguin subdomain with witness penguinNoFly
  have h := hsub penguinDomain penguin_sub_bird
    (show penguinFlies ∈ penguinDomain from True.intro)
    penguinNoFly (show penguinNoFly ∈ penguinDomain from True.intro)
  -- h : (tweetyFrame.pattern penguinDomain).le penguinFlies penguinNoFly
  change (tweetyPattern penguinDomain).le penguinFlies penguinNoFly at h
  rw [pat_penguin] at h
  -- h : ¬flies penguinNoFly → ¬flies penguinFlies
  -- flies penguinNoFly = False, so ¬flies penguinNoFly holds (by id)
  -- flies penguinFlies = True, so ¬flies penguinFlies is False
  exact h id True.intro

-- ─── Positive: penguinNoFly is normal among penguins ───

/-- penguinNoFly is normal among penguins: the penguin default works. -/
theorem penguinNoFly_normal_in_penguins :
    penguinNoFly ∈ tweetyFrame.normal penguinDomain := by
  refine ⟨True.intro, fun d' hd' hwd' v hv => ?_⟩
  change (tweetyPattern d').le penguinNoFly v
  by_cases hp : d' = penguinDomain
  · -- penguin ordering: ¬flies v → ¬flies penguinNoFly
    -- flies penguinNoFly = False, so ¬flies penguinNoFly is trivially true
    subst hp; rw [pat_penguin]; exact fun _ h => h
  · -- d' ⊆ penguinDomain ⊊ birdDomain, so d' ≠ birdDomain
    have hb : d' ≠ birdDomain := sub_penguin_ne_bird d' (hd'.trans (fun x h => h))
    rw [pat_other d' hp hb]; exact True.intro

end Tweety

end Phenomena.DefaultReasoning.Bridge
