import Linglib.Core.Basic

/-!
# Intentional Identity Data @cite{chatzikyriakidis-etal-2025}

Empirical data for intentional identity — the phenomenon where
two attitude reports appear to be "about the same thing" even
when that thing may not exist.

## The Geach puzzle (Geach 1967)

"Hob thinks a witch has blighted Bob's mare,
 and Nob wonders whether she killed Cob's sow."

The pronoun "she" in Nob's attitude seems to refer to the same
witch that Hob's attitude is about — but the witch may not exist.
Possible-worlds semantics struggles: the pronoun can't be a
regular variable (no accessible referent), and it can't be an
E-type pronoun (no unique salient witch across the two agents'
belief states).

## References

- Geach, P.T. (1967). Intentional Identity. Journal of Philosophy 64(20): 627–632.
- Edelberg, W. (1986). A New Puzzle about Intentional Identity.
  Journal of Philosophical Logic 15: 1–25.
- Chatzikyriakidis et al. (2025). Types and the Structure of Meaning. §2.
-/

namespace Phenomena.Attitudes.IntentionalIdentity

/-- An intentional identity datum: two attitude reports linked
by a pronoun or definite description across agents. -/
structure IntentionalIdentityDatum where
  /-- The full sentence -/
  sentence : String
  /-- First agent -/
  agent₁ : String
  /-- First attitude verb -/
  verb₁ : String
  /-- Second agent -/
  agent₂ : String
  /-- Second attitude verb -/
  verb₂ : String
  /-- The shared intentional object description -/
  sharedObject : String
  /-- Whether the shared object need not exist -/
  nonExistentOk : Bool
  deriving Repr

/-- Geach's original Hob-Nob example.
Geach (1967): "Hob thinks a witch has blighted Bob's mare,
and Nob wonders whether she killed Cob's sow." -/
def hobNob : IntentionalIdentityDatum :=
  { sentence := "Hob thinks a witch has blighted Bob's mare, and Nob wonders whether she killed Cob's sow"
    agent₁ := "Hob"
    verb₁ := "thinks"
    agent₂ := "Nob"
    verb₂ := "wonders"
    sharedObject := "a witch"
    nonExistentOk := true }

/-- Edelberg's variant: "Ralph believes someone is a spy,
and Ortcutt wonders whether he is dangerous."
Same structure: cross-agent pronoun to possibly nonexistent entity. -/
def edelbergSpy : IntentionalIdentityDatum :=
  { sentence := "Ralph believes someone is a spy, and Ortcutt wonders whether he is dangerous"
    agent₁ := "Ralph"
    verb₁ := "believes"
    agent₂ := "Ortcutt"
    verb₂ := "wonders"
    sharedObject := "someone (a spy)"
    nonExistentOk := true }

/-- All intentional identity data. -/
def iiData : List IntentionalIdentityDatum := [hobNob, edelbergSpy]

/-- All examples allow the shared object to be nonexistent. -/
theorem all_nonexistent_ok :
    ∀ d ∈ iiData, d.nonExistentOk = true := by
  intro d hd
  simp [iiData] at hd
  rcases hd with rfl | rfl <;> rfl

end Phenomena.Attitudes.IntentionalIdentity
