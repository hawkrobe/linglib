import Linglib.Discourse.SpeechAct

/-!
# Layered Assertive Clauses

[krifka-2020] [speas-2004] [wiltschko-2014]

Four-layer decomposition of an assertive clause from [krifka-2020]:
TP (propositional content), JP (epistemic judgement), ComP (commitment
strength), ActP (speech act type). JP terminology and the layered idea
trace to [speas-2004] and [wiltschko-2014]; [krifka-2020]
synthesises them with the commitment-space framework.

| Layer | Contribution | Example Modifier |
|-------|-------------|-----------------|
| TP | Propositional content | tense, aspect |
| JP (Judge Phrase) | Epistemic judgment | "I think", evidentials |
| ComP (Commitment Phrase) | Commitment strength | "I swear", "perhaps" |
| ActP (Act Phrase) | Speech act type | declarative, imperative |

JP and ComP are independent: "I think I swear p" vs "I swear I think p"
both involve TP content p, but with different epistemic/commitment profiles.

This file is sibling to `Discourse/CommitmentSpace.lean` (the 2015
commitment-space framework). The two are independent — neither imports
the other — and study files target whichever is appropriate:

- `Studies/Krifka2015.lean` consumes `CommitmentSpace`
- `Studies/Krifka2020.lean` consumes this file
-/

namespace Discourse.Krifka

open Semantics.Mood (IllocutionaryMood)

-- ════════════════════════════════════════════════════
-- § 1. Commitment Strength
-- ════════════════════════════════════════════════════

/-- Graded commitment strength, controlled by ComP modifiers.

    - `weak`: hedged ("I think p", "maybe p")
    - `standard`: default declarative assertion
    - `strong`: oath formulae ("I swear p", "I promise p") -/
inductive CommitmentStrength where
  | weak
  | standard
  | strong
  deriving DecidableEq, Repr, Inhabited

/-- Numerical ordering of commitment strengths. -/
def CommitmentStrength.rank : CommitmentStrength → Nat
  | .weak => 0
  | .standard => 1
  | .strong => 2

/-- Standard is the default. -/
theorem standard_is_default : CommitmentStrength.standard.rank = 1 := rfl

/-- Strong > standard > weak. -/
theorem strength_ordering :
    CommitmentStrength.weak.rank < CommitmentStrength.standard.rank ∧
    CommitmentStrength.standard.rank < CommitmentStrength.strong.rank :=
  ⟨by decide, by decide⟩

-- ════════════════════════════════════════════════════
-- § 2. Layered Assertion Structure
-- ════════════════════════════════════════════════════

/-- A fully layered assertion, decomposed into the four clause layers.

    Each layer is independent: the epistemic status (JP) can vary without
    affecting the commitment strength (ComP), and vice versa. The actType
    uses `IllocutionaryMood` from `Discourse/SpeechAct.lean`. -/
structure LayeredAssertion (W : Type*) where
  /-- TP: the propositional content -/
  content : Set W
  /-- JP: the speaker's epistemic status toward the content -/
  epistemicStatus : CommitmentStrength := .standard
  /-- ComP: the strength of the speaker's public commitment -/
  commitmentStrength : CommitmentStrength := .standard
  /-- ActP: the type of speech act performed -/
  actType : IllocutionaryMood := .declarative

-- ════════════════════════════════════════════════════
-- § 3. Informative vs Performative Updates
-- ════════════════════════════════════════════════════

/-- Update type for assertions.

    Krifka distinguishes two fundamentally different ways an assertion
    can change the common ground:

    - **informative** (`·φ`): eliminates worlds incompatible with φ.
      Example: "The meeting is at 5" — reduces uncertainty.

    - **performative** (`•φ`): changes world indices so φ becomes true.
      Example: "I hereby name this ship the Queen Elizabeth" — makes
      φ true by the act of uttering it.

    This distinction is orthogonal to commitment strength (ComP) and
    epistemic status (JP). -/
inductive UpdateType where
  | informative   -- ·φ : eliminates worlds where φ is false
  | performative  -- •φ : changes worlds so φ becomes true
  deriving DecidableEq, Repr, Inhabited

/-- Informative update: restrict context set to worlds satisfying φ.

    -- UNVERIFIED: [krifka-2020] eq. number for the informative-update
    -- definition (the 2020 paper PDF was not available for this audit;
    -- the underlying concept is clearly Krifka's, but the equation tag
    -- needs human verification before promoting to a precise citation). -/
def informativeUpdate {W : Type*} (cs : List W) (φ : W → Prop)
    [DecidablePred φ] : List W :=
  cs.filter (fun w => φ w)

/-- A fully specified assertion with update type. -/
structure TypedAssertion (W : Type*) extends LayeredAssertion W where
  /-- Whether the update is informative or performative -/
  updateType : UpdateType := .informative

/-- Default assertions are informative (the common case). -/
theorem default_assertion_informative {W : Type*} (p : Set W) :
    ({ content := p : TypedAssertion W }).updateType = .informative := rfl

end Discourse.Krifka
