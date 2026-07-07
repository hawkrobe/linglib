import Linglib.Discourse.SpeechAct

/-!
# Layered Assertive Clauses: JP/ComP modifiers
[krifka-2020] [speas-2004] [wiltschko-2014]

Worked examples for [krifka-2020]'s four-layer clause structure
(TP > JP > ComP > ActP). The JP layer originates with [speas-2004]
and is developed crosslinguistically by [wiltschko-2014];
[krifka-2020] synthesises them with the commitment-space framework
of [krifka-2015] (see sibling
`Studies/Krifka2015.lean`).

## Coverage

- §1 — Hedges as JP modifiers ("I think p" → epistemicStatus := weak)
- §2 — Oaths as ComP modifiers ("I swear p" → commitmentStrength := strong)
- §3 — JP/ComP independence (commute, layer non-interaction)
- §4 — Rank orderings: hedges weaken, oaths strengthen, relative to the
  `.standard` default

## Out of scope

- The actual commitment-space dynamics — see Krifka2015.lean.
- Proxy assertions ("Mary says p") — flagged in [krifka-2015]
  conclusion, not exercised here.
- Conjunct/disjunct systems (Newari etc.) — typological extension noted
  in [krifka-2015] conclusion but separate study.
-/

/-!### Layered Assertive Clauses

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

This file is sibling to `Discourse/Commitment/Space.lean` (the 2015
commitment-space framework). The two are independent — neither imports
the other — and study files target whichever is appropriate:

- `Studies/Krifka2015.lean` consumes `CommitmentSpace`
- `Studies/Krifka2020.lean` consumes this file
-/

namespace Discourse.Krifka

open Semantics.Mood (Illocutionary)

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
    uses `Illocutionary` from `Discourse/SpeechAct.lean`. -/
structure LayeredAssertion (W : Type*) where
  /-- TP: the propositional content -/
  content : Set W
  /-- JP: the speaker's epistemic status toward the content -/
  epistemicStatus : CommitmentStrength := .standard
  /-- ComP: the strength of the speaker's public commitment -/
  commitmentStrength : CommitmentStrength := .standard
  /-- ActP: the type of speech act performed -/
  actType : Illocutionary := .declarative

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


namespace Krifka2020

open Discourse.Krifka

-- ════════════════════════════════════════════════════
-- § 1. Hedges as JP Modifiers
-- ════════════════════════════════════════════════════

/-- A hedge modifies the JP layer (epistemic status) to `weak`.

    "I think p" = assertion with `epistemicStatus := .weak`.
    The TP content (p) is unchanged; only the JP layer is modified. -/
def hedgeAsJP {W : Type*} (la : LayeredAssertion W) : LayeredAssertion W :=
  { la with epistemicStatus := .weak }

/-- Hedging preserves content (TP is untouched by JP modification). -/
theorem hedgeAsJP_content_eq {W : Type*} (la : LayeredAssertion W) :
    (hedgeAsJP la).content = la.content := rfl

/-- Hedging sets epistemic status to weak. -/
theorem hedgeAsJP_epistemicStatus_eq_weak {W : Type*} (la : LayeredAssertion W) :
    (hedgeAsJP la).epistemicStatus = .weak := rfl

/-- Hedging does not affect commitment strength. -/
theorem hedgeAsJP_commitmentStrength_eq {W : Type*} (la : LayeredAssertion W) :
    (hedgeAsJP la).commitmentStrength = la.commitmentStrength := rfl

-- ════════════════════════════════════════════════════
-- § 2. Oaths as ComP Modifiers
-- ════════════════════════════════════════════════════

/-- An oath modifies the ComP layer (commitment strength) to `strong`.

    "I swear p" = assertion with `commitmentStrength := .strong`.
    The TP content (p) is unchanged; only the ComP layer is modified. -/
def oathAsComP {W : Type*} (la : LayeredAssertion W) : LayeredAssertion W :=
  { la with commitmentStrength := .strong }

/-- Oaths preserve content. -/
theorem oathAsComP_content_eq {W : Type*} (la : LayeredAssertion W) :
    (oathAsComP la).content = la.content := rfl

/-- Oaths set commitment strength to strong. -/
theorem oathAsComP_commitmentStrength_eq_strong {W : Type*}
    (la : LayeredAssertion W) :
    (oathAsComP la).commitmentStrength = .strong := rfl

/-- Oaths do not affect epistemic status. -/
theorem oathAsComP_epistemicStatus_eq {W : Type*} (la : LayeredAssertion W) :
    (oathAsComP la).epistemicStatus = la.epistemicStatus := rfl

-- ════════════════════════════════════════════════════
-- § 3. JP/ComP Independence
-- ════════════════════════════════════════════════════

/-- JP and ComP can co-occur: hedging + oath on the same assertion.

    "I think I swear p": epistemicStatus = weak, commitmentStrength = strong.
    "I swear I think p": same result (layers are independent). -/
def hedgedOath {W : Type*} (la : LayeredAssertion W) : LayeredAssertion W :=
  { la with epistemicStatus := .weak, commitmentStrength := .strong }

/-- Order doesn't matter: hedge(oath(la)) = oath(hedge(la)). -/
theorem hedgeAsJP_oathAsComP_comm {W : Type*} (la : LayeredAssertion W) :
    hedgeAsJP (oathAsComP la) = oathAsComP (hedgeAsJP la) := rfl

/-- Hedged oath has weak epistemic + strong commitment. -/
theorem hedgedOath_profile {W : Type*} (la : LayeredAssertion W) :
    (hedgedOath la).epistemicStatus = .weak ∧
    (hedgedOath la).commitmentStrength = .strong :=
  ⟨rfl, rfl⟩

/-- Both layered modifications preserve TP content. -/
theorem hedgedOath_content_eq {W : Type*} (la : LayeredAssertion W) :
    (hedgedOath la).content = la.content := rfl

-- ════════════════════════════════════════════════════
-- § 4. Rank Orderings
-- ════════════════════════════════════════════════════

/-- Hedging produces a strictly lower-rank epistemic status than the
    `.standard` default: "I think p" weakens the assertion. -/
theorem hedgeAsJP_rank_lt_standard {W : Type*} (la : LayeredAssertion W) :
    (hedgeAsJP la).epistemicStatus.rank < CommitmentStrength.standard.rank :=
  show CommitmentStrength.weak.rank < CommitmentStrength.standard.rank by decide

/-- Oaths produce a strictly higher-rank commitment strength than the
    `.standard` default: "I swear p" strengthens the assertion. -/
theorem oathAsComP_rank_gt_standard {W : Type*} (la : LayeredAssertion W) :
    (oathAsComP la).commitmentStrength.rank > CommitmentStrength.standard.rank :=
  show CommitmentStrength.strong.rank > CommitmentStrength.standard.rank by decide

end Krifka2020
