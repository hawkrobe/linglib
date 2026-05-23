import Mathlib.Tactic.DeriveFintype

/-!
# Embedded Scalar Implicature Types

Shared types and definitions for modeling embedded scalar implicatures
(the "Every student read some book" scenario). Used by both
`RSAExhExpressivity` (comparing RSA vs EXH expressivity) and
`CompositionalRSA` (extending RSA to local readings).

## The Scenario

We model 2 students (Alice, Bob), each of whom either read
"some but not all" (S) or "all" (A) books.

## Definitions

- `EmbeddedSIWorld`: 4 world states (SS, SA, AS, AA)
- `EmbeddedSIMessage`: 2 messages (everySome, everyAll)
- `embeddedMeaning`: literal meaning function
- `ExhScope`: global vs local EXH scope
- `globalExhMeaning`, `localExhMeaning`: truth conditions under each scope
- `exhScopedMeaning`: scope-parameterized meaning
-/

namespace RSA.EmbeddedSI

/-- World states for the embedded SI scenario.
    Each student either read "some but not all" (S) or "all" (A). -/
inductive EmbeddedSIWorld where
  | SS : EmbeddedSIWorld  -- Alice: some, Bob: some
  | SA : EmbeddedSIWorld  -- Alice: some, Bob: all
  | AS : EmbeddedSIWorld  -- Alice: all, Bob: some
  | AA : EmbeddedSIWorld  -- Alice: all, Bob: all
  deriving DecidableEq, Fintype, Repr

/-- Messages in the embedded SI scenario -/
inductive EmbeddedSIMessage where
  | everySome : EmbeddedSIMessage  -- "Every student read some book"
  | everyAll  : EmbeddedSIMessage  -- "Every student read all books"
  deriving DecidableEq, Fintype, Repr

/-- Literal meaning: when is each message true?
    - "every some" is true in all worlds (some ⊆ all)
    - "every all" is true only in AA -/
def embeddedMeaning : EmbeddedSIMessage → EmbeddedSIWorld → Bool
  | .everySome, _ => true      -- "some" true everywhere
  | .everyAll, .AA => true     -- "all" true only when both read all
  | .everyAll, _ => false

/-- Scope position for EXH -/
inductive ExhScope where
  | global : ExhScope  -- EXH > ∀
  | local_ : ExhScope  -- ∀ > EXH
  deriving DecidableEq, Repr

/-- Truth conditions under global EXH:
    "every student read some" ∧ ¬"every student read all"

    True at: SS, SA, AS (not AA) -/
def globalExhMeaning : EmbeddedSIWorld → Bool
  | .SS => true   -- some ∧ ¬all: ✓
  | .SA => true   -- some ∧ ¬all: ✓ (Bob read all, but not everyone)
  | .AS => true   -- some ∧ ¬all: ✓ (Alice read all, but not everyone)
  | .AA => false  -- some ∧ ¬all: ✗ (everyone read all)

/-- Truth conditions under local EXH:
    "every student [read some but not all]"

    True at: SS only -/
def localExhMeaning : EmbeddedSIWorld → Bool
  | .SS => true   -- both read some-but-not-all: ✓
  | .SA => false  -- Bob read all: ✗
  | .AS => false  -- Alice read all: ✗
  | .AA => false  -- both read all: ✗

/-- EXH-with-scope: meaning depends on scope position -/
def exhScopedMeaning (scope : ExhScope) : EmbeddedSIWorld → Bool :=
  match scope with
  | .global => globalExhMeaning
  | .local_ => localExhMeaning

end RSA.EmbeddedSI
