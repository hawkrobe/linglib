import Linglib.Core.Empirical

/-!
# Assertion Phenomena: Theory-Neutral Data
@cite{gunlogson-2001} @cite{lauer-2013} @cite{searle-1969}

Empirical observations about assertion that any theory should account for.
These data points are theory-neutral: they describe observable patterns
without importing from `Theories/`.

## Data Points

1. **Hedged assertions** reduce commitment strength
2. **Oath formulae** increase commitment strength
3. **Rising declaratives** shift commitment source
4. **Retraction** withdraws a prior commitment
5. **Lying** involves commitment without belief

-/

namespace Phenomena.Assertion

-- ════════════════════════════════════════════════════
-- § 1. Hedged Assertions
-- ════════════════════════════════════════════════════

/-- Hedged assertion datum: hedging expressions reduce commitment.

    "I think it's raining" commits the speaker less strongly than
    "It's raining." The propositional content is the same; the
    commitment profile differs. -/
structure HedgedAssertionDatum where
  /-- The hedge expression ("I think", "maybe", "probably") -/
  hedge : String
  /-- The propositional content -/
  content : String
  /-- Does the hedge reduce commitment? (always true empirically) -/
  reducesCommitment : Bool
  deriving Repr

/-- Canonical hedging examples. -/
def hedgeExamples : List HedgedAssertionDatum :=
  [ ⟨"I think", "it's raining", true⟩
  , ⟨"maybe", "it's raining", true⟩
  , ⟨"probably", "it's raining", true⟩
  , ⟨"apparently", "it's raining", true⟩ ]

/-- All canonical hedges reduce commitment. -/
theorem all_hedges_reduce : hedgeExamples.all (·.reducesCommitment) = true := rfl

-- ════════════════════════════════════════════════════
-- § 2. Oath Formulae
-- ════════════════════════════════════════════════════

/-- Oath formula datum: oath expressions increase commitment.

    "I swear it's raining" commits the speaker more strongly than
    "It's raining." The speaker stakes their credibility on the content. -/
structure OathFormulaDatum where
  /-- The oath expression ("I swear", "I promise", "I guarantee") -/
  oath : String
  /-- The propositional content -/
  content : String
  /-- Does the oath increase commitment? (always true empirically) -/
  increasesCommitment : Bool
  deriving Repr

/-- Canonical oath examples. -/
def oathExamples : List OathFormulaDatum :=
  [ ⟨"I swear", "it's raining", true⟩
  , ⟨"I promise", "I'll be there", true⟩
  , ⟨"I guarantee", "it will work", true⟩ ]

/-- All canonical oaths increase commitment. -/
theorem all_oaths_increase : oathExamples.all (·.increasesCommitment) = true := rfl

-- ════════════════════════════════════════════════════
-- § 3. Rising Declaratives
-- ════════════════════════════════════════════════════

/-- Rising declarative datum: intonation shifts commitment source.

    "It's raining?" (rising) attributes the content to the addressee,
    while "It's raining." (falling) commits the speaker. Same words,
    different intonation, different commitment profile. -/
structure RisingDeclarativeDatum where
  /-- The content -/
  content : String
  /-- Is the intonation rising? -/
  isRising : Bool
  /-- Does the speaker commit? -/
  speakerCommits : Bool
  /-- Is the content attributed to the addressee? -/
  attributedToAddressee : Bool
  deriving Repr

/-- Falling vs rising contrast. -/
def risingExamples : List RisingDeclarativeDatum :=
  [ ⟨"It's raining", false, true, false⟩    -- falling: speaker commits
  , ⟨"It's raining", true, false, true⟩ ]   -- rising: attributed to addressee

/-- Rising declaratives do not commit the speaker. -/
theorem rising_no_speaker_commitment :
    (risingExamples.filter (·.isRising)).all (! ·.speakerCommits) = true := rfl

/-- Falling declaratives commit the speaker. -/
theorem falling_speaker_commits :
    (risingExamples.filter (! ·.isRising)).all (·.speakerCommits) = true := rfl

-- ════════════════════════════════════════════════════
-- § 4. Retraction
-- ════════════════════════════════════════════════════

/-- Retraction datum: withdrawing a prior commitment.

    "I take that back" / "Actually, never mind" removes a previously
    asserted proposition from the speaker's commitments. Not all theories
    support this operation. -/
structure RetractionDatum where
  /-- The retracted content -/
  content : String
  /-- The retraction expression -/
  retraction : String
  /-- Is the retraction felicitous? -/
  isFelicitous : Bool
  deriving Repr

/-- Retraction examples. -/
def retractionExamples : List RetractionDatum :=
  [ ⟨"It's raining", "I take that back", true⟩
  , ⟨"John is tall", "Actually, never mind", true⟩ ]

-- ════════════════════════════════════════════════════
-- § 5. Lying
-- ════════════════════════════════════════════════════

/-- Lying datum: commitment without belief.

    A liar publicly commits to p while privately believing ¬p.
    The assertion has the same surface form as a sincere assertion,
    but the speaker's internal state diverges from their public commitment. -/
structure LyingDatum where
  /-- What the speaker asserts (public commitment) -/
  asserted : String
  /-- What the speaker believes (private state) -/
  believed : String
  /-- Do commitment and belief diverge? -/
  commitmentBeliefDiverge : Bool
  deriving Repr

/-- Lying involves commitment-belief divergence. -/
def lyingExamples : List LyingDatum :=
  [ ⟨"I was home all evening", "I was at the party", true⟩
  , ⟨"The check is in the mail", "I haven't sent it", true⟩ ]

/-- All lying examples show commitment-belief divergence. -/
theorem lying_diverges :
    lyingExamples.all (·.commitmentBeliefDiverge) = true := rfl

end Phenomena.Assertion
