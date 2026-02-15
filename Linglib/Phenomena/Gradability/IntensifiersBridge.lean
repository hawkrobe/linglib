/-
# Deadjectival Intensifiers: Empirical Patterns

Nouwen (2024) "The semantics and probabilistic pragmatics of deadjectival
intensifiers" identifies two generalizations about adverbs derived from
evaluative adjectives (e.g., "horribly warm", "pleasantly warm"):

1. **Goldilocks effect**: Negative-evaluative bases (horrible, terrible)
   yield high-degree intensifiers; positive-evaluative bases (pleasant, nice)
   yield moderate-degree intensifiers.

2. **Zwicky's generalization**: Modal adjectives with negative polarity
   (unusual, surprising, impossible) can intensify, but their positive
   counterparts (usual, expected, possible) cannot.

This file records pure empirical data — no theoretical commitments.

## References

- Nouwen, R. (2024). The semantics and probabilistic pragmatics of
  deadjectival intensifiers. Linguistics and Philosophy.
- Zwicky, A. M. (1970). Greek-letter variables and the Sanskrit ruki class.
-/

import Linglib.Theories.TruthConditional.Adjective.Intensification

namespace Phenomena.Gradability.Intensifiers

open TruthConditional.Adjective.Intensification (EvaluativeValence)

/--
Intensifier degree class (Nouwen 2024, Figure 2).

- **H** (high): targets extreme degrees ("horribly warm" ≈ very warm)
- **M** (moderate): targets moderate degrees ("pleasantly warm" ≈ nicely warm)
-/
inductive IntensifierClass where
  | H  -- high degree
  | M  -- moderate degree
  deriving Repr, DecidableEq, BEq

/--
A deadjectival intensifier entry.

Records the adverb form, its adjectival base, evaluative properties,
modal status, and attestation pattern.
-/
structure IntensifierEntry where
  /-- Adverb form -/
  adverb : String
  /-- Adjectival base -/
  adjBase : String
  /-- Evaluative valence of the base -/
  valence : EvaluativeValence
  /-- Degree class as intensifier -/
  class_ : IntensifierClass
  /-- Whether the base is a modal adjective -/
  isModal : Bool := false
  /-- For modal bases: polarity of the modal (negative = unlikely/impossible) -/
  modalPolarity : Option EvaluativeValence := none
  /-- Whether the evaluative content is bleached in adverbial use -/
  bleached : Bool := false
  /-- Whether the intensifier use is attested -/
  attested : Bool := true
  deriving Repr

-- Intensifier Data (Nouwen 2024, Figure 2)

-- Negative-evaluative → High degree (H)

def horribly : IntensifierEntry :=
  { adverb := "horribly", adjBase := "horrible"
  , valence := .negative, class_ := .H, bleached := true }

def terribly : IntensifierEntry :=
  { adverb := "terribly", adjBase := "terrible"
  , valence := .negative, class_ := .H, bleached := true }

def awfully : IntensifierEntry :=
  { adverb := "awfully", adjBase := "awful"
  , valence := .negative, class_ := .H, bleached := true }

def dreadfully : IntensifierEntry :=
  { adverb := "dreadfully", adjBase := "dreadful"
  , valence := .negative, class_ := .H, bleached := true }

def frighteningly : IntensifierEntry :=
  { adverb := "frighteningly", adjBase := "frightening"
  , valence := .negative, class_ := .H, bleached := true }

-- Positive-evaluative → Moderate degree (M)

def pleasantly : IntensifierEntry :=
  { adverb := "pleasantly", adjBase := "pleasant"
  , valence := .positive, class_ := .M }

def nicely : IntensifierEntry :=
  { adverb := "nicely", adjBase := "nice"
  , valence := .positive, class_ := .M }

def decently : IntensifierEntry :=
  { adverb := "decently", adjBase := "decent"
  , valence := .positive, class_ := .M }

-- Negative modal → High degree (H), attested

def unusually : IntensifierEntry :=
  { adverb := "unusually", adjBase := "unusual"
  , valence := .negative, class_ := .H
  , isModal := true, modalPolarity := some .negative }

def surprisingly : IntensifierEntry :=
  { adverb := "surprisingly", adjBase := "surprising"
  , valence := .negative, class_ := .H
  , isModal := true, modalPolarity := some .negative }

def impossibly : IntensifierEntry :=
  { adverb := "impossibly", adjBase := "impossible"
  , valence := .negative, class_ := .H
  , isModal := true, modalPolarity := some .negative }

def remarkably : IntensifierEntry :=
  { adverb := "remarkably", adjBase := "remarkable"
  , valence := .negative, class_ := .H
  , isModal := true, modalPolarity := some .negative }

-- Positive modal → unattested as intensifiers

def usually_ : IntensifierEntry :=
  { adverb := "*usually", adjBase := "usual"
  , valence := .positive, class_ := .M
  , isModal := true, modalPolarity := some .positive
  , attested := false }

def expectedly_ : IntensifierEntry :=
  { adverb := "*expectedly", adjBase := "expected"
  , valence := .positive, class_ := .M
  , isModal := true, modalPolarity := some .positive
  , attested := false }

def possibly_ : IntensifierEntry :=
  { adverb := "*possibly", adjBase := "possible"
  , valence := .positive, class_ := .M
  , isModal := true, modalPolarity := some .positive
  , attested := false }

-- All entries

def allEntries : List IntensifierEntry :=
  [ horribly, terribly, awfully, dreadfully, frighteningly
  , pleasantly, nicely, decently
  , unusually, surprisingly, impossibly, remarkably
  , usually_, expectedly_, possibly_ ]

-- Goldilocks Effect (Nouwen 2024, §3)

/--
The Goldilocks effect: evaluative valence determines degree class.

- Negative-evaluative bases yield high-degree (H) intensifiers
- Positive-evaluative bases yield moderate-degree (M) intensifiers

Named after the "Goldilocks zone" — positive evaluation targets
a middle sweet spot, while negative evaluation targets extremes.
-/
def goldilocksHolds (e : IntensifierEntry) : Bool :=
  match e.valence with
  | .negative => e.class_ == .H
  | .positive => e.class_ == .M
  | .neutral  => true  -- neutral bases don't constrain

-- Per-datum verification

theorem horribly_goldilocks : goldilocksHolds horribly = true := by native_decide
theorem terribly_goldilocks : goldilocksHolds terribly = true := by native_decide
theorem awfully_goldilocks : goldilocksHolds awfully = true := by native_decide
theorem dreadfully_goldilocks : goldilocksHolds dreadfully = true := by native_decide
theorem frighteningly_goldilocks : goldilocksHolds frighteningly = true := by native_decide
theorem pleasantly_goldilocks : goldilocksHolds pleasantly = true := by native_decide
theorem nicely_goldilocks : goldilocksHolds nicely = true := by native_decide
theorem decently_goldilocks : goldilocksHolds decently = true := by native_decide

-- Zwicky's Generalization (Nouwen 2024, §3.2)

/--
Zwicky's generalization: modal adjectives with negative polarity
can serve as intensifiers; positive-polarity modal adjectives cannot.

- "unusually warm" ✓ (negative modal → attested)
- "*usually warm" ✗ (positive modal → unattested)
-/
def zwickyHolds (e : IntensifierEntry) : Bool :=
  if e.isModal then
    match e.modalPolarity with
    | some .negative => e.attested
    | some .positive => !e.attested
    | _ => true
  else true

-- Per-datum verification

theorem unusually_zwicky : zwickyHolds unusually = true := by native_decide
theorem surprisingly_zwicky : zwickyHolds surprisingly = true := by native_decide
theorem impossibly_zwicky : zwickyHolds impossibly = true := by native_decide
theorem remarkably_zwicky : zwickyHolds remarkably = true := by native_decide
theorem usually_zwicky : zwickyHolds usually_ = true := by native_decide
theorem expectedly_zwicky : zwickyHolds expectedly_ = true := by native_decide
theorem possibly_zwicky : zwickyHolds possibly_ = true := by native_decide

-- Summary statistics

/-- Count of attested intensifiers -/
def attestedCount : Nat := (allEntries.filter (·.attested)).length

/-- Count of unattested intensifiers -/
def unattestedCount : Nat := (allEntries.filter (!·.attested)).length

#guard attestedCount == 12
#guard unattestedCount == 3

end Phenomena.Gradability.Intensifiers
