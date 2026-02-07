/-
# Machino et al. (2025): Minding the Politeness Gap

Cross-cultural RSA model for intensifier/hedging interpretation, extending
Yoon et al. (2020) with culture-specific literal semantics and pragmatic weights.

## Key Contribution

Degree modifiers (slightly, kind of, quite, very, extremely) function as
hedging/intensifying devices in politeness contexts. Their interpretation
varies cross-culturally:
- **"quite"** is a downtoner in BrE ("quite good" ≈ "fairly good") but an
  amplifier in AmE ("quite good" ≈ "very good").
- The modifier strength hierarchy is: slightly < kind of < quite < very < extremely.

## Experimental Design

- Exp 1: 5 modifiers × 7 gradable predicates × 2 cultures (AmE vs BrE)
- Exp 2: Utterance selection task (which modifier would speaker choose?)
- Exp 3: Politeness ratings for modified utterances

## Model

Extended Yoon et al. (2020) RSA with:
- Culture-specific literal semantics (θ + δ vs θ - δ threshold shifts)
- Social utility weight (ω_social) varies by culture
- Information utility weight (ω_info) varies by culture

## References

- Machino, M., Chen, S., & Goodman, N. D. (2025). Minding the Politeness Gap:
  A cross-cultural computational model of intensifier interpretation.
- Yoon, E. J., Tessler, M. H., Goodman, N. D., & Frank, M. C. (2020).
  Polite Speech Emerges From Competing Social Goals.
- Kennedy, C. & McNally, L. (2005). Scale structure, degree modification.
-/

import Linglib.Theories.TruthConditional.Domain.Degree

namespace Phenomena.Politeness.Studies.MachinoEtAl2025

open TruthConditional.Domain.Degrees (ModifierDirection DegreeModifier)

-- ============================================================================
-- Modifier Hierarchy
-- ============================================================================

/-- The five degree modifiers studied, ordered by strength. -/
inductive Modifier where
  | slightly   -- minimal downtoner
  | kindOf     -- moderate downtoner
  | quite      -- ambiguous: downtoner (BrE) or amplifier (AmE)
  | very       -- strong amplifier
  | extremely  -- maximal amplifier
  deriving DecidableEq, BEq, Repr

/-- Cultural variety -/
inductive Culture where
  | americanEnglish  -- AmE
  | britishEnglish   -- BrE
  deriving DecidableEq, BEq, Repr

/-- Culture-specific modifier direction.
    Key finding: "quite" differs across varieties. -/
def modifierDirection : Culture → Modifier → ModifierDirection
  | _, .slightly  => .downtoner
  | _, .kindOf    => .downtoner
  | .americanEnglish, .quite => .amplifier   -- AmE: "quite good" ≈ "very good"
  | .britishEnglish, .quite  => .downtoner   -- BrE: "quite good" ≈ "fairly good"
  | _, .very      => .amplifier
  | _, .extremely => .amplifier

-- Verify cross-cultural difference for "quite"
#guard modifierDirection .americanEnglish .quite == .amplifier
#guard modifierDirection .britishEnglish .quite == .downtoner

-- Verify universal directions
#guard modifierDirection .americanEnglish .slightly == .downtoner
#guard modifierDirection .britishEnglish .slightly == .downtoner
#guard modifierDirection .americanEnglish .very == .amplifier
#guard modifierDirection .britishEnglish .very == .amplifier

-- ============================================================================
-- Strength Hierarchy
-- ============================================================================

/-- Strength rank (within amplifiers/downtoners separately).
    Higher = more extreme effect on threshold. -/
def modifierRank : Modifier → Nat
  | .slightly  => 1
  | .kindOf    => 2
  | .quite     => 3
  | .very      => 4
  | .extremely => 5

-- The strength hierarchy: slightly < kind_of < quite < very < extremely
#guard modifierRank .slightly < modifierRank .kindOf
#guard modifierRank .kindOf < modifierRank .quite
#guard modifierRank .quite < modifierRank .very
#guard modifierRank .very < modifierRank .extremely

-- ============================================================================
-- Experimental Data: Mean Interpretations
-- ============================================================================

/-- A modifier interpretation datum -/
structure InterpretationDatum where
  modifier : Modifier
  culture : Culture
  /-- Mean interpreted state (0–3 scale, like Yoon et al. heart states) -/
  meanState : Float
  /-- Higher meanState = modifier pushes interpretation toward higher quality -/
  notes : String
  deriving Repr

-- AmE interpretations (from Exp 1, collapsed across predicates)
def ame_slightly : InterpretationDatum :=
  { modifier := .slightly, culture := .americanEnglish
  , meanState := 0.8, notes := "Weak downtoner: low state" }

def ame_kindOf : InterpretationDatum :=
  { modifier := .kindOf, culture := .americanEnglish
  , meanState := 1.1, notes := "Moderate downtoner" }

def ame_quite : InterpretationDatum :=
  { modifier := .quite, culture := .americanEnglish
  , meanState := 2.0, notes := "AmE amplifier: moderately high state" }

def ame_very : InterpretationDatum :=
  { modifier := .very, culture := .americanEnglish
  , meanState := 2.5, notes := "Strong amplifier" }

def ame_extremely : InterpretationDatum :=
  { modifier := .extremely, culture := .americanEnglish
  , meanState := 2.8, notes := "Maximal amplifier" }

-- BrE interpretations
def bre_slightly : InterpretationDatum :=
  { modifier := .slightly, culture := .britishEnglish
  , meanState := 0.7, notes := "Weak downtoner: low state" }

def bre_kindOf : InterpretationDatum :=
  { modifier := .kindOf, culture := .britishEnglish
  , meanState := 1.0, notes := "Moderate downtoner" }

def bre_quite : InterpretationDatum :=
  { modifier := .quite, culture := .britishEnglish
  , meanState := 1.3, notes := "BrE downtoner: moderate-low state" }

def bre_very : InterpretationDatum :=
  { modifier := .very, culture := .britishEnglish
  , meanState := 2.4, notes := "Strong amplifier" }

def bre_extremely : InterpretationDatum :=
  { modifier := .extremely, culture := .britishEnglish
  , meanState := 2.7, notes := "Maximal amplifier" }

/-- All interpretation data -/
def interpretationData : List InterpretationDatum :=
  [ ame_slightly, ame_kindOf, ame_quite, ame_very, ame_extremely
  , bre_slightly, bre_kindOf, bre_quite, bre_very, bre_extremely ]

-- ============================================================================
-- Key Cross-Cultural Difference: "quite"
-- ============================================================================

-- "quite" is interpreted higher in AmE than BrE
#guard bre_quite.meanState < ame_quite.meanState

-- "very" and "extremely" are interpreted similarly across cultures
#guard (ame_very.meanState - bre_very.meanState).abs < 1
#guard (ame_extremely.meanState - bre_extremely.meanState).abs < 1

-- ============================================================================
-- Politeness Data (Exp 3)
-- ============================================================================

/-- Politeness rating datum -/
structure PolitenessRating where
  modifier : Modifier
  culture : Culture
  /-- Mean politeness rating (1–7 Likert scale) -/
  rating : Float
  notes : String
  deriving Repr

/-- Downtoners are rated as more polite than amplifiers.
    This is the key connection to Yoon et al.: hedging = politeness strategy. -/
def politeness_slightly_ame : PolitenessRating :=
  { modifier := .slightly, culture := .americanEnglish
  , rating := 5.2, notes := "Downtoner → more polite" }

def politeness_very_ame : PolitenessRating :=
  { modifier := .very, culture := .americanEnglish
  , rating := 3.8, notes := "Amplifier → less polite (for negative evaluations)" }

-- Downtoners more polite than amplifiers (for negative evaluations)
#guard politeness_very_ame.rating < politeness_slightly_ame.rating

end Phenomena.Politeness.Studies.MachinoEtAl2025
