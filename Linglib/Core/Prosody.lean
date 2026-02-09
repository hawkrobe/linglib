/-
# Core.Prosody

Theory-neutral prosodic types: pitch accents, boundary tones, and the
prosodic hierarchy.

## Overview

These types are used across multiple theories:
- CCG/Intonation (Steedman 2000): prosodic CCG derivations
- Information Structure (Kratzer & Selkirk 2020): spellout constraints
- Focus theory: prosodic realization of focus/givenness

## References

- Pierrehumbert, J. (1980). The Phonology and Phonetics of English Intonation.
- Beckman, M. & Pierrehumbert, J. (1986). Intonational Structure in Japanese and English.
- Selkirk, E. (2009, 2011). The prosodic hierarchy.
-/

namespace Core.Prosody

-- Pitch Accents

/--
Pitch accent types (Pierrehumbert 1980, ToBI conventions).

Pitch accents mark focus/contrast at the word level:
- H*: Sharp rise, typically marks rheme focus ("the BEANS")
- L+H*: Rise from low, typically marks theme focus ("FRED ate")
- null: No accent (background material)
-/
inductive PitchAccent where
  | H_star      -- H*: rheme accent (sharp rise to peak)
  | L_plus_H_star  -- L+H*: theme accent (rise from distinctive low)
  | null        -- No accent (background)
  deriving Repr, DecidableEq, Inhabited, BEq

-- Boundary Tones

/--
Boundary tones mark prosodic phrase edges.

Following Pierrehumbert (1980) and Beckman & Pierrehumbert (1986):
- L: Low intermediate phrase boundary
- LH%: Rising intonational phrase boundary (continuation)
- LL%: Falling intonational phrase boundary (finality)
-/
inductive BoundaryTone where
  | L      -- Low phrase boundary (intermediate)
  | LH_pct -- Rising boundary (LH%) - continuation, theme
  | LL_pct -- Falling boundary (LL%) - finality, rheme
  deriving Repr, DecidableEq, Inhabited, BEq

-- Prosodic Hierarchy

/-- Prosodic hierarchy levels (Selkirk 2009, 2011).

    σ < f < ω < φ < ι

    Used by Kratzer & Selkirk (2020) spellout constraints. -/
inductive ProsodicLevel where
  | σ  -- syllable
  | f  -- foot
  | ω  -- prosodic word
  | φ  -- phonological phrase
  | ι  -- intonational phrase
  deriving DecidableEq, Repr, BEq, Ord

instance : LT ProsodicLevel where
  lt a b := a.ctorIdx < b.ctorIdx

instance : LE ProsodicLevel where
  le a b := a.ctorIdx ≤ b.ctorIdx

/-- Head-prominence: each prosodic constituent has exactly one
    prominent daughter (its head). K&S (32). -/
structure ProsodicConstituent where
  level : ProsodicLevel
  /-- Whether this constituent is the head (most prominent) of its parent -/
  isHead : Bool
  deriving Repr

end Core.Prosody
