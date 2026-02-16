/-
# Allocutive Agreement and Honorifics: Crosslinguistic Data

Theory-neutral typological data on allocutive agreement (AA) — where verbs
encode addressee features — and the morphosyntactic expression of honorifics.

## Key Distinctions

- **AMType**: How the allocutive marker is realized morphosyntactically
- **Embeddability**: Where allocutive marking can appear (root-only vs embedded)
- **HonDomain**: Where honorification surfaces (verbal, nominal, or both)

## References

- Alok, D. & A. Bhalla (2026). Allocutive agreement and the syntax of honorifics.
- Alok, D. (2020). The syntax and semantics of allocutive agreement in Magahi.
- Oyharçabal, B. (1993). Verb agreement with non-arguments: On allocutive
  agreement. In J. I. Hualde & J. Ortiz de Urbina (eds.), Generative Studies
  in Basque Linguistics.
- Portner, P., M. Pak & R. Zanuttini (2019). The speaker-addressee relation at
  the syntax-semantics interface.
-/

import Linglib.Core.Basic

namespace Phenomena.Politeness.Honorifics

/-- Morphosyntactic type of allocutive marker (§2). -/
inductive AMType where
  | agreeMorpheme    -- verbal inflectional morpheme (Magahi, Basque)
  | particle         -- free-standing particle (Korean, Japanese)
  | cliticPronoun    -- clitic pronoun attached to verb (Galician)
  deriving Repr, DecidableEq, BEq

/-- Distribution across clause types (§3.1). -/
inductive Embeddability where
  | rootOnly       -- allocutive marking restricted to root clauses
  | limitedEmbed   -- can embed under some predicates (e.g., speech/thought)
  | freelyEmbed    -- no embedding restriction
  deriving Repr, DecidableEq, BEq

/-- Where honorification surfaces. -/
inductive HonDomain where
  | verbal   -- verbal agreement only
  | nominal  -- nominal morphology only (e.g., Japanese -san)
  | both     -- verbal and nominal
  deriving Repr, DecidableEq, BEq

/-- A single allocutive datum: one language's profile. -/
structure AllocDatum where
  language : String
  amType : AMType
  embeddability : Embeddability
  /-- Whether the language has a T/V pronoun distinction -/
  hasTV : Bool
  /-- Whether 3rd person honorifics exist -/
  has3PHon : Bool
  /-- Where honorification is realized -/
  domain : HonDomain
  deriving Repr, DecidableEq, BEq

-- ============================================================================
-- Crosslinguistic Data (Alok & Bhalla 2026, Table 1)
-- ============================================================================

def basque : AllocDatum :=
  ⟨"Souletian Basque", .agreeMorpheme, .rootOnly, true, false, .verbal⟩

def magahi : AllocDatum :=
  ⟨"Magahi", .agreeMorpheme, .freelyEmbed, true, true, .both⟩

def korean : AllocDatum :=
  ⟨"Korean", .particle, .rootOnly, true, true, .both⟩

def japanese : AllocDatum :=
  ⟨"Japanese", .particle, .rootOnly, true, true, .both⟩

def tamil : AllocDatum :=
  ⟨"Tamil", .agreeMorpheme, .limitedEmbed, true, true, .verbal⟩

def galician : AllocDatum :=
  ⟨"Galician", .cliticPronoun, .freelyEmbed, true, false, .verbal⟩

def hindi : AllocDatum :=
  ⟨"Hindi", .agreeMorpheme, .freelyEmbed, true, true, .both⟩

def maithili : AllocDatum :=
  ⟨"Maithili", .agreeMorpheme, .freelyEmbed, true, true, .both⟩

def punjabi : AllocDatum :=
  ⟨"Punjabi", .agreeMorpheme, .limitedEmbed, true, true, .verbal⟩

def allAllocData : List AllocDatum :=
  [basque, magahi, korean, japanese, tamil, galician, hindi, maithili, punjabi]

-- ============================================================================
-- Verification Theorems
-- ============================================================================

/-- At least one language restricts allocutive marking to root clauses. -/
theorem rootOnly_languages_exist :
    ∃ d ∈ allAllocData, d.embeddability = .rootOnly :=
  ⟨basque, by simp [allAllocData], rfl⟩

/-- At least one language freely embeds allocutive marking. -/
theorem freelyEmbed_languages_exist :
    ∃ d ∈ allAllocData, d.embeddability = .freelyEmbed :=
  ⟨magahi, by simp [allAllocData], rfl⟩

/-- All allocutive languages in the survey mark the verbal domain
    (verbal or both). -/
theorem all_have_verbal :
    allAllocData.all (λ d => d.domain == .verbal || d.domain == .both) = true := by
  native_decide

/-- All surveyed allocutive languages have a T/V pronoun distinction. -/
theorem all_have_tv :
    allAllocData.all (λ d => d.hasTV) = true := by native_decide

end Phenomena.Politeness.Honorifics
