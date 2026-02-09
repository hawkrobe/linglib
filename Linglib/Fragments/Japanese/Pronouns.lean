/-
# Japanese Pronoun & Allocutive Fragment

Second-person pronouns and allocutive particles in Japanese. Japanese has
particle-based politeness marking (*-desu*/*-masu*) hosted in the SAP layer,
restricted to root clauses.

## References

- Miyagawa, S. (2012). Agreements that occur mainly in the main clause.
- Portner, P., M. Pak & R. Zanuttini (2019). The speaker-addressee relation at
  the syntax-semantics interface.
- Alok, D. & A. Bhalla (2026). Allocutive agreement and the syntax of
  honorifics.
-/

import Linglib.Core.Basic

namespace Fragments.Japanese.Pronouns


-- ============================================================================
-- Pronoun Entries
-- ============================================================================

/-- A Japanese pronoun entry with formality level. -/
structure PronounEntry where
  form : String
  kanji : String
  person : Option Person := none
  number : Option Number := none
  /-- 0 = plain, 1 = polite -/
  formality : Nat := 0
  deriving Repr, BEq

/-- 君 *kimi* — 2sg plain. -/
def kimi : PronounEntry :=
  { form := "kimi", kanji := "君", person := some .second, number := some .sg, formality := 0 }

/-- あなた *anata* — 2sg polite. -/
def anata : PronounEntry :=
  { form := "anata", kanji := "あなた", person := some .second, number := some .sg, formality := 1 }

def allPronouns : List PronounEntry := [kimi, anata]

-- ============================================================================
-- Allocutive Particles (SAP-layer)
-- ============================================================================

/-- An allocutive particle entry. -/
structure AllocParticleEntry where
  form : String
  /-- 0 = plain (no particle), 1 = polite -/
  formality : Nat
  gloss : String
  deriving Repr, BEq

/-- *-desu* polite copula / *-masu* polite verbal (Miyagawa 2012). -/
def desuMasu : AllocParticleEntry :=
  { form := "-desu/-masu", formality := 1, gloss := "POL" }

def allAllocParticles : List AllocParticleEntry := [desuMasu]

-- ============================================================================
-- Verb Agreement Examples
-- ============================================================================

/-- A verb form showing speech-level inflection. -/
structure VerbForm where
  form : String
  gloss : String
  formality : Nat
  deriving Repr, BEq

/-- 行く *iku* — "go" (plain). -/
def iku : VerbForm := { form := "iku", gloss := "go.PLN", formality := 0 }

/-- 行きます *ikimasu* — "go" (polite). -/
def ikimasu : VerbForm := { form := "ikimasu", gloss := "go.POL", formality := 1 }

-- ============================================================================
-- Verification
-- ============================================================================

/-- All pronouns are 2nd person. -/
theorem all_second_person :
    allPronouns.all (·.person == some .second) = true := rfl

/-- The T/V formality distinction is present. -/
theorem tv_distinction :
    allPronouns.any (·.formality == 0) = true ∧
    allPronouns.any (·.formality == 1) = true := ⟨rfl, rfl⟩

/-- Verb forms span plain and polite levels. -/
theorem verb_formality_span :
    iku.formality = 0 ∧ ikimasu.formality = 1 := ⟨rfl, rfl⟩

end Fragments.Japanese.Pronouns
