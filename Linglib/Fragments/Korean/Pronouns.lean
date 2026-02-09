/-
# Korean Pronoun & Allocutive Fragment

Second-person pronouns and allocutive particles in Korean. Korean has
particle-based allocutive marking (*-yo* polite, *-(su)pnida* formal)
hosted in the SAP layer, restricted to root clauses.

## References

- Portner, P., M. Pak & R. Zanuttini (2019). The speaker-addressee relation at
  the syntax-semantics interface.
- Alok, D. & A. Bhalla (2026). Allocutive agreement and the syntax of
  honorifics.
-/

import Linglib.Core.Basic

namespace Fragments.Korean.Pronouns


-- ============================================================================
-- Pronoun Entries
-- ============================================================================

/-- A Korean pronoun entry with formality level. -/
structure PronounEntry where
  form : String
  hangul : String
  person : Option Person := none
  number : Option Number := none
  /-- 0 = plain, 1 = polite -/
  formality : Nat := 0
  deriving Repr, BEq

/-- 너 *neo* — 2sg plain. -/
def neo : PronounEntry :=
  { form := "neo", hangul := "너", person := some .second, number := some .sg, formality := 0 }

/-- 당신 *dangsin* — 2sg polite. -/
def dangsin : PronounEntry :=
  { form := "dangsin", hangul := "당신", person := some .second, number := some .sg, formality := 1 }

def allPronouns : List PronounEntry := [neo, dangsin]

-- ============================================================================
-- Allocutive Particles (SAP-layer)
-- ============================================================================

/-- An allocutive particle entry. -/
structure AllocParticleEntry where
  form : String
  /-- 0 = plain (no particle), 1 = polite, 2 = formal -/
  formality : Nat
  gloss : String
  deriving Repr, BEq

/-- *-yo* polite particle (Portner, Pak & Zanuttini 2019). -/
def yo : AllocParticleEntry :=
  { form := "-yo", formality := 1, gloss := "POL" }

/-- *-(su)pnida* formal particle. -/
def supnida : AllocParticleEntry :=
  { form := "-(su)pnida", formality := 2, gloss := "FORM" }

def allAllocParticles : List AllocParticleEntry := [yo, supnida]

-- ============================================================================
-- Verb Agreement Examples
-- ============================================================================

/-- A verb form showing speech-level inflection. -/
structure VerbForm where
  form : String
  gloss : String
  formality : Nat
  deriving Repr, BEq

/-- 가 *ga* — "go" (plain/intimate). -/
def ga : VerbForm := { form := "ga", gloss := "go.PLN", formality := 0 }

/-- 가요 *gayo* — "go" (polite). -/
def gayo : VerbForm := { form := "gayo", gloss := "go.POL", formality := 1 }

/-- 갑니다 *gamnida* — "go" (formal). -/
def gamnida : VerbForm := { form := "gamnida", gloss := "go.FORM", formality := 2 }

-- ============================================================================
-- Verification
-- ============================================================================

/-- All pronouns are 2nd person. -/
theorem all_second_person :
    allPronouns.all (·.person == some .second) = true := rfl

/-- The T/V formality distinction is present in pronouns. -/
theorem tv_distinction :
    allPronouns.any (·.formality == 0) = true ∧
    allPronouns.any (·.formality == 1) = true := ⟨rfl, rfl⟩

/-- Verb forms span all three speech levels. -/
theorem verb_three_levels :
    ga.formality = 0 ∧ gayo.formality = 1 ∧ gamnida.formality = 2 := ⟨rfl, rfl, rfl⟩

end Fragments.Korean.Pronouns
