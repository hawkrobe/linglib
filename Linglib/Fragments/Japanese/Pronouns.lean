/-
# Japanese Pronoun & Allocutive Fragment

Personal pronouns and allocutive particles in Japanese. Japanese has
particle-based politeness marking (*-desu*/*-masu*) hosted in the SAP layer,
restricted to root clauses. 1st person has register-sensitive variants
(*watashi* neutral, *boku* male informal, *ore* male very informal).
3rd person pronouns (*kare*, *kanojo*) are literary/modern innovations;
traditional Japanese relies heavily on null reference.

## References

- Miyagawa, S. (2012). Agreements that occur mainly in the main clause.
- Portner, P., M. Pak & R. Zanuttini (2019). The speaker-addressee relation at
  the syntax-semantics interface.
- Alok, D. & A. Bhalla (2026). Allocutive agreement and the syntax of
  honorifics.
-/

import Linglib.Core.Pronouns

namespace Fragments.Japanese.Pronouns

open Core.Pronouns

-- ============================================================================
-- First Person
-- ============================================================================

/-- 私 *watashi* — 1sg neutral/polite. -/
def watashi : PronounEntry :=
  { form := "watashi", script := some "私", person := some .first, number := some .sg, formality := 1 }

/-- 僕 *boku* — 1sg male informal. -/
def boku : PronounEntry :=
  { form := "boku", script := some "僕", person := some .first, number := some .sg, formality := 0 }

/-- 私たち *watashitachi* — 1pl. -/
def watashitachi : PronounEntry :=
  { form := "watashitachi", script := some "私たち", person := some .first, number := some .pl }

-- ============================================================================
-- Second Person (T/V)
-- ============================================================================

/-- 君 *kimi* — 2sg plain. -/
def kimi : PronounEntry :=
  { form := "kimi", script := some "君", person := some .second, number := some .sg, formality := 0 }

/-- あなた *anata* — 2sg polite. -/
def anata : PronounEntry :=
  { form := "anata", script := some "あなた", person := some .second, number := some .sg, formality := 1 }

-- ============================================================================
-- Third Person
-- ============================================================================

/-- 彼 *kare* — 3sg masculine. -/
def kare : PronounEntry :=
  { form := "kare", script := some "彼", person := some .third, number := some .sg }

/-- 彼女 *kanojo* — 3sg feminine. -/
def kanojo : PronounEntry :=
  { form := "kanojo", script := some "彼女", person := some .third, number := some .sg }

/-- 彼ら *karera* — 3pl. -/
def karera : PronounEntry :=
  { form := "karera", script := some "彼ら", person := some .third, number := some .pl }

-- ============================================================================
-- Pronoun Lists
-- ============================================================================

def secondPersonPronouns : List PronounEntry := [kimi, anata]

def allPronouns : List PronounEntry :=
  [watashi, boku, watashitachi] ++ secondPersonPronouns ++ [kare, kanojo, karera]

-- ============================================================================
-- Allocutive Particles (SAP-layer)
-- ============================================================================

/-- *-desu* polite copula / *-masu* polite verbal (Miyagawa 2012). -/
def desuMasu : AllocutiveEntry :=
  { form := "-desu/-masu", formality := 1, gloss := "POL" }

def allAllocParticles : List AllocutiveEntry := [desuMasu]

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

/-- All three persons are attested. -/
theorem has_all_persons :
    allPronouns.any (·.person == some .first) = true ∧
    allPronouns.any (·.person == some .second) = true ∧
    allPronouns.any (·.person == some .third) = true := ⟨rfl, rfl, rfl⟩

/-- Both singular and plural are attested. -/
theorem has_both_numbers :
    allPronouns.any (·.number == some .sg) = true ∧
    allPronouns.any (·.number == some .pl) = true := ⟨rfl, rfl⟩

/-- 1st person has register-based formality distinction. -/
theorem first_person_register :
    boku.formality = 0 ∧ watashi.formality = 1 := ⟨rfl, rfl⟩

/-- 2nd person pronouns are all second person. -/
theorem second_person_all_2p :
    secondPersonPronouns.all (·.person == some .second) = true := rfl

/-- The T/V formality distinction is present in 2nd person. -/
theorem tv_distinction :
    secondPersonPronouns.any (·.formality == 0) = true ∧
    secondPersonPronouns.any (·.formality == 1) = true := ⟨rfl, rfl⟩

/-- Verb forms span plain and polite levels. -/
theorem verb_formality_span :
    iku.formality = 0 ∧ ikimasu.formality = 1 := ⟨rfl, rfl⟩

end Fragments.Japanese.Pronouns
