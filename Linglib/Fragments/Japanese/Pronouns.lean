/-
# Japanese Pronoun & Allocutive Fragment

Personal pronouns and allocutive particles in Japanese. Japanese has
particle-based politeness marking (*-desu*/*-masu*) hosted in the SAP layer,
restricted to root clauses. 1st person has register-sensitive variants
(*watashi* neutral, *boku* male informal, *ore* male very informal).
3rd person pronouns (*kare*, *kanojo*) are literary/modern innovations;
traditional Japanese relies heavily on null reference.

-/

import Linglib.Syntax.Category.Pronoun.Basic

namespace Japanese.Pronouns

open Pronoun
open Features.Register (Level)

-- ============================================================================
-- First Person
-- ============================================================================

/-- 私 *watashi* — 1sg neutral/polite. -/
def watashi : PersonalPronoun :=
  { form := "watashi", script := some "私", person := some .first, number := some .singular, register := .formal }

/-- 僕 *boku* — 1sg informal, masculine-associated via register
    (no inherent gender feature; cf. [ochs-1992]). -/
def boku : PersonalPronoun :=
  { form := "boku", script := some "僕", person := some .first, number := some .singular, register := .informal }

/-- 俺 *ore* — 1sg male very informal. Strongly indexes masculine identity
    through assertive/coarse interactional stance ([ochs-1992]). -/
def ore : PersonalPronoun :=
  { form := "ore", script := some "俺", person := some .first, number := some .singular, register := .informal }

/-- 私たち *watashitachi* — 1pl. -/
def watashitachi : PersonalPronoun :=
  { form := "watashitachi", script := some "私たち", person := some .first, number := some .plural }

-- ============================================================================
-- Second Person (T/V)
-- ============================================================================

/-- 君 *kimi* — 2sg plain. -/
def kimi : PersonalPronoun :=
  { form := "kimi", script := some "君", person := some .second, number := some .singular, register := .informal }

/-- あなた *anata* — 2sg polite. -/
def anata : PersonalPronoun :=
  { form := "anata", script := some "あなた", person := some .second, number := some .singular, register := .formal }

-- ============================================================================
-- Third Person
-- ============================================================================

/-- 彼 *kare* — 3sg masculine. -/
def kare : PersonalPronoun :=
  { form := "kare", script := some "彼", person := some .third, number := some .singular }

/-- 彼女 *kanojo* — 3sg feminine. -/
def kanojo : PersonalPronoun :=
  { form := "kanojo", script := some "彼女", person := some .third, number := some .singular }

/-- 彼ら *karera* — 3pl. -/
def karera : PersonalPronoun :=
  { form := "karera", script := some "彼ら", person := some .third, number := some .plural }

-- ============================================================================
-- Reciprocal Pronoun
-- ============================================================================

/-- 互い *otagai* — reciprocal pronoun 'each other, one another'.
    Formally distinct from the reflexive *jibun* (自分). This is an
    NP/argument reciprocal strategy (reciprocal pronoun), unlike
    languages that mark reciprocity on the verb. -/
def otagai : PersonalPronoun :=
  { form := "otagai", script := some "互い", person := some .third, number := some .plural }

-- ============================================================================
-- Pronoun Lists
-- ============================================================================

def secondPersonPronouns : List PersonalPronoun := [kimi, anata]

def allPronouns : List PersonalPronoun :=
  [watashi, boku, ore, watashitachi] ++ secondPersonPronouns ++ [kare, kanojo, karera, otagai]

-- ============================================================================
-- Allocutive Particles (SAP-layer)
-- ============================================================================

/-- *-desu* polite copula / *-masu* polite verbal. -/
def desuMasu : AllocutiveEntry :=
  { form := "-desu/-masu", register := .formal, gloss := "POL" }

def allAllocParticles : List AllocutiveEntry := [desuMasu]

-- ============================================================================
-- Verb Agreement Examples
-- ============================================================================

/-- A verb form showing speech-level inflection. -/
structure VerbForm where
  form : String
  gloss : String
  register : Level
  deriving Repr, BEq

/-- 行く *iku* — "go" (plain). -/
def iku : VerbForm := { form := "iku", gloss := "go.PLN", register := .informal }

/-- 行きます *ikimasu* — "go" (polite). -/
def ikimasu : VerbForm := { form := "ikimasu", gloss := "go.POL", register := .formal }

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
    allPronouns.any (·.number == some .singular) = true ∧
    allPronouns.any (·.number == some .plural) = true := ⟨rfl, rfl⟩

/-- 1st person has register-based distinction. -/
theorem first_person_register :
    boku.register = .informal ∧ watashi.register = .formal := ⟨rfl, rfl⟩

/-- 2nd person pronouns are all second person. -/
theorem second_person_all_2p :
    secondPersonPronouns.all (·.person == some .second) = true := rfl

/-- The T/V register distinction is present in 2nd person. -/
theorem tv_distinction :
    secondPersonPronouns.any (·.register == .informal) = true ∧
    secondPersonPronouns.any (·.register == .formal) = true := ⟨rfl, rfl⟩

/-- Verb forms span plain and polite levels. -/
theorem verb_register_span :
    iku.register = .informal ∧ ikimasu.register = .formal := ⟨rfl, rfl⟩

end Japanese.Pronouns
