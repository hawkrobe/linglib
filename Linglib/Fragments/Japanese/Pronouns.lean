/-
# Japanese Pronoun & Allocutive Fragment

Personal pronouns and allocutive particles in Japanese. Japanese has
particle-based politeness marking (*-desu*/*-masu*) hosted in the SAP layer,
restricted to root clauses. 1st person has register-sensitive variants
(*watashi* neutral, *boku* male informal, *ore* male very informal).
3rd person pronouns (*kare*, *kanojo*) are literary/modern innovations;
traditional Japanese relies heavily on null reference.

-/

import Linglib.Core.Lexical.Pronouns
import Linglib.Typology.Pronouns

namespace Fragments.Japanese.Pronouns

open Core.Pronouns
open Features.Register (Level)

-- ============================================================================
-- First Person
-- ============================================================================

/-- 私 *watashi* — 1sg neutral/polite. -/
def watashi : PronounEntry :=
  { form := "watashi", script := some "私", person := some .first, number := some .sg, register := .formal }

/-- 僕 *boku* — 1sg informal, masculine-associated via register
    (no inherent gender feature; cf. @cite{ochs-1992}). -/
def boku : PronounEntry :=
  { form := "boku", script := some "僕", person := some .first, number := some .sg, register := .informal }

/-- 俺 *ore* — 1sg male very informal. Strongly indexes masculine identity
    through assertive/coarse interactional stance (@cite{ochs-1992}). -/
def ore : PronounEntry :=
  { form := "ore", script := some "俺", person := some .first, number := some .sg, register := .informal }

/-- 私たち *watashitachi* — 1pl. -/
def watashitachi : PronounEntry :=
  { form := "watashitachi", script := some "私たち", person := some .first, number := some .pl }

-- ============================================================================
-- Second Person (T/V)
-- ============================================================================

/-- 君 *kimi* — 2sg plain. -/
def kimi : PronounEntry :=
  { form := "kimi", script := some "君", person := some .second, number := some .sg, register := .informal }

/-- あなた *anata* — 2sg polite. -/
def anata : PronounEntry :=
  { form := "anata", script := some "あなた", person := some .second, number := some .sg, register := .formal }

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
-- Reciprocal Pronoun
-- ============================================================================

/-- 互い *otagai* — reciprocal pronoun 'each other, one another'.
    Formally distinct from the reflexive *jibun* (自分). This is an
    NP/argument reciprocal strategy (reciprocal pronoun), unlike
    languages that mark reciprocity on the verb. -/
def otagai : PronounEntry :=
  { form := "otagai", script := some "互い", person := some .third, number := some .pl }

-- ============================================================================
-- Pronoun Lists
-- ============================================================================

def secondPersonPronouns : List PronounEntry := [kimi, anata]

def allPronouns : List PronounEntry :=
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
    allPronouns.any (·.number == some .sg) = true ∧
    allPronouns.any (·.number == some .pl) = true := ⟨rfl, rfl⟩

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

end Fragments.Japanese.Pronouns

namespace Fragments.Japanese

/-- Japanese (Japonic) WALS pronoun typology profile. No incl/excl in
    pronouns; no person marking on verbs; gender in 3rd person only
    including non-singular (kare/kanojo); pronouns avoided for
    politeness; interrogative-based indefinites (dare-ka 'who-Q' =
    'someone'); intensifier and reflexive identical (jibun); no person
    marking on adpositions. -/
def pronounProfile : Typology.PronounProfile :=
  { language := "Japanese"
  , family := "Japonic"
  , iso := "jpn"
  , inclusiveExclusive := some .noDistinction
  , inclusiveExclusiveVerbal := some .noPersonMarking
  , genderInPronouns := some .in3rdPersonIncludingNonSg
  , politeness := some .pronounsAvoided
  , indefiniteType := some .interrogativeBased
  , intensifierReflexive := some .identical
  , personMarkingAdpositions := some .noPersonMarking }

end Fragments.Japanese
