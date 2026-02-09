/-
# Galician Pronoun & Allocutive Fragment

Second-person pronouns and allocutive clitic in Galician (Romance).
Galician has a T/V distinction (*ti* familiar vs *vostede* formal) and a
familiar dative clitic *che* that attaches to the verb for allocutive marking.
AA is Fin-based and freely embeddable.

## References

- Alok, D. & A. Bhalla (2026). Allocutive agreement and the syntax of
  honorifics.
-/

import Linglib.Core.Basic

namespace Fragments.Galician.Pronouns


-- ============================================================================
-- Pronoun Entries
-- ============================================================================

/-- A Galician pronoun entry with formality level. -/
structure PronounEntry where
  form : String
  person : Option Person := none
  number : Option Number := none
  case_ : Option Case := none
  /-- 0 = familiar (T), 1 = formal (V) -/
  formality : Nat := 0
  deriving Repr, BEq

/-- *ti* — 2sg familiar (T form). -/
def ti : PronounEntry :=
  { form := "ti", person := some .second, number := some .sg, formality := 0 }

/-- *vostede* — 2sg formal (V form). -/
def vostede : PronounEntry :=
  { form := "vostede", person := some .second, number := some .sg, formality := 1 }

def allPronouns : List PronounEntry := [ti, vostede]

-- ============================================================================
-- Allocutive Clitic
-- ============================================================================

/-- An allocutive clitic entry. -/
structure AllocCliticEntry where
  form : String
  /-- 0 = familiar -/
  formality : Nat
  gloss : String
  deriving Repr, BEq

/-- *che* — familiar dative clitic (2sg ethical dative). -/
def che : AllocCliticEntry :=
  { form := "che", formality := 0, gloss := "2sg.DAT.fam" }

def allAllocClitics : List AllocCliticEntry := [che]

-- ============================================================================
-- Verb Agreement Examples
-- ============================================================================

/-- A verb form with optional allocutive clitic. -/
structure VerbForm where
  form : String
  gloss : String
  formality : Nat
  deriving Repr, BEq

/-- *vas* — "you go" (familiar, can host *che*). -/
def vas : VerbForm := { form := "vas", gloss := "go.2sg.fam", formality := 0 }

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

/-- The allocutive clitic *che* is familiar-level. -/
theorem che_is_familiar : che.formality = 0 := rfl

end Fragments.Galician.Pronouns
