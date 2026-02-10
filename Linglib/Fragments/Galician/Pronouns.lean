/-
# Galician Pronoun & Allocutive Fragment

Personal pronouns and allocutive clitic in Galician (Romance).
Galician has a T/V distinction (*ti* familiar vs *vostede* formal) and a
familiar dative clitic *che* that attaches to the verb for allocutive marking.
2nd person plural distinguishes familiar *vós* from formal *vostedes*.
3rd person distinguishes masculine and feminine in both singular and plural.
AA is Fin-based and freely embeddable.

## References

- Alok, D. & A. Bhalla (2026). Allocutive agreement and the syntax of
  honorifics.
-/

import Linglib.Core.Pronouns

namespace Fragments.Galician.Pronouns

open Core.Pronouns

-- ============================================================================
-- First Person
-- ============================================================================

/-- *eu* — 1sg. -/
def eu : PronounEntry :=
  { form := "eu", person := some .first, number := some .sg }

/-- *nós* — 1pl. -/
def nos : PronounEntry :=
  { form := "nós", person := some .first, number := some .pl }

-- ============================================================================
-- Second Person (T/V, sg and pl)
-- ============================================================================

/-- *ti* — 2sg familiar (T form). -/
def ti : PronounEntry :=
  { form := "ti", person := some .second, number := some .sg, formality := 0 }

/-- *vostede* — 2sg formal (V form). -/
def vostede : PronounEntry :=
  { form := "vostede", person := some .second, number := some .sg, formality := 1 }

/-- *vós* — 2pl familiar. -/
def vos_pl : PronounEntry :=
  { form := "vós", person := some .second, number := some .pl, formality := 0 }

/-- *vostedes* — 2pl formal. -/
def vostedes : PronounEntry :=
  { form := "vostedes", person := some .second, number := some .pl, formality := 1 }

-- ============================================================================
-- Third Person
-- ============================================================================

/-- *el* — 3sg masculine. -/
def el : PronounEntry :=
  { form := "el", person := some .third, number := some .sg }

/-- *ela* — 3sg feminine. -/
def ela : PronounEntry :=
  { form := "ela", person := some .third, number := some .sg }

/-- *eles* — 3pl masculine. -/
def eles : PronounEntry :=
  { form := "eles", person := some .third, number := some .pl }

/-- *elas* — 3pl feminine. -/
def elas : PronounEntry :=
  { form := "elas", person := some .third, number := some .pl }

-- ============================================================================
-- Pronoun Lists
-- ============================================================================

def secondPersonPronouns : List PronounEntry := [ti, vostede]

def allPronouns : List PronounEntry :=
  [eu, nos] ++ secondPersonPronouns ++ [vos_pl, vostedes, el, ela, eles, elas]

-- ============================================================================
-- Allocutive Clitic
-- ============================================================================

/-- *che* — familiar dative clitic (2sg ethical dative). -/
def che : AllocutiveEntry :=
  { form := "che", formality := 0, gloss := "2sg.DAT.fam" }

def allAllocClitics : List AllocutiveEntry := [che]

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

/-- All three persons are attested. -/
theorem has_all_persons :
    allPronouns.any (·.person == some .first) = true ∧
    allPronouns.any (·.person == some .second) = true ∧
    allPronouns.any (·.person == some .third) = true := ⟨rfl, rfl, rfl⟩

/-- Both singular and plural are attested. -/
theorem has_both_numbers :
    allPronouns.any (·.number == some .sg) = true ∧
    allPronouns.any (·.number == some .pl) = true := ⟨rfl, rfl⟩

/-- 2nd person pronouns are all second person. -/
theorem second_person_all_2p :
    secondPersonPronouns.all (·.person == some .second) = true := rfl

/-- The T/V formality distinction is present in 2nd person. -/
theorem tv_distinction :
    secondPersonPronouns.any (·.formality == 0) = true ∧
    secondPersonPronouns.any (·.formality == 1) = true := ⟨rfl, rfl⟩

/-- The allocutive clitic *che* is familiar-level. -/
theorem che_is_familiar : che.formality = 0 := rfl

/-- 2pl preserves the T/V distinction (vós fam / vostedes form). -/
theorem plural_tv :
    vos_pl.formality = 0 ∧ vostedes.formality = 1 := ⟨rfl, rfl⟩

end Fragments.Galician.Pronouns
