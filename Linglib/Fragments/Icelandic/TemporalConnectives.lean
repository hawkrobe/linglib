import Linglib.Fragments.English.TemporalExpressions
import Linglib.Fragments.Greek.TemporalConnectives

/-!
# Icelandic Temporal Connectives Fragment
@cite{giannakidou-2002} @cite{karttunen-1974}

Icelandic lexicalizes the two-*until* distinction despite lacking overt
verbal aspect marking (@cite{giannakidou-2002}, ex. 43–46, from Gunnar
Hansson p.c.):

- **flanga til** / **til** ('until'): durative endpoint type, combines only
  with stative/durative meanings. "*Prinsessan kom flanga til klukkan fimm"
  ('*The princess arrived until five o'clock') is ungrammatical.

- **fyrr en** ('earlier than', lit. 'before-than'): eventive NPI type,
  requires negation (*ekki*). Morphologically distinct from *til* and
  transparently built on *before* — paralleling Finnish *ennenkuin*
  ('before-than') and confirming @cite{karttunen-1974}'s identity
  NPI-*until* = ¬*before*.

This shows that the aspect parameter is not decisive for whether a language
lexicalizes the durative/eventive distinction: Icelandic has no overt
perfective/imperfective marking but still distinguishes the two *until*s.
-/

namespace Fragments.Icelandic.TemporalConnectives

open Fragments.English.TemporalExpressions (TemporalExprEntry Reading TemporalOrder ComplementType)

-- ============================================================================
-- § 1: Connective Entries
-- ============================================================================

/-- Icelandic *(flanga) til* ('until'): durative endpoint type.
    Combines only with stative/activity main clauses.
    "Prinsessan svaf flanga til klukkan fimm."
    ('The princess slept until five o'clock.') -/
def flangaTil : TemporalExprEntry :=
  { form := "flanga til / til"
  , complementType := .nominal
  , order := .until_
  , licensesNPI := false
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := true
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

/-- Icelandic *fyrr en* ('earlier than'): eventive NPI type.
    Requires negation (*ekki*). Morphologically *fyrr* ('earlier/before')
    + *en* ('than') — transparently *before*-based, confirming
    @cite{karttunen-1974}'s NPI-*until* = ¬*before*.
    "Prinsessan kom *(ekki) fyrr en klukkan fimm."
    ('The princess arrived *(not) until five o'clock.') -/
def fyrrEn : TemporalExprEntry :=
  { form := "fyrr en"
  , complementType := .nominal
  , order := .until_
  , licensesNPI := false  -- fyrr en IS an NPI; it doesn't license them
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := false
  , complementVeridical := false
  , forcesPunctual := true
  , triggeredCoercion := none }

-- ============================================================================
-- § 2: Two-*Until* Distinction
-- ============================================================================

/-- Icelandic lexicalizes the two-*until* distinction with different lexemes. -/
theorem two_until_lexicalized :
    flangaTil.form ≠ fyrrEn.form := by decide

/-- *Flanga til* is veridical (endpoint type); *fyrr en* is non-veridical
    (eventive NPI type). -/
theorem veridicality_split :
    flangaTil.complementVeridical = true ∧
    fyrrEn.complementVeridical = false :=
  ⟨rfl, rfl⟩

/-- *Fyrr en* forces punctual reading; *flanga til* does not. -/
theorem punctuality_split :
    flangaTil.forcesPunctual = false ∧
    fyrrEn.forcesPunctual = true :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- § 3: Cross-Linguistic Agreement
-- ============================================================================

open Fragments.English.TemporalExpressions in
/-- Icelandic *flanga til* matches English durative *until*. -/
theorem flangaTil_matches_until :
    flangaTil.order = until_.order ∧
    flangaTil.complementVeridical = until_.complementVeridical ∧
    flangaTil.defaultReading = until_.defaultReading :=
  ⟨rfl, rfl, rfl⟩

open Fragments.Greek.TemporalConnectives in
/-- Icelandic *flanga til* matches Greek *mexri* on key properties. -/
theorem flangaTil_matches_mexri :
    flangaTil.complementVeridical = mexri.complementVeridical ∧
    flangaTil.forcesPunctual = mexri.forcesPunctual :=
  ⟨rfl, rfl⟩

open Fragments.Greek.TemporalConnectives in
/-- Icelandic *fyrr en* matches Greek *para monon* on key properties. -/
theorem fyrrEn_matches_paraMonon :
    fyrrEn.complementVeridical = paraMonon.complementVeridical ∧
    fyrrEn.forcesPunctual = paraMonon.forcesPunctual :=
  ⟨rfl, rfl⟩

end Fragments.Icelandic.TemporalConnectives
