import Linglib.Fragments.English.TemporalExpressions

/-!
# Dutch Temporal Connectives Fragment
@cite{giannakidou-2002} @cite{karttunen-1974}

Dutch (and German) represent a third strategy for the two-*until* problem:
rather than collapsing both types under one lexeme (English) or lexicalizing
both separately (Greek, Icelandic), Dutch excludes durative *until* from
negation altogether and uses a **positive polarity item** instead.

- **tot** ('until'): durative endpoint type. Cannot co-occur with negation.
  "*Marie kwam tot 9 uur (niet) aan" is ungrammatical.

- **pas** ('only then', lit. 'not before'): PPI replacement for NPI-*until*.
  "Marie kwam pas om 9 uur aan" ('Mary only arrived at 9').
  Unlike Greek *para monon* (NPI, requires negation), Dutch *pas* is a
  PPI that appears WITHOUT negation and contributes the 'not before'
  meaning lexically.

German parallels Dutch exactly: *bis* (durative until, blocked under
negation) and *erst* (PPI, 'only then').

This typological pattern — PPI replacement instead of NPI *until* — was
noted by @cite{giannakidou-2002} (ex. 47) and Declerk 1995.
-/

namespace Fragments.Dutch.TemporalConnectives

open Fragments.English.TemporalExpressions (TemporalExprEntry Reading TemporalOrder ComplementType)

-- ============================================================================
-- § 1: Connective Entries
-- ============================================================================

/-- Dutch *tot* ('until'): durative endpoint type.
    Veridical, requires durative main clause.
    CANNOT co-occur with negation — negation blocks durative *until*
    entirely in Dutch (unlike English/Greek where negation triggers
    a different reading).
    "Marie wachtte tot 9 uur." ('Marie waited until 9 o'clock.') -/
def tot : TemporalExprEntry :=
  { form := "tot"
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

/-- Dutch *pas* ('only then'): PPI replacement for NPI-*until*.
    Contributes 'not before' meaning WITHOUT negation — it is a PPI,
    not an NPI. Classified as `order := .until_` because it occupies the
    same slot as NPI-*until* in other languages, but with reversed polarity.
    "Marie kwam pas om 9 uur aan." ('Mary only arrived at 9.') -/
def pas : TemporalExprEntry :=
  { form := "pas"
  , complementType := .nominal
  , order := .until_
  , licensesNPI := false
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := false
  , complementVeridical := false
  , forcesPunctual := true
  , triggeredCoercion := none }

-- ============================================================================
-- § 2: PPI Strategy
-- ============================================================================

/-- Dutch uses different lexemes for durative and eventive *until*,
    like Greek and Icelandic. -/
theorem two_forms :
    tot.form ≠ pas.form := by decide

/-- *Tot* is veridical; *pas* is non-veridical (like NPI-*until*). -/
theorem veridicality_split :
    tot.complementVeridical = true ∧
    pas.complementVeridical = false :=
  ⟨rfl, rfl⟩

/-- *Pas* forces punctual reading (eventive); *tot* does not (durative). -/
theorem punctuality_split :
    tot.forcesPunctual = false ∧
    pas.forcesPunctual = true :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- § 3: Cross-Linguistic Agreement
-- ============================================================================

open Fragments.English.TemporalExpressions in
/-- Dutch *tot* matches English durative *until* on core properties. -/
theorem tot_matches_until :
    tot.order = until_.order ∧
    tot.complementVeridical = until_.complementVeridical ∧
    tot.defaultReading = until_.defaultReading :=
  ⟨rfl, rfl, rfl⟩

end Fragments.Dutch.TemporalConnectives
