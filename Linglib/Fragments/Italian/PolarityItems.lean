import Linglib.Core.Lexical.PolarityItem

/-!
# Italian Polarity-Sensitive Items
@cite{chierchia-2006} @cite{chierchia-2013}

Lexical entries for Italian PSIs, typed by the theory-neutral categories
from `Core.Lexical.PolarityItem`.

## The Italian PSI system

Italian lexicalizes the NPI/FCI distinction that English *any* collapses:
- **nessuno/niente/mai**: Pure NPIs (negative concord, DE only)
- **qualsiasi/qualunque**: Pure universal FCIs (FC only, positive polarity)
- **un N qualsiasi**: Existential FCIs (FC under modals)
-/

namespace Fragments.Italian.PolarityItems

open Core.Lexical.PolarityItem

-- ============================================================================
-- Pure NPIs
-- ============================================================================

/-- *nessuno/nessuna* — N-word, pure NPI.
    Requires negative concord (postverbal: *non* ... *nessuno*).
    Base existential force; negative force from concord, not lexical. -/
def nessuno : PolarityItemEntry :=
  { form := "nessuno/nessuna"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts :=
      [.negation, .nobody, .without_clause, .conditional_ant, .question]
  , scalarDirection := .strengthening
  , alternativeType := .domain
  , notes := "N-word; postverbal requires 'non': 'Non ho visto nessuno'" }

/-- *niente/nulla* — N-word for non-human, pure NPI. -/
def niente : PolarityItemEntry :=
  { form := "niente/nulla"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .without_clause]
  , scalarDirection := .strengthening
  , notes := "Non-human N-word: 'Non ho fatto niente'" }

/-- *mai* — Temporal pure NPI (= English *ever*).
    Disallows FC use (contrast with English *any*). -/
def mai : PolarityItemEntry :=
  { form := "mai"
  , polarityType := .npiWeak
  , baseForce := .temporal
  , licensingContexts :=
      [.negation, .nobody, .without_clause, .question, .conditional_ant]
  , scalarDirection := .strengthening
  , alternativeType := .domain
  , notes := "Pure NPI; 'Non l'ho mai visto'; no FC use" }

/-- *alcuno* — Pure NPI (formal register).
    Listed in @cite{chierchia-2006} table (76)/(94) alongside *mai* and *ever*.
    Restricted distribution: negation + formal contexts. -/
def alcuno : PolarityItemEntry :=
  { form := "alcuno"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody]
  , scalarDirection := .strengthening
  , notes := "Formal NPI; 'Non ho visto alcuno studente'" }

/-- *neanche/nemmeno* — Additive focus NPI (*not even*). -/
def neanche : PolarityItemEntry :=
  { form := "neanche/nemmeno"
  , polarityType := .npiWeak
  , baseForce := .degree
  , licensingContexts := [.negation, .nobody]
  , scalarDirection := .strengthening
  , notes := "Focus NPI: 'Non ha neanche provato' (didn't even try)" }

-- ============================================================================
-- Pure Universal FCIs
-- ============================================================================

/-- *qualsiasi* — Pure universal FCI.
    Universal force in positive/modal contexts.
    Under negation: only rhetorical ¬∀ reading ("not just any").
    Does NOT have NPI use (unlike English *any*). -/
def qualsiasi : PolarityItemEntry :=
  { form := "qualsiasi"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts :=
      [.modal_possibility, .modal_necessity, .imperative, .generic]
  , alternativeType := .domain
  , notes := "Pure FCI; 'qualsiasi studente' = any/every student; no NPI reading" }

/-- *qualunque* — Pure universal FCI (post-nominal only). -/
def qualunque : PolarityItemEntry :=
  { form := "qualunque"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts :=
      [.modal_possibility, .modal_necessity, .imperative, .generic]
  , alternativeType := .domain
  , notes := "Post-nominal FCI; 'libro qualunque' = any/whatever book" }

-- ============================================================================
-- Existential FCIs
-- ============================================================================

/-- *un N qualsiasi* — Existential FCI.
    Both domain and scalar alternatives active.
    Requires modal context; ungrammatical in plain episodic. -/
def uno_qualsiasi : PolarityItemEntry :=
  { form := "un N qualsiasi"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts := [.modal_possibility, .modal_necessity, .imperative]
  , alternativeType := .domain
  , notes := "Existential FCI; 'un dottore qualsiasi' = a doctor whatever; needs modal" }

-- ============================================================================
-- Verification
-- ============================================================================

/-- Italian lexicalizes the NPI/FCI distinction: mai ≠ qualsiasi. -/
theorem mai_qualsiasi_distinct :
    mai.polarityType ≠ qualsiasi.polarityType := by decide

/-- All Italian NPIs have strengthening scalar direction. -/
theorem italian_npis_strengthening :
    [nessuno, niente, mai, alcuno, neanche].all
      (λ e => e.scalarDirection == .strengthening) = true := by native_decide

end Fragments.Italian.PolarityItems
