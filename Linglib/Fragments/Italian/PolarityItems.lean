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
      [.negation, .nobody, .withoutClause, .conditionalAntecedent, .question]
  , scalarDirection := .strengthening
  , alternativeType := .domain
  , notes := "N-word; postverbal requires 'non': 'Non ho visto nessuno'" }

/-- *niente/nulla* — N-word for non-human, pure NPI. -/
def niente : PolarityItemEntry :=
  { form := "niente/nulla"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := .strengthening
  , notes := "Non-human N-word: 'Non ho fatto niente'" }

/-- *mai* — Temporal pure NPI (= English *ever*).
    Disallows FC use (contrast with English *any*). -/
def mai : PolarityItemEntry :=
  { form := "mai"
  , polarityType := .npiWeak
  , baseForce := .temporal
  , licensingContexts :=
      [.negation, .nobody, .withoutClause, .question, .conditionalAntecedent]
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

/-- *pur* (in *con tutta la fantasia che pur si possa avere*, "with all the
    fantasy in the world that one could have") — weak NPI licensed in
    DE/comparative environments where the speaker presupposes a contradicted
    prior belief.

    @cite{napoli-nespor-1976} §3.11 ex. 46–48: licensed under comparative
    *non₂* alongside subjunctive co-occurrence and *neanche*-conjunction.
    Treated by N&N as a diagnostic for underlying negation in the comparative
    clause: where *pur* surfaces, *non₂* is licensed too. -/
def pur : PolarityItemEntry :=
  { form := "pur"
  , polarityType := .npiWeak
  , baseForce := .degree
  , licensingContexts := [.negation, .comparative]
  , scalarDirection := .strengthening
  , notes :=
      "Weak NPI in comparatives + bias-licensed contexts; @cite{napoli-nespor-1976} §3.11" }

/-- *affatto* ("at all", "completely") — weak NPI requiring *precise*
    knowledge of the listener's belief; blocked in N&N's comparative *non₂*
    on independent precision grounds.

    @cite{napoli-nespor-1976} §3.22 fn (i): *affatto* is *not* licensed by
    bias-conditioned negation, even though it is a weak NPI elsewhere. The
    block is semantic — *affatto* requires the listener's belief to be
    explicit, which fails N&N's "imprecise/inferred" Condition 4. The
    distributional fact is therefore *orthogonal* to NPI licensing.
    Bottom-line: *affatto* is licensed by negation in general but blocked
    by the imprecise condition that bias-conditioned negation requires. -/
def affatto : PolarityItemEntry :=
  { form := "affatto"
  , polarityType := .npiWeak
  , baseForce := .degree
  , licensingContexts := [.negation]  -- not .comparative: blocked by precision
  , scalarDirection := .strengthening
  , notes :=
      "Weak NPI but requires precise prior belief; blocked under bias-conditioned " ++
      "negation by the imprecise condition; @cite{napoli-nespor-1976} §3.22 fn 6" }

/-- N&N's central diagnostic: *pur* is licensed in comparative-clause
    contexts (which encode bias-conditioned negation in Italian), *affatto*
    is not. The contrast is structural in the registry — *pur*'s
    `licensingContexts` includes `.comparative` while *affatto*'s does not,
    so the Italian Fragment alone witnesses the distributional contrast
    that motivated the *non₂* analysis. -/
theorem pur_licensed_in_comparative :
    pur.licensingContexts.contains .comparative = true := by decide

theorem affatto_not_licensed_in_comparative :
    affatto.licensingContexts.contains .comparative = false := by decide

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
      [.modalPossibility, .modalNecessity, .imperative, .generic]
  , alternativeType := .domain
  , notes := "Pure FCI; 'qualsiasi studente' = any/every student; no NPI reading" }

/-- *qualunque* — Pure universal FCI (post-nominal only). -/
def qualunque : PolarityItemEntry :=
  { form := "qualunque"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts :=
      [.modalPossibility, .modalNecessity, .imperative, .generic]
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
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative]
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
