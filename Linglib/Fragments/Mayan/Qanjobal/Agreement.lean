import Linglib.Core.Case.Basic
import Linglib.Fragments.Mayan.Params

/-!
# Q'anjob'al Agreement and Case Fragment @cite{mateo-toledo-2008} @cite{imanishi-2020}

Agreement morphology and case assignment for Q'anjob'al (Q'anjob'alan,
Mayan), a **high absolutive** VSO language with aspect-based split
ergativity. Per @cite{mateo-toledo-2008} p. 9, Q'anjob'al is in the
"Q'anjob'alan group, Q'anjob'alan branch, Western division" of the
Mayan family (citing England 1992:21, Kaufman 1974) — sister to the
Cholan-Tzeltalan branch (where Chol lives) within Western Mayan.

## The System

Q'anjob'al has the same Set A (ergative) / Set B (absolutive) paradigm
as other Mayan languages. Per @cite{mateo-toledo-2008} §1.3, ex. (35),
the verbal predicate structure is:

  `Asp + (Particle) + Abs + (Particle) + Erg-Verb + (Particle) + (DIRs)`

i.e., `[Asp] [Abs Erg-Verb]` — the **high absolutive** template. Compares
to Chol's low-absolutive `[Aux] [Erg-Verb-Abs]` (per
@cite{vazquez-alvarez-2011} §3.4).

## Cross-language difference: aspect-marker word class

A real difference between Cholan and Q'anjob'alan that the shared
substrate `caseExtErg` does NOT capture: aspect-marker morphological
status differs.

- **Chol** (@cite{vazquez-alvarez-2011} §3.4): aspect markers are
  **auxiliaries** (independent words: `tyi` perfective, `mi` imperfective).
- **Q'anjob'al** (@cite{mateo-toledo-2008} §1.1.2 + Kaufman 1990:71,
  Robertson 1992:57): aspect markers are **clitics** / "grammaticized
  particles" (`(ma)x-` completive, `chi/ch-` incompletive, `(ho)q-`
  irrealis).

Despite this morphological difference, the alignment behavior is the
same: split ergativity in any clause without an overt preverbal aspect
marker (per @cite{mateo-toledo-2008} §1.1.1, citing Mateo 2004a/2007b),
attributed to nominalization following Larsen & Norman 1979. The shared
case-assignment table in `Fragments.Mayan.caseExtErg` captures the
*alignment* convergence, not the *morpheme-class* convergence.

## Descriptive vs analytical framing of the non-perfective pattern

Identical situation to Chol. @cite{mateo-toledo-2008} §1.1.1 (p. 50)
characterizes Q'anjob'al's non-perfective alignment as
"nominative-accusative system (Dixon 1994:104)" — Set A/ergative
morphemes mark BOTH transitive and intransitive subjects in aspectless
contexts. The "extended ergative / Set A = GEN-from-D" framing is from
formal-syntactic analyses (Coon 2013, Imanishi 2020), where Set A is
analyzed as genitive licensed by D under nominalization. The substrate's
`extendedErgative.assignCase` returns `.gen` (analytical view); a
descriptive-grammar implementation would return `.nom`.

## Why the shared substrate works

@cite{mateo-toledo-2008} footnote 3 (p. 50): "in Q'anjob'alan languages,
split ergativity is associated with the lack of an aspect marker (that
is likely to be driven by nominalization, see Larsen and Norman 1979)."
This is the same nominalization-driven mechanism Coon (2013) argues for
Chol. The two languages converge on the alignment pattern via
independent grammaticalization (sister branches of Western Mayan, no
common-inheritance unit), which is why the substrate is named
`caseExtErg` (the typological convergence) rather than after a single
language family.
-/

namespace Fragments.Mayan.Qanjobal

-- ============================================================================
-- § 1: Argument Positions (alias to canonical SAP type)
-- ============================================================================

/-- Argument positions in a Q'anjob'al clause. Aliased to the canonical
    `Features.Prominence.ArgumentRole` (S/A/P/R/T) so cross-Mayan and
    cross-framework code shares one inventory. Use the canonical
    constructor names `.A` / `.P` / `.S` directly. -/
abbrev ArgPosition := Features.Prominence.ArgumentRole

/-- Perfective case assignment for Q'anjob'al. Shared with Chol via
    `Fragments.Mayan.ergCaseQanjobalan` (= `Alignment.ergative.assignCase`). -/
abbrev ArgPosition.case : ArgPosition → Core.Case := Fragments.Mayan.ergCaseQanjobalan

/-- Non-perfective case assignment for Q'anjob'al. Shared with Chol via
    `Fragments.Mayan.accCaseQanjobalan` (= `Alignment.extendedErgative.assignCase`).
    The shared substrate makes the Chol/Q'anjob'al accusative-side parallel
    explicit by construction rather than coincidentally true. -/
abbrev ArgPosition.accCase : ArgPosition → Core.Case := Fragments.Mayan.accCaseQanjobalan

-- ============================================================================
-- § 2: Absolutive Position (HIGH-ABS)
-- ============================================================================

/-- Q'anjob'al's absolutive morphemes appear in high position (on the
    aspect marker, pre-stem). Observable from morpheme order:
    ASP-ABS-ERG-ROOT-SUFFIX. -/
def absPosition : Fragments.Mayan.ABSPosition := .high

end Fragments.Mayan.Qanjobal
