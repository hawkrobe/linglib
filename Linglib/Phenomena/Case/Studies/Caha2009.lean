import Linglib.Theories.Interfaces.Morphosyntax.CaseContainment
import Linglib.Fragments.Slavic.Czech.Case
import Linglib.Fragments.Dargwa.Case
import Linglib.Fragments.Finnish.Case
import Linglib.Fragments.German.Case
import Linglib.Fragments.Greek.Case
import Linglib.Fragments.Hindi.Case
import Linglib.Fragments.Hungarian.Case
import Linglib.Fragments.Icelandic.Case
import Linglib.Fragments.Japanese.Case
import Linglib.Fragments.Korean.Case
import Linglib.Fragments.Latin.Case
import Linglib.Fragments.Mongolian.Case
import Linglib.Fragments.Slavic.Polish.Case
import Linglib.Fragments.Slavic.Russian.Case
import Linglib.Fragments.Slavic.Serbian.Case
import Linglib.Fragments.Slavic.Slovenian.Case
import Linglib.Fragments.SwissGerman.Case
import Linglib.Fragments.Tamil.Case
import Linglib.Fragments.Telugu.Case
import Linglib.Fragments.Turkish.Case
import Linglib.Fragments.Slavic.Ukrainian.Case
import Linglib.Fragments.Yakut.Case

/-!
# Caha (2009) — The Nanosyntax of Case
@cite{caha-2009}

Caha's central proposal: the morphosyntactic representation of each case
on a universal hierarchy literally *contains* the representations of all
cases below it.

    [[[[[ NOM ] ACC ] GEN ] DAT ] P ]

A vocabulary insertion rule conditioned on a feature `F` matches every
case whose representation contains `F`, which together with the Superset
Principle derives the cross-linguistic *ABA constraint
(@cite{bobaljik-2012}): in any case-conditioned suppletion paradigm
ordered by containment, A–B–A patterns are unattested.

This study file applies Caha's containment as a typological prediction
to the case inventories in `Fragments/*/Case.lean`. The predicate
`RespectsCahaContainment` (defined in
`Theories/Interfaces/Morphosyntax/CaseContainment.lean`) checks whether
the on-hierarchy cases in an inventory form a contiguous prefix
NOM, NOM-ACC, NOM-ACC-GEN, NOM-ACC-GEN-DAT, NOM-ACC-GEN-DAT-LOC.

## Predictions and exceptions

Of 22 Fragment case inventories, 20 conform; 2 fall out of strict
prefix contiguity, both for principled reasons:

- **Dargwa** (ergative): `[abs, erg, gen, dat, com, ess]` — Caha's
  hierarchy is keyed to accusative alignment; ergative ABS/ERG are
  off-hierarchy. Dargwa's GEN/DAT presence without NOM/ACC reflects
  alignment, not a Caha counterexample.
- **Finnish** (DAT-less): no dedicated dative — the allative (-lle)
  covers recipient function. @cite{blake-1994} Ch. 6 documents this as
  the ALL → DAT extension pattern; @cite{karlsson-2017} confirms.

Both violations sit naturally in the "off-hierarchy cases are
incomparable" region of the `PartialOrder Core.Case` instance that
realizes Caha's containment as the canonical order on cases.
-/

namespace Phenomena.Case.Studies.Caha2009

open Core
open Interfaces.Morphosyntax.CaseContainment

-- ============================================================================
-- § 1: Conformers
-- ============================================================================

theorem czech :
    RespectsCahaContainment Fragments.Slavic.Czech.Case.caseInventory := by decide

theorem german :
    RespectsCahaContainment Fragments.German.Case.caseInventory := by decide

theorem greek :
    RespectsCahaContainment Fragments.Greek.Case.caseInventory := by decide

theorem hindi :
    RespectsCahaContainment Fragments.Hindi.Case.caseInventory := by decide

theorem hungarian :
    RespectsCahaContainment Fragments.Hungarian.Case.caseInventory := by decide

theorem icelandic :
    RespectsCahaContainment Fragments.Icelandic.Case.caseInventory := by decide

theorem japanese :
    RespectsCahaContainment Fragments.Japanese.Case.caseInventory := by decide

theorem korean :
    RespectsCahaContainment Fragments.Korean.Case.caseInventory := by decide

theorem latin :
    RespectsCahaContainment Fragments.Latin.Case.caseInventory := by decide

theorem mongolian :
    RespectsCahaContainment Fragments.Mongolian.Case.caseInventory := by decide

theorem polish :
    RespectsCahaContainment Fragments.Slavic.Polish.Case.caseInventory := by decide

theorem russian :
    RespectsCahaContainment Fragments.Slavic.Russian.Case.caseInventory := by decide

theorem serbian :
    RespectsCahaContainment Fragments.Slavic.Serbian.Case.caseInventory := by decide

theorem slovenian :
    RespectsCahaContainment Fragments.Slavic.Slovenian.Case.caseInventory := by decide

theorem swissgerman :
    RespectsCahaContainment Fragments.SwissGerman.Case.caseInventory := by decide

theorem tamil :
    RespectsCahaContainment Fragments.Tamil.Case.caseInventory := by decide

theorem telugu :
    RespectsCahaContainment Fragments.Telugu.Case.caseInventory := by decide

theorem turkish :
    RespectsCahaContainment Fragments.Turkish.Case.caseInventory := by decide

theorem ukrainian :
    RespectsCahaContainment Fragments.Slavic.Ukrainian.Case.caseInventory := by decide

theorem yakut :
    RespectsCahaContainment Fragments.Yakut.Case.caseInventory := by decide

-- ============================================================================
-- § 2: Predicted Violators
-- ============================================================================

/-- Dargwa is ergative: its inventory contains GEN and DAT (ranks 2, 3) but
    no NOM or ACC (ranks 0, 1). Ergative S/A/P alignment puts ABS where
    NOM would be, and Caha's containment is keyed to accusative alignment.
    The ergative cases (ERG, ABS) are off-hierarchy in `containmentRank`. -/
theorem dargwa_ergative :
    ¬ RespectsCahaContainment Fragments.Dargwa.Case.caseInventory := by decide

/-- Finnish has no dedicated dative — the allative (-lle) covers recipient
    function. Its inventory has rank 4 (LOC) without rank 3 (DAT).
    @cite{blake-1994} Ch. 6 documents this as the ALL → DAT extension
    pattern; @cite{karlsson-2017} confirms the lack of a Finnish dative.

    This is the canonical Finnish exception to strict hierarchy contiguity:
    the language genuinely lacks the missing case rather than reorganizing
    it under Caha's containment. -/
theorem finnish_dat_gap :
    ¬ RespectsCahaContainment Fragments.Finnish.Case.caseInventory := by decide

end Phenomena.Case.Studies.Caha2009
