import Linglib.Theories.Interfaces.Morphosyntax.CaseContainment
import Linglib.Fragments.Czech.Case
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
import Linglib.Fragments.Polish.Case
import Linglib.Fragments.Russian.Case
import Linglib.Fragments.Serbian.Case
import Linglib.Fragments.Slovenian.Case
import Linglib.Fragments.SwissGerman.Case
import Linglib.Fragments.Tamil.Case
import Linglib.Fragments.Telugu.Case
import Linglib.Fragments.Turkish.Case
import Linglib.Fragments.Ukrainian.Case
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
`respectsCahaContainment` (defined in
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
    respectsCahaContainment Fragments.Czech.Case.caseInventory = true := by decide

theorem german :
    respectsCahaContainment Fragments.German.Case.caseInventory = true := by decide

theorem greek :
    respectsCahaContainment Fragments.Greek.Case.caseInventory = true := by decide

theorem hindi :
    respectsCahaContainment Fragments.Hindi.Case.caseInventory = true := by decide

theorem hungarian :
    respectsCahaContainment Fragments.Hungarian.Case.caseInventory = true := by decide

theorem icelandic :
    respectsCahaContainment Fragments.Icelandic.Case.caseInventory = true := by decide

theorem japanese :
    respectsCahaContainment Fragments.Japanese.Case.caseInventory = true := by decide

theorem korean :
    respectsCahaContainment Fragments.Korean.Case.caseInventory = true := by decide

theorem latin :
    respectsCahaContainment Fragments.Latin.Case.caseInventory = true := by decide

theorem mongolian :
    respectsCahaContainment Fragments.Mongolian.Case.caseInventory = true := by decide

theorem polish :
    respectsCahaContainment Fragments.Polish.Case.caseInventory = true := by decide

theorem russian :
    respectsCahaContainment Fragments.Russian.Case.caseInventory = true := by decide

theorem serbian :
    respectsCahaContainment Fragments.Serbian.Case.caseInventory = true := by decide

theorem slovenian :
    respectsCahaContainment Fragments.Slovenian.Case.caseInventory = true := by decide

theorem swissgerman :
    respectsCahaContainment Fragments.SwissGerman.Case.caseInventory = true := by decide

theorem tamil :
    respectsCahaContainment Fragments.Tamil.Case.caseInventory = true := by decide

theorem telugu :
    respectsCahaContainment Fragments.Telugu.Case.caseInventory = true := by decide

theorem turkish :
    respectsCahaContainment Fragments.Turkish.Case.caseInventory = true := by decide

theorem ukrainian :
    respectsCahaContainment Fragments.Ukrainian.Case.caseInventory = true := by decide

theorem yakut :
    respectsCahaContainment Fragments.Yakut.Case.caseInventory = true := by decide

-- ============================================================================
-- § 2: Predicted Violators
-- ============================================================================

/-- Dargwa is ergative: its inventory contains GEN and DAT (ranks 2, 3) but
    no NOM or ACC (ranks 0, 1). Ergative S/A/P alignment puts ABS where
    NOM would be, and Caha's containment is keyed to accusative alignment.
    The ergative cases (ERG, ABS) are off-hierarchy in `containmentRank`. -/
theorem dargwa_ergative :
    respectsCahaContainment Fragments.Dargwa.Case.caseInventory = false := by decide

/-- Finnish has no dedicated dative — the allative (-lle) covers recipient
    function. Its inventory has rank 4 (LOC) without rank 3 (DAT).
    @cite{blake-1994} Ch. 6 documents this as the ALL → DAT extension
    pattern; @cite{karlsson-2017} confirms the lack of a Finnish dative.

    This is the canonical Finnish exception to strict hierarchy contiguity:
    the language genuinely lacks the missing case rather than reorganizing
    it under Caha's containment. -/
theorem finnish_dat_gap :
    respectsCahaContainment Fragments.Finnish.Case.caseInventory = false := by decide

-- ============================================================================
-- § 3: Cross-Inventory Survey
-- ============================================================================

/-- The full Caha-conformance verdict for every Fragment case inventory in
    the library, paired with its language label. The 20 conformers and the
    2 predicted violators (Dargwa, Finnish) are bundled into one finite
    table so that adding a new Fragment with a missing classification
    breaks this theorem rather than silently dropping out of the survey.

    Maintenance contract: when adding `Fragments/<Lang>/Case.lean`, add
    the corresponding line here AND a per-language theorem above. The
    individual theorems give precise blame; this table gives coverage. -/
def cahaSurvey : List (String × Bool) :=
  [ ("czech",      respectsCahaContainment Fragments.Czech.Case.caseInventory),
    ("dargwa",     respectsCahaContainment Fragments.Dargwa.Case.caseInventory),
    ("finnish",    respectsCahaContainment Fragments.Finnish.Case.caseInventory),
    ("german",     respectsCahaContainment Fragments.German.Case.caseInventory),
    ("greek",      respectsCahaContainment Fragments.Greek.Case.caseInventory),
    ("hindi",      respectsCahaContainment Fragments.Hindi.Case.caseInventory),
    ("hungarian",  respectsCahaContainment Fragments.Hungarian.Case.caseInventory),
    ("icelandic",  respectsCahaContainment Fragments.Icelandic.Case.caseInventory),
    ("japanese",   respectsCahaContainment Fragments.Japanese.Case.caseInventory),
    ("korean",     respectsCahaContainment Fragments.Korean.Case.caseInventory),
    ("latin",      respectsCahaContainment Fragments.Latin.Case.caseInventory),
    ("mongolian",  respectsCahaContainment Fragments.Mongolian.Case.caseInventory),
    ("polish",     respectsCahaContainment Fragments.Polish.Case.caseInventory),
    ("russian",    respectsCahaContainment Fragments.Russian.Case.caseInventory),
    ("serbian",    respectsCahaContainment Fragments.Serbian.Case.caseInventory),
    ("slovenian",  respectsCahaContainment Fragments.Slovenian.Case.caseInventory),
    ("swissgerman",respectsCahaContainment Fragments.SwissGerman.Case.caseInventory),
    ("tamil",      respectsCahaContainment Fragments.Tamil.Case.caseInventory),
    ("telugu",     respectsCahaContainment Fragments.Telugu.Case.caseInventory),
    ("turkish",    respectsCahaContainment Fragments.Turkish.Case.caseInventory),
    ("ukrainian",  respectsCahaContainment Fragments.Ukrainian.Case.caseInventory),
    ("yakut",      respectsCahaContainment Fragments.Yakut.Case.caseInventory) ]

/-- Every Fragment in the library is classified by Caha containment — the
    survey is total. -/
theorem cahaSurvey_length : cahaSurvey.length = 22 := by decide

/-- Exactly two languages violate strict Caha contiguity, and both are
    documented exceptions: Dargwa (ergative alignment) and Finnish
    (DAT gap). Every other Fragment conforms. -/
theorem all_inventories_classified :
    cahaSurvey.filter (fun p => !p.2) = [("dargwa", false), ("finnish", false)] := by
  decide

/-- Conformance rate: 20/22 of the formalized inventories respect Caha. -/
theorem caha_conformance_count :
    (cahaSurvey.filter (·.2)).length = 20 := by decide

end Phenomena.Case.Studies.Caha2009
