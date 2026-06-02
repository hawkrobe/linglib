import Linglib.Typology.Modality
import Linglib.Typology.Evidentiality
import Linglib.Semantics.Evidential.Basic
import Linglib.Fragments.French.Evidentiality
import Linglib.Fragments.Japanese.Evidentiality
import Linglib.Fragments.Turkish.Evidentiality
import Linglib.Fragments.Slavic.Bulgarian.Evidentiality
import Linglib.Fragments.Georgian.Evidentiality
import Linglib.Fragments.Quechua.Evidentiality
import Linglib.Fragments.Tuyuca.Evidentiality
import Linglib.Fragments.Kashaya.Evidentiality
import Linglib.Fragments.Tariana.Evidentiality
import Linglib.Fragments.Abkhaz.Evidentiality

/-!
# Aikhenvald (2004): Evidentiality typology
[aikhenvald-2004] [de-haan-2013] [barnes-1984] [oswalt-1986]

This file holds only the **analytical disagreements**: where
[aikhenvald-2004]'s own paradigm-type letter for a language differs
from `Typology.Evidentiality.AikhenvaldSystem.fromInventory` applied to the
Fragment-declared inventory, or where the resulting classification differs
from [de-haan-2013]'s WALS Ch 77 coding.

Per-language Aikhenvald classifications are *derived* in
`Typology/Evidentiality.lean`; per-language inventories live in
`Fragments/{Lang}/Evidentiality.lean`. There are no per-language
verification examples here — those would be unit tests of the derivation
algorithm, not theorems about the typology.

## Disagreements recorded

* **§1**: 4 paper-vs-derived disagreements (Turkish, Bulgarian, Abkhaz,
  Kashaya). Each is an analytical choice about which morphemes count as
  marked evidentials.
* **§2**: Aikhenvald-vs-WALS disagreements for languages where the two
  classifications diverge. Three representative cases.
-/

set_option autoImplicit false

namespace Aikhenvald2004

open Semantics.Evidential
open Typology.Modality (EvidentialSystem walsEvidentialSystem)
open Typology.Evidentiality (AikhenvaldSystem)

/-! ### §1. Paper-vs-derived disagreements

[aikhenvald-2004]'s own letter assignment for the four sample languages
where it differs from `AikhenvaldSystem.fromInventory`:
- Turkish, Bulgarian, Abkhaz: Aikhenvald treats one term as unmarked default
  (A2 = single marked non-firsthand); Fragment counts both terms (A1).
- Kashaya: Aikhenvald assigns D1 as closest fit; derivation returns `none`
  because the auditory cell plus missing nonvisualSensory and assumed cells
  break D1's structural pattern. -/

/-- Aikhenvald 2004's own letter for the four divergent languages. `none`
    for any language whose derivation matches the paper. -/
def paperType : String → Option AikhenvaldSystem
  | "tur" => some .A2  -- paper A2; derivation A1 (counts -DI as marked direct)
  | "bul" => some .A2  -- paper A2; derivation A1 (counts aorist as marked direct)
  | "abk" => some .A2  -- paper A2; derivation A1 (counts finite verb as marked)
  | "kju" => some .D1  -- paper D1 closest-fit; derivation `none` (auditory split)
  | _     => none

theorem turkish_paper_vs_derived :
    AikhenvaldSystem.fromInventory Turkish.Evidentiality.evidentials = some .A1 ∧
    paperType "tur" = some .A2 := by decide

theorem bulgarian_paper_vs_derived :
    AikhenvaldSystem.fromInventory Bulgarian.Evidentiality.evidentials = some .A1 ∧
    paperType "bul" = some .A2 := by decide

theorem abkhaz_paper_vs_derived :
    AikhenvaldSystem.fromInventory Abkhaz.Evidentiality.evidentials = some .A1 ∧
    paperType "abk" = some .A2 := by decide

theorem kashaya_paper_vs_derived :
    AikhenvaldSystem.fromInventory Kashaya.Evidentiality.evidentials = none ∧
    paperType "kju" = some .D1 := by decide

/-! ### §2. Aikhenvald-vs-WALS disagreements

Representative cases — same structural pattern repeats across the other
indirectOnly-via-modal cases (German, Korean, Finnish) and the other
WALS-lumps-rich-systems cases (Tariana, Kashaya). -/

/-- Empty inventory per Aikhenvald-strict vs WALS `indirectOnly`. French
    is the canonical case: the journalistic conditional has reportative
    use that WALS counts but Aikhenvald excludes. Same pattern holds for
    German, Japanese, Korean, Finnish. -/
theorem french_wals_divergence :
    AikhenvaldSystem.fromInventory French.Evidentiality.evidentials = none ∧
    walsEvidentialSystem "fra" = some .indirectOnly := by decide

theorem japanese_wals_divergence :
    AikhenvaldSystem.fromInventory Japanese.Evidentiality.evidentials = none ∧
    walsEvidentialSystem "jpn" = some .indirectOnly := by decide

/-- The signature divergence: Tuyuca's D1 5-term system per Aikhenvald
    (projecting to `threeOrMore`) vs WALS's `directAndIndirect` lump. Same
    paradigm, two classifications, both kernel-verified. -/
theorem tuyuca_wals_divergence :
    AikhenvaldSystem.fromInventory Tuyuca.Evidentiality.evidentials = some .D1 ∧
    AikhenvaldSystem.D1.toWALS = .threeOrMore ∧
    walsEvidentialSystem "tue" = some .directAndIndirect := by decide

/-- Andean B1: Aikhenvald has classification; WALS has no entry. -/
theorem quechua_no_wals_entry :
    AikhenvaldSystem.fromInventory Quechua.Evidentiality.evidentials = some .B1 ∧
    walsEvidentialSystem "quz" = none := by decide

/-- Turkish: derivation's A1 happens to project to the same WALS coding
    (`directAndIndirect`) WALS assigns directly; the Aikhenvald *paper*
    A2 projects to `indirectOnly`. Triple-comparison divergence. -/
theorem turkish_wals_divergence :
    AikhenvaldSystem.A2.toWALS = .indirectOnly ∧
    walsEvidentialSystem "tur" = some .directAndIndirect := by decide

end Aikhenvald2004
