import Linglib.Data.WALS.Features.F77A
import Linglib.Data.WALS.Features.F78A
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
from `AikhenvaldSystem.fromInventory` applied to the
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

/-! ### Evidentiality typology (consolidated from the former Typology/Modality + Typology/Evidentiality; single-paper [aikhenvald-2004] apparatus) -/


-- ============================================================================
-- §1. Ch 77 / 78 substrate enums
-- ============================================================================

/-- WALS Ch 77: how many evidential distinctions a language grammaticalises.
    Extends the WALS 3-way classification with a `threeOrMore` value to
    distinguish Quechua/Tuyuca-style rich systems from canonical 2-way
    systems (Turkish/Bulgarian). -/
inductive EvidentialSystem where
  /-- No grammatical evidentials (e.g. English, French, Mandarin). -/
  | noGrammatical
  /-- Indirect evidential only (e.g. Georgian, West Greenlandic). -/
  | indirectOnly
  /-- Two-choice direct vs indirect (e.g. Turkish, Bulgarian, Tibetan, Abkhaz). -/
  | directAndIndirect
  /-- Three or more evidential choices (e.g. Quechua, Tuyuca, Aymara, Tariana). -/
  | threeOrMore
  deriving DecidableEq, BEq, Repr

namespace EvidentialSystem

/-- Whether a language has any grammatical evidential marking. -/
def HasEvidentials : EvidentialSystem → Prop
  | .noGrammatical => False
  | .indirectOnly | .directAndIndirect | .threeOrMore => True
@[simp] theorem hasEvidentials_iff (s : EvidentialSystem) :
    s.HasEvidentials ↔ s ≠ .noGrammatical := by cases s <;> simp [HasEvidentials]
instance : DecidablePred HasEvidentials := fun s => by
  cases s <;> unfold HasEvidentials <;> infer_instance

/-- Whether a language grammaticalizes a direct evidence category. -/
def HasDirect : EvidentialSystem → Prop
  | .directAndIndirect | .threeOrMore => True
  | .noGrammatical | .indirectOnly => False
@[simp] theorem hasDirect_iff (s : EvidentialSystem) :
    s.HasDirect ↔ (s = .directAndIndirect ∨ s = .threeOrMore) := by
  cases s <;> simp [HasDirect]
instance : DecidablePred HasDirect := fun s => by
  cases s <;> unfold HasDirect <;> infer_instance

/-- Number of evidential choices in the system (0, 1, 2, or 3+). -/
def numChoices : EvidentialSystem → Nat
  | .noGrammatical => 0
  | .indirectOnly => 1
  | .directAndIndirect => 2
  | .threeOrMore => 3

end EvidentialSystem

/-- WALS Ch 78: how evidentiality is morphologically expressed. -/
inductive EvidentialCoding where
  /-- Evidential is a verbal affix or clitic (bound morpheme). Dominant
      strategy worldwide (131/418 in WALS Ch 78). -/
  | verbalAffix
  /-- Evidential is a clitic (phrasal-level, not strictly verbal). -/
  | clitic
  /-- Evidential is a free separate particle (65/418). -/
  | particle
  /-- Evidential distinctions fused into the TAM paradigm. -/
  | partOfTAM
  /-- Not applicable: language has no grammatical evidentials. -/
  | notApplicable
  deriving DecidableEq, BEq, Repr

namespace EvidentialCoding

/-- Whether the coding strategy involves a bound morpheme (affix or clitic). -/
def IsBound : EvidentialCoding → Prop
  | .verbalAffix | .clitic => True
  | .particle | .partOfTAM | .notApplicable => False
@[simp] theorem isBound_iff (c : EvidentialCoding) :
    c.IsBound ↔ (c = .verbalAffix ∨ c = .clitic) := by cases c <;> simp [IsBound]
instance : DecidablePred IsBound := fun c => by
  cases c <;> unfold IsBound <;> infer_instance

end EvidentialCoding

-- ============================================================================
-- §2. WALS converters
-- ============================================================================

/-- WALS Ch 77 → `EvidentialSystem`. WALS Ch 77's 3-way classification maps
    onto our 4-way; `threeOrMore` cannot be reached from WALS alone (WALS
    lumps three-or-more systems with `directAndIndirect`). -/
def fromWALS77A : Data.WALS.F77A.EvidentialityDistinctions → EvidentialSystem
  | .noGrammaticalEvidentials => .noGrammatical
  | .indirectOnly             => .indirectOnly
  | .directAndIndirect        => .directAndIndirect

/-- WALS Ch 78 → `EvidentialCoding`. WALS lumps "verbal affix or clitic";
    the `mixed` and `modalMorpheme` categories are mapped to closest local
    cells (best-effort). -/
def fromWALS78A : Data.WALS.F78A.EvidentialityCoding → EvidentialCoding
  | .noGrammaticalEvidentials => .notApplicable
  | .verbalAffixOrClitic      => .verbalAffix
  | .partOfTheTenseSystem     => .partOfTAM
  | .separateParticle         => .particle
  | .modalMorpheme            => .particle
  | .mixed                    => .partOfTAM

-- ============================================================================
-- §3. WALS lookup helpers
-- ============================================================================

/-- WALS Ch 77 lookup by ISO 639-3 code. `none` for languages WALS doesn't
    cover. Used by Aikhenvald-vs-WALS divergence theorems. -/
def walsEvidentialSystem (iso : String) : Option EvidentialSystem :=
  (Data.WALS.F77A.lookupISO iso).map (fromWALS77A ·.value)

/-- WALS Ch 78 lookup by ISO 639-3 code. -/
def walsEvidentialCoding (iso : String) : Option EvidentialCoding :=
  (Data.WALS.F78A.lookupISO iso).map (fromWALS78A ·.value)



/-- [aikhenvald-2004] Ch 2 paradigm system-type classification. The
    letter encodes term count (A=2, B=3, C=4, D=5); the digit encodes
    paradigm shape. -/
inductive AikhenvaldSystem where
  /-- A1: Firsthand vs Non-firsthand. The most common 2-term type
      (Cherokee, Jarawara, Yukaghir, Tibetan).
      Aikhenvald 2004 Ch 2 §2.1.1. -/
  | A1
  /-- A2: Non-firsthand vs 'everything else'. The single marked term
      covers inference and report. Common in Turkic and Caucasian
      languages (Turkish, Abkhaz, Hunzib).
      Aikhenvald 2004 Ch 2 §2.1.1. -/
  | A2
  /-- A3: Reported (or 'hearsay') vs 'everything else'. The single
      marked term is the reportative. Widespread (Lezgian, Estonian,
      Enga, Kham, many North American Indian languages).
      Aikhenvald 2004 Ch 2 §2.1.1. -/
  | A3
  /-- A4: Sensory evidence and Reported. Both terms marked (Ngiyambaa,
      Diyari, Lakondê/Latundê, reduced Wintu).
      Aikhenvald 2004 Ch 2 §2.1.1. -/
  | A4
  /-- A5: Auditory vs 'everything else'. Attested only in Euchee.
      Aikhenvald 2004 Ch 2 §2.1.1. -/
  | A5
  /-- B1: Direct (or Visual) + Inferred + Reported. The most common
      3-term system. The Quechua family (`-mi`, `-chi`, `-shi`),
      Wanka Quechua, Shasta, Amdo Tibetan, Qiang, Mosetén.
      Aikhenvald 2004 Ch 2 §2.2. -/
  | B1
  /-- B2: Visual + Non-visual sensory + Inferred. No reportative.
      Rare (Washo, Siona).
      Aikhenvald 2004 Ch 2 §2.2. -/
  | B2
  /-- B3: Visual + Non-visual sensory + Reported. No inferential.
      Oksapmin, Maricopa, Dulong.
      Aikhenvald 2004 Ch 2 §2.2. -/
  | B3
  /-- B4: Non-visual sensory + Inferred + Reported. Visual is unmarked
      default (Nganasan, Enets, Retuarã).
      Aikhenvald 2004 Ch 2 §2.2. -/
  | B4
  /-- B5: Reported + Quotative + 'everything else'. Two distinct
      reported-type evidentials, similar to A3 with quotative split
      (Comanche, Dakota, Tonkawa).
      Aikhenvald 2004 Ch 2 §2.2. -/
  | B5
  /-- C1: Visual + Non-visual sensory + Inferred + Reported. The most
      common 4-term system; East Tucanoan languages (Tucano, Barasano,
      Tatuyo, Siriano, Macuna), Eastern Pomo, traditional Tariana.
      Aikhenvald 2004 Ch 2 §2.3. -/
  | C1
  /-- C2: Direct (or Visual) + Inferred + Assumed + Reported. The
      sensory may be just visual (Tsafiki, Shipibo-Konibo, Pawnee,
      Mamainde).
      Aikhenvald 2004 Ch 2 §2.3. -/
  | C2
  /-- C3: Direct + Inferred + Reported + Quotative. Two distinct
      reportative types (Cora, Northern Embera, SE Tepehuan).
      Aikhenvald 2004 Ch 2 §2.3. -/
  | C3
  /-- D1: Visual + Non-visual sensory + Inferred + Assumed + Reported.
      The classical 5-term system: current Tariana, Tuyuca, Desano,
      traditional Wintu. Kashaya is comparable but distinguishes
      auditory within non-visual.
      Aikhenvald 2004 Ch 2 §2.4. -/
  | D1
  deriving DecidableEq, BEq, Repr, Inhabited

namespace AikhenvaldSystem

/-- Number of evidential terms in the paradigm. The letter prefix
    encodes the count directly: A=2, B=3, C=4, D=5. Note: A2/A3/A5
    have only one *marked* term but Aikhenvald counts the unmarked
    'everything else' form, giving 2 (see Ch 2 §2.1). -/
def termCount : AikhenvaldSystem → Nat
  | .A1 | .A2 | .A3 | .A4 | .A5 => 2
  | .B1 | .B2 | .B3 | .B4 | .B5 => 3
  | .C1 | .C2 | .C3             => 4
  | .D1                         => 5

/-- Projection to the WALS Ch 77 ([de-haan-2013]) classification,
    extended with `threeOrMore`. A-systems map per their direct/indirect
    coverage; B/C/D map uniformly to `.threeOrMore`. WALS itself
    collapses B/C/D into `.directAndIndirect`; the `.threeOrMore`
    extension is linglib's, preserving Aikhenvald's richer typology
    (see `Typology/Modality.lean` and Aikhenvald 2004 Ch 2 §2.2). -/
def toWALS : AikhenvaldSystem → EvidentialSystem
  | .A1                         => .directAndIndirect
  | .A2 | .A3                   => .indirectOnly
  | .A4 | .A5                   => .directAndIndirect
  | .B1 | .B2 | .B3 | .B4 | .B5 => .threeOrMore
  | .C1 | .C2 | .C3             => .threeOrMore
  | .D1                         => .threeOrMore

/-- The Aikhenvald typology is always richer-or-equal to the WALS one:
    `.threeOrMore` for all 3+-term systems (B/C/D), the appropriate
    2-way value for 2-term systems (A). -/
@[simp] theorem termCount_pos (s : AikhenvaldSystem) : 0 < s.termCount := by
  cases s <;> decide

@[simp] theorem termCount_le_5 (s : AikhenvaldSystem) : s.termCount ≤ 5 := by
  cases s <;> decide

end AikhenvaldSystem

/-! ### Derivation from a typed inventory -/

open Semantics.Evidential
open Semantics.Evidential.Entry (Cell)

namespace AikhenvaldSystem

/-- Derive [aikhenvald-2004]'s paradigm system-type letter from a
    declared inventory by inspecting which cells of her paradigm space are
    covered. Mirrors `Determiner.markingStrategy`'s derivation pattern.
    Returns `none` for inventories whose cell pattern doesn't fit any
    standard A–D letter; per-paper editorial overrides for such cases
    live in the relevant `Studies/AuthorYear.lean`. -/
def fromInventory (es : List Entry) : Option AikhenvaldSystem :=
  let cells := es.map Entry.cell
  let has (c : Cell) : Bool := cells.any (fun x => x == c)
  let hasF   := has .firsthand
  let hasV   := has .visual
  let hasNVS := has .nonvisualSensory
  let hasA   := has .auditory
  let hasI   := has .inferred
  let hasS   := has .assumed
  let hasR   := has .reported
  let hasQ   := has .quotative
  let count : Nat := (if hasF then 1 else 0) + (if hasV then 1 else 0) +
                     (if hasNVS then 1 else 0) + (if hasA then 1 else 0) +
                     (if hasI then 1 else 0) + (if hasS then 1 else 0) +
                     (if hasR then 1 else 0) + (if hasQ then 1 else 0)
  match count with
  | 0 => none
  | 1 =>
    if hasR then some .A3
    else if hasA then some .A5
    else if hasI || hasS then some .A2
    else none
  | 2 =>
    if hasF && (hasI || hasR || hasS) then some .A1
    else if (hasV || hasNVS || hasA) && hasR then some .A4
    else none
  | 3 =>
    if hasV && hasNVS && hasI && !hasR then some .B2
    else if hasV && hasNVS && hasR && !hasI then some .B3
    else if !hasV && !hasF && hasNVS && hasI && hasR then some .B4
    else if (hasF || hasV) && hasI && hasR then some .B1
    else if hasR && hasQ then some .B5
    else none
  | 4 =>
    if hasV && hasNVS && hasI && hasR then some .C1
    else if (hasF || hasV) && hasI && hasS && hasR then some .C2
    else if (hasF || hasV) && hasI && hasR && hasQ then some .C3
    else none
  | 5 =>
    if hasV && hasNVS && hasI && hasS && hasR then some .D1
    else none
  | _ => none

end AikhenvaldSystem

/-! ### Worked examples documenting the API -/

example : AikhenvaldSystem.termCount .A1 = 2 := by decide
example : AikhenvaldSystem.termCount .B1 = 3 := by decide
example : AikhenvaldSystem.termCount .C1 = 4 := by decide
example : AikhenvaldSystem.termCount .D1 = 5 := by decide

example : AikhenvaldSystem.toWALS .A1 = .directAndIndirect := by decide
example : AikhenvaldSystem.toWALS .A2 = .indirectOnly := by decide
example : AikhenvaldSystem.toWALS .A3 = .indirectOnly := by decide
example : AikhenvaldSystem.toWALS .B1 = .threeOrMore := by decide
example : AikhenvaldSystem.toWALS .C1 = .threeOrMore := by decide
example : AikhenvaldSystem.toWALS .D1 = .threeOrMore := by decide


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
