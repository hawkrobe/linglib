import Linglib.Typology.Modality
import Linglib.Semantics.Evidential.Basic

/-!
# Typology.Evidentiality
@cite{aikhenvald-2004} @cite{de-haan-2013}

@cite{aikhenvald-2004}'s system-type classification of evidentiality
paradigms by paradigm shape (term count + cell distribution),
complementing the WALS Ch 77 (@cite{de-haan-2013}) 3-way classification
already encoded in `Typology.Modality.EvidentialSystem`.

The catalog runs A1–D1, where the letter encodes term count
(A: 2-term, B: 3-term, C: 4-term, D: 5+-term) and the digit encodes
paradigm shape (which cells of the source × inference space are
distinguished). Catalog drawn from @cite{aikhenvald-2004} Ch 2 §§2.1-2.4.

## Main declarations

* `AikhenvaldSystem` — the 14-case paradigm-type classification (Ch 2).
* `AikhenvaldSystem.termCount` — number of evidential terms in the system.
* `AikhenvaldSystem.toWALS` — projection to the WALS Ch 77 3-way
  classification (extended with `threeOrMore`).

## Out of scope

Per-language `AikhenvaldSystem` assignments live in
`Studies/Aikhenvald2004.lean` (cross-linguistic facts about the
declared 18-language sample), and ultimately in per-Fragment Profile
records. Derivation of `AikhenvaldSystem` from a declared `List
Semantics.Evidential.Entry` inventory is deferred to a later phase
once the Profile record settles.
-/

set_option autoImplicit false

namespace Typology.Evidentiality

open Typology.Modality (EvidentialSystem)

/-- @cite{aikhenvald-2004} Ch 2 paradigm system-type classification. The
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

/-- Projection to the WALS Ch 77 (@cite{de-haan-2013}) classification,
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

/-- Derive @cite{aikhenvald-2004}'s paradigm system-type letter from a
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

end Typology.Evidentiality
