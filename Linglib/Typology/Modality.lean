import Linglib.Features.Evidentiality
import Linglib.Data.WALS.Features.F74A
import Linglib.Data.WALS.Features.F75A
import Linglib.Data.WALS.Features.F76A
import Linglib.Data.WALS.Features.F77A
import Linglib.Data.WALS.Features.F78A

/-!
# Typology.Modality
@cite{aikhenvald-2004} @cite{de-haan-2013} @cite{vanderauwera-ammann-2013}
@cite{de-haan-2013b} @cite{wals-2013}

Per-language typological substrate for modality and evidentiality. Covers
five WALS chapters by @cite{de-haan-2013} and others:

- **Ch 74**: situational possibility (root, dynamic) — verbal, affixal, other.
- **Ch 75**: epistemic possibility — verbal, affixal, other.
- **Ch 76**: overlap between situational and epistemic modal marking.
- **Ch 77**: semantic distinctions of evidentiality (no grammatical /
  indirect-only / direct + indirect / three+).
- **Ch 78**: coding of evidentiality (verbal affix, particle, TAM-fused, ...).

Mirrors the `Linglib/Typology/{Possession,Negation,Comparison,Coordination}`
substrate-extension pattern. Fragment-importable.

## What lives here

- `EvidentialSystem` (Ch 77 4-way), `EvidentialCoding` (Ch 78 5-way) enums.
- `EvidentialityProfile` per-language struct.
- WALS converters: `fromWALS77A`, `fromWALS78A`.
- Aggregate distribution theorems for Ch 74-78 (corpus-only, theory-neutral).
- Helper predicates (`hasEvidentials`, `hasDirect`, `numChoices`, `isBound`,
  `countBySystem`, `countByCoding`).

## Theory-laden caveats

- **`EvidentialSystem` extends WALS Ch 77's 3-way to a 4-way** by adding
  `threeOrMore`. WALS collapses Quechua / Tuyuca / Aymara / Tariana into
  the same `directAndIndirect` bucket as Turkish / Bulgarian.
- **`EvidentialCoding` extends WALS Ch 78** with a separate `clitic` value
  (WALS lumps "verbal affix or clitic"). Used by analyses that distinguish
  affix from clitic.
- @cite{aikhenvald-2004}'s richer evidential typology (4-term, 5-term, etc.
  with finer category labels — visual / nonvisual / inferential / etc.) is
  beyond what WALS encodes; per-language profiles can record additional
  detail in `markers` and `notes`.

## Out of scope

Cross-linguistic generalisations consuming Fragment per-language data
live in `Studies/Aikhenvald2004.lean` (evidentiality
typology + the 18-language sample) and other paper-anchored studies
(Narrog2010/2012 for deontic necessity; Rubinstein2014 for weak
necessity; ImelGuoST2026 for modal-meaning typology).
-/

set_option autoImplicit false

namespace Typology.Modality

private abbrev ch74 := Data.WALS.F74A.allData
private abbrev ch75 := Data.WALS.F75A.allData
private abbrev ch76 := Data.WALS.F76A.allData
private abbrev ch77 := Data.WALS.F77A.allData
private abbrev ch78 := Data.WALS.F78A.allData

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
instance : DecidablePred HasEvidentials := fun s => by cases s <;> unfold HasEvidentials <;> infer_instance

/-- Whether a language grammaticalizes a direct evidence category. -/
def HasDirect : EvidentialSystem → Prop
  | .directAndIndirect | .threeOrMore => True
  | .noGrammatical | .indirectOnly => False
@[simp] theorem hasDirect_iff (s : EvidentialSystem) :
    s.HasDirect ↔ (s = .directAndIndirect ∨ s = .threeOrMore) := by
  cases s <;> simp [HasDirect]
instance : DecidablePred HasDirect := fun s => by cases s <;> unfold HasDirect <;> infer_instance

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
instance : DecidablePred IsBound := fun c => by cases c <;> unfold IsBound <;> infer_instance

end EvidentialCoding

-- ============================================================================
-- §2. EvidentialityProfile (Fragment-side joint)
-- ============================================================================

/-- A language's evidentiality profile across WALS Chs 77-78. -/
structure EvidentialityProfile where
  /-- Language name. -/
  language : String
  /-- ISO 639-3 code. -/
  iso : String
  /-- Language family. -/
  family : String
  /-- WALS Ch 77: evidential system type. -/
  system : EvidentialSystem
  /-- WALS Ch 78: coding strategy. -/
  coding : EvidentialCoding
  /-- Evidential marker forms (if applicable). -/
  markers : List String := []
  /-- Notes on the evidential system. -/
  notes : String := ""
  /-- Bridge to the lexical-layer `Features.Evidentiality.EvidentialSource`
      taxonomy: the canonical Aikhenvald-style source categories
      (direct / hearsay / inference) attested in this language. Defaults to
      `[]` for no-grammatical-evidentials languages. For 5-term systems
      (Tuyuca, Tariana, Kashaya) the visual/nonvisual distinction collapses
      onto `.direct`; the finer Aikhenvald categories live in `markers`. -/
  attestedEvidentials : List Features.Evidentiality.EvidentialSource := []
  deriving Repr, DecidableEq

-- ============================================================================
-- §3. WALS converters
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
-- §4. Helper predicates
-- ============================================================================

namespace EvidentialityProfile

/-- Does a language have grammatical evidentials? -/
def HasEvidentials (p : EvidentialityProfile) : Prop := p.system.HasEvidentials
@[simp] theorem hasEvidentials_iff (p : EvidentialityProfile) :
    p.HasEvidentials ↔ p.system.HasEvidentials := Iff.rfl
instance : DecidablePred HasEvidentials :=
  fun p => decidable_of_iff _ (hasEvidentials_iff p).symm

/-- Does a language have a direct evidence category? -/
def HasDirect (p : EvidentialityProfile) : Prop := p.system.HasDirect
@[simp] theorem hasDirect_iff (p : EvidentialityProfile) :
    p.HasDirect ↔ p.system.HasDirect := Iff.rfl
instance : DecidablePred HasDirect :=
  fun p => decidable_of_iff _ (hasDirect_iff p).symm

end EvidentialityProfile

/-- Count of languages in a sample with a given system type. -/
def countBySystem (langs : List EvidentialityProfile) (s : EvidentialSystem) :
    Nat :=
  (langs.filter (·.system == s)).length

/-- Count of languages in a sample with a given coding type. -/
def countByCoding (langs : List EvidentialityProfile) (c : EvidentialCoding) :
    Nat :=
  (langs.filter (·.coding == c)).length

-- ============================================================================
-- §5. WALS Lookup Helpers + Smart Constructor
-- ============================================================================

def walsEvidentialSystem (iso : String) : Option EvidentialSystem :=
  (Data.WALS.F77A.lookupISO iso).map (fromWALS77A ·.value)

def walsEvidentialCoding (iso : String) : Option EvidentialCoding :=
  (Data.WALS.F78A.lookupISO iso).map (fromWALS78A ·.value)

/-- Build an `EvidentialityProfile` from an ISO 639-3 code via WALS lookups
    for Chs 77/78. Required-field fallbacks (`systemFb`, `codingFb`) fire
    only when WALS is silent for that ISO. The `markers`, `notes`,
    `attestedEvidentials`, and `family` fields are paper-stipulated.

    Note: WALS Ch 77 only encodes a 3-way classification (no `threeOrMore`);
    languages with rich evidential systems (Quechua, Tuyuca, Tariana, etc.)
    will get `.directAndIndirect` from `fromWALS77A` rather than
    `.threeOrMore`. Per @cite{aikhenvald-2004}'s richer typology, those
    languages need a Studies-side override (mirrors the Corbett 1991 vs
    2013 record-update pattern in `Studies/Corbett1991`). -/
def EvidentialityProfile.fromWALS
    (language iso family : String)
    (markers : List String := [])
    (notes : String := "")
    (attestedEvidentials : List Features.Evidentiality.EvidentialSource := [])
    (systemFb : EvidentialSystem := .noGrammatical)
    (codingFb : EvidentialCoding := .notApplicable) : EvidentialityProfile :=
  { language, iso, family
  , system := (walsEvidentialSystem iso).getD systemFb
  , coding := (walsEvidentialCoding iso).getD codingFb
  , markers, notes, attestedEvidentials }

-- ============================================================================
-- §6. WALS distribution facts
-- ============================================================================

/-! Earlier revisions of this file carried 11 aggregate-count corpus
    theorems on the full WALS Ch 74-78 datasets (`ch74_verbal_dominant`,
    `ch77_no_evidentials_most_common`, etc.). These were the
    "aggregate-count theorems go stale" anti-pattern AND required
    `native_decide` for ~250-418-element list reductions; deleted as part
    of the EvidentialityProfile mathlib polish. The corpus distributions
    remain documentary in @cite{de-haan-2013}'s WALS chapters. -/

end Typology.Modality
