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

Per-language typological substrate enums + WALS lookups for modality and
evidentiality. Covers five WALS chapters:

- **Ch 74**: situational possibility (root, dynamic).
- **Ch 75**: epistemic possibility.
- **Ch 76**: overlap between situational and epistemic modal marking.
- **Ch 77**: semantic distinctions of evidentiality.
- **Ch 78**: coding of evidentiality.

## What lives here

* `EvidentialSystem` (Ch 77, extended), `EvidentialCoding` (Ch 78, extended)
  enums + their helper predicates.
* `fromWALS77A`, `fromWALS78A` converters.
* `walsEvidentialSystem`, `walsEvidentialCoding` ISO lookups for cross-author
  comparison theorems.

Per-language inventories live in `Fragments/{Lang}/Evidentiality.lean` as
`evidentials : List Semantics.Evidential.Entry`. Aikhenvald paradigm
system-types live in `Typology/Evidentiality.lean` and are *derived* from
inventories via `AikhenvaldSystem.fromInventory`. Cross-author divergences
live in `Studies/Aikhenvald2004.lean`.

## Theory-laden caveats

* **`EvidentialSystem` extends WALS Ch 77's 3-way to a 4-way** by adding
  `threeOrMore`. WALS collapses Quechua / Tuyuca / Aymara / Tariana into
  the same `directAndIndirect` bucket as Turkish / Bulgarian.
* **`EvidentialCoding` extends WALS Ch 78** with a separate `clitic` value.
-/

set_option autoImplicit false

namespace Typology.Modality

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

end Typology.Modality
