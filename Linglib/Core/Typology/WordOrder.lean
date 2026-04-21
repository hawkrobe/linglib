import Linglib.Core.WALS.Features.F81A
import Linglib.Core.WALS.Features.F82A
import Linglib.Core.WALS.Features.F83A

/-!
# Word-order typology: shared record types

Framework-agnostic record types for storing per-language word-order data
(WALS Chapters 81–83). These types live in `Core/` so that both `Fragments/`
(per-language profiles) and `Phenomena/WordOrder/` (cross-linguistic
generalizations) can import them without violating the layered dependency
hierarchy.

The key record is `WordOrderProfile` — a plain bundle of order values plus a
free-text `notes` field. Provenance for individual values lives in the
`@cite{...}` keys of whichever Fragment populates the record, not in a runtime
wrapper.

`WordOrderProfile.ofWALS` provides the canonical "derive from WALS by ISO
lookup" convenience so per-language Fragments can write `ofWALS "eng"` rather
than re-implementing the lookup-and-fall-back boilerplate. Languages absent
from a given WALS chapter get `.noDominant` for that field.
-/

namespace Core.Typology.WordOrder

/-- WALS Ch 81: six-way classification of basic constituent order, plus
    a `noDominant` cell for languages where no single order clearly dominates. -/
inductive BasicOrder where
  | sov | svo | vso | vos | ovs | osv | noDominant
  deriving DecidableEq, Repr

/-- WALS Ch 82: binary classification of subject–verb order. -/
inductive SVOrder where
  | sv | vs | noDominant
  deriving DecidableEq, Repr

/-- WALS Ch 83: binary classification of object–verb order. -/
inductive OVOrder where
  | ov | vo | noDominant
  deriving DecidableEq, Repr

/-- A bundle of WALS-style word-order classifications for a single language.
    `notes` carries free-text commentary (and is the natural home for the
    `@cite{...}` keys that document non-WALS sources for hand-coded values). -/
structure WordOrderProfile where
  basicOrder : BasicOrder
  svOrder : SVOrder
  ovOrder : OVOrder
  notes : String := ""
  deriving Repr, DecidableEq

/-- Convert WALS F81A's `BasicWordOrder` to our local `BasicOrder`. -/
def fromWALS81A : Core.WALS.F81A.BasicWordOrder → BasicOrder
  | .sov => .sov
  | .svo => .svo
  | .vso => .vso
  | .vos => .vos
  | .ovs => .ovs
  | .osv => .osv
  | .noDominantOrder => .noDominant

/-- Convert WALS F82A's `SubjectVerbOrder` to our local `SVOrder`. -/
def fromWALS82A : Core.WALS.F82A.SubjectVerbOrder → SVOrder
  | .sv => .sv
  | .vs => .vs
  | .noDominantOrder => .noDominant

/-- Convert WALS F83A's `ObjectVerbOrder` to our local `OVOrder`. -/
def fromWALS83A : Core.WALS.F83A.ObjectVerbOrder → OVOrder
  | .ov => .ov
  | .vo => .vo
  | .noDominantOrder => .noDominant

/-- Look up Ch 81 basic order for an ISO 639-3 code; `.noDominant` if absent. -/
def basicOrderOfWALS (iso : String) : BasicOrder :=
  match Core.WALS.Datapoint.lookupISO Core.WALS.F81A.allData iso with
  | some d => fromWALS81A d.value
  | none => .noDominant

/-- Look up Ch 82 subject–verb order for an ISO 639-3 code; `.noDominant` if absent. -/
def svOrderOfWALS (iso : String) : SVOrder :=
  match Core.WALS.Datapoint.lookupISO Core.WALS.F82A.allData iso with
  | some d => fromWALS82A d.value
  | none => .noDominant

/-- Look up Ch 83 object–verb order for an ISO 639-3 code; `.noDominant` if absent. -/
def ovOrderOfWALS (iso : String) : OVOrder :=
  match Core.WALS.Datapoint.lookupISO Core.WALS.F83A.allData iso with
  | some d => fromWALS83A d.value
  | none => .noDominant

/-- Construct a `WordOrderProfile` for a language by ISO 639-3 lookup against
    WALS chapters 81/82/83. Each field independently falls back to `.noDominant`
    if its WALS chapter has no entry for the language. Use this as the default
    backend in Fragment files; override per-field when grammar-grounded sources
    disagree with WALS or fill its gaps. -/
def WordOrderProfile.ofWALS (iso : String) (notes : String := "") : WordOrderProfile :=
  { basicOrder := basicOrderOfWALS iso
    svOrder := svOrderOfWALS iso
    ovOrder := ovOrderOfWALS iso
    notes := notes }

end Core.Typology.WordOrder
