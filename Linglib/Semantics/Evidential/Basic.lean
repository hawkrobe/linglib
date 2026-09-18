import Mathlib.Order.Partition.Finpartition
import Linglib.Semantics.Evidential.Defs

/-!
# Evidential paradigms

This file connects the six semantic parameters to Willett's three types of evidence and
builds the paradigm a well-formed inventory forms: its terms partition the parameters the
language expresses, a `Finpartition`. An evidential has an evidence type exactly when its
coverage lies within one type.

## Main definitions

* `Evidential.EvidenceType.block`, `Parameter.evidenceType` — the types as blocks of
  parameters.
* `Evidential.evidenceType?` — the evidence type of a term, when defined.
* `Evidential.finpartition` — the paradigm of a well-formed inventory.

## References

* [aikhenvald-2004], §2.5
* [willett-1988]
-/

namespace Evidential

/-- Willett's types of evidence as blocks of parameters. -/
def EvidenceType.block : EvidenceType → Finset Parameter
  | .attested => {.visual, .sensory}
  | .inferring => {.inference, .assumption}
  | .reported => {.hearsay, .quotative}

/-- The type of evidence a parameter falls under. -/
def Parameter.evidenceType : Parameter → EvidenceType
  | .visual | .sensory => .attested
  | .inference | .assumption => .inferring
  | .hearsay | .quotative => .reported

theorem Parameter.mem_block (p : Parameter) : p ∈ p.evidenceType.block := by
  cases p <;> decide

end Evidential

namespace Evidential

open Evidential

/-- The evidence type of an evidential, when its coverage lies within one of Willett's
types; a non-firsthand term has none. -/
def evidenceType? (e : Evidential) : Option EvidenceType :=
  if e.IsDirect then some .attested
  else if e.IsInferential then some .inferring
  else if e.IsReportative then some .reported
  else none

/-- The paradigm of a well-formed inventory: its terms partition the parameters it expresses. -/
def finpartition (es : List Evidential) (h : WellFormed es) : Finpartition (expressed es) :=
  Finpartition.ofErase (es.map covers).toFinset
    (Finset.supIndep_iff_pairwiseDisjoint.2 fun _ hx _ hy hxy =>
      (h.map covers fun _ _ => id).forall (List.mem_toFinset.1 hx) (List.mem_toFinset.1 hy) hxy)
    rfl

end Evidential
