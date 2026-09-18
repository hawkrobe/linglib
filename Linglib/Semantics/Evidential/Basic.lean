import Mathlib.Order.Partition.Finpartition
import Linglib.Semantics.Evidential.Defs

/-!
# Evidential paradigms

This file connects the six semantic parameters to Willett's three coarse domains and builds
the paradigm a well-formed inventory forms: its terms partition the parameters the language
expresses, a `Finpartition`. An evidential has a coarse source exactly when its coverage lies
within one domain.

## Main definitions

* `Evidential.CoarseSource.block`, `Parameter.coarse` — the domains as blocks.
* `Evidential.toCoarseSource` — the coarse source of a term, when defined.
* `Evidential.finpartition` — the paradigm of a well-formed inventory.

## References

* [aikhenvald-2004], §2.5
* [willett-1988]
-/

namespace Evidential

/-- Willett's coarse domains as blocks of parameters. -/
def CoarseSource.block : CoarseSource → Finset Parameter
  | .direct => {.visual, .sensory}
  | .inference => {.inference, .assumption}
  | .hearsay => {.hearsay, .quotative}

/-- The coarse domain of a parameter. -/
def Parameter.coarse : Parameter → CoarseSource
  | .visual | .sensory => .direct
  | .inference | .assumption => .inference
  | .hearsay | .quotative => .hearsay

theorem Parameter.mem_block (p : Parameter) : p ∈ p.coarse.block := by cases p <;> decide

end Evidential

namespace Evidential

open Evidential

/-- The coarse source of an evidential, when its coverage lies within one of Willett's
domains; a non-firsthand term has none. -/
def toCoarseSource (e : Evidential) : Option CoarseSource :=
  if e.IsDirect then some .direct
  else if e.IsInferential then some .inference
  else if e.IsReportative then some .hearsay
  else none

/-- The paradigm of a well-formed inventory: its terms partition the parameters it expresses. -/
def finpartition (es : List Evidential) (h : WellFormed es) : Finpartition (expressed es) :=
  Finpartition.ofErase (es.map covers).toFinset
    (Finset.supIndep_iff_pairwiseDisjoint.2 fun _ hx _ hy hxy =>
      (h.map covers fun _ _ => id).forall (List.mem_toFinset.1 hx) (List.mem_toFinset.1 hy) hxy)
    rfl

end Evidential
