import Mathlib.Order.Partition.Finpartition
import Linglib.Semantics.Evidential.Defs
import Linglib.Semantics.Evidential.Source

/-!
# Evidential paradigms

This file connects the six semantic parameters to Willett's three coarse domains and builds
the paradigm a well-formed inventory forms: its terms partition the parameters the language
expresses, a `Finpartition`. An evidential has a coarse source exactly when its coverage lies
within one domain, and every evidential is nonfuture — contemporaneous when it covers
firsthand evidence only, retrospective otherwise.

## Main definitions

* `Evidential.CoarseSource.block`, `Parameter.coarse` — the domains as blocks.
* `Evidential.toCoarseSource` — the coarse source of a term, when defined.
* `Evidential.finpartition` — the paradigm of a well-formed inventory.

## Main statements

* `Evidential.isNonfuture` — every evidential is nonfuture.

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

instance : HasCoarseSource Evidential where
  toCoarseSource := toCoarseSource

/-- Evidence is contemporaneous with the event when the term covers firsthand evidence only,
and retrospective otherwise. -/
instance : HasEvidentialPerspective Evidential where
  toEvidentialPerspective e :=
    if e.covers ⊆ {.visual, .sensory} then some .contemporaneous else some .retrospective

/-- Every evidential is nonfuture: its evidence is acquired no earlier than the event. -/
theorem isNonfuture (e : Evidential) : IsNonfuture e := by
  unfold IsNonfuture
  by_cases h : e.covers ⊆ {.visual, .sensory}
  · exact .inr (by simp [HasEvidentialPerspective.toEvidentialPerspective, h])
  · exact .inl (by simp [HasEvidentialPerspective.toEvidentialPerspective, h])

/-- The paradigm of a well-formed inventory: its terms partition the parameters it expresses. -/
def finpartition (es : List Evidential) (h : WellFormed es) : Finpartition (expressed es) :=
  Finpartition.ofErase (es.map covers).toFinset
    (Finset.supIndep_iff_pairwiseDisjoint.2 fun x hx y hy hxy => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hx)
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hy)
      exact h a ha b hb (fun hab => hxy (hab ▸ rfl)))
    rfl

end Evidential
