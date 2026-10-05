module

public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Semantics.Homogeneity.Defs
public import Linglib.Semantics.Exhaustification.InnocentExclusion
public import Linglib.Semantics.Exhaustification.InnocentInclusion

/-!
# Presuppositional exhaustification

The presuppositional exhaustivity operator `pex^{IE+II}` of Del Pinal, Bassi and Sauerland,
extending the `pex^{IE}` of Bassi, Del Pinal and Sauerland, asserts its prejacent alone. It
presupposes that the relevant innocently excludable alternatives are false and that the relevant
innocently includable ones other than the prejacent are homogeneous, true together or false
together, so negation denies the assertion and leaves the presupposition. When the prejacent lies
between the meet and the join of those alternatives, as `◇(p ∨ q)` lies between `◇p ∧ ◇q` and
`◇p ∨ ◇q`, homogeneity makes it true where all of them are and false where none is.

## Main declarations

* `pexIEII`: the operator.
* `pexIEII_holds_iff`, `pexIEII_neg_holds_iff`: a prejacent between the meet and the join of its
  relevant includable alternatives holds together with all of them and fails together with all
  of them.

## References

* [delpinal-bassi-sauerland-2024]
* [bassi-delpinal-sauerland-2021]
* [bar-lev-fox-2020]
-/

@[expose] public section

namespace Exhaustification

open Presupposition Homogeneity

variable {World : Type*}

/-- `pex^{IE+II}` asserts the prejacent and presupposes that the innocently excludable
alternatives in the relevance set `Rc` are false and that the innocently includable ones in it,
other than the prejacent, are homogeneous. -/
def pexIEII (ALT : Set (Set World)) (φ : Set World) (Rc : Set (Set World)) :
    PartialProp World where
  assertion := (· ∈ φ)
  presup w := (∀ ψ, IsInnocentlyExcludable ALT φ ψ → ψ ∈ Rc → w ∉ ψ) ∧
    Homogeneous (II ALT φ \ {φ} ∩ Rc) w

variable {ALT : Set (Set World)} {φ : Set World} {Rc : Set (Set World)} {w : World}

/-- A prejacent between the meet and the join of its relevant includable alternatives holds
under `pex` exactly where the presupposition does and all of them are true. -/
theorem pexIEII_holds_iff (hl : ⋂₀ (II ALT φ \ {φ} ∩ Rc) ⊆ φ)
    (hu : φ ⊆ ⋃₀ (II ALT φ \ {φ} ∩ Rc)) :
    (pexIEII ALT φ Rc).holds w ↔
      (pexIEII ALT φ Rc).presup w ∧ ∀ α ∈ II ALT φ \ {φ} ∩ Rc, w ∈ α :=
  and_congr_right fun h ↦ h.2.mem_iff hl hu

/-- A prejacent between the meet and the join of its relevant includable alternatives fails
under `pex` exactly where the presupposition holds and all of them are false. -/
theorem pexIEII_neg_holds_iff (hl : ⋂₀ (II ALT φ \ {φ} ∩ Rc) ⊆ φ)
    (hu : φ ⊆ ⋃₀ (II ALT φ \ {φ} ∩ Rc)) :
    (pexIEII ALT φ Rc).neg.holds w ↔
      (pexIEII ALT φ Rc).presup w ∧ ∀ α ∈ II ALT φ \ {φ} ∩ Rc, w ∉ α :=
  and_congr_right fun h ↦ h.2.notMem_iff hl hu

/-- With no relevant includable alternative besides the prejacent, as for a basic scalar
sentence, the presupposition is that the relevant excludable alternatives are false. -/
theorem pexIEII_presup_of_inter_eq_empty (h : II ALT φ \ {φ} ∩ Rc = ∅) :
    (pexIEII ALT φ Rc).presup w ↔ ∀ ψ, IsInnocentlyExcludable ALT φ ψ → ψ ∈ Rc → w ∉ ψ := by
  simp [pexIEII, h]

end Exhaustification
