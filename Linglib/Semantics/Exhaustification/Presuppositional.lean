module

public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Semantics.Exhaustification.InnocentExclusion
public import Linglib.Semantics.Exhaustification.InnocentInclusion

/-!
# Presuppositional exhaustification

The presuppositional exhaustivity operator `pex^{IE+II}` of Del Pinal, Bassi and Sauerland,
extending the `pex^{IE}` of Bassi, Del Pinal and Sauerland, asserts its prejacent alone. It
presupposes that the relevant innocently excludable alternatives are false and that the relevant
innocently includable ones are homogeneous, true together or false together, so negation denies
the assertion and leaves the presupposition. The includable alternatives are those of Bar-Lev and
Fox with the prejacent removed. When the prejacent lies between the meet and the join of the
relevant ones, as `◇(p ∨ q)` lies between `◇p ∧ ◇q` and `◇p ∨ ◇q`, homogeneity makes it true
where all of them are and false where none is.

## Main declarations

* `Homogeneous`: the members of a set of propositions are all true or all false.
* `includable`: the innocently includable alternatives, the prejacent removed.
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

namespace Exhaustification.Presuppositional

open Exhaustification Presupposition

variable {World : Type*}

/-- The propositions of `S` are homogeneous at `w` when they are all true there or all false
there. -/
def Homogeneous (S : Set (Set World)) (w : World) : Prop :=
  (∀ α ∈ S, w ∈ α) ∨ ∀ α ∈ S, w ∉ α

section Homogeneous

variable {S : Set (Set World)} {φ : Set World} {w : World}

@[simp] theorem homogeneous_empty : Homogeneous (∅ : Set (Set World)) w :=
  .inl fun _ h ↦ h.elim

@[simp] theorem homogeneous_pair {p q : Set World} :
    Homogeneous {p, q} w ↔ (w ∈ p ↔ w ∈ q) := by
  grind [Homogeneous]

/-- Under homogeneity, a proposition between the meet and the join of `S` is true where every
member of `S` is. -/
theorem Homogeneous.mem_iff (h : Homogeneous S w) (hl : ⋂₀ S ⊆ φ) (hu : φ ⊆ ⋃₀ S) :
    w ∈ φ ↔ ∀ α ∈ S, w ∈ α := by
  grind [Homogeneous]

/-- Under homogeneity, a proposition between the meet and the join of `S` is false where every
member of `S` is. -/
theorem Homogeneous.notMem_iff (h : Homogeneous S w) (hl : ⋂₀ S ⊆ φ) (hu : φ ⊆ ⋃₀ S) :
    w ∉ φ ↔ ∀ α ∈ S, w ∉ α := by
  grind [Homogeneous]

end Homogeneous

/-- `includable ALT φ` is the set of innocently includable alternatives other than the
prejacent. -/
def includable (ALT : Set (Set World)) (φ : Set World) : Set (Set World) :=
  II ALT φ \ {φ}

/-- `pex^{IE+II}` asserts the prejacent and presupposes that the innocently excludable
alternatives in the relevance set `Rc` are false and the innocently includable ones in it
homogeneous. -/
def pexIEII (ALT : Set (Set World)) (φ : Set World) (Rc : Set (Set World)) :
    PartialProp World where
  assertion := (· ∈ φ)
  presup w := (∀ ψ, IsInnocentlyExcludable ALT φ ψ → ψ ∈ Rc → w ∉ ψ) ∧
    Homogeneous (includable ALT φ ∩ Rc) w

variable {ALT : Set (Set World)} {φ : Set World} {Rc : Set (Set World)} {w : World}

/-- A prejacent between the meet and the join of its relevant includable alternatives holds
under `pex` exactly where the presupposition does and all of them are true. -/
theorem pexIEII_holds_iff (hl : ⋂₀ (includable ALT φ ∩ Rc) ⊆ φ)
    (hu : φ ⊆ ⋃₀ (includable ALT φ ∩ Rc)) :
    (pexIEII ALT φ Rc).holds w ↔
      (pexIEII ALT φ Rc).presup w ∧ ∀ α ∈ includable ALT φ ∩ Rc, w ∈ α :=
  and_congr_right fun h ↦ h.2.mem_iff hl hu

/-- A prejacent between the meet and the join of its relevant includable alternatives fails
under `pex` exactly where the presupposition holds and all of them are false. -/
theorem pexIEII_neg_holds_iff (hl : ⋂₀ (includable ALT φ ∩ Rc) ⊆ φ)
    (hu : φ ⊆ ⋃₀ (includable ALT φ ∩ Rc)) :
    (pexIEII ALT φ Rc).neg.holds w ↔
      (pexIEII ALT φ Rc).presup w ∧ ∀ α ∈ includable ALT φ ∩ Rc, w ∉ α :=
  and_congr_right fun h ↦ h.2.notMem_iff hl hu

/-- With no relevant includable alternative, as for a basic scalar sentence, the presupposition
is that the relevant excludable alternatives are false. -/
theorem pexIEII_presup_of_includable_inter_eq_empty (h : includable ALT φ ∩ Rc = ∅) :
    (pexIEII ALT φ Rc).presup w ↔ ∀ ψ, IsInnocentlyExcludable ALT φ ψ → ψ ∈ Rc → w ∉ ψ := by
  simp [pexIEII, h]

end Exhaustification.Presuppositional
