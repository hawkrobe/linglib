import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic

/-!
# Excluders

Exhaustification theories agree that the operator asserts the prejacent and denies a
selection of the alternatives, and disagree on the selection. An `Excluder` is such a
selection over finite world types, `Excluder.exh` the resulting operator. `tolerant` denies
every alternative not entailed by the prejacent, contradiction or not ([chierchia-2013]);
`Excluder.restrict` keeps only the relevant alternatives among those an excluder denies
([magri-2009]) and can only weaken the result, while `Excluder.preFilter` removes
alternatives before the excluder sees them and can strengthen it — the asymmetry
[fox-katzir-2011] state between contextual restriction and the formal alternative source.
The innocent excluder is `innocent` in `Finite`.

## References

* [chierchia-2013]
* [fox-2007]
* [fox-katzir-2011]
* [magri-2009]
-/

namespace Exhaustification

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The worlds satisfying a `Bool` predicate. -/
def predToFinset (p : W → Bool) : Finset W :=
  Finset.univ.filter (fun w => p w)

/-- The alternative set of a list of `Bool` predicates. -/
def altsFromPreds (alts : List (W → Bool)) : Finset (Finset W) :=
  (alts.map predToFinset).toFinset

/-- `altsFromPreds [p]` is the singleton `{predToFinset p}`. -/
@[simp] theorem altsFromPreds_singleton (p : W → Bool) :
    altsFromPreds [p] = ({predToFinset p} : Finset (Finset W)) := by
  simp [altsFromPreds]

/-- A choice, for each alternative set and prejacent, of the alternatives to deny. -/
structure Excluder (W : Type*) [Fintype W] [DecidableEq W] where
  /-- Given a prejacent `φ` and an alternative set `ALT`, return the
      alternatives whose negation should be conjoined with `φ`. -/
  excluded : Finset (Finset W) → Finset W → Finset (Finset W)
  /-- The strategy returns a sub-collection of the offered alternatives. -/
  excluded_subset : ∀ ALT φ, excluded ALT φ ⊆ ALT

namespace Excluder

variable (E : Excluder W) (ALT : Finset (Finset W)) (φ : Finset W)

/-- The prejacent with every excluded alternative denied. -/
def exh : Finset W :=
  φ \ (E.excluded ALT φ).biUnion id

/-- The exhaustified meaning is contained in the prejacent. -/
theorem exh_subset_phi : E.exh ALT φ ⊆ φ := Finset.sdiff_subset

/-- Membership characterization for `exh`. -/
theorem mem_exh_iff {w : W} :
    w ∈ E.exh ALT φ ↔ w ∈ φ ∧ ∀ a ∈ E.excluded ALT φ, w ∉ a := by
  simp only [exh, Finset.mem_sdiff, Finset.mem_biUnion, id_eq, not_exists, not_and]

end Excluder



namespace Excluder

/-! ### Restricting the excluded alternatives -/

/-- Deny only the excluded alternatives satisfying `R`. -/
def restrict (E : Excluder W) (R : Finset W → Bool) : Excluder W where
  excluded ALT φ := (E.excluded ALT φ).filter (fun a => R a)
  excluded_subset ALT φ :=
    (Finset.filter_subset _ _).trans (E.excluded_subset ALT φ)

@[simp] theorem restrict_excluded (E : Excluder W) (R : Finset W → Bool)
    (ALT : Finset (Finset W)) (φ : Finset W) :
    (E.restrict R).excluded ALT φ
      = (E.excluded ALT φ).filter (fun a => R a) := rfl

/-- A constantly-true relevance predicate leaves the excluder unchanged. -/
theorem restrict_const_true (E : Excluder W) :
    E.restrict (fun _ => true) = E := by
  cases E with
  | mk excluded excluded_subset =>
    simp [restrict]

/-- Restriction weakens the exhaustification. -/
theorem exh_subset_restrict_exh (E : Excluder W) (R : Finset W → Bool)
    (ALT : Finset (Finset W)) (φ : Finset W) :
    E.exh ALT φ ⊆ (E.restrict R).exh ALT φ := by
  intro w hw
  rw [mem_exh_iff] at hw ⊢
  refine ⟨hw.1, ?_⟩
  intro a ha
  rw [restrict_excluded, Finset.mem_filter] at ha
  exact hw.2 a ha.1

/-- Restriction licenses no implicature the excluder does not ([fox-katzir-2011]'s
contextual restriction cannot break symmetry). -/
theorem restrict_preserves_no_implicature (E : Excluder W)
    (R : Finset W → Bool) (ALT : Finset (Finset W)) (φ ψ : Finset W)
    (h : ¬ E.exh ALT φ ⊆ ψ) :
    ¬ (E.restrict R).exh ALT φ ⊆ ψ :=
  fun hres => h ((exh_subset_restrict_exh E R ALT φ).trans hres)

/-! ### Filtering the offered alternatives -/

/-- Offer the excluder only the alternatives satisfying `P`. -/
def preFilter (E : Excluder W) (P : Finset W → Bool) : Excluder W where
  excluded ALT φ := E.excluded (ALT.filter (fun a => P a)) φ
  excluded_subset _ _ :=
    (E.excluded_subset _ _).trans (Finset.filter_subset _ _)

@[simp] theorem preFilter_excluded (E : Excluder W) (P : Finset W → Bool)
    (ALT : Finset (Finset W)) (φ : Finset W) :
    (E.preFilter P).excluded ALT φ
      = E.excluded (ALT.filter (fun a => P a)) φ := rfl

/-- A constantly-true pre-filter leaves the excluder unchanged. -/
theorem preFilter_const_true (E : Excluder W) :
    E.preFilter (fun _ => true) = E := by
  cases E with
  | mk excluded excluded_subset =>
    simp [preFilter]

end Excluder

/-! ### The tolerant excluder -/

/-- The tolerant excluder denies every alternative not entailed by the prejacent. -/
def tolerant : Excluder W where
  excluded ALT φ := ALT.filter (fun a => ¬ φ ⊆ a)
  excluded_subset _ _ := Finset.filter_subset _ _

@[simp] theorem tolerant_excluded (ALT : Finset (Finset W)) (φ : Finset W) :
    tolerant.excluded ALT φ = ALT.filter (fun a => ¬ φ ⊆ a) := rfl

theorem mem_tolerant_excluded {ALT : Finset (Finset W)} {φ a : Finset W} :
    a ∈ tolerant.excluded ALT φ ↔ a ∈ ALT ∧ ¬ φ ⊆ a := by
  simp [tolerant_excluded, Finset.mem_filter]

/-- Membership in the tolerant exhaustification. -/
theorem mem_tolerant_exh_iff (ALT : Finset (Finset W)) (φ : Finset W) {w : W} :
    w ∈ tolerant.exh ALT φ ↔ w ∈ φ ∧ ∀ a ∈ ALT, ¬ φ ⊆ a → w ∉ a := by
  rw [Excluder.mem_exh_iff]
  refine and_congr_right (fun _ => ?_)
  simp [tolerant_excluded, Finset.mem_filter, and_imp]

/-- Alternatives entailed by the prejacent are kept, never negated. -/
theorem entailed_not_excluded {ALT : Finset (Finset W)} {φ a : Finset W}
    (h : φ ⊆ a) : a ∉ tolerant.excluded ALT φ := by
  simp [h]

end Exhaustification
