module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Basic

/-!
# Exhaustification

An exhaustification operator asserts a prejacent and denies a selection of its alternatives.
This file defines the selection every theory of *only* and of exhaustification shares, the
alternatives the prejacent does not entail, and the finite excluders that vary it.

`excludes C p` is the exclusion component: every true alternative in `C` is entailed by `p`.
It is the assertion of *only* with the prejacent factored out ([horn-1969], [rooth-1992],
[von-fintel-1999]), and `exh C p`, the prejacent together with the exclusion, is
[chierchia-2006]'s operator `O`. Over an `Irredundant` family, where each alternative has a
world of its own, exclusion separates resolutions of the alternative set
(`Irredundant.excludes_injOn`), and narrowing the alternatives weakens it
(`excludes_antitone`). When the prejacent is maximal among the alternatives, exclusion is
[rooth-1992]'s condition that every true alternative *equals* the prejacent
(`mem_excludes_iff_forall_eq`).

An `Excluder` is a selection over finite world types, `Excluder.exh` the resulting operator,
and `tolerant` is `exh` there, contradiction or not ([chierchia-2013]); `Excluder.restrict`
keeps only the relevant alternatives among those an excluder denies ([magri-2009]) and can
only weaken the result, while `Excluder.preFilter` removes alternatives before the excluder
sees them and can strengthen it, the asymmetry [fox-katzir-2011] state between contextual
restriction and the formal alternative source. The innocent excluder is `innocent` in
`Finite`.

## References

* [horn-1969]
* [rooth-1992]
* [von-fintel-1999]
* [chierchia-2006]
* [chierchia-2013]
* [fox-2007]
* [fox-katzir-2011]
* [magri-2009]
-/

@[expose] public section

namespace Exhaustification

variable {W : Type*}

/-! ### Exclusion and exhaustification -/

section Exh

variable {C C' : Set (Set W)} {p q : Set W} {w : W}

/-- The worlds at which every true alternative in `C` is entailed by `p`: the assertion of
*only* with its prejacent `p` presupposed separately. -/
def excludes (C : Set (Set W)) (p : Set W) : Set W := {w | ∀ q ∈ C, w ∈ q → p ⊆ q}

@[simp] theorem mem_excludes : w ∈ excludes C p ↔ ∀ q ∈ C, w ∈ q → p ⊆ q := Iff.rfl

/-- The prejacent `p` with every alternative it does not entail denied
([chierchia-2006]'s `O`). -/
def exh (C : Set (Set W)) (p : Set W) : Set W := p ∩ excludes C p

@[simp] theorem mem_exh : w ∈ exh C p ↔ w ∈ p ∧ ∀ q ∈ C, w ∈ q → p ⊆ q := Iff.rfl

theorem exh_subset (C : Set (Set W)) (p : Set W) : exh C p ⊆ p := λ _ h => h.1

theorem exh_subset_excludes (C : Set (Set W)) (p : Set W) : exh C p ⊆ excludes C p :=
  λ _ h => h.2

/-- A true alternative the prejacent does not entail is excluded. -/
theorem notMem_excludes (hq : q ∈ C) (hw : w ∈ q) (h : ¬ p ⊆ q) : w ∉ excludes C p :=
  λ he => h (he q hq hw)

theorem notMem_exh (hq : q ∈ C) (hw : w ∈ q) (h : ¬ p ⊆ q) : w ∉ exh C p :=
  λ he => notMem_excludes hq hw h he.2

/-- Exclusion from refuting every alternative the prejacent does not entail. -/
theorem mem_excludes_of_forall_notMem (h : ∀ q ∈ C, ¬ p ⊆ q → w ∉ q) : w ∈ excludes C p :=
  λ q hq hwq => not_not.mp λ hne => h q hq hne hwq

/-- Exclusion denies the union of the alternatives the prejacent does not entail. -/
theorem excludes_eq_compl_sUnion (C : Set (Set W)) (p : Set W) :
    excludes C p = (⋃₀ {q ∈ C | ¬ p ⊆ q})ᶜ := by
  ext w
  simp only [mem_excludes, Set.mem_compl_iff, Set.mem_sUnion, Set.mem_ofPred_eq, not_exists,
    not_and, and_imp]
  exact ⟨λ h q hq hpq hw => hpq (h q hq hw), λ h q hq hw => not_not.mp λ hpq => h q hq hpq hw⟩

theorem exh_eq_sdiff (C : Set (Set W)) (p : Set W) : exh C p = p \ ⋃₀ {q ∈ C | ¬ p ⊆ q} := by
  rw [exh, excludes_eq_compl_sUnion, Set.sdiff_eq]

/-- Exhaustification is vacuous exactly when every alternative compatible with the prejacent is
entailed by it. -/
theorem exh_eq_self_iff : exh C p = p ↔ ∀ q ∈ C, (p ∩ q).Nonempty → p ⊆ q :=
  ⟨λ h q hq ⟨w, hw, hwq⟩ => by rw [← h] at hw; exact hw.2 q hq hwq,
    λ h => (exh_subset C p).antisymm λ w hw => ⟨hw, λ q hq hwq => h q hq ⟨w, hw, hwq⟩⟩⟩

/-- Exhaustification cannot exhaustify away entailments. -/
theorem exh_eq_self (h : ∀ q ∈ C, p ⊆ q) : exh C p = p :=
  exh_eq_self_iff.2 λ q hq _ => h q hq

/-- Narrowing the alternatives weakens the exclusion. -/
theorem excludes_antitone (h : C ⊆ C') (p : Set W) : excludes C' p ⊆ excludes C p :=
  λ _ hw q hq => hw q (h hq)

theorem exh_antitone (h : C ⊆ C') (p : Set W) : exh C' p ⊆ exh C p :=
  Set.inter_subset_inter_right _ (excludes_antitone h p)

/-- When the prejacent is maximal among the alternatives, exclusion asks that every true
alternative be the prejacent itself, [rooth-1992]'s semantics of *only*. -/
theorem mem_excludes_iff_forall_eq (h : ∀ q ∈ C, p ⊆ q → q = p) :
    w ∈ excludes C p ↔ ∀ q ∈ C, w ∈ q → q = p :=
  forall₂_congr λ q hq => imp_congr_right λ _ => ⟨h q hq, λ hqp => hqp ▸ subset_rfl⟩

end Exh

/-! ### Irredundant alternatives -/

section Irredundant

variable {ι : Type*} {f : ι → Set W}

/-- An **irredundant** family of alternatives: each member can hold while every other member
fails, so no member is covered by the union of the rest. Strictly weaker than the mutual
exclusivity of partition semantics (`irredundant_of_pairwise_disjoint`). -/
def Irredundant (f : ι → Set W) : Prop :=
  ∀ i, ∃ w ∈ f i, ∀ j, j ≠ i → w ∉ f j

/-- Pairwise-disjoint nonempty alternatives are irredundant. -/
theorem irredundant_of_pairwise_disjoint (hd : Pairwise λ i j => Disjoint (f i) (f j))
    (hne : ∀ i, (f i).Nonempty) : Irredundant f := λ i =>
  let ⟨w, hw⟩ := hne i
  ⟨w, hw, λ _ hj hwj => Set.disjoint_left.mp (hd hj) hwj hw⟩

/-- No member of an irredundant family entails another. -/
theorem Irredundant.not_subset (hf : Irredundant f) {i j : ι} (hij : i ≠ j) : ¬ f i ⊆ f j :=
  let ⟨_, hw, hother⟩ := hf i
  λ h => hother j hij.symm (h hw)

/-- Over an irredundant family, resolving the exclusion to alternative sets that differ beyond
the prejacent yields distinct propositions: the alternative present in one resolution and
absent from the other separates them. -/
theorem Irredundant.excludes_ne (hf : Irredundant f) {i₀ j : ι} {s₁ s₂ : Finset ι}
    (hj₂ : j ∈ s₂) (hj₁ : j ∉ s₁) (hji : j ≠ i₀) :
    excludes (f '' ↑s₁) (f i₀) ≠ excludes (f '' ↑s₂) (f i₀) := by
  obtain ⟨w, hwj, hother⟩ := hf j
  refine ne_of_mem_of_not_mem' (mem_excludes_of_forall_notMem ?_)
    (notMem_excludes ⟨j, hj₂, rfl⟩ hwj (hf.not_subset hji.symm))
  rintro q ⟨k, hk, rfl⟩ _
  exact hother k λ h => hj₁ (h ▸ hk)

/-- Over an irredundant family, exclusion is injective in the resolved alternative set, on
resolutions containing the prejacent. -/
theorem Irredundant.excludes_injOn (hf : Irredundant f) (i₀ : ι) :
    Set.InjOn (λ s : Finset ι => excludes (f '' ↑s) (f i₀)) {s | i₀ ∈ s} := by
  intro s₁ h₁ s₂ h₂ heq
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, ¬ (j ∈ s₁ ↔ j ∈ s₂) := by simpa [Finset.ext_iff] using hne
  by_cases hmem : j ∈ s₁
  · have h₂j : j ∉ s₂ := λ h => hj ⟨λ _ => h, λ _ => hmem⟩
    exact hf.excludes_ne hmem h₂j (λ h => h₂j (h ▸ h₂)) heq.symm
  · have h₂j : j ∈ s₂ := by
      by_contra h2
      exact hj ⟨λ h => absurd h hmem, λ h => absurd h h2⟩
    exact hf.excludes_ne h₂j hmem (λ h => hmem (h ▸ h₁)) heq

end Irredundant

variable [Fintype W] [DecidableEq W]

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
