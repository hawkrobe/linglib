import Linglib.Theories.Semantics.Exhaustification.Operators.Basic
import Linglib.Theories.Semantics.Exhaustification.Innocent

/-!
# Set/Finset bridge for innocent exclusion

`Operators/Basic.lean` formalises Spector 2016 over `Set World` /
`Set (Set World)`; `Innocent.lean` reformulates the same algorithm over
`Finset W` / `Finset (Finset W)` so it lives inside the `Excluder` API
and produces decidable, computable exhaustifications.

The two presentations agree whenever the world space is finite. This
file establishes the correspondence and the equation
`IE (coeSet ALT) ↑φ = coeSet (Innocent.IE ALT φ) ∪ {↑φ}`.

## Coercion

`Finset W` embeds into `Set W` via the standard `↑·` coercion, and
`Finset (Finset W)` therefore embeds into `Set (Set W)` by lifting that
coercion through `Finset.image`. We package this as `coeSet`. The
inverse `dropToFinset` filters the bound `excludables ALT φ` by Set
membership — using the bound rather than `Finset.univ` avoids needing
`Fintype (Finset W)` and keeps the construction `[DecidableEq W]`-only.

## MC-set bridge

* `liftToSet_isMCSet` — Finset MC-set lifts to Set MC-set
* `dropToFinset_isMCSet` — Set MC-set drops to Finset MC-set

## IE bridge

* `phi_mem_IE_set` — the prejacent is in the Set IE
* `coeSet_innocentlyExcludable_iff` — Finset/Set innocent-exclusion agree
* `IE_set_eq_coeSet_IE_finset` — full Set IE / Finset IE correspondence

## Status of the two APIs

The Set-side API in `Operators/Basic.lean` is the canonical *reference*
formalization, faithful to Spector 2016's prose, and is what 30+
downstream consumers import. The Finset/`Excluder` API in `Innocent.lean`
is the computational refinement — decidable, no `Fintype (Set W)`
needed, integrates with the `Excluder` strategy interface used by
sibling excluders. They are not competing theories; they are abstract
spec and computable refinement of the same algorithm. This file proves
the bridge so that either side can be cited without rederiving the
other. New code that needs decidability or Excluder uniformity should
prefer the Finset side; new code engaging directly with Spector's prose
or proving paper-level theorems should use the Set side.
-/

namespace Exhaustification

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Lift a `Finset (Finset W)` into a `Set (Set W)` by coercing each
    inner Finset to a Set. -/
def coeSet (X : Finset (Finset W)) : Set (Set W) :=
  (fun a : Finset W => (↑a : Set W)) '' (↑X : Set (Finset W))

/-- Drop a Set-side compatible set on `(coeSet ALT, ↑φ)` back to a
    `Finset (Finset W)` by filtering `excludables ALT φ` by Set
    membership. Compatible Set-side sets have all members in
    `coeSet (excludables ALT φ)`, so this filter recovers the
    Finset image precisely. -/
def dropToFinset (ALT : Finset (Finset W)) (φ : Finset W) (E : Set (Set W))
    [DecidablePred fun s : Finset W => (↑s : Set W) ∈ E] :
    Finset (Finset W) :=
  (Innocent.excludables ALT φ).filter (fun s => (↑s : Set W) ∈ E)

private lemma coe_univ_sdiff (a : Finset W) :
    ((Finset.univ \ a : Finset W) : Set W) = (↑a : Set W)ᶜ := by
  rw [Finset.coe_sdiff, Finset.coe_univ, ← Set.compl_eq_univ_diff]

private lemma mem_inf_id {s : Finset (Finset W)} {w : W} :
    w ∈ s.inf id ↔ ∀ a ∈ s, w ∈ a := by
  refine ⟨fun h a ha => ?_, fun h => ?_⟩
  · exact (Finset.le_iff_subset.mp (Finset.inf_le ha)) h
  · exact Finset.singleton_subset_iff.mp
      (Finset.le_iff_subset.mp (Finset.le_inf
        (fun a ha => Finset.le_iff_subset.mpr (Finset.singleton_subset_iff.mpr (h a ha)))))

omit [Fintype W] [DecidableEq W] in
private lemma mem_coeSet {X : Finset (Finset W)} {ψ : Set W} :
    ψ ∈ coeSet X ↔ ∃ s ∈ X, (↑s : Set W) = ψ := by
  simp [coeSet]

private lemma mem_dropToFinset {ALT : Finset (Finset W)} {φ : Finset W}
    {E : Set (Set W)}
    [DecidablePred fun s : Finset W => (↑s : Set W) ∈ E] {s : Finset W} :
    s ∈ dropToFinset ALT φ E ↔ s ∈ Innocent.excludables ALT φ ∧ (↑s : Set W) ∈ E := by
  simp [dropToFinset]

/-- The Set-side prejacent always lies in the Set IE — this matches
    `Innocent.phi_mem_IE` on the Finset side. -/
theorem phi_mem_IE_set {V : Type*} (ALT : Set (Set V)) (φ : Set V) :
    φ ∈ IE ALT φ := by
  intro E hE_mc
  exact hE_mc.1.1

/-- A `Finset (Finset W)` lifted to `Set (Set W)` via member-wise coercion. -/
private def liftToSet (F : Finset (Finset W)) : Set (Set W) :=
  (fun s : Finset W => (↑s : Set W)) '' (↑F : Set (Finset W))

omit [Fintype W] [DecidableEq W] in
private lemma mem_liftToSet {F : Finset (Finset W)} {ψ : Set W} :
    ψ ∈ liftToSet F ↔ ∃ s ∈ F, (↑s : Set W) = ψ := by
  simp [liftToSet]

/-- A Set-side compatible set on `(coeSet ALT, ↑φ)` has every member of
    the form `↑φ` or `↑(Finset.univ \ a)` for `a ∈ ALT`. We use this to
    decide membership when dropping a Set MC-set to a Finset. -/
private lemma compat_set_form
    {ALT : Finset (Finset W)} {φ : Finset W} {E : Set (Set W)}
    (hE : IsCompatible (coeSet ALT) (↑φ) E) {ψ : Set W} (hψ : ψ ∈ E) :
    ψ = ↑φ ∨ ∃ a ∈ ALT, ψ = ↑(Finset.univ \ a) := by
  rcases hE.2.1 ψ hψ with h | ⟨b, hb_coe, hψ_eq⟩
  · exact Or.inl h
  · obtain ⟨a, ha_ALT, hb_eq⟩ := mem_coeSet.mp hb_coe
    refine Or.inr ⟨a, ha_ALT, ?_⟩
    rw [hψ_eq, ← hb_eq, coe_univ_sdiff]

/-- A member of a compatible Set on `(coeSet ALT, ↑φ)` is the coercion
    of a Finset that lies in `excludables ALT φ`. -/
private lemma compat_member_in_excludables_image
    {ALT : Finset (Finset W)} {φ : Finset W} {E : Set (Set W)}
    (hE : IsCompatible (coeSet ALT) (↑φ) E) {ψ : Set W} (hψ : ψ ∈ E) :
    ∃ s ∈ Innocent.excludables ALT φ, (↑s : Set W) = ψ := by
  rcases compat_set_form hE hψ with hφ | ⟨a, ha_ALT, ha_eq⟩
  · exact ⟨φ, Finset.mem_insert_self _ _, hφ.symm⟩
  · refine ⟨Finset.univ \ a, ?_, ha_eq.symm⟩
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a, ha_ALT, rfl⟩)

/-- A Finset-side compatible set lifts to a Set-side compatible set. -/
private lemma liftToSet_isCompatible
    {ALT : Finset (Finset W)} {φ : Finset W} {F : Finset (Finset W)}
    (hF : Innocent.IsCompatible ALT φ F) :
    IsCompatible (coeSet ALT) (↑φ) (liftToSet F) := by
  obtain ⟨hF_sub, hφF, hF_inf⟩ := hF
  refine ⟨?_, ?_, ?_⟩
  · exact mem_liftToSet.mpr ⟨φ, hφF, rfl⟩
  · intro ψ hψ
    obtain ⟨s, hs_F, hs_eq⟩ := mem_liftToSet.mp hψ
    rcases Finset.mem_insert.mp (hF_sub hs_F) with hs_φ | hs_im
    · left; rw [← hs_eq, hs_φ]
    · right
      obtain ⟨a, ha_ALT, ha_eq⟩ := Finset.mem_image.mp hs_im
      refine ⟨↑a, mem_coeSet.mpr ⟨a, ha_ALT, rfl⟩, ?_⟩
      rw [← hs_eq, ← ha_eq, coe_univ_sdiff]
  · obtain ⟨w, hw⟩ := hF_inf
    rw [mem_inf_id] at hw
    refine ⟨w, ?_⟩
    intro ψ hψ
    obtain ⟨s, hs_F, hs_eq⟩ := mem_liftToSet.mp hψ
    have : w ∈ (↑s : Set W) := hw _ hs_F
    exact hs_eq ▸ this

/-- A Set-side compatible set on `(coeSet ALT, ↑φ)` drops to a
    Finset-side compatible set. -/
private lemma dropToFinset_isCompatible
    {ALT : Finset (Finset W)} {φ : Finset W} {E : Set (Set W)}
    [DecidablePred fun s : Finset W => (↑s : Set W) ∈ E]
    (hE : IsCompatible (coeSet ALT) (↑φ) E) :
    Innocent.IsCompatible ALT φ (dropToFinset ALT φ E) := by
  obtain ⟨hφE, hE_form, hE_consist⟩ := hE
  refine ⟨?_, ?_, ?_⟩
  · -- dropToFinset ⊆ excludables (immediate from filter)
    intro s hs
    exact (mem_dropToFinset.mp hs).1
  · -- φ ∈ dropToFinset
    refine mem_dropToFinset.mpr ⟨Finset.mem_insert_self _ _, hφE⟩
  · -- nonempty intersection
    obtain ⟨w, hw⟩ := hE_consist
    refine ⟨w, ?_⟩
    rw [mem_inf_id]
    intro s hs_F
    exact hw _ (mem_dropToFinset.mp hs_F).2

/-- A Finset-side MC-set lifts to a Set-side MC-set. -/
private lemma liftToSet_isMCSet
    {ALT : Finset (Finset W)} {φ : Finset W} {F : Finset (Finset W)}
    (hF : Innocent.IsMCSet ALT φ F) :
    IsMCSet (coeSet ALT) (↑φ) (liftToSet F) := by
  refine ⟨liftToSet_isCompatible hF.1, ?_⟩
  intro E' hE'_compat hLift_sub_E'
  classical
  -- Drop E' to a Finset, show it extends F, apply Finset maximality.
  let F' : Finset (Finset W) := dropToFinset ALT φ E'
  have hF'_compat : Innocent.IsCompatible ALT φ F' := dropToFinset_isCompatible hE'_compat
  have hF'_pow : F' ∈ (Innocent.excludables ALT φ).powerset :=
    Finset.mem_powerset.mpr hF'_compat.1
  have hF_sub_F' : F ⊆ F' := by
    intro s hs_F
    have hs_excl : s ∈ Innocent.excludables ALT φ := hF.1.1 hs_F
    have hs_lift : (↑s : Set W) ∈ liftToSet F := mem_liftToSet.mpr ⟨s, hs_F, rfl⟩
    exact mem_dropToFinset.mpr ⟨hs_excl, hLift_sub_E' hs_lift⟩
  have hF'_sub_F : F' ⊆ F := hF.2 F' hF'_pow hF'_compat hF_sub_F'
  -- E' ⊆ liftToSet F: every ψ ∈ E' has the form ↑s for s ∈ F' ⊆ F.
  intro ψ hψ_E'
  obtain ⟨s, hs_excl, hs_eq⟩ := compat_member_in_excludables_image hE'_compat hψ_E'
  have hs_F' : s ∈ F' := mem_dropToFinset.mpr ⟨hs_excl, hs_eq ▸ hψ_E'⟩
  exact mem_liftToSet.mpr ⟨s, hF'_sub_F hs_F', hs_eq⟩

/-- A Set-side MC-set on `(coeSet ALT, ↑φ)` drops to a Finset-side MC-set. -/
private lemma dropToFinset_isMCSet
    {ALT : Finset (Finset W)} {φ : Finset W} {E : Set (Set W)}
    [DecidablePred fun s : Finset W => (↑s : Set W) ∈ E]
    (hE : IsMCSet (coeSet ALT) (↑φ) E) :
    Innocent.IsMCSet ALT φ (dropToFinset ALT φ E) := by
  refine ⟨dropToFinset_isCompatible hE.1, ?_⟩
  intro F' _ hF'_compat hDrop_sub_F'
  classical
  -- Lift F' to a Set, show it extends E, apply Set maximality.
  let E' : Set (Set W) := liftToSet F'
  have hE'_compat : IsCompatible (coeSet ALT) (↑φ) E' := liftToSet_isCompatible hF'_compat
  have hE_sub_E' : E ⊆ E' := by
    intro ψ hψ_E
    obtain ⟨s, hs_excl, hs_eq⟩ := compat_member_in_excludables_image hE.1 hψ_E
    have hs_drop : s ∈ dropToFinset ALT φ E :=
      mem_dropToFinset.mpr ⟨hs_excl, hs_eq ▸ hψ_E⟩
    exact mem_liftToSet.mpr ⟨s, hDrop_sub_F' hs_drop, hs_eq⟩
  have hE'_sub_E : E' ⊆ E := hE.2 E' hE'_compat hE_sub_E'
  intro s hs_F'
  have hs_E' : (↑s : Set W) ∈ E' := mem_liftToSet.mpr ⟨s, hs_F', rfl⟩
  have hs_E : (↑s : Set W) ∈ E := hE'_sub_E hs_E'
  exact mem_dropToFinset.mpr ⟨hF'_compat.1 hs_F', hs_E⟩

/-- **Set/Finset agreement on innocent exclusion**: `a` is innocently
    excludable on the Finset side iff `↑a` is innocently excludable on
    the Set side. -/
theorem coeSet_innocentlyExcludable_iff
    (ALT : Finset (Finset W)) (φ : Finset W) (a : Finset W) :
    a ∈ Innocent.innocentlyExcludable ALT φ ↔
      IsInnocentlyExcludable (coeSet ALT) (↑φ) (↑a) := by
  constructor
  · intro ha
    have ha_ALT : a ∈ ALT := (Finset.mem_filter.mp ha).1
    refine ⟨mem_coeSet.mpr ⟨a, ha_ALT, rfl⟩, ?_⟩
    -- Show (↑a)ᶜ ∈ IE on the Set side.
    have h_finset : (Finset.univ \ a) ∈ Innocent.IE ALT φ := (Finset.mem_filter.mp ha).2
    intro E hE_mc
    classical
    -- Drop E to a Finset MC-set; pull (Finset.univ \ a) out; coerce back.
    let F : Finset (Finset W) := dropToFinset ALT φ E
    have hF_mc : Innocent.IsMCSet ALT φ F := dropToFinset_isMCSet hE_mc
    have hF_pow : F ∈ (Innocent.excludables ALT φ).powerset :=
      Finset.mem_powerset.mpr hF_mc.1.1
    have h_in_F : (Finset.univ \ a) ∈ F :=
      (Finset.mem_filter.mp h_finset).2 F hF_pow hF_mc
    have : (↑(Finset.univ \ a) : Set W) ∈ E := (mem_dropToFinset.mp h_in_F).2
    rw [coe_univ_sdiff] at this
    exact this
  · intro ⟨ha_coe, h_compl_IE⟩
    obtain ⟨a', ha'_ALT, ha_eq⟩ := mem_coeSet.mp ha_coe
    have h_a : a' = a := Finset.coe_injective ha_eq
    have ha_ALT : a ∈ ALT := h_a ▸ ha'_ALT
    refine Finset.mem_filter.mpr ⟨ha_ALT, ?_⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a, ha_ALT, rfl⟩)
    · intro F _ hF_mc
      have hF_lift : IsMCSet (coeSet ALT) (↑φ) (liftToSet F) := liftToSet_isMCSet hF_mc
      have h_compl_in_lift : (↑a : Set W)ᶜ ∈ liftToSet F := h_compl_IE _ hF_lift
      obtain ⟨s, hs_F, hs_eq⟩ := mem_liftToSet.mp h_compl_in_lift
      have h_s : s = Finset.univ \ a := by
        apply Finset.coe_injective
        rw [hs_eq, coe_univ_sdiff]
      exact h_s ▸ hs_F

/-- **Full Set/Finset bridge for IE**: the Set IE on `(coeSet ALT, ↑φ)`
    is exactly `↑φ` together with the coerced Finset IE.

    Requires `φ.Nonempty` so that `IE_structure` applies on the Set side
    (otherwise the Set IE collapses to `Set.univ`, while the Finset side
    remains a finite set). -/
theorem IE_set_eq_coeSet_IE_finset
    (ALT : Finset (Finset W)) (φ : Finset W) (hφ : φ.Nonempty) :
    IE (coeSet ALT) (↑φ) =
      coeSet (Innocent.IE ALT φ) ∪ {(↑φ : Set W)} := by
  have hfin : Set.Finite (coeSet ALT) :=
    Set.Finite.image _ (Set.toFinite _)
  obtain ⟨w, hw⟩ := hφ
  have hsat : ∃ w, (↑φ : Set W) w := ⟨w, hw⟩
  apply Set.Subset.antisymm
  · intro ψ hψ_IE
    rcases IE_structure (coeSet ALT) (↑φ) hfin ψ hψ_IE hsat with hψ_eq | ⟨b, hb_coeALT, hψ_eq⟩
    · -- ψ = ↑φ
      right; exact hψ_eq
    · -- ψ = bᶜ for b ∈ coeSet ALT
      obtain ⟨b', hb'_ALT, hb_eq⟩ := mem_coeSet.mp hb_coeALT
      have hψ_compl : ψ = (↑b' : Set W)ᶜ := by rw [hψ_eq, ← hb_eq]
      have hψ_eq' : ψ = ↑(Finset.univ \ b') := by
        rw [hψ_compl, coe_univ_sdiff]
      have hIE_b' : IsInnocentlyExcludable (coeSet ALT) (↑φ) (↑b') :=
        ⟨mem_coeSet.mpr ⟨b', hb'_ALT, rfl⟩, hψ_compl ▸ hψ_IE⟩
      have hb'_finset : b' ∈ Innocent.innocentlyExcludable ALT φ :=
        (coeSet_innocentlyExcludable_iff ALT φ b').mpr hIE_b'
      have h_compl_IE : (Finset.univ \ b') ∈ Innocent.IE ALT φ :=
        (Finset.mem_filter.mp hb'_finset).2
      left
      exact mem_coeSet.mpr ⟨Finset.univ \ b', h_compl_IE, hψ_eq'.symm⟩
  · rintro ψ (hψ_coe | hψ_eq)
    · obtain ⟨s, hs_IE, hψ_eq⟩ := mem_coeSet.mp hψ_coe
      have hs_excl : s ∈ Innocent.excludables ALT φ := (Finset.mem_filter.mp hs_IE).1
      rcases Finset.mem_insert.mp hs_excl with hs_φ | hs_im
      · -- s = φ
        rw [← hψ_eq, hs_φ]
        exact phi_mem_IE_set _ _
      · -- s = Finset.univ \ a' for some a' ∈ ALT
        obtain ⟨a', ha'_ALT, hs_eq⟩ := Finset.mem_image.mp hs_im
        have ha'_finset : a' ∈ Innocent.innocentlyExcludable ALT φ := by
          refine Finset.mem_filter.mpr ⟨ha'_ALT, ?_⟩
          rw [hs_eq]; exact hs_IE
        have ha'_set : IsInnocentlyExcludable (coeSet ALT) (↑φ) (↑a') :=
          (coeSet_innocentlyExcludable_iff ALT φ a').mp ha'_finset
        rw [← hψ_eq, ← hs_eq, coe_univ_sdiff]
        exact ha'_set.2
    · rw [Set.mem_singleton_iff] at hψ_eq
      rw [hψ_eq]
      exact phi_mem_IE_set _ _

end Exhaustification
