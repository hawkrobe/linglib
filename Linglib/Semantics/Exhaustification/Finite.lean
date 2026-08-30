import Linglib.Semantics.Exhaustification.InnocentInclusion
import Linglib.Semantics.Exhaustification.Excluder
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Exhaustification over finite world types

Over a `Fintype` of worlds, with propositions as `Finset`s, compatibility, maximal
compatibility, innocent excludability and the cell are decidable: every compatible set lies
in `excludables`, so maximality is a search over its powerset. `innocent` packages innocent
exclusion as an `Excluder`, and the structural theorems compute `innocent.exh` and
`tolerant.exh` for alternative sets of a given shape. `preFilter_can_create_implicature`
witnesses that removing a symmetric alternative before exclusion strengthens the result.

## References

* [fox-2007]
* [spector-2016]
* [chierchia-2013]
* [fox-katzir-2011]
-/

namespace Exhaustification

variable {W : Type*}

/-! ### Coercion -/

/-- The alternatives of a finite family, as sets. -/
def asSetOfSets (E : Finset (Finset W)) : Set (Set W) :=
  (fun s : Finset W => (↑s : Set W)) '' (↑E : Set (Finset W))

@[simp] theorem mem_asSetOfSets {E : Finset (Finset W)} {s : Set W} :
    s ∈ asSetOfSets E ↔ ∃ a ∈ E, (↑a : Set W) = s := by
  simp [asSetOfSets]

variable [Fintype W] [DecidableEq W]

/-- The complement of a `Finset`, as a set. -/
theorem coe_univ_sdiff (a : Finset W) :
    ((Finset.univ \ a : Finset W) : Set W) = (↑a : Set W)ᶜ := by
  rw [Finset.coe_sdiff, Finset.coe_univ, ← Set.compl_eq_univ_sdiff]

/-- Membership in the intersection of a finite family. -/
theorem mem_inf_id_iff {s : Finset (Finset W)} {w : W} :
    w ∈ s.inf id ↔ ∀ a ∈ s, w ∈ a := by
  refine ⟨fun h a ha => Finset.mem_of_subset (Finset.inf_le ha) h, fun h => ?_⟩
  exact Finset.singleton_subset_iff.mp
    (Finset.le_inf fun a ha => Finset.singleton_subset_iff.mpr (h a ha))

variable (ALT : Finset (Finset W)) (φ : Finset W)

/-! ### Compatible sets -/

/-- The prejacent with the complement of every alternative: every compatible set lies in
it. -/
def excludables : Finset (Finset W) :=
  insert φ (ALT.image (fun a => Finset.univ \ a))

/-- Compatibility over finite families is a `Finset` condition. -/
theorem isCompatible_iff_finset (E : Finset (Finset W)) :
    IsCompatible (asSetOfSets ALT) ↑φ (asSetOfSets E) ↔
    E ⊆ excludables ALT φ ∧ φ ∈ E ∧ (E.inf id).Nonempty := by
  unfold IsCompatible
  refine ⟨?_, ?_⟩
  · rintro ⟨hphi, hform, hcons⟩
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      have : (↑a : Set W) ∈ asSetOfSets E := mem_asSetOfSets.mpr ⟨a, ha, rfl⟩
      rcases hform _ this with hphi_case | ⟨a', ha'_mem, ha_eq⟩
      · rw [Finset.coe_inj.1 hphi_case]
        exact Finset.mem_insert_self φ _
      · rcases mem_asSetOfSets.mp ha'_mem with ⟨b', hb'_ALT, rfl⟩
        rw [← coe_univ_sdiff] at ha_eq
        rw [Finset.coe_inj.1 ha_eq]
        exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨b', hb'_ALT, rfl⟩)
    · rcases mem_asSetOfSets.mp hphi with ⟨a, ha_mem, ha_eq⟩
      rwa [Finset.coe_inj.1 ha_eq] at ha_mem
    · obtain ⟨u, hu⟩ := hcons
      refine ⟨u, ?_⟩
      rw [mem_inf_id_iff]
      intro a ha
      have : (↑a : Set W) ∈ asSetOfSets E := mem_asSetOfSets.mpr ⟨a, ha, rfl⟩
      exact Finset.mem_coe.mp (hu _ this)
  · rintro ⟨hsub, hphi, ⟨u, hu⟩⟩
    refine ⟨?_, ?_, ?_⟩
    · exact mem_asSetOfSets.mpr ⟨φ, hphi, rfl⟩
    · intro s hs
      rcases mem_asSetOfSets.mp hs with ⟨a, ha_mem, rfl⟩
      have ha_excl := hsub ha_mem
      simp [excludables] at ha_excl
      rcases ha_excl with rfl | ⟨b, hb_ALT, rfl⟩
      · left; rfl
      · right
        refine ⟨↑b, mem_asSetOfSets.mpr ⟨b, hb_ALT, rfl⟩, coe_univ_sdiff b⟩
    · refine ⟨u, ?_⟩
      intro s hs
      rcases mem_asSetOfSets.mp hs with ⟨a, ha_mem, rfl⟩
      rw [mem_inf_id_iff] at hu
      exact Finset.mem_coe.mpr (hu a ha_mem)

instance decidableIsCompatible (E : Finset (Finset W)) :
    Decidable (IsCompatible (asSetOfSets ALT) ↑φ (asSetOfSets E)) :=
  decidable_of_iff _ (isCompatible_iff_finset ALT φ E).symm

/-- Maximal compatibility is a search over the powerset of `excludables`. -/
theorem isMCSet_iff_finset (E : Finset (Finset W)) :
    IsMCSet (asSetOfSets ALT) ↑φ (asSetOfSets E) ↔
    IsCompatible (asSetOfSets ALT) ↑φ (asSetOfSets E) ∧
    ∀ E' ∈ (excludables ALT φ).powerset,
      IsCompatible (asSetOfSets ALT) ↑φ (asSetOfSets E') → E ⊆ E' → E' ⊆ E := by
  refine ⟨?_, ?_⟩
  · -- Forward: Set MC-set → Finset MC-set characterization
    rintro ⟨hE_compat, hmax⟩
    refine ⟨hE_compat, ?_⟩
    intro E' _hE'_powerset hE'_compat hE_sub
    have hE_sub_set : asSetOfSets E ⊆ asSetOfSets E' := by
      intro s hs
      rcases mem_asSetOfSets.mp hs with ⟨a, ha_mem, rfl⟩
      exact mem_asSetOfSets.mpr ⟨a, hE_sub ha_mem, rfl⟩
    have := hmax _ hE'_compat hE_sub_set
    intro a ha_E'
    have : (↑a : Set W) ∈ asSetOfSets E := this (mem_asSetOfSets.mpr ⟨a, ha_E', rfl⟩)
    rcases mem_asSetOfSets.mp this with ⟨b, hb_E, hb_eq⟩
    rwa [Finset.coe_inj.1 hb_eq] at hb_E
  · -- Backward: Finset characterization → Set MC-set
    rintro ⟨hE_compat, hmax⟩
    refine ⟨hE_compat, ?_⟩
    intro E' hE'_compat hE_sub_set
    classical
    -- Construct the Finset corresponding to E'
    let E'_f : Finset (Finset W) :=
      (excludables ALT φ).filter (fun ψ => (↑ψ : Set W) ∈ E')
    have hE'_f_powerset : E'_f ∈ (excludables ALT φ).powerset :=
      Finset.mem_powerset.mpr (Finset.filter_subset _ _)
    -- Show asSetOfSets E'_f = E'
    have h_eq : asSetOfSets E'_f = E' := by
      ext s
      constructor
      · intro hs
        rcases mem_asSetOfSets.mp hs with ⟨a, ha_mem, rfl⟩
        exact (Finset.mem_filter.mp ha_mem).2
      · intro hs
        rcases hE'_compat.2.1 s hs with rfl | ⟨a, ha_alt, rfl⟩
        · refine mem_asSetOfSets.mpr ⟨φ, ?_, rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_insert_self φ _, hs⟩
        · rcases mem_asSetOfSets.mp ha_alt with ⟨b, hb_ALT, rfl⟩
          refine mem_asSetOfSets.mpr ⟨Finset.univ \ b, ?_, ?_⟩
          · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
            · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨b, hb_ALT, rfl⟩)
            · rwa [coe_univ_sdiff]
          · exact coe_univ_sdiff b
    have hE'_f_compat : IsCompatible (asSetOfSets ALT) ↑φ (asSetOfSets E'_f) := by
      show IsCompatible (asSetOfSets ALT) (↑φ) (asSetOfSets E'_f)
      rw [h_eq]; exact hE'_compat
    have hE_sub_f : E ⊆ E'_f := by
      intro a ha_E
      have : (↑a : Set W) ∈ E' :=
        hE_sub_set (mem_asSetOfSets.mpr ⟨a, ha_E, rfl⟩)
      have ha_excl : a ∈ excludables ALT φ :=
        ((isCompatible_iff_finset ALT φ E).mp hE_compat).1 ha_E
      exact Finset.mem_filter.mpr ⟨ha_excl, this⟩
    have hE'_sub_E := hmax E'_f hE'_f_powerset hE'_f_compat hE_sub_f
    intro s hs
    rw [← h_eq] at hs
    rcases mem_asSetOfSets.mp hs with ⟨a, ha_E'_f, rfl⟩
    exact mem_asSetOfSets.mpr ⟨a, hE'_sub_E ha_E'_f, rfl⟩

instance decidableIsMCSet (E : Finset (Finset W)) :
    Decidable (IsMCSet (asSetOfSets ALT) ↑φ (asSetOfSets E)) :=
  decidable_of_iff _ (isMCSet_iff_finset ALT φ E).symm

/-- The propositions in every maximal compatible set, computed within `excludables`. -/
def ieFinset : Finset (Finset W) :=
  (excludables ALT φ).filter fun ψ =>
    ∀ E ∈ (excludables ALT φ).powerset, IsMCSet (asSetOfSets ALT) ↑φ (asSetOfSets E) → ψ ∈ E

/-- The innocently excludable alternatives of a finite family. -/
def innocentlyExcludable : Finset (Finset W) :=
  ALT.filter (fun a => (Finset.univ \ a) ∈ ieFinset ALT φ)

theorem innocentlyExcludable_subset (ALT : Finset (Finset W)) (φ : Finset W) :
    innocentlyExcludable ALT φ ⊆ ALT := Finset.filter_subset _ _

/-- The prejacent lies in every maximal compatible set. -/
theorem self_mem_ieFinset : φ ∈ ieFinset ALT φ := by
  unfold ieFinset
  refine Finset.mem_filter.mpr ⟨Finset.mem_insert_self φ _, ?_⟩
  intro E _ hMC
  exact ((isCompatible_iff_finset ALT φ E).mp hMC.1).2.1

/-! ### Innocent excludability -/

/-- Innocent excludability over a finite family is membership in `innocentlyExcludable`. -/
theorem isInnocentlyExcludable_iff (a : Finset W) :
    IsInnocentlyExcludable
      (asSetOfSets ALT) (↑φ) (↑a) ↔
    a ∈ innocentlyExcludable ALT φ := by
  unfold IsInnocentlyExcludable innocentlyExcludable
  refine ⟨?_, ?_⟩
  · rintro ⟨hMem, hIE⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rcases mem_asSetOfSets.mp hMem with ⟨b, hb_ALT, hb_eq⟩
      rwa [Finset.coe_inj.1 hb_eq] at hb_ALT
    · -- aᶜ as a Set equals (Finset.univ \ a) coerced
      rw [show ((↑a : Set W)ᶜ : Set W) = ((Finset.univ \ a : Finset W) : Set W)
          from (coe_univ_sdiff a).symm] at hIE
      -- Bridge: Set-IE membership of the coerced Finset complement →
      -- Finset-IE membership. This requires the Set-IE / Finset-IE bridge,
      -- which follows from MC-set bridges already in scope.
      unfold ieFinset
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · -- (Finset.univ \ a) ∈ excludables ALT φ (by membership of a in ALT)
        have ha_ALT : a ∈ ALT := by
          rcases mem_asSetOfSets.mp hMem with ⟨b, hb_ALT, hb_eq⟩
          rwa [Finset.coe_inj.1 hb_eq] at hb_ALT
        exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a, ha_ALT, rfl⟩)
      · intro E _ hE_mc
        have hE_set : IsMCSet
            (asSetOfSets ALT) (↑φ) (asSetOfSets E) := hE_mc
        have h_aux := hIE _ hE_set
        rcases mem_asSetOfSets.mp h_aux with ⟨b, hb_E, hb_eq⟩
        have : b = Finset.univ \ a := by
          apply Finset.coe_inj.1
          rw [hb_eq, coe_univ_sdiff]
        rwa [this] at hb_E
  · intro ha
    rw [Finset.mem_filter] at ha
    refine ⟨?_, ?_⟩
    · exact mem_asSetOfSets.mpr ⟨a, ha.1, rfl⟩
    · -- (↑a)ᶜ = (Finset.univ \ a) as Sets; need it in Set-IE
      rw [show ((↑a : Set W)ᶜ : Set W) = ((Finset.univ \ a : Finset W) : Set W)
          from (coe_univ_sdiff a).symm]
      intro E hE_set_mc
      -- Bridge from Set-MC-set to Finset-MC-set, then use ha.2 (Finset IE)
      classical
      let E_f : Finset (Finset W) :=
        (excludables ALT φ).filter (fun ψ => (↑ψ : Set W) ∈ E)
      have hE_f_powerset : E_f ∈ (excludables ALT φ).powerset :=
        Finset.mem_powerset.mpr (Finset.filter_subset _ _)
      have hE_f_eq : asSetOfSets E_f = E := by
        ext s
        constructor
        · intro hs
          rcases mem_asSetOfSets.mp hs with ⟨c, hc_mem, rfl⟩
          exact (Finset.mem_filter.mp hc_mem).2
        · intro hs
          have hE_compat : IsCompatible
              (asSetOfSets ALT) (↑φ) E := hE_set_mc.1
          rcases hE_compat.2.1 s hs with rfl | ⟨c, hc_alt, rfl⟩
          · refine mem_asSetOfSets.mpr ⟨φ, ?_, rfl⟩
            exact Finset.mem_filter.mpr ⟨Finset.mem_insert_self φ _, hs⟩
          · rcases mem_asSetOfSets.mp hc_alt with ⟨d, hd_ALT, rfl⟩
            refine mem_asSetOfSets.mpr ⟨Finset.univ \ d, ?_, ?_⟩
            · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
              · exact Finset.mem_insert_of_mem
                  (Finset.mem_image.mpr ⟨d, hd_ALT, rfl⟩)
              · rwa [coe_univ_sdiff]
            · exact coe_univ_sdiff d
      have hE_f_mc : IsMCSet (asSetOfSets ALT) ↑φ (asSetOfSets E_f) := by
        show IsMCSet (asSetOfSets ALT) (↑φ) (asSetOfSets E_f)
        rw [hE_f_eq]; exact hE_set_mc
      have h_in_E_f : Finset.univ \ a ∈ E_f :=
        (Finset.mem_filter.mp ha.2).2 E_f hE_f_powerset hE_f_mc
      have h_in_E : (((Finset.univ \ a : Finset W) : Set W)) ∈ E := by
        rw [← hE_f_eq]; exact mem_asSetOfSets.mpr ⟨_, h_in_E_f, rfl⟩
      exact h_in_E

/-- Innocent excludability is decidable over finite families. -/
instance decidableIsInnocentlyExcludable (a : Finset W) :
    Decidable (IsInnocentlyExcludable
      (asSetOfSets ALT) (↑φ) (↑a)) :=
  decidable_of_iff _ (isInnocentlyExcludable_iff ALT φ a).symm

/-! ### The cell -/

/-- The cell of the prejacent, as a `Finset`. -/
def cellFinset : Finset W :=
  Finset.univ.filter fun w =>
    w ∈ φ ∧
    (∀ a ∈ innocentlyExcludable ALT φ, w ∉ a) ∧
    (∀ r ∈ ALT \ innocentlyExcludable ALT φ, w ∈ r)

/-- Membership in `cellFinset` is membership in the cell. -/
theorem mem_cellFinset_iff (w : W) :
    w ∈ cellFinset ALT φ ↔ cell (asSetOfSets ALT) (↑φ) w := by
  unfold cellFinset cell nonExcludable
  rw [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · rintro ⟨_, hφ, hexcl, hne⟩
    refine ⟨hφ, ?_, ?_⟩
    · -- IE side: ∀ q with IsInnocentlyExcludable, ¬ q w
      intro q hq
      -- q is a Set; need to recover its Finset form
      have hq_alt : q ∈ asSetOfSets ALT := hq.1
      rcases mem_asSetOfSets.mp hq_alt with ⟨q_f, hq_f_ALT, rfl⟩
      have : q_f ∈ innocentlyExcludable ALT φ :=
        (isInnocentlyExcludable_iff ALT φ q_f).mp hq
      intro hw_q_f
      exact hexcl q_f this hw_q_f
    · rintro r ⟨hr_alt, hr_not_ie⟩
      rcases mem_asSetOfSets.mp hr_alt with ⟨r_f, hr_f_ALT, rfl⟩
      have hr_not_ie_finset : r_f ∉ innocentlyExcludable ALT φ := by
        intro h
        exact hr_not_ie ((isInnocentlyExcludable_iff ALT φ r_f).mpr h)
      exact hne r_f
        (Finset.mem_sdiff.mpr ⟨hr_f_ALT, hr_not_ie_finset⟩)
  · rintro ⟨hφ, hexcl, hne⟩
    refine ⟨Finset.mem_univ _, hφ, ?_, ?_⟩
    · intro a ha hw_a
      have ha_set_ie : IsInnocentlyExcludable
          (asSetOfSets ALT) (↑φ) (↑a) :=
        (isInnocentlyExcludable_iff ALT φ a).mpr ha
      exact hexcl _ ha_set_ie hw_a
    · intro r hr
      rcases Finset.mem_sdiff.mp hr with ⟨hr_ALT, hr_not_ie⟩
      have hr_set_alt : (↑r : Set W) ∈ asSetOfSets ALT :=
        mem_asSetOfSets.mpr ⟨r, hr_ALT, rfl⟩
      have hr_not_ie_set : ¬ IsInnocentlyExcludable
          (asSetOfSets ALT) (↑φ) (↑r) := by
        intro h
        exact hr_not_ie ((isInnocentlyExcludable_iff ALT φ r).mp h)
      exact hne (↑r) ⟨hr_set_alt, hr_not_ie_set⟩

/-- The cell is decidable over finite families. -/
instance decidableCell (w : W) :
    Decidable (cell (asSetOfSets ALT) (↑φ) w) :=
  decidable_of_iff _ (mem_cellFinset_iff ALT φ w)

/-! ### The innocent excluder -/

/-- The innocent excluder ([fox-2007]): `innocent.exh ALT φ` is `exhIE` over finite worlds. -/
def innocent {W : Type*} [Fintype W] [DecidableEq W] : Excluder W where
  excluded := innocentlyExcludable
  excluded_subset := innocentlyExcludable_subset

/-- With nothing innocently excludable, exhaustification is vacuous. -/
theorem innocent_exh_eq_phi_of_innocentlyExcludable_empty
    {ALT : Finset (Finset W)} {φ : Finset W}
    (h : innocentlyExcludable ALT φ = ∅) :
    innocent.exh ALT φ = φ := by
  show φ \ ((innocentlyExcludable ALT φ).biUnion id) = φ
  rw [h]
  simp

/-! ### Tolerant exhaustification -/

/-- Tolerant exhaustification is contradictory when every prejacent world lies in a
non-entailed alternative. -/
theorem tolerant_exh_eq_empty_of_covered
    {ALT : Finset (Finset W)} {φ : Finset W}
    (h : ∀ w ∈ φ, ∃ α ∈ ALT, ¬ φ ⊆ α ∧ w ∈ α) :
    tolerant.exh ALT φ = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro w hmem
  rw [mem_tolerant_exh_iff] at hmem
  obtain ⟨hw_phi, hw_neg⟩ := hmem
  obtain ⟨α, hα_ALT, hα_neg, hw_α⟩ := h w hw_phi
  exact hw_neg α hα_ALT hα_neg hw_α

/-- A contradictory tolerant exhaustification covers the prejacent by non-entailed
alternatives. -/
theorem covered_of_tolerant_exh_eq_empty
    {ALT : Finset (Finset W)} {φ : Finset W}
    (h : tolerant.exh ALT φ = ∅) (w : W) (hw : w ∈ φ) :
    ∃ α ∈ ALT, ¬ φ ⊆ α ∧ w ∈ α := by
  by_contra hcon
  push Not at hcon
  have hw_exh : w ∈ tolerant.exh ALT φ := by
    rw [mem_tolerant_exh_iff]
    refine ⟨hw, fun α hα_ALT hα_neg hw_α => ?_⟩
    exact hcon α hα_ALT hα_neg hw_α
  simp [h] at hw_exh

/-- Tolerant exhaustification is contradictory iff the non-entailed alternatives cover the
prejacent. -/
theorem tolerant_exh_eq_empty_iff (ALT : Finset (Finset W)) (φ : Finset W) :
    tolerant.exh ALT φ = ∅ ↔ ∀ w ∈ φ, ∃ α ∈ ALT, ¬ φ ⊆ α ∧ w ∈ α :=
  ⟨covered_of_tolerant_exh_eq_empty, tolerant_exh_eq_empty_of_covered⟩

/-! ### Innocent exhaustification -/

/-- The tolerant excluder denies every alternative the innocent one does. -/
theorem tolerant_exh_subset_innocent_exh
    (ALT : Finset (Finset W)) (φ : Finset W) :
    tolerant.exh ALT φ ⊆ innocent.exh ALT φ := by
  intro w hw
  rw [mem_tolerant_exh_iff] at hw
  rw [Excluder.mem_exh_iff]
  obtain ⟨hw_phi, hw_neg⟩ := hw
  refine ⟨hw_phi, fun a ha_ie hw_a => ?_⟩
  have ha_alt : a ∈ ALT := innocentlyExcludable_subset ALT φ ha_ie
  -- a is innocently excludable, so its negation is consistent with φ —
  -- i.e., there is some φ-world outside a. So ¬(φ ⊆ a), and tolerant
  -- negates a. Then if w ∈ a, tolerant would have excluded w, contra.
  apply hw_neg a ha_alt
  · -- ¬ φ ⊆ a: follows from a being innocently excludable.
    intro hsub
    -- Bridge Finset → Set, then apply `not_isInnocentlyExcludable_of_phi_subset`.
    have hSet : IsInnocentlyExcludable
        (asSetOfSets ALT) (↑φ : Set W) (↑a : Set W) :=
      (isInnocentlyExcludable_iff ALT φ a).mpr ha_ie
    have hfin : Set.Finite (asSetOfSets ALT) :=
      (Set.toFinite _).image _
    have hsat : ∃ x : W, (↑φ : Set W) x := ⟨w, hw_phi⟩
    have h_subset_set : (↑φ : Set W) ⊆ (↑a : Set W) := fun x hx => hsub hx
    exact not_isInnocentlyExcludable_of_phi_subset
        hfin hsat h_subset_set hSet
  · exact hw_a

/-- When some prejacent world lies in no alternative, every alternative is innocently
excludable and exhaustification removes their union. -/
theorem innocent_exh_pairwise_disjoint_partial
    {ALT : Finset (Finset W)} {φ : Finset W}
    (hcompat : (φ \ ALT.sup id).Nonempty) :
    innocent.exh ALT φ = φ \ ALT.sup id := by
  -- Step 1: innocentlyExcludable ALT φ = ALT.
  have h_ie_eq : innocentlyExcludable ALT φ = ALT := by
    refine Finset.Subset.antisymm (innocentlyExcludable_subset _ _) ?_
    intro α hα
    rw [← isInnocentlyExcludable_iff]
    apply IsInnocentlyExcludable.of_full_exclusion_consistent
    · exact mem_asSetOfSets.mpr ⟨α, hα, rfl⟩
    · obtain ⟨w, hw⟩ := hcompat
      rw [Finset.mem_sdiff] at hw
      obtain ⟨hw_phi, hw_not_sup⟩ := hw
      refine ⟨w, hw_phi, ?_⟩
      intro b hb
      rcases mem_asSetOfSets.mp hb with ⟨β, hβ_mem, rfl⟩
      intro hw_β
      apply hw_not_sup
      rw [Finset.sup_eq_biUnion]
      exact Finset.mem_biUnion.mpr ⟨β, hβ_mem, hw_β⟩
  -- Step 2: unfold `exh` and convert `biUnion id` to `sup id`.
  show φ \ ((innocentlyExcludable ALT φ).biUnion id) = φ \ ALT.sup id
  rw [h_ie_eq, ← Finset.sup_eq_biUnion]

/-- A single alternative strictly below the prejacent is denied. -/
theorem innocent_exh_singleton_proper {α φ : Finset W} (h : α ⊂ φ) :
    innocent.exh ({α} : Finset (Finset W)) φ = φ \ α := by
  have hsup : ({α} : Finset (Finset W)).sup id = α := Finset.sup_singleton
  have hcompat : (φ \ ({α} : Finset (Finset W)).sup id).Nonempty := by
    rw [hsup]; exact (Finset.exists_of_ssubset h).imp fun _ ⟨h₁, h₂⟩ =>
      Finset.mem_sdiff.mpr ⟨h₁, h₂⟩
  rw [innocent_exh_pairwise_disjoint_partial hcompat, hsup]

/-- An alternative entailed by the prejacent can be dropped without changing the
exhaustification. -/
theorem innocent_exh_erase_entailed
    {ALT : Finset (Finset W)} {a φ : Finset W}
    (h_entails : φ ⊆ a) (hphi_nonempty : φ.Nonempty) :
    innocent.exh ALT φ = innocent.exh (ALT.erase a) φ := by
  -- Reduce to showing innocentlyExcludable sets coincide.
  suffices h_ie_eq :
      innocentlyExcludable ALT φ
        = innocentlyExcludable (ALT.erase a) φ by
    show φ \ ((innocentlyExcludable ALT φ).biUnion id)
      = φ \ ((innocentlyExcludable (ALT.erase a) φ).biUnion id)
    rw [h_ie_eq]
  -- Pre-cook hypotheses used to invoke `not_isInnocentlyExcludable_of_phi_subset`.
  have hsat : ∃ x : W, (↑φ : Set W) x := hphi_nonempty.imp (fun _ h => h)
  have h_subset_set : (↑φ : Set W) ⊆ (↑a : Set W) := fun x hx => h_entails hx
  -- IsCompatible E coincides between (ALT, φ) and (ALT.erase a, φ).
  -- Forward direction uses the witness: the consistency witness satisfies
  -- φ ⊆ a, so cannot satisfy aᶜ, hence aᶜ ∉ E and every bᶜ ∈ E has b ≠ a.
  have h_compat_iff : ∀ E' : Finset (Finset W),
      IsCompatible (asSetOfSets ALT) ↑φ (asSetOfSets E') ↔
        IsCompatible (asSetOfSets (ALT.erase a)) ↑φ (asSetOfSets E') := by
    intro E'
    constructor
    · intro ⟨hphi_mem, hform, hcons⟩
      refine ⟨hphi_mem, ?_, hcons⟩
      intro ψ hψ
      rcases hform ψ hψ with hphi_case | ⟨c, hc_mem, hc_eq⟩
      · exact Or.inl hphi_case
      · rcases mem_asSetOfSets.mp hc_mem with ⟨c', hc'_ALT, hc'_eq⟩
        obtain ⟨u, hu⟩ := hcons
        have hu_phi : (↑φ : Set W) u := hu φ hphi_mem
        have hu_psi : ψ u := hu ψ hψ
        -- hu_psi : ψ u, with ψ = cᶜ, so u ∉ c. Combined with c = ↑c', u ∉ ↑c'.
        have hu_not_c : u ∉ c := by
          intro h; apply (show u ∈ ψ → False from by rw [hc_eq]; exact fun h' => h' h)
          exact hu_psi
        have hu_not_c' : u ∉ (↑c' : Set W) := by rw [hc'_eq]; exact hu_not_c
        have hc'_ne_a : c' ≠ a := by
          intro heq; subst heq
          exact hu_not_c' (h_subset_set hu_phi)
        exact Or.inr ⟨c, mem_asSetOfSets.mpr
          ⟨c', Finset.mem_erase.mpr ⟨hc'_ne_a, hc'_ALT⟩, hc'_eq⟩, hc_eq⟩
    · intro ⟨hphi_mem, hform, hcons⟩
      refine ⟨hphi_mem, ?_, hcons⟩
      intro ψ hψ
      rcases hform ψ hψ with hphi_case | ⟨c, hc_mem, hc_eq⟩
      · exact Or.inl hphi_case
      · rcases mem_asSetOfSets.mp hc_mem with ⟨c', hc'_erase, hc'_eq⟩
        have hc'_ALT : c' ∈ ALT := (Finset.mem_erase.mp hc'_erase).2
        exact Or.inr ⟨c, mem_asSetOfSets.mpr ⟨c', hc'_ALT, hc'_eq⟩, hc_eq⟩
  -- Hence IsMCSet coincides as well: maximality transports via h_compat_iff,
  -- and the powerset bound is whichever excludables-set fits.
  have h_mc_iff : ∀ E : Finset (Finset W),
      IsMCSet (asSetOfSets ALT) ↑φ (asSetOfSets E) ↔
        IsMCSet (asSetOfSets (ALT.erase a)) ↑φ (asSetOfSets E) := by
    intro E
    simp only [isMCSet_iff_finset]
    refine ⟨?_, ?_⟩
    · rintro ⟨hE_compat, hmax⟩
      refine ⟨(h_compat_iff E).mp hE_compat, ?_⟩
      intro E' _ hE'_compat hE_sub
      have hE'_compat_ALT : IsCompatible (asSetOfSets ALT) ↑φ (asSetOfSets E') :=
        (h_compat_iff E').mpr hE'_compat
      have hE'_powerset_ALT : E' ∈ (excludables ALT φ).powerset :=
        Finset.mem_powerset.mpr
          ((isCompatible_iff_finset _ _ _).mp hE'_compat_ALT).1
      exact hmax E' hE'_powerset_ALT hE'_compat_ALT hE_sub
    · rintro ⟨hE_compat, hmax⟩
      refine ⟨(h_compat_iff E).mpr hE_compat, ?_⟩
      intro E' _ hE'_compat hE_sub
      have hE'_compat_erase : IsCompatible (asSetOfSets (ALT.erase a)) ↑φ (asSetOfSets E') :=
        (h_compat_iff E').mp hE'_compat
      have hE'_powerset_erase : E' ∈ (excludables (ALT.erase a) φ).powerset :=
        Finset.mem_powerset.mpr
          ((isCompatible_iff_finset _ _ _).mp hE'_compat_erase).1
      exact hmax E' hE'_powerset_erase hE'_compat_erase hE_sub
  -- Set equality by extensionality on the alternative b.
  ext b
  -- `a` is in neither innocentlyExcludable set: not in ALT.erase a (by erase),
  -- and not in innocentlyExcludable ALT φ by `not_isInnocentlyExcludable_of_phi_subset`.
  have h_a_not_ie_ALT : a ∉ innocentlyExcludable ALT φ := by
    intro h
    have hSet : IsInnocentlyExcludable
        (asSetOfSets ALT) (↑φ : Set W) (↑a : Set W) :=
      (isInnocentlyExcludable_iff ALT φ a).mpr h
    have hfin : Set.Finite (asSetOfSets ALT) := (Set.toFinite _).image _
    exact not_isInnocentlyExcludable_of_phi_subset
      hfin hsat h_subset_set hSet
  by_cases hba : b = a
  · -- b = a: both sides are False.
    subst hba
    refine ⟨fun h => (h_a_not_ie_ALT h).elim, fun h => ?_⟩
    have hmem : b ∈ ALT.erase b :=
      innocentlyExcludable_subset _ _ h
    exact (Finset.notMem_erase _ _ hmem).elim
  · -- b ≠ a: `b ∈ ALT ↔ b ∈ ALT.erase a`, and the IE filter conditions
    -- coincide via h_mc_iff (and the underlying h_compat_iff for the
    -- powerset/excludables bound).
    simp only [innocentlyExcludable, Finset.mem_filter, ieFinset]
    have h_b_alt : b ∈ ALT ↔ b ∈ ALT.erase a :=
      ⟨fun h => Finset.mem_erase.mpr ⟨hba, h⟩,
       fun h => (Finset.mem_erase.mp h).2⟩
    -- The two filter components (powerset bound + MC-set membership) transfer.
    constructor
    · rintro ⟨hb_ALT, hbex_ALT, hb_in_every_MC⟩
      have hb_erase : b ∈ ALT.erase a := h_b_alt.mp hb_ALT
      refine ⟨hb_erase, ?_, ?_⟩
      · simp only [excludables] at hbex_ALT ⊢
        rcases Finset.mem_insert.mp hbex_ALT with heq | himg
        · exact Finset.mem_insert.mpr (Or.inl heq)
        · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨b, hb_erase, rfl⟩)
      · intro E _ hE_mc_erase
        have hE_mc_ALT : IsMCSet (asSetOfSets ALT) ↑φ (asSetOfSets E) :=
          (h_mc_iff E).mpr hE_mc_erase
        have hE_pow_ALT : E ∈ (excludables ALT φ).powerset :=
          Finset.mem_powerset.mpr
            ((isCompatible_iff_finset _ _ _).mp hE_mc_ALT.1).1
        exact hb_in_every_MC E hE_pow_ALT hE_mc_ALT
    · rintro ⟨hb_erase, hbex_erase, hb_in_every_MC⟩
      have hb_ALT : b ∈ ALT := h_b_alt.mpr hb_erase
      refine ⟨hb_ALT, ?_, ?_⟩
      · simp only [excludables] at hbex_erase ⊢
        rcases Finset.mem_insert.mp hbex_erase with heq | himg
        · exact Finset.mem_insert.mpr (Or.inl heq)
        · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨b, hb_ALT, rfl⟩)
      · intro E _ hE_mc_ALT
        have hE_mc_erase : IsMCSet (asSetOfSets (ALT.erase a)) ↑φ (asSetOfSets E) :=
          (h_mc_iff E).mp hE_mc_ALT
        have hE_pow_erase : E ∈ (excludables (ALT.erase a) φ).powerset :=
          Finset.mem_powerset.mpr
            ((isCompatible_iff_finset _ _ _).mp hE_mc_erase.1).1
        exact hb_in_every_MC E hE_pow_erase hE_mc_erase

/-! ### Filtering alternatives can strengthen -/


private def cAlt : Finset (Finset Bool) := {{true}, {false}}
private def cPhi : Finset Bool := Finset.univ
private def cPsi : Finset Bool := {false}
private def cPred : Finset Bool → Bool := fun a => decide (a = ({true} : Finset Bool))

private theorem innocent_exh_at_symmetric_pair :
    innocent.exh cAlt cPhi = cPhi := by decide

private theorem preFilter_innocent_exh_at_symmetric_pair :
    (innocent.preFilter cPred).exh cAlt cPhi = cPsi := by decide

/-- Filtering the alternatives before exclusion can license an implicature the unfiltered
excluder does not: removing one of two symmetric alternatives makes the other excludable
([fox-katzir-2011]'s formal alternative source can break symmetry). -/
theorem preFilter_can_create_implicature :
    ∃ (E : Excluder Bool) (ALT : Finset (Finset Bool)) (φ ψ : Finset Bool)
      (P : Finset Bool → Bool),
      ¬ E.exh ALT φ ⊆ ψ ∧ (E.preFilter P).exh ALT φ ⊆ ψ := by
  refine ⟨innocent, cAlt, cPhi, cPsi, cPred, ?_, ?_⟩
  · rw [innocent_exh_at_symmetric_pair]; decide
  · rw [preFilter_innocent_exh_at_symmetric_pair]

end Exhaustification
