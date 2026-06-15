import Linglib.Semantics.Exhaustification.Operators.Basic
import Linglib.Semantics.Exhaustification.Operators.InnocentInclusion
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Finset-typed refinement of the IE substrate
[fox-2007] [spector-2016]

`Finset`-typed computable refinement of the canonical Set-side
definitions in `Operators/Basic.lean`. There is no parallel theory:
`Innocent.IsCompatible` / `IsMCSet` are `abbrev`s over their Set-side
counterparts under the `Finset → Set` coercion, with bridge `iff`s
that recover the explicit Finset characterizations + provide the
`Decidable` instances downstream `Excluder.exh` needs.

Worlds are an arbitrary `[Fintype W] [DecidableEq W]`. A proposition
is a `Finset W`. An alternative collection is a `Finset (Finset W)`.

## Architecture

The Set-side `Exhaustification.IsCompatible` / `IsMCSet` / `IE`
(defined in `Operators/Basic.lean`) are the canonical specifications.
Here:

1. `asSetOfSets : Finset (Finset W) → Set (Set W)` — the obvious
   coercion (lift each inner Finset to a Set, take the image).
2. `Innocent.IsCompatible E := Exhaustification.IsCompatible (asSetOfSets ALT) ↑φ (asSetOfSets E)`
   and similarly for `IsMCSet`. These are `abbrev`s, so any Set-side
   theorem about `IsCompatible` / `IsMCSet` automatically applies.
3. Bridge `iff`s to the explicit Finset characterizations:
   `IsCompatible ↔ E ⊆ excludables ∧ φ ∈ E ∧ (E.inf id).Nonempty`, etc.
4. `Decidable` instances via the bridges (the Finset characterization
   is decidable by construction).
5. `IE` / `innocentlyExcludable` as `Finset` filters using the
   derived `Decidable` instances.

Standard mathlib pattern for "abstract spec + computable refinement"
(cf. `Set.Finite` + `Set.Finite.toFinset`, `Set.image` +
`Finset.image`, etc.).

## Key definitions

- `excludables ALT φ` — bound on every `IsCompatible` witness
- `IsCompatible ALT φ E` — Spector Definition 3.2 (Finset-typed,
  defined as a Set-side abbrev)
- `IsMCSet ALT φ E` — Spector Definition 3.3 (similarly)
- `IE ALT φ` — Spector Definition 3.4: alternatives in every MC-set
- `innocentlyExcludable ALT φ` — alternatives whose complement is in `IE`

The Fox 2007 `Excluder` packaging lives in
`InnocentExclusion.lean` (sibling Excluder file, parallel to
`Tolerant.lean` / `Relevance.lean`).
-/

namespace Exhaustification.Innocent

variable {W : Type*} [Fintype W] [DecidableEq W]

/-! ### Coercion -/

/-- Lift a `Finset (Finset W)` to `Set (Set W)` by coercing each inner
    Finset to a Set. -/
def asSetOfSets (E : Finset (Finset W)) : Set (Set W) :=
  (fun s : Finset W => (↑s : Set W)) '' (↑E : Set (Finset W))

@[simp] theorem mem_asSetOfSets {E : Finset (Finset W)} {s : Set W} :
    s ∈ asSetOfSets E ↔ ∃ a ∈ E, (↑a : Set W) = s := by
  simp [asSetOfSets]

/-- `↑(univ \ a) = (↑a)ᶜ`: Finset complement coerces to Set complement. -/
theorem coe_univ_sdiff (a : Finset W) :
    ((Finset.univ \ a : Finset W) : Set W) = (↑a : Set W)ᶜ := by
  rw [Finset.coe_sdiff, Finset.coe_univ, ← Set.compl_eq_univ_diff]

/-- Two Finsets are equal iff their Set coercions are equal. -/
theorem finset_ext_of_coe_eq {a b : Finset W} (h : (↑a : Set W) = ↑b) : a = b := by
  ext w
  have := congrArg (fun (s : Set W) => w ∈ s) h
  simpa using this

/-- Membership in the Finset `inf id` (intersection of a family of Finsets). -/
theorem mem_inf_id_iff {s : Finset (Finset W)} {w : W} :
    w ∈ s.inf id ↔ ∀ a ∈ s, w ∈ a := by
  refine ⟨fun h a ha => ?_, fun h => ?_⟩
  · exact (Finset.le_iff_subset.mp (Finset.inf_le ha)) h
  · exact Finset.singleton_subset_iff.mp
      (Finset.le_iff_subset.mp (Finset.le_inf
        (fun a ha => Finset.le_iff_subset.mpr (Finset.singleton_subset_iff.mpr (h a ha)))))

variable (ALT : Finset (Finset W)) (φ : Finset W)

/-! ### Excludables: the bound on compatible sets -/

/-- Bound on every `IsCompatible` set: the prejacent plus complements
    of every alternative. Every member of any compatible set is either
    `φ` or `aᶜ` for some `a ∈ ALT`, so the powerset of this set is the
    natural search space. -/
def excludables : Finset (Finset W) :=
  insert φ (ALT.image (fun a => Finset.univ \ a))

/-! ### IsCompatible: Spector Def 3.2

Defined as a thin specialization of the Set-side `IsCompatible` under
coercion. The Finset shape is recovered via `isCompatible_iff_finset`,
which also yields the `Decidable` instance. -/

/-- Spector Def 3.2 (Finset-typed). Defined as the Set-side
    `IsCompatible` applied to the coercions of `ALT`, `φ`, and `E`. -/
abbrev IsCompatible (E : Finset (Finset W)) : Prop :=
  Exhaustification.IsCompatible (asSetOfSets ALT) (↑φ) (asSetOfSets E)

/-- Bridge: the abbrev unfolds to the explicit Finset condition. -/
theorem isCompatible_iff_finset (E : Finset (Finset W)) :
    IsCompatible ALT φ E ↔
    E ⊆ excludables ALT φ ∧ φ ∈ E ∧ (E.inf id).Nonempty := by
  unfold IsCompatible Exhaustification.IsCompatible
  refine ⟨?_, ?_⟩
  · rintro ⟨hphi, hform, hcons⟩
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      have : (↑a : Set W) ∈ asSetOfSets E := mem_asSetOfSets.mpr ⟨a, ha, rfl⟩
      rcases hform _ this with hphi_case | ⟨a', ha'_mem, ha_eq⟩
      · rw [finset_ext_of_coe_eq hphi_case]
        exact Finset.mem_insert_self φ _
      · rcases mem_asSetOfSets.mp ha'_mem with ⟨b', hb'_ALT, rfl⟩
        rw [← coe_univ_sdiff] at ha_eq
        rw [finset_ext_of_coe_eq ha_eq]
        exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨b', hb'_ALT, rfl⟩)
    · rcases mem_asSetOfSets.mp hphi with ⟨a, ha_mem, ha_eq⟩
      rwa [finset_ext_of_coe_eq ha_eq] at ha_mem
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
    Decidable (IsCompatible ALT φ E) :=
  decidable_of_iff _ (isCompatible_iff_finset ALT φ E).symm

/-! ### IsMCSet: Spector Def 3.3 -/

/-- Spector Def 3.3 (Finset-typed). Defined as the Set-side `IsMCSet`
    on the coercions. -/
abbrev IsMCSet (E : Finset (Finset W)) : Prop :=
  Exhaustification.IsMCSet (asSetOfSets ALT) (↑φ) (asSetOfSets E)

/-- Bridge: equivalent to the explicit Finset MC-set condition (using
    `excludables.powerset` as the bounded search space, which suffices
    because every compatible set is bounded by `excludables`). -/
theorem isMCSet_iff_finset (E : Finset (Finset W)) :
    IsMCSet ALT φ E ↔
    IsCompatible ALT φ E ∧
    ∀ E' ∈ (excludables ALT φ).powerset,
      IsCompatible ALT φ E' → E ⊆ E' → E' ⊆ E := by
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
    rwa [finset_ext_of_coe_eq hb_eq] at hb_E
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
    have hE'_f_compat : IsCompatible ALT φ E'_f := by
      show Exhaustification.IsCompatible (asSetOfSets ALT) (↑φ) (asSetOfSets E'_f)
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
    Decidable (IsMCSet ALT φ E) :=
  decidable_of_iff _ (isMCSet_iff_finset ALT φ E).symm

/-! ### IE: Spector Def 3.4

`IE` is the set of alternatives in every MC-set. On the Finset side it
is a `Finset` (filter from `excludables`); membership corresponds to
membership in the Set-side `Exhaustification.IE`. -/

/-- Spector Def 3.4: `IE = {ψ : ψ is in every MC-set}`. Bounded by
    `excludables`, since every MC-set is a subset of `excludables`. -/
def IE : Finset (Finset W) :=
  (excludables ALT φ).filter fun ψ =>
    ∀ E ∈ (excludables ALT φ).powerset, IsMCSet ALT φ E → ψ ∈ E

/-- The innocently-excludable alternatives: `a ∈ ALT` such that `aᶜ ∈ IE`.
    For each such `a`, exhaustification negates `a` (asserts `aᶜ`). -/
def innocentlyExcludable : Finset (Finset W) :=
  ALT.filter (fun a => (Finset.univ \ a) ∈ IE ALT φ)

theorem innocentlyExcludable_subset (ALT : Finset (Finset W)) (φ : Finset W) :
    innocentlyExcludable ALT φ ⊆ ALT := Finset.filter_subset _ _

/-- The prejacent is in every MC-set (it's in every compatible set), hence in `IE`.
    Specialization of `Exhaustification.phi_mem_IE` to the Finset side. -/
theorem phi_mem_IE : φ ∈ IE ALT φ := by
  unfold IE
  refine Finset.mem_filter.mpr ⟨Finset.mem_insert_self φ _, ?_⟩
  intro E _ hMC
  exact ((isCompatible_iff_finset ALT φ E).mp hMC.1).2.1

/-! ### IsInnocentlyExcludable: bridge + decidability

The Set-typed `Exhaustification.IsInnocentlyExcludable a` requires
`a ∈ ALT` AND `aᶜ ∈ IE`. The Finset side already has
`innocentlyExcludable ALT φ` as a Finset (alternatives whose complements
are in `IE`). Bridge theorem + Decidable instance below. -/

/-- Bridge: Set-side `IsInnocentlyExcludable` on the coercion ↔
    Finset-side membership in `innocentlyExcludable`. -/
theorem isInnocentlyExcludable_iff (a : Finset W) :
    Exhaustification.IsInnocentlyExcludable
      (asSetOfSets ALT) (↑φ) (↑a) ↔
    a ∈ innocentlyExcludable ALT φ := by
  unfold Exhaustification.IsInnocentlyExcludable innocentlyExcludable
  refine ⟨?_, ?_⟩
  · rintro ⟨hMem, hIE⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rcases mem_asSetOfSets.mp hMem with ⟨b, hb_ALT, hb_eq⟩
      rwa [finset_ext_of_coe_eq hb_eq] at hb_ALT
    · -- aᶜ as a Set equals (Finset.univ \ a) coerced
      rw [show ((↑a : Set W)ᶜ : Set W) = ((Finset.univ \ a : Finset W) : Set W)
          from (coe_univ_sdiff a).symm] at hIE
      -- Bridge: Set-IE membership of the coerced Finset complement →
      -- Finset-IE membership. This requires the Set-IE / Finset-IE bridge,
      -- which follows from MC-set bridges already in scope.
      unfold IE
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · -- (Finset.univ \ a) ∈ excludables ALT φ (by membership of a in ALT)
        have ha_ALT : a ∈ ALT := by
          rcases mem_asSetOfSets.mp hMem with ⟨b, hb_ALT, hb_eq⟩
          rwa [finset_ext_of_coe_eq hb_eq] at hb_ALT
        exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a, ha_ALT, rfl⟩)
      · intro E _ hE_mc
        have hE_set : Exhaustification.IsMCSet
            (asSetOfSets ALT) (↑φ) (asSetOfSets E) := hE_mc
        have h_aux := hIE _ hE_set
        rcases mem_asSetOfSets.mp h_aux with ⟨b, hb_E, hb_eq⟩
        have : b = Finset.univ \ a := by
          apply finset_ext_of_coe_eq
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
          have hE_compat : Exhaustification.IsCompatible
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
      have hE_f_mc : IsMCSet ALT φ E_f := by
        show Exhaustification.IsMCSet (asSetOfSets ALT) (↑φ) (asSetOfSets E_f)
        rw [hE_f_eq]; exact hE_set_mc
      have h_in_E_f : Finset.univ \ a ∈ E_f :=
        (Finset.mem_filter.mp ha.2).2 E_f hE_f_powerset hE_f_mc
      have h_in_E : (((Finset.univ \ a : Finset W) : Set W)) ∈ E := by
        rw [← hE_f_eq]; exact mem_asSetOfSets.mpr ⟨_, h_in_E_f, rfl⟩
      exact h_in_E

/-- `IsInnocentlyExcludable` is decidable on the Finset side via the
    bridge to `innocentlyExcludable` membership. -/
instance decidableIsInnocentlyExcludable (a : Finset W) :
    Decidable (Exhaustification.IsInnocentlyExcludable
      (asSetOfSets ALT) (↑φ) (↑a)) :=
  decidable_of_iff _ (isInnocentlyExcludable_iff ALT φ a).symm

/-! ### Cell: bridge + decidability

The Set-typed `Exhaustification.cell` predicate at world `w` requires:
`w ∈ φ ∧ (∀q IE, w ∉ q) ∧ (∀ r ∈ nonExcludable, w ∈ r)`. The Finset
version `cellFinset` enumerates worlds satisfying this; bridge below
recovers the Set predicate from Finset membership. -/

/-- Finset-side cell witness predicate at a world. Decidable by
    construction (all quantifications are over Finsets). -/
def cellFinset : Finset W :=
  Finset.univ.filter fun w =>
    w ∈ φ ∧
    (∀ a ∈ innocentlyExcludable ALT φ, w ∉ a) ∧
    (∀ r ∈ ALT \ innocentlyExcludable ALT φ, w ∈ r)

/-- Bridge: Finset-side `cellFinset` membership ↔ Set-side `cell`
    predicate. Lets `decide` proofs of cell-witness facts on the
    Finset side discharge Set-typed cell-witness hypotheses required
    by the general substrate theorems
    (`Operators/InnocentInclusion.lean::mem_II_of_cell_witness`,
    `exhIEII_implies_cell_witnessed_alt`, etc.). -/
theorem mem_cellFinset_iff (w : W) :
    w ∈ cellFinset ALT φ ↔ Exhaustification.cell (asSetOfSets ALT) (↑φ) w := by
  unfold cellFinset Exhaustification.cell Exhaustification.nonExcludable
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
      have ha_set_ie : Exhaustification.IsInnocentlyExcludable
          (asSetOfSets ALT) (↑φ) (↑a) :=
        (isInnocentlyExcludable_iff ALT φ a).mpr ha
      exact hexcl _ ha_set_ie hw_a
    · intro r hr
      rcases Finset.mem_sdiff.mp hr with ⟨hr_ALT, hr_not_ie⟩
      have hr_set_alt : (↑r : Set W) ∈ asSetOfSets ALT :=
        mem_asSetOfSets.mpr ⟨r, hr_ALT, rfl⟩
      have hr_not_ie_set : ¬ Exhaustification.IsInnocentlyExcludable
          (asSetOfSets ALT) (↑φ) (↑r) := by
        intro h
        exact hr_not_ie ((isInnocentlyExcludable_iff ALT φ r).mp h)
      exact hne (↑r) ⟨hr_set_alt, hr_not_ie_set⟩

/-- `Exhaustification.cell` on the Finset coercion is decidable via the
    bridge to `cellFinset` membership. -/
instance decidableCell (w : W) :
    Decidable (Exhaustification.cell (asSetOfSets ALT) (↑φ) w) :=
  decidable_of_iff _ (mem_cellFinset_iff ALT φ w)

end Exhaustification.Innocent
