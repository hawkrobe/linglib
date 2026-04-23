import Linglib.Theories.Semantics.Exhaustification.Operators.Basic
import Linglib.Theories.Semantics.Exhaustification.Excluder
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Innocent Exclusion (Fox 2007), computable refinement
@cite{fox-2007} @cite{spector-2016}

Fox's innocent-exclusion algorithm packaged as an `Excluder`. This file
is the **`Finset`-typed computable refinement** of the canonical
Set-side definitions in `Operators/Basic.lean`. There is no parallel
theory: `Innocent.IsCompatible`/`IsMCSet` are `abbrev`s over their
Set-side counterparts under the standard `Finset → Set` coercion. The
Finset characterization is recovered as a bridge `iff`, which also
provides the `Decidable` instances needed for `Excluder.exh` to compute.

Worlds are an arbitrary `[Fintype W] [DecidableEq W]`. A proposition is
a `Finset W`. An alternative collection is a `Finset (Finset W)`.
Exhaustification returns a `Finset W`.

## Architecture

The Set-side `Exhaustification.IsCompatible`/`IsMCSet`/`IE` (defined in
`Operators/Basic.lean`) are the canonical specifications. Here we:

1. Define `asSetOfSets : Finset (Finset W) → Set (Set W)` as the obvious
   coercion (lift each inner Finset to a Set, take the image).
2. Define `Innocent.IsCompatible E := Exhaustification.IsCompatible (asSetOfSets ALT) ↑φ (asSetOfSets E)`
   and similarly for `IsMCSet`. These are `abbrev`s, so any Set-side
   theorem about `IsCompatible`/`IsMCSet` automatically applies.
3. Prove bridge `iff`s to the explicit Finset characterizations:
   `IsCompatible ↔ E ⊆ excludables ∧ φ ∈ E ∧ (E.inf id).Nonempty`, etc.
4. Derive `Decidable` instances via the bridges (the Finset
   characterization is decidable by construction).
5. Define `IE`/`innocentlyExcludable` as `Finset` filters using the
   derived `Decidable` instances.

This is the standard mathlib pattern for "abstract spec + computable
refinement" (cf. `Set.Finite` + `Set.Finite.toFinset`,
`Set.image` + `Finset.image`, etc.).

## Key definitions

- `excludables ALT φ` — bound on every `IsCompatible` witness
- `IsCompatible ALT φ E` — Spector Definition 3.2 (Finset-typed,
  defined as a Set-side abbrev)
- `IsMCSet ALT φ E` — Spector Definition 3.3 (similarly)
- `IE ALT φ` — Spector Definition 3.4: alternatives in every MC-set
- `innocentlyExcludable ALT φ` — alternatives whose complement is in `IE`
- `Exhaustification.innocent : Excluder W` — the `Excluder` package

Consumers call `innocent.exh ALT φ` for the exhaustified meaning.
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

/-- Membership in `s.inf id : Finset W` for `s : Finset (Finset W)` is
    membership in every element. -/
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
      simpa using hu _ this
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
      simpa using hu a ha_mem

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

end Exhaustification.Innocent

namespace Exhaustification

/-- The Fox 2007 innocent-exclusion excluder. The `Excluder` package
    around `Innocent.innocentlyExcludable`; `innocent.exh ALT φ` is the
    exhaustified meaning. -/
def innocent {W : Type*} [Fintype W] [DecidableEq W] : Excluder W where
  excluded := Innocent.innocentlyExcludable
  excluded_subset := Innocent.innocentlyExcludable_subset

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- **Vacuity**: when no alternative is innocently excludable,
    `innocent.exh` returns the prejacent unchanged. -/
theorem innocent_exh_eq_phi_of_innocentlyExcludable_empty
    {ALT : Finset (Finset W)} {φ : Finset W}
    (h : Innocent.innocentlyExcludable ALT φ = ∅) :
    innocent.exh ALT φ = φ := by
  show φ \ ((Innocent.innocentlyExcludable ALT φ).biUnion id) = φ
  rw [h]
  simp

end Exhaustification
