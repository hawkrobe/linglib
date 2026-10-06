module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.WellFounded

/-!
# Alternatives and minimal worlds

A set of alternatives `ALT : Set (Set World)` preorders worlds by the alternatives they
verify: `u ≤[ALT] v` when every alternative true at `u` is true at `v`. The minimal-world
exhaustifier `exhMW` keeps the prejacent worlds that are minimal in this preorder; for finite
`ALT` the strict order is well-founded, so a satisfiable prejacent has minimal worlds. A set
of prejacent worlds is an `IsMinimalCover` when it represents the minimal worlds up to
equivalence; the exhaustifiers of `InnocentExclusion` and `InnocentInclusion` are computed
from one.

## References

* [groenendijk-stokhof-1984]
* [spector-2016]
-/

@[expose] public section

namespace Exhaustification

variable {World : Type*} (ALT : Set (Set World))

/-- `u ≤[ALT] v` holds when every alternative true at `u` is true at `v`. -/
def leALT (u v : World) : Prop := ∀ a ∈ ALT, a u → a v

/-- `u <[ALT] v` holds when `u` verifies strictly fewer alternatives than `v`. -/
def ltALT (u v : World) : Prop := leALT ALT u v ∧ ¬ leALT ALT v u

@[inherit_doc] notation:50 u " ≤[" ALT "] " v => leALT ALT u v
@[inherit_doc] notation:50 u " <[" ALT "] " v => ltALT ALT u v

theorem leALT_iff {u v : World} : (u ≤[ALT] v) ↔ ∀ a ∈ ALT, u ∈ a → v ∈ a := Iff.rfl

theorem leALT_refl (u : World) : u ≤[ALT] u := fun _ _ h ↦ h

theorem leALT_trans (u v w : World) (huv : u ≤[ALT] v) (hvw : v ≤[ALT] w) : u ≤[ALT] w :=
  fun a ha hau ↦ hvw a ha (huv a ha hau)

variable (φ : Set World)

/-- The minimal-world exhaustifier keeps the prejacent worlds with no prejacent world strictly
below them. -/
def exhMW : Set World := fun u ↦ φ u ∧ ¬ ∃ v, φ v ∧ (v <[ALT] u)

theorem mem_exhMW {u : World} : u ∈ exhMW ALT φ ↔ u ∈ φ ∧ ¬∃ v ∈ φ, v <[ALT] u := Iff.rfl

/-- A world is minimal when it is a prejacent world with no prejacent world strictly below it. -/
def IsMinimal (u : World) : Prop := u ∈ exhMW ALT φ

theorem exhMW_subset : exhMW ALT φ ⊆ φ := fun _ ⟨h, _⟩ ↦ h

/-- For finite `ALT` the strict order is well-founded, being the pullback of strict inclusion
along the finite set of alternatives a world verifies. -/
theorem ltALT_wf_of_finite (hfin : ALT.Finite) : WellFounded (ltALT ALT) := by
  classical
  have hfin' : ∀ w, {a ∈ ALT | a w}.Finite := fun w ↦ hfin.subset fun _ h ↦ h.1
  let f : World → Finset (Set World) := fun w ↦ (hfin' w).toFinset
  have hmem : ∀ w a, a ∈ f w ↔ a ∈ ALT ∧ a w := fun w a ↦ Set.Finite.mem_toFinset (hfin' w)
  have hle : ∀ u v, leALT ALT u v ↔ f u ⊆ f v := by
    intro u v
    simp only [leALT, Finset.subset_iff, hmem]
    exact ⟨fun h a ha ↦ ⟨ha.1, h a ha.1 ha.2⟩, fun h a ha hau ↦ (h ⟨ha, hau⟩).2⟩
  have : ltALT ALT = InvImage (· ⊂ ·) f := by
    ext u v
    simp only [ltALT, hle, InvImage, Finset.ssubset_iff_subset_ne]
    exact and_congr_right fun h ↦
      ⟨fun hn heq ↦ hn (heq ▸ le_rfl), fun hne h' ↦ hne (le_antisymm h h')⟩
  rw [this]
  exact InvImage.wf f Finset.isWellFounded_ssubset

/-- A satisfiable prejacent has a minimal world when `ALT` is finite. -/
theorem exists_minimal_of_finite (hfin : ALT.Finite) (hsat : ∃ w, φ w) :
    ∃ u, IsMinimal ALT φ u :=
  let ⟨u, hu, hmin⟩ := (ltALT_wf_of_finite ALT hfin).has_min {w | φ w} hsat
  ⟨u, hu, fun ⟨v, hv, hlt⟩ ↦ hmin v hv hlt⟩

/-- Every prejacent world lies above a minimal one when `ALT` is finite. -/
theorem exists_isMinimal_le (hfin : ALT.Finite) {w : World} (hw : φ w) :
    ∃ u, IsMinimal ALT φ u ∧ u ≤[ALT] w :=
  let ⟨u, ⟨hu, huw⟩, hmin⟩ :=
    (ltALT_wf_of_finite ALT hfin).has_min {v | φ v ∧ v ≤[ALT] w} ⟨w, hw, leALT_refl ALT w⟩
  ⟨u, ⟨hu, fun ⟨v, hv, hlt⟩ ↦ hmin v ⟨hv, leALT_trans ALT v u w hlt.1 huw⟩ hlt⟩, huw⟩

/-- Against all propositions every prejacent world is minimal, since a world verifying every
proposition true at another is that world, whose singleton is a proposition. -/
theorem exhMW_univ : exhMW Set.univ φ = φ := by
  refine Set.Subset.antisymm (exhMW_subset _ _) fun u hu ↦ ⟨hu, ?_⟩
  rintro ⟨v, -, hle, hnle⟩
  obtain rfl : u = v := hle {v} trivial rfl
  exact hnle (leALT_refl _ u)

/-! ### Representative minimal worlds -/

/-- A set of prejacent worlds represents the minimal worlds when every prejacent world lies
above one of its members and no member lies strictly below another. -/
structure IsMinimalCover (M : Set World) : Prop where
  mem : ∀ v ∈ M, φ v
  le : ∀ w, φ w → ∃ v ∈ M, v ≤[ALT] w
  antisymm : ∀ v ∈ M, ∀ u ∈ M, (u ≤[ALT] v) → v ≤[ALT] u

variable {ALT φ} {M : Set World}

/-- The minimal worlds are the prejacent worlds equivalent to a representative. -/
theorem IsMinimalCover.exhMW_eq (hM : IsMinimalCover ALT φ M) :
    exhMW ALT φ = {u | φ u ∧ ∃ v ∈ M, (v ≤[ALT] u) ∧ (u ≤[ALT] v)} := by
  ext u
  refine ⟨fun ⟨hu, hmin⟩ ↦ ⟨hu, ?_⟩, fun ⟨hu, v, hv, hvu, huv⟩ ↦ ⟨hu, ?_⟩⟩
  · obtain ⟨v, hv, hvu⟩ := hM.le u hu
    exact ⟨v, hv, hvu, not_not.1 fun h ↦ hmin ⟨v, hM.mem v hv, hvu, h⟩⟩
  · rintro ⟨x, hx, hxu, hnux⟩
    obtain ⟨v', hv', hv'x⟩ := hM.le x hx
    exact hnux (leALT_trans ALT _ _ _ huv (leALT_trans ALT _ _ _
      (hM.antisymm v hv v' hv' (leALT_trans ALT _ _ _ hv'x (leALT_trans ALT _ _ _ hxu huv))) hv'x))

end Exhaustification
