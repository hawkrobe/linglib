import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.WellFounded

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

namespace Exhaustification

variable {World : Type*} (ALT : Set (Set World))

/-- `u ≤[ALT] v` when every alternative true at `u` is true at `v`. -/
def leALT (u v : World) : Prop := ∀ a ∈ ALT, a u → a v

/-- `u <[ALT] v` when `u` verifies strictly fewer alternatives than `v`. -/
def ltALT (u v : World) : Prop := leALT ALT u v ∧ ¬ leALT ALT v u

@[inherit_doc] notation:50 u " ≤[" ALT "] " v => leALT ALT u v
@[inherit_doc] notation:50 u " <[" ALT "] " v => ltALT ALT u v

theorem leALT_refl (u : World) : u ≤[ALT] u := λ _ _ h => h

theorem leALT_trans (u v w : World) (huv : u ≤[ALT] v) (hvw : v ≤[ALT] w) : u ≤[ALT] w :=
  λ a ha hau => hvw a ha (huv a ha hau)

variable (φ : Set World)

/-- The minimal-world exhaustifier: the prejacent worlds with no prejacent world strictly
below them. -/
def exhMW : Set World := λ u => φ u ∧ ¬ ∃ v, φ v ∧ (v <[ALT] u)

/-- A minimal prejacent world. -/
def IsMinimal (u : World) : Prop := u ∈ exhMW ALT φ

theorem exhMW_subset : exhMW ALT φ ⊆ φ := λ _ ⟨h, _⟩ => h

/-- For finite `ALT` the strict order is well-founded: it is the pullback of strict inclusion
along the finite set of alternatives a world verifies. -/
theorem ltALT_wf_of_finite (hfin : ALT.Finite) : WellFounded (ltALT ALT) := by
  classical
  have hfin' : ∀ w, {a ∈ ALT | a w}.Finite := λ w => hfin.subset λ _ h => h.1
  let f : World → Finset (Set World) := λ w => (hfin' w).toFinset
  have hmem : ∀ w a, a ∈ f w ↔ a ∈ ALT ∧ a w := λ w a => Set.Finite.mem_toFinset (hfin' w)
  have hle : ∀ u v, leALT ALT u v ↔ f u ⊆ f v := by
    intro u v
    simp only [leALT, Finset.subset_iff, hmem]
    exact ⟨λ h a ha => ⟨ha.1, h a ha.1 ha.2⟩, λ h a ha hau => (h ⟨ha, hau⟩).2⟩
  have : ltALT ALT = InvImage (· ⊂ ·) f := by
    ext u v
    simp only [ltALT, hle, InvImage, Finset.ssubset_iff_subset_ne]
    exact and_congr_right λ h => ⟨λ hn heq => hn (heq ▸ le_rfl), λ hne h' => hne (le_antisymm h h')⟩
  rw [this]
  exact InvImage.wf f IsWellFounded.wf

/-- A satisfiable prejacent has a minimal world when `ALT` is finite. -/
theorem exists_minimal_of_finite (hfin : ALT.Finite) (hsat : ∃ w, φ w) :
    ∃ u, IsMinimal ALT φ u :=
  let ⟨u, hu, hmin⟩ := (ltALT_wf_of_finite ALT hfin).has_min {w | φ w} hsat
  ⟨u, hu, λ ⟨v, hv, hlt⟩ => hmin v hv hlt⟩

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
  refine ⟨λ ⟨hu, hmin⟩ => ⟨hu, ?_⟩, λ ⟨hu, v, hv, hvu, huv⟩ => ⟨hu, ?_⟩⟩
  · obtain ⟨v, hv, hvu⟩ := hM.le u hu
    exact ⟨v, hv, hvu, not_not.1 λ h => hmin ⟨v, hM.mem v hv, hvu, h⟩⟩
  · rintro ⟨x, hx, hxu, hnux⟩
    obtain ⟨v', hv', hv'x⟩ := hM.le x hx
    exact hnux (leALT_trans ALT _ _ _ huv (leALT_trans ALT _ _ _
      (hM.antisymm v hv v' hv' (leALT_trans ALT _ _ _ hv'x (leALT_trans ALT _ _ _ hxu huv))) hv'x))

end Exhaustification
