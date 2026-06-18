import Linglib.Semantics.Modality.Orthologic.Frames
import Linglib.Core.Order.Ortholattice
import Linglib.Core.Order.Orthoframe
import Mathlib.Data.SetLike.Basic

/-!
# Regular Propositions of a Compatibility Frame
[holliday-mandelkern-2024]

The bundled type `RegularProp F` of `◇`-regular subsets of a compatibility
frame `F`, equipped with its `OrthocomplementedLattice` structure.

## Construction

`RegularProp F` is a bundled structure (mathlib `Submodule`/`SetLike`
pattern) wrapping a `Set S` together with its regularity proof. The
underlying mathematical object is `(regularClosure F).fixedPoints` —
the fixed points of the `c_◇` closure operator (Holliday–Mandelkern
footnote 19); this file proves the lattice operations on these fixed
points form an orthocomplemented lattice.

The four `OrthocomplementedLattice` axioms:

| axiom | difficulty | uses regularity? |
|-------|------------|------------------|
| `compl_antitone`  | trivial from `orthoNeg` def      | no  |
| `inf_compl_le_bot`| one-liner via reflexivity         | no  |
| `top_le_sup_compl`| from `orthoNeg²` containment       | no  |
| `compl_compl`     | the substantive theorem (Prop 4.8) | YES |

The load-bearing fact is `orthoNeg_orthoNeg_of_isRegular` — the
involutivity of `orthoNeg` on regular sets, which is precisely
Holliday–Mandelkern's Proposition 4.8.

## Architecture

This file depends on:
- `Linglib.Semantics.Modality.Orthologic.Frames` — substrate
  (compatibility frames, `orthoNeg`, `disj`, `IsRegular`, `regularClosure`).
- `Linglib.Core.Order.Ortholattice` — abstract `OrthocomplementedLattice`
  typeclass.

The `RegularProp F` carrier is the natural mathlib subobject for any
future ortholattice consumer (BSML, inquisitive semantics, truthmaker
semantics — all of which traffic in non-Boolean propositional algebras).
-/

namespace Orthologic

variable {S : Type*} {F : CompatFrame S}

/-! ### Closure-under-regularity helpers -/

/-- The orthocomplement of any set is regular (whether or not the original set is). -/
theorem orthoNeg_isRegular (F : CompatFrame S) (A : Set S) :
    IsRegular F (orthoNeg F A) := by
  intro x
  by_cases h : x ∈ orthoNeg F A
  · exact Or.inl h
  · right
    rw [mem_orthoNeg] at h
    push Not at h
    obtain ⟨y, hxy, hyA⟩ := h
    refine ⟨y, hxy, fun z hyz hzN => ?_⟩
    rw [mem_orthoNeg] at hzN
    exact hzN y (hyz.symm) hyA

/-- Regular sets are closed under intersection. -/
theorem inter_isRegular {F : CompatFrame S} {A B : Set S}
    (hA : IsRegular F A) (hB : IsRegular F B) : IsRegular F (A ∩ B) := by
  intro x
  by_cases h : x ∈ A ∩ B
  · exact Or.inl h
  · right
    rw [Set.mem_inter_iff, not_and_or] at h
    rcases h with hxA | hxB
    · rcases hA x with hAx | ⟨y, hxy, hy⟩
      · exact absurd hAx hxA
      · exact ⟨y, hxy, fun z hyz hz => hy z hyz hz.1⟩
    · rcases hB x with hBx | ⟨y, hxy, hy⟩
      · exact absurd hBx hxB
      · exact ⟨y, hxy, fun z hyz hz => hy z hyz hz.2⟩

/-- The disjunction `disj F A B = orthoNeg F (orthoNeg F A ∩ orthoNeg F B)`
    is regular (immediate from `orthoNeg_isRegular`). -/
theorem disj_isRegular (F : CompatFrame S) (A B : Set S) :
    IsRegular F (disj F A B) :=
  orthoNeg_isRegular F _

/-- The empty set is regular (vacuously: take `y = x` by reflexivity). -/
theorem empty_isRegular (F : CompatFrame S) : IsRegular F (∅ : Set S) := by
  intro x
  exact Or.inr ⟨x, F.refl x, fun _ _ h => h.elim⟩

/-- The full set is regular (trivially). -/
theorem univ_isRegular (F : CompatFrame S) : IsRegular F (Set.univ : Set S) :=
  fun _ => Or.inl trivial

/-- The load-bearing involutivity: `orthoNeg² A = A` for regular `A`.
    [holliday-mandelkern-2024] Proposition 4.8. -/
theorem orthoNeg_orthoNeg_of_isRegular (F : CompatFrame S) {A : Set S}
    (hA : IsRegular F A) : orthoNeg F (orthoNeg F A) = A := by
  apply Set.eq_of_subset_of_subset
  · intro x hx
    rcases hA x with hxA | ⟨y, hxy, hy⟩
    · exact hxA
    · exfalso
      rw [mem_orthoNeg] at hx
      have hyN : ¬ y ∈ orthoNeg F A := hx y hxy
      rw [mem_orthoNeg] at hyN
      push Not at hyN
      obtain ⟨z, hyz, hzA⟩ := hyN
      exact hy z hyz hzA
  · intro x hxA
    rw [mem_orthoNeg]
    intro y hxy
    rw [mem_orthoNeg]
    push Not
    exact ⟨x, hxy.symm, hxA⟩

/-! ### The Bundled Type RegularProp F -/

/-- A regular proposition of a compatibility frame `F`: a `Set S` satisfying
    the `◇`-regularity condition. Bundled as a structure with `SetLike`
    instance, mirroring mathlib's subobject pattern (`Submodule`, `Subgroup`,
    `Subalgebra`). -/
@[ext]
structure RegularProp (F : CompatFrame S) where
  /-- The underlying set of the regular proposition. -/
  carrier : Set S
  /-- The regularity proof. -/
  regular' : IsRegular F carrier

namespace RegularProp

instance : SetLike (RegularProp F) S where
  coe := RegularProp.carrier
  coe_injective := by
    rintro ⟨A, _⟩ ⟨B, _⟩ (rfl : A = B)
    rfl

@[simp] theorem mem_mk (A : Set S) (hA : IsRegular F A) (x : S) :
    x ∈ (⟨A, hA⟩ : RegularProp F) ↔ x ∈ A := Iff.rfl

@[simp] theorem coe_mk (A : Set S) (hA : IsRegular F A) :
    ((⟨A, hA⟩ : RegularProp F) : Set S) = A := rfl

theorem regular (A : RegularProp F) : IsRegular F (A : Set S) := A.regular'

/-! ### Lattice Operations -/

instance : Min (RegularProp F) where
  min A B := ⟨(A : Set S) ∩ (B : Set S), inter_isRegular A.regular B.regular⟩

instance : Max (RegularProp F) where
  max A B := ⟨disj F (A : Set S) (B : Set S), disj_isRegular F _ _⟩

instance : Bot (RegularProp F) where
  bot := ⟨∅, empty_isRegular F⟩

instance : Top (RegularProp F) where
  top := ⟨Set.univ, univ_isRegular F⟩

instance : Compl (RegularProp F) where
  compl A := ⟨orthoNeg F (A : Set S), orthoNeg_isRegular F _⟩

@[simp] theorem coe_inf (A B : RegularProp F) :
    ((A ⊓ B : RegularProp F) : Set S) = (A : Set S) ∩ (B : Set S) := rfl

@[simp] theorem coe_sup (A B : RegularProp F) :
    ((A ⊔ B : RegularProp F) : Set S) = disj F (A : Set S) (B : Set S) := rfl

@[simp] theorem coe_bot : ((⊥ : RegularProp F) : Set S) = ∅ := rfl

@[simp] theorem coe_top : ((⊤ : RegularProp F) : Set S) = Set.univ := rfl

@[simp] theorem coe_compl (A : RegularProp F) :
    ((Aᶜ : RegularProp F) : Set S) = orthoNeg F (A : Set S) := rfl

/-! ### Lattice + BoundedOrder Instance -/

instance : PartialOrder (RegularProp F) := PartialOrder.ofSetLike (RegularProp F) S

instance : Lattice (RegularProp F) where
  inf := (· ⊓ ·)
  sup := (· ⊔ ·)
  inf_le_left A B := fun _ hx => hx.1
  inf_le_right A B := fun _ hx => hx.2
  le_inf A B C hAB hAC := fun x hx => ⟨hAB hx, hAC hx⟩
  le_sup_left A B := by
    intro x hxA
    show x ∈ disj F (A : Set S) (B : Set S)
    intro y hxy hy
    exact hy.1 x (hxy.symm) hxA
  le_sup_right A B := by
    intro x hxB
    show x ∈ disj F (A : Set S) (B : Set S)
    intro y hxy hy
    exact hy.2 x (hxy.symm) hxB
  sup_le A B C hAC hBC := by
    intro x hx
    -- hx : x ∈ disj F A.carrier B.carrier
    by_contra hxC
    rcases C.regular x with hxC' | ⟨y, hxy, hy⟩
    · exact hxC hxC'
    · have habs : ¬ (y ∈ orthoNeg F (A : Set S) ∩ orthoNeg F (B : Set S)) :=
        hx y hxy
      rw [Set.mem_inter_iff, not_and_or] at habs
      rcases habs with hyN | hyN
      all_goals
        rw [mem_orthoNeg] at hyN
        push Not at hyN
      · obtain ⟨z, hyz, hzA⟩ := hyN
        exact hy z hyz (hAC hzA)
      · obtain ⟨z, hyz, hzB⟩ := hyN
        exact hy z hyz (hBC hzB)

instance : BoundedOrder (RegularProp F) where
  bot_le := fun _ _ hx => hx.elim
  le_top := fun _ _ _ => trivial

/-! ### OrthocomplementedLattice Instance -/

instance instOrthocomplementedLattice : OrthocomplementedLattice (RegularProp F) where
  compl_compl A := SetLike.coe_injective <|
    orthoNeg_orthoNeg_of_isRegular F A.regular
  compl_antitone {A B} hAB := by
    intro x hxBN y hxy hyA
    exact hxBN y hxy (hAB hyA)
  inf_compl_le_bot A := by
    intro x hx
    exact hx.2 x (F.refl x) hx.1
  top_le_sup_compl A := by
    intro x _
    show x ∈ disj F (A : Set S) (orthoNeg F (A : Set S))
    intro y hxy hy
    -- hy : y ∈ orthoNeg F A ∩ orthoNeg F (orthoNeg F A)
    -- Apply hy.2 (= y ∈ orthoNeg² A) at z = y via reflexivity:
    -- y ∉ orthoNeg F A. Contradicts hy.1.
    exact hy.2 y (F.refl y) hy.1

end RegularProp

/-! ### Bridge to the abstract orthoframe construction -/

open Order

/-- The orthogonality (incompatibility) orthoframe of a compatibility frame:
    `x ⊥ y ↔ ¬ compat x y`. Symmetry and irreflexivity come from symmetry and
    reflexivity of `compat`. -/
def CompatFrame.toOrthoframe (F : CompatFrame S) : Orthoframe S where
  ortho x y := ¬ F.compat x y
  ortho_symm := ⟨fun _ _ h hc => h hc.symm⟩
  ortho_irrefl := ⟨fun a h => h (F.refl a)⟩

/-- `orthoNeg` is the `upperPolar` of the orthogonality relation. -/
theorem orthoNeg_eq_upperPolar (F : CompatFrame S) (A : Set S) :
    orthoNeg F A = upperPolar F.toOrthoframe.ortho A := by
  ext x
  constructor
  · intro hx a ha hc
    exact hx a hc.symm ha
  · intro hx y hxy hyA
    exact hx hyA hxy.symm

/-- `IsRegular` is the double-orthonegation fixed-point condition. -/
theorem isRegular_iff_orthoNeg_orthoNeg (F : CompatFrame S) (A : Set S) :
    IsRegular F A ↔ orthoNeg F (orthoNeg F A) = A :=
  ⟨orthoNeg_orthoNeg_of_isRegular F, fun h => h ▸ orthoNeg_isRegular F _⟩

/-- The `◇`-regular sets of `F` are exactly the concept extents of its
    orthogonality relation; Holliday–Mandelkern's Proposition 4.8 is mathlib's
    `upperPolar_lowerPolar_upperPolar` (see `Core.Order.Orthoframe`). -/
theorem isRegular_iff_isExtent (F : CompatFrame S) (A : Set S) :
    IsRegular F A ↔ IsExtent F.toOrthoframe.ortho A := by
  rw [isRegular_iff_orthoNeg_orthoNeg, isExtent_iff,
      orthoNeg_eq_upperPolar, orthoNeg_eq_upperPolar,
      upperPolar_eq_lowerPolar F.toOrthoframe.ortho]

/-- **The bridge.** `RegularProp F` is order-isomorphic to the ortholattice of
    regular propositions of its orthogonality orthoframe (`Orthoframe.Regular`) —
    i.e. the concept extents of `¬ compat`. The hand-built
    `OrthocomplementedLattice (RegularProp F)` and the abstract `Concept`-based
    one coincide. -/
def RegularProp.equivReg (F : CompatFrame S) :
    RegularProp F ≃o Orthoframe.Regular F.toOrthoframe where
  toFun A := Concept.ofIsExtent F.toOrthoframe.ortho A.carrier
    ((isRegular_iff_isExtent F A.carrier).mp A.regular')
  invFun c := ⟨c.extent, (isRegular_iff_isExtent F c.extent).mpr c.isExtent_extent⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => Concept.ext rfl
  map_rel_iff' := Iff.rfl

end Orthologic
