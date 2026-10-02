module

public import Linglib.Logic.Aristotelian.Basic
public import Mathlib.Order.BooleanSubalgebra

/-!
# Isomorphisms of Aristotelian diagrams

An *Aristotelian diagram* is a fragment of a Boolean algebra, here an indexed family
`φ : ι → α`. Demey and Smessaert call a bijection of corners an *Aristotelian isomorphism* when
it preserves and reflects the four Aristotelian relations, and a *Boolean isomorphism* when it
extends to an order isomorphism of the Boolean closures. Every Boolean isomorphism is an
Aristotelian one but not conversely, as their Keynes–Johnson octagons show. Aristotelian
isomorphisms form a groupoid, the core of De Klerck, Vignero and Demey's category of
Aristotelian diagrams.

## Main definitions

* `AristotelianIso`, with `refl`, `symm` and `trans`.
* `BooleanIso`, with `refl`, `symm` and `trans`.

## Main results

* `BooleanIso.toAristotelianIso`: every Boolean isomorphism is an Aristotelian isomorphism.

## Implementation notes

The family `φ : ι → α` stands in for the paper's set `F ⊆ α`, and a corner bijection is a
bijection of index types. `AristotelianIso` asks for `Disjoint`, `Codisjoint` and `<` to be
preserved and reflected. This is equivalent to asking it of the four relations, since each of
`IsCompl`, `IsContrary`, `IsSubcontrary` and `<` is a Boolean combination of the three, and
conversely (`disjoint_iff_isCompl_or_isContrary`, `codisjoint_iff_isCompl_or_isSubcontrary`).

## References

* [demey-smessaert-2018]
* [demey-smessaert-2024]
* [deklerck-vignero-demey-2024]
-/

@[expose] public section

namespace BooleanSubalgebra
variable {β : Type*} [BooleanAlgebra β] {L : BooleanSubalgebra β} {a b : L}

/-- `Disjoint` transfers across a Boolean subalgebra's coercion.
UPSTREAM: belongs in `Mathlib.Order.BooleanSubalgebra`, cf. `Complementeds.disjoint_coe`. -/
@[simp, norm_cast] theorem disjoint_coe : Disjoint (a : β) b ↔ Disjoint a b := by
  rw [disjoint_iff, disjoint_iff, ← val_inf, ← val_bot, Subtype.coe_inj]

/-- `Codisjoint` transfers across a Boolean subalgebra's coercion.
UPSTREAM: belongs in `Mathlib.Order.BooleanSubalgebra`, cf. `Complementeds.codisjoint_coe`. -/
@[simp, norm_cast] theorem codisjoint_coe : Codisjoint (a : β) b ↔ Codisjoint a b := by
  rw [codisjoint_iff, codisjoint_iff, ← val_sup, ← val_top, Subtype.coe_inj]

end BooleanSubalgebra

namespace Aristotelian

variable {ι ι' ι'' α α' α'' : Type*} [BooleanAlgebra α] [BooleanAlgebra α'] [BooleanAlgebra α'']
  {φ : ι → α} {φ' : ι' → α'} {φ'' : ι'' → α''}

open BooleanSubalgebra
open Equiv (toFun_as_coe apply_symm_apply)

/-- An **Aristotelian isomorphism** is a corner bijection preserving and reflecting `Disjoint`,
`Codisjoint` and `<`, and hence the four Aristotelian relations (`map_isCompl` and
siblings). -/
structure AristotelianIso (φ : ι → α) (φ' : ι' → α') extends ι ≃ ι' where
  /-- Joint inconsistency (`⊓ = ⊥`) is preserved and reflected. -/
  map_disjoint : ∀ i j, Disjoint (φ i) (φ j) ↔ Disjoint (φ' (toFun i)) (φ' (toFun j))
  /-- Joint exhaustiveness (`⊔ = ⊤`) is preserved and reflected. -/
  map_codisjoint : ∀ i j, Codisjoint (φ i) (φ j) ↔ Codisjoint (φ' (toFun i)) (φ' (toFun j))
  /-- Subalternation (`<`) is preserved and reflected. -/
  map_lt : ∀ i j, φ i < φ j ↔ φ' (toFun i) < φ' (toFun j)

namespace AristotelianIso

instance : EquivLike (AristotelianIso φ φ') ι ι' where
  coe e := e.toFun
  inv e := e.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' e e' h _ := by
    obtain ⟨e, _, _, _⟩ := e; obtain ⟨e', _, _, _⟩ := e'; congr; exact Equiv.coe_fn_injective h

@[simp] theorem coe_fn_toEquiv (e : AristotelianIso φ φ') : (e.toEquiv : ι → ι') = e := rfl

@[ext]
theorem ext {e e' : AristotelianIso φ φ'} (h : ∀ i, e i = e' i) : e = e' := DFunLike.ext _ _ h

/-- The identity Aristotelian isomorphism. -/
@[refl] protected def refl (φ : ι → α) : AristotelianIso φ φ where
  toEquiv := Equiv.refl ι
  map_disjoint _ _ := Iff.rfl
  map_codisjoint _ _ := Iff.rfl
  map_lt _ _ := Iff.rfl

/-- The inverse Aristotelian isomorphism. -/
@[symm] protected def symm (e : AristotelianIso φ φ') : AristotelianIso φ' φ where
  toEquiv := e.toEquiv.symm
  map_disjoint i j := by
    simpa only [toFun_as_coe, apply_symm_apply]
      using (e.map_disjoint (e.toEquiv.symm i) (e.toEquiv.symm j)).symm
  map_codisjoint i j := by
    simpa only [toFun_as_coe, apply_symm_apply]
      using (e.map_codisjoint (e.toEquiv.symm i) (e.toEquiv.symm j)).symm
  map_lt i j := by
    simpa only [toFun_as_coe, apply_symm_apply]
      using (e.map_lt (e.toEquiv.symm i) (e.toEquiv.symm j)).symm

/-- Composition of Aristotelian isomorphisms. -/
@[trans] protected def trans (e : AristotelianIso φ φ') (e' : AristotelianIso φ' φ'') :
    AristotelianIso φ φ'' where
  toEquiv := e.toEquiv.trans e'.toEquiv
  map_disjoint i j := (e.map_disjoint i j).trans (e'.map_disjoint _ _)
  map_codisjoint i j := (e.map_codisjoint i j).trans (e'.map_codisjoint _ _)
  map_lt i j := (e.map_lt i j).trans (e'.map_lt _ _)

/-- An Aristotelian isomorphism preserves and reflects contradiction. -/
theorem map_isCompl (e : AristotelianIso φ φ') (i j : ι) :
    IsCompl (φ i) (φ j) ↔ IsCompl (φ' (e i)) (φ' (e j)) := by
  simp only [isCompl_iff, e.map_disjoint, e.map_codisjoint, toFun_as_coe, coe_fn_toEquiv]

/-- An Aristotelian isomorphism preserves and reflects contrariety. -/
theorem map_isContrary (e : AristotelianIso φ φ') (i j : ι) :
    IsContrary (φ i) (φ j) ↔ IsContrary (φ' (e i)) (φ' (e j)) := by
  simp only [IsContrary, e.map_disjoint, e.map_codisjoint, toFun_as_coe, coe_fn_toEquiv]

/-- An Aristotelian isomorphism preserves and reflects subcontrariety. -/
theorem map_isSubcontrary (e : AristotelianIso φ φ') (i j : ι) :
    IsSubcontrary (φ i) (φ j) ↔ IsSubcontrary (φ' (e i)) (φ' (e j)) := by
  simp only [IsSubcontrary, e.map_disjoint, e.map_codisjoint, toFun_as_coe, coe_fn_toEquiv]

end AristotelianIso

/-! ### Boolean isomorphism (Definition 7) and the nesting -/

/-- The `i`-th corner of a diagram, viewed inside its Boolean closure. -/
def corner (φ : ι → α) (i : ι) : closure (Set.range φ) :=
  ⟨φ i, subset_closure (Set.mem_range_self i)⟩

@[simp, norm_cast]
theorem coe_corner (φ : ι → α) (i : ι) : (corner φ i : α) = φ i := rfl

/-- A **Boolean isomorphism** is a corner bijection that extends to an order isomorphism of the
Boolean closures. -/
@[ext]
structure BooleanIso (φ : ι → α) (φ' : ι' → α') where
  /-- The underlying corner bijection. -/
  toEquiv : ι ≃ ι'
  /-- The order-isomorphism of Boolean closures extending it. -/
  closureIso : closure (Set.range φ) ≃o closure (Set.range φ')
  /-- `closureIso` carries corners to corners. -/
  extends_corners : ∀ i, closureIso (corner φ i) = corner φ' (toEquiv i)

namespace BooleanIso

/-- The identity Boolean isomorphism. -/
@[refl] protected def refl (φ : ι → α) : BooleanIso φ φ :=
  ⟨Equiv.refl ι, OrderIso.refl _, fun _ ↦ rfl⟩

/-- The inverse Boolean isomorphism. -/
@[symm] protected def symm (e : BooleanIso φ φ') : BooleanIso φ' φ where
  toEquiv := e.toEquiv.symm
  closureIso := e.closureIso.symm
  extends_corners i := by rw [e.closureIso.symm_apply_eq, e.extends_corners, apply_symm_apply]

/-- Composition of Boolean isomorphisms. -/
@[trans] protected def trans (e : BooleanIso φ φ') (e' : BooleanIso φ' φ'') : BooleanIso φ φ'' where
  toEquiv := e.toEquiv.trans e'.toEquiv
  closureIso := e.closureIso.trans e'.closureIso
  extends_corners i := by
    simp only [OrderIso.trans_apply, e.extends_corners, e'.extends_corners, Equiv.trans_apply]

/-- Every Boolean isomorphism is an Aristotelian isomorphism. -/
def toAristotelianIso (bi : BooleanIso φ φ') : AristotelianIso φ φ' where
  toEquiv := bi.toEquiv
  map_disjoint i j := by
    simp only [toFun_as_coe, ← coe_corner φ, ← coe_corner φ', disjoint_coe, ← bi.extends_corners,
      disjoint_map_orderIso_iff]
  map_codisjoint i j := by
    simp only [toFun_as_coe, ← coe_corner φ, ← coe_corner φ', codisjoint_coe,
      ← bi.extends_corners, codisjoint_map_orderIso_iff]
  map_lt i j := by
    simp only [toFun_as_coe, ← coe_corner φ, ← coe_corner φ', Subtype.coe_lt_coe,
      ← bi.extends_corners, bi.closureIso.lt_iff_lt]

/-- Forget a Boolean isomorphism down to its underlying Aristotelian isomorphism. -/
instance : CoeOut (BooleanIso φ φ') (AristotelianIso φ φ') := ⟨toAristotelianIso⟩

end BooleanIso

end Aristotelian
