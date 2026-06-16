import Linglib.Core.Logic.Aristotelian.Diagram
import Mathlib.Order.BooleanSubalgebra

/-!
# Isomorphisms of Aristotelian diagrams

Per [deklerck-vignero-demey-2024] and [demey-smessaert-2024]. An *Aristotelian isomorphism* is a
bijection of corners preserving the labeled relation matrix; these form a groupoid — the core of
the category of Aristotelian diagrams of [deklerck-vignero-demey-2024]. A *Boolean isomorphism*
([demey-smessaert-2024], Definition 7) is the stronger notion of a corner bijection extending to an
order-isomorphism of the Boolean closures; every Boolean isomorphism is an Aristotelian one, but not
conversely (the Keynes–Johnson octagons of [demey-smessaert-2024] witness the gap).

## Main declarations

* `AristotelianIso` — a relation-matrix-preserving corner bijection, with `refl`/`symm`/`trans`.
* `BooleanIso`, `BooleanIso.toAristotelianIso` — the stronger notion and the nesting.
-/

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

variable {ι ι' ι'' : Type*} [Fintype ι] [Fintype ι'] [Fintype ι'']
  {α α' α'' : Type*} [BooleanAlgebra α] [BooleanAlgebra α'] [BooleanAlgebra α'']
  {D : Diagram ι α} {D' : Diagram ι' α'} {D'' : Diagram ι'' α''}

open BooleanSubalgebra
open Equiv (toFun_as_coe apply_symm_apply)

/-- An **Aristotelian isomorphism** ([demey-smessaert-2024], Definition 6): a corner bijection
preserving and reflecting `Disjoint`, `Codisjoint`, and `<` — equivalently all four Aristotelian
relations (`map_isContradictory` etc.), since these are boolean combinations. -/
structure AristotelianIso (D : Diagram ι α) (D' : Diagram ι' α') extends ι ≃ ι' where
  /-- Joint inconsistency (`⊓ = ⊥`) is preserved and reflected. -/
  map_disjoint : ∀ i j, Disjoint (D.φ i) (D.φ j) ↔ Disjoint (D'.φ (toFun i)) (D'.φ (toFun j))
  /-- Joint exhaustiveness (`⊔ = ⊤`) is preserved and reflected. -/
  map_codisjoint : ∀ i j, Codisjoint (D.φ i) (D.φ j) ↔ Codisjoint (D'.φ (toFun i)) (D'.φ (toFun j))
  /-- Strict entailment (subalternation) is preserved and reflected. -/
  map_lt : ∀ i j, D.φ i < D.φ j ↔ D'.φ (toFun i) < D'.φ (toFun j)

namespace AristotelianIso

instance : EquivLike (AristotelianIso D D') ι ι' where
  coe e := e.toFun
  inv e := e.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' e e' h _ := by
    obtain ⟨e, _, _, _⟩ := e; obtain ⟨e', _, _, _⟩ := e'; congr; exact Equiv.coe_fn_injective h

@[simp] theorem coe_fn_toEquiv (e : AristotelianIso D D') : (e.toEquiv : ι → ι') = e := rfl

@[ext]
theorem ext {e e' : AristotelianIso D D'} (h : ∀ i, e i = e' i) : e = e' := DFunLike.ext _ _ h

/-- The identity Aristotelian isomorphism. -/
@[refl] protected def refl (D : Diagram ι α) : AristotelianIso D D where
  toEquiv := Equiv.refl ι
  map_disjoint _ _ := Iff.rfl
  map_codisjoint _ _ := Iff.rfl
  map_lt _ _ := Iff.rfl

/-- The inverse Aristotelian isomorphism. -/
@[symm] protected def symm (e : AristotelianIso D D') : AristotelianIso D' D where
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
@[trans] protected def trans (e : AristotelianIso D D') (e' : AristotelianIso D' D'') :
    AristotelianIso D D'' where
  toEquiv := e.toEquiv.trans e'.toEquiv
  map_disjoint i j := (e.map_disjoint i j).trans (e'.map_disjoint _ _)
  map_codisjoint i j := (e.map_codisjoint i j).trans (e'.map_codisjoint _ _)
  map_lt i j := (e.map_lt i j).trans (e'.map_lt _ _)

/-- An Aristotelian isomorphism preserves and reflects contradictoriness (Definition 6). -/
theorem map_isContradictory (e : AristotelianIso D D') (i j : ι) :
    IsContradictory (D.φ i) (D.φ j) ↔ IsContradictory (D'.φ (e i)) (D'.φ (e j)) := by
  simp only [IsContradictory, isCompl_iff, e.map_disjoint, e.map_codisjoint,
    toFun_as_coe, coe_fn_toEquiv]

/-- An Aristotelian isomorphism preserves and reflects contrariety (Definition 6). -/
theorem map_isContrary (e : AristotelianIso D D') (i j : ι) :
    IsContrary (D.φ i) (D.φ j) ↔ IsContrary (D'.φ (e i)) (D'.φ (e j)) := by
  simp only [IsContrary, e.map_disjoint, e.map_codisjoint, toFun_as_coe, coe_fn_toEquiv]

/-- An Aristotelian isomorphism preserves and reflects subcontrariety (Definition 6). -/
theorem map_isSubcontrary (e : AristotelianIso D D') (i j : ι) :
    IsSubcontrary (D.φ i) (D.φ j) ↔ IsSubcontrary (D'.φ (e i)) (D'.φ (e j)) := by
  simp only [IsSubcontrary, e.map_disjoint, e.map_codisjoint, toFun_as_coe, coe_fn_toEquiv]

/-- An Aristotelian isomorphism preserves and reflects subalternation (Definition 6). -/
theorem map_isSubaltern (e : AristotelianIso D D') (i j : ι) :
    IsSubaltern (D.φ i) (D.φ j) ↔ IsSubaltern (D'.φ (e i)) (D'.φ (e j)) :=
  e.map_lt i j

end AristotelianIso

/-! ### Boolean isomorphism (Definition 7) and the nesting -/

/-- The `i`-th corner of a diagram, viewed inside its Boolean closure. -/
def Diagram.corner (D : Diagram ι α) (i : ι) : closure (Set.range D.φ) :=
  ⟨D.φ i, subset_closure (Set.mem_range_self i)⟩

@[simp, norm_cast]
theorem Diagram.coe_corner (D : Diagram ι α) (i : ι) : (D.corner i : α) = D.φ i := rfl

/-- A **Boolean isomorphism** ([demey-smessaert-2024], Definition 7): a corner bijection that
extends to an order-isomorphism of the Boolean closures. -/
@[ext]
structure BooleanIso (D : Diagram ι α) (D' : Diagram ι' α') where
  /-- The underlying corner bijection. -/
  toEquiv : ι ≃ ι'
  /-- The order-isomorphism of Boolean closures extending it. -/
  closureIso : closure (Set.range D.φ) ≃o closure (Set.range D'.φ)
  /-- `closureIso` carries corners to corners. -/
  extends_corners : ∀ i, closureIso (D.corner i) = D'.corner (toEquiv i)

namespace BooleanIso
open Diagram

/-- The identity Boolean isomorphism. -/
@[refl] protected def refl (D : Diagram ι α) : BooleanIso D D :=
  ⟨Equiv.refl ι, OrderIso.refl _, fun _ => rfl⟩

/-- The inverse Boolean isomorphism. -/
@[symm] protected def symm (e : BooleanIso D D') : BooleanIso D' D where
  toEquiv := e.toEquiv.symm
  closureIso := e.closureIso.symm
  extends_corners i := by rw [e.closureIso.symm_apply_eq, e.extends_corners, apply_symm_apply]

/-- Composition of Boolean isomorphisms. -/
@[trans] protected def trans (e : BooleanIso D D') (e' : BooleanIso D' D'') : BooleanIso D D'' where
  toEquiv := e.toEquiv.trans e'.toEquiv
  closureIso := e.closureIso.trans e'.closureIso
  extends_corners i := by
    simp only [OrderIso.trans_apply, e.extends_corners, e'.extends_corners, Equiv.trans_apply]

/-- **Every Boolean isomorphism is an Aristotelian isomorphism** ([demey-smessaert-2024], p.13); the
converse fails (the Keynes–Johnson octagons witness the gap). -/
def toAristotelianIso (bi : BooleanIso D D') : AristotelianIso D D' where
  toEquiv := bi.toEquiv
  map_disjoint i j := by
    simp only [toFun_as_coe, ← coe_corner, disjoint_coe, ← bi.extends_corners,
      disjoint_map_orderIso_iff]
  map_codisjoint i j := by
    simp only [toFun_as_coe, ← coe_corner, codisjoint_coe, ← bi.extends_corners,
      codisjoint_map_orderIso_iff]
  map_lt i j := by
    simp only [toFun_as_coe, ← coe_corner, Subtype.coe_lt_coe, ← bi.extends_corners,
      bi.closureIso.lt_iff_lt]

/-- Forget a Boolean isomorphism down to its underlying Aristotelian isomorphism. -/
instance : CoeOut (BooleanIso D D') (AristotelianIso D D') := ⟨toAristotelianIso⟩

end BooleanIso

end Aristotelian
