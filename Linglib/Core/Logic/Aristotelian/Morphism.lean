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

/-- Order transfers across a Boolean subalgebra's coercion (the order is `PartialOrder.lift` of the
coercion).
UPSTREAM: belongs in `Mathlib.Order.BooleanSubalgebra`. -/
@[simp, norm_cast] theorem coe_le_coe : (a : β) ≤ b ↔ a ≤ b := Iff.rfl

/-- Strict order transfers across a Boolean subalgebra's coercion.
UPSTREAM: belongs in `Mathlib.Order.BooleanSubalgebra`. -/
@[simp, norm_cast] theorem coe_lt_coe : (a : β) < b ↔ a < b := Iff.rfl

end BooleanSubalgebra

namespace Aristotelian

variable {ι ι' ι'' : Type*} [Fintype ι] [Fintype ι'] [Fintype ι'']
  {α α' α'' : Type*} [BooleanAlgebra α] [BooleanAlgebra α'] [BooleanAlgebra α'']
  {D : Diagram ι α} {D' : Diagram ι' α'} {D'' : Diagram ι'' α''}

/-- An **Aristotelian isomorphism** ([demey-smessaert-2024], Definition 6): a bijection of corners
preserving and reflecting all four Aristotelian relations. Equivalently (and as defined here, since
the four relations are boolean combinations of these) it preserves `Disjoint`, `Codisjoint`, and `<`.
The four-relation characterization is `map_isContradictory` and siblings. Equality of coincident
corners is not tracked (faithful to Definition 6): Aristotelian-unconnected corners may be permuted
freely. -/
@[ext]
structure AristotelianIso (D : Diagram ι α) (D' : Diagram ι' α') where
  /-- The underlying corner bijection. -/
  toEquiv : ι ≃ ι'
  /-- Joint inconsistency (`⊓ = ⊥`) is preserved and reflected. -/
  map_disjoint : ∀ i j, Disjoint (D.φ i) (D.φ j) ↔ Disjoint (D'.φ (toEquiv i)) (D'.φ (toEquiv j))
  /-- Joint exhaustiveness (`⊔ = ⊤`) is preserved and reflected. -/
  map_codisjoint : ∀ i j,
    Codisjoint (D.φ i) (D.φ j) ↔ Codisjoint (D'.φ (toEquiv i)) (D'.φ (toEquiv j))
  /-- Strict entailment (subalternation) is preserved and reflected. -/
  map_lt : ∀ i j, D.φ i < D.φ j ↔ D'.φ (toEquiv i) < D'.φ (toEquiv j)

namespace AristotelianIso

/-- The identity Aristotelian isomorphism. -/
@[refl] protected def refl (D : Diagram ι α) : AristotelianIso D D :=
  ⟨Equiv.refl ι, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

/-- The inverse Aristotelian isomorphism. -/
@[symm] protected def symm (e : AristotelianIso D D') : AristotelianIso D' D where
  toEquiv := e.toEquiv.symm
  map_disjoint i j := by
    simpa only [Equiv.apply_symm_apply] using (e.map_disjoint (e.toEquiv.symm i) (e.toEquiv.symm j)).symm
  map_codisjoint i j := by
    simpa only [Equiv.apply_symm_apply] using (e.map_codisjoint (e.toEquiv.symm i) (e.toEquiv.symm j)).symm
  map_lt i j := by
    simpa only [Equiv.apply_symm_apply] using (e.map_lt (e.toEquiv.symm i) (e.toEquiv.symm j)).symm

/-- Composition of Aristotelian isomorphisms. -/
@[trans] protected def trans (e : AristotelianIso D D') (e' : AristotelianIso D' D'') :
    AristotelianIso D D'' where
  toEquiv := e.toEquiv.trans e'.toEquiv
  map_disjoint i j := (e.map_disjoint i j).trans (e'.map_disjoint _ _)
  map_codisjoint i j := (e.map_codisjoint i j).trans (e'.map_codisjoint _ _)
  map_lt i j := (e.map_lt i j).trans (e'.map_lt _ _)

/-- An Aristotelian isomorphism preserves and reflects contradictoriness (Definition 6). -/
theorem map_isContradictory (e : AristotelianIso D D') (i j : ι) :
    IsContradictory (D.φ i) (D.φ j) ↔ IsContradictory (D'.φ (e.toEquiv i)) (D'.φ (e.toEquiv j)) := by
  simp only [IsContradictory, isCompl_iff, e.map_disjoint, e.map_codisjoint]

/-- An Aristotelian isomorphism preserves and reflects contrariety (Definition 6). -/
theorem map_isContrary (e : AristotelianIso D D') (i j : ι) :
    IsContrary (D.φ i) (D.φ j) ↔ IsContrary (D'.φ (e.toEquiv i)) (D'.φ (e.toEquiv j)) := by
  simp only [IsContrary, e.map_disjoint, e.map_codisjoint]

/-- An Aristotelian isomorphism preserves and reflects subcontrariety (Definition 6). -/
theorem map_isSubcontrary (e : AristotelianIso D D') (i j : ι) :
    IsSubcontrary (D.φ i) (D.φ j) ↔ IsSubcontrary (D'.φ (e.toEquiv i)) (D'.φ (e.toEquiv j)) := by
  simp only [IsSubcontrary, e.map_disjoint, e.map_codisjoint]

/-- An Aristotelian isomorphism preserves and reflects subalternation (Definition 6). -/
theorem map_isSubaltern (e : AristotelianIso D D') (i j : ι) :
    IsSubaltern (D.φ i) (D.φ j) ↔ IsSubaltern (D'.φ (e.toEquiv i)) (D'.φ (e.toEquiv j)) :=
  e.map_lt i j

end AristotelianIso

/-! ### Boolean isomorphism (Definition 7) and the nesting -/

/-- The `i`-th corner of a diagram, viewed inside its Boolean closure. -/
def Diagram.corner (D : Diagram ι α) (i : ι) : BooleanSubalgebra.closure (Set.range D.φ) :=
  ⟨D.φ i, BooleanSubalgebra.subset_closure (Set.mem_range_self i)⟩

@[simp, norm_cast]
theorem Diagram.coe_corner (D : Diagram ι α) (i : ι) : (D.corner i : α) = D.φ i := rfl

/-- A **Boolean isomorphism** ([demey-smessaert-2024], Definition 7): a corner bijection that
extends to an order-isomorphism of the Boolean closures. -/
@[ext]
structure BooleanIso (D : Diagram ι α) (D' : Diagram ι' α') where
  /-- The underlying corner bijection. -/
  toEquiv : ι ≃ ι'
  /-- The order-isomorphism of Boolean closures extending it. -/
  closureIso :
    BooleanSubalgebra.closure (Set.range D.φ) ≃o BooleanSubalgebra.closure (Set.range D'.φ)
  /-- `closureIso` carries corners to corners. -/
  extends_corners : ∀ i, closureIso (D.corner i) = D'.corner (toEquiv i)

namespace BooleanIso

/-- The identity Boolean isomorphism. -/
@[refl] protected def refl (D : Diagram ι α) : BooleanIso D D :=
  ⟨Equiv.refl ι, OrderIso.refl _, fun _ => rfl⟩

/-- The inverse Boolean isomorphism. -/
@[symm] protected def symm (e : BooleanIso D D') : BooleanIso D' D where
  toEquiv := e.toEquiv.symm
  closureIso := e.closureIso.symm
  extends_corners i := by rw [e.closureIso.symm_apply_eq, e.extends_corners, Equiv.apply_symm_apply]

/-- Composition of Boolean isomorphisms. -/
@[trans] protected def trans (e : BooleanIso D D') (e' : BooleanIso D' D'') : BooleanIso D D'' where
  toEquiv := e.toEquiv.trans e'.toEquiv
  closureIso := e.closureIso.trans e'.closureIso
  extends_corners i := by
    simp only [OrderIso.trans_apply, e.extends_corners, e'.extends_corners, Equiv.trans_apply]

/-- **Every Boolean isomorphism is an Aristotelian isomorphism** ([demey-smessaert-2024], p.13). The
converse fails — the Keynes–Johnson octagons are Aristotelian-isomorphic but not Boolean-isomorphic.
(To discharge the resulting `AristotelianIso` fields by `decide` over a finite `W → Bool` carrier,
rewrite with `disjoint_iff_forall` / `codisjoint_iff_forall` / `le_iff_forall` from `Basic.lean`.) -/
def toAristotelianIso (bi : BooleanIso D D') : AristotelianIso D D' where
  toEquiv := bi.toEquiv
  map_disjoint i j := by
    simp only [← Diagram.coe_corner, BooleanSubalgebra.disjoint_coe, ← bi.extends_corners,
      disjoint_map_orderIso_iff]
  map_codisjoint i j := by
    simp only [← Diagram.coe_corner, BooleanSubalgebra.codisjoint_coe, ← bi.extends_corners,
      codisjoint_map_orderIso_iff]
  map_lt i j := by
    simp only [← Diagram.coe_corner, BooleanSubalgebra.coe_lt_coe, ← bi.extends_corners,
      bi.closureIso.lt_iff_lt]

/-- Forget a Boolean isomorphism down to its underlying Aristotelian isomorphism. -/
instance : CoeOut (BooleanIso D D') (AristotelianIso D D') := ⟨toAristotelianIso⟩

end BooleanIso

end Aristotelian
