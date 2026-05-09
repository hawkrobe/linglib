import Linglib.Core.Algebra.RootedTree.Coproduct
import Linglib.Core.Combinatorics.RootedTree.Nonplanar

set_option autoImplicit false

/-!
# Δ^p on `ConnesKreimer R (Nonplanar α)` via projection from `Planar`
@cite{marcolli-chomsky-berwick-2025} @cite{foissy-introduction-hopf-algebras-trees}

Phase A.7 substrate. The Nonplanar Δ^p is obtained by descending the
planar Δ^p (`Coproduct.lean`) through the projection
`mk : Planar α → Nonplanar α`. Foissy's clean proof of coassociativity
(via the Hochschild 1-cocycle property of `B+_a = Nonplanar.node a`) then
gives a sorry-free `Bialgebra` instance.

## Status

`[UPSTREAM]` candidate. Phase A.7-α (this file's first section): the
projection algebra hom + API. Δ^p, cocycle, coassoc, Bialgebra instance
land in subsequent sub-phases (A.7-β / γ / δ).

## Architecture

The projection algebra hom is built directly on top of mathlib's
`AddMonoidAlgebra.mapDomainAlgHom`, applied to the additive monoid hom
`Multiset.mapAddMonoidHom Nonplanar.mk`. No bespoke construction —
the universal property of `AddMonoidAlgebra` does the heavy lifting.
-/

namespace RootedTree

namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α : Type*}

/-! ## §1: Projection algebra hom `Planar → Nonplanar`

`Nonplanar.mk : Planar α → Nonplanar α` extends to an algebra hom on
`ConnesKreimer R` via `AddMonoidAlgebra.mapDomainAlgHom`. Surjective at
the carrier level; the kernel encodes PlanarEquiv-equivalence of forests
of trees, which is what subsequent sub-phases will need to factor through. -/

/-- The additive monoid hom from forests of planar trees to forests of
    nonplanar trees, given by mapping `Nonplanar.mk` componentwise. -/
noncomputable def forestProjAddHom :
    Forest (Planar α) →+ Forest (Nonplanar α) :=
  Multiset.mapAddMonoidHom Nonplanar.mk

/-- The **projection algebra hom** `ConnesKreimer R (Planar α) →ₐ[R]
    ConnesKreimer R (Nonplanar α)` induced by `Nonplanar.mk`. -/
noncomputable def planarToNonplanarAlg :
    ConnesKreimer R (Planar α) →ₐ[R] ConnesKreimer R (Nonplanar α) :=
  AddMonoidAlgebra.mapDomainAlgHom R R (forestProjAddHom (α := α))

/-! ## §2: API lemmas — action on `of'` and `ofTree` -/

@[simp] theorem planarToNonplanarAlg_of' (F : Forest (Planar α)) :
    planarToNonplanarAlg (R := R) (of' F) =
      of' (R := R) (F.map Nonplanar.mk) := by
  show Finsupp.mapDomain (forestProjAddHom (α := α)) (Finsupp.single F 1) =
       Finsupp.single (F.map Nonplanar.mk) 1
  rw [Finsupp.mapDomain_single]
  rfl

@[simp] theorem planarToNonplanarAlg_ofTree (t : Planar α) :
    planarToNonplanarAlg (R := R) (ofTree t) =
      ofTree (Nonplanar.mk t) := by
  unfold ofTree
  rw [planarToNonplanarAlg_of', Multiset.map_singleton]

@[simp] theorem planarToNonplanarAlg_one :
    planarToNonplanarAlg (R := R) (1 : ConnesKreimer R (Planar α)) = 1 :=
  map_one _

@[simp] theorem planarToNonplanarAlg_mul
    (x y : ConnesKreimer R (Planar α)) :
    planarToNonplanarAlg (R := R) (x * y) =
      planarToNonplanarAlg x * planarToNonplanarAlg y :=
  map_mul _ _ _

/-! ## §3: Phase A.7-β — projection of cut summands

To descend Δ^p from `Planar` to `Nonplanar`, we need a Nonplanar-side
cut-summand multiset that is `PlanarEquiv`-invariant. The strategy:
project each planar cut summand through `mk` componentwise, then prove
the resulting multiset depends on `T : Planar α` only through `mk T`.

The proof factors cleanly through an intermediate `projForest` that
discards the list-order of the remainder children (since
`mk (.node a L)` only depends on `L` as a multiset). -/

/-- Project a planar cut summand to a nonplanar one. -/
def projSummand : Forest (Planar α) × Planar α →
    Forest (Nonplanar α) × Nonplanar α :=
  fun p => (p.1.map Nonplanar.mk, Nonplanar.mk p.2)

/-- Project a `cutListSummandsP` summand to nonplanar level, discarding
    the list-order of the remainder children. The discarded order doesn't
    affect the eventual `mk (.node a remainder)`, since
    `mk` is invariant under children-list permutation
    (`Planar.planarEquiv_root_perm`). -/
def projForest : Forest (Planar α) × List (Planar α) →
    Forest (Nonplanar α) × Multiset (Nonplanar α) :=
  fun p => (p.1.map Nonplanar.mk, Multiset.ofList (p.2.map Nonplanar.mk))

/-- The bridge: applying `cutSummandsP_node`'s wrapper `(p.1, .node a p.2)`
    then `projSummand` factors through `projForest` followed by
    `(F, ms) ↦ (F, Nonplanar.node a ms)`. -/
theorem projSummand_node_factors (a : α) (p : Forest (Planar α) × List (Planar α)) :
    projSummand (p.1, .node a p.2) =
      ((projForest p).1, Nonplanar.node a (projForest p).2) := by
  show (p.1.map Nonplanar.mk, Nonplanar.mk (.node a p.2)) =
       (p.1.map Nonplanar.mk, Nonplanar.node a (Multiset.ofList (p.2.map Nonplanar.mk)))
  congr 1
  exact (Nonplanar.node_mk_planar_list a p.2).symm

/-! ### §3a: Tier 2.1 — list-perm invariance (TO PROVE)

`cutListSummandsP cs` viewed at the `projForest` level is
permutation-invariant in `cs`. Substantive content: the cartesian-product
structure of `cutListSummandsP`'s recursive case is symmetric in its
factors at the multiset level, so swapping two adjacent siblings in `cs`
gives a multiset that's bijection-related and yields equal `projForest`
values per pair.

Proof strategy (next session): induction on `List.Perm`; the `swap` case
is the substantive work and may benefit from an intermediate
characterization of `cutListSummandsP` as `Multiset.product`-style
cartesian product over `cs`. The `cons` case follows from a
`combine_proj` factoring lemma showing `projForest ∘ combine` only
depends on the second factor through `projForest` itself. -/

/-- TODO Phase A.7-β Tier 2.1. Decomposed: `nil`/`trans` close
    structurally; `cons`/`swap` are the substantive remaining
    obligations. -/
theorem cutListSummandsP_proj_perm
    {cs ds : List (Planar α)} (h : cs.Perm ds) :
    (cutListSummandsP cs).map projForest =
      (cutListSummandsP ds).map projForest := by
  induction h with
  | nil => rfl
  | cons _ _ ih =>
    -- TODO: combine_proj factoring lemma — projForest ∘ combine
    -- factors through (id × projForest) on the multiset product
    sorry
  | swap _ _ _ =>
    -- TODO: substantive — Multiset.product symmetry + projForest's
    -- multiset-of-list invariance under decision-order swap
    sorry
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ### §3b: Tier 2.2 + Tier 3 — mutually recursive PlanarEquiv invariance (TO PROVE)

The `cutSummandsP` headline theorem and the `cutListSummandsP`
componentwise-PlanarEquiv variant are mutually recursive (via
`augActionP`). Strategy chosen: mutual `theorem` block with termination
measured by tree weight (`Planar.weight`). For now, structural
EqvGen/Forall₂ cases close inline; substantive PlanarStep `swapAtRoot`/
`recurse` cases remain `sorry`. -/

/-- TODO Phase A.7-β Tier 2.2 (mutual with cutSummandsP_proj_planarEquiv).
    Decomposed: `nil` closes structurally; `cons` is substantive
    (needs Tier 3 plus combine_proj factoring). -/
theorem cutListSummandsP_proj_componentwise
    {cs ds : List (Planar α)}
    (h : List.Forall₂ Planar.PlanarEquiv cs ds) :
    (cutListSummandsP cs).map projForest =
      (cutListSummandsP ds).map projForest := by
  induction h with
  | nil => rfl
  | cons _ _ _ =>
    -- TODO: substantive — apply Tier 3 to head equiv, IH to tail,
    -- then combine_proj factoring on the multiset product
    sorry

/-- TODO Phase A.7-β Tier 3 (mutual with cutListSummandsP_proj_componentwise).
    The headline invariance: PlanarEquiv-equivalent trees produce equal
    projected cut-summand multisets. Decomposed: structural
    `refl`/`symm`/`trans` close inline; the `rel` case dispatches on
    PlanarStep into substantive `swapAtRoot` and `recurse` cases. -/
theorem cutSummandsP_proj_planarEquiv
    {t s : Planar α} (h : Planar.PlanarEquiv t s) :
    (cutSummandsP t).map projSummand =
      (cutSummandsP s).map projSummand := by
  induction h with
  | rel _ _ hstep =>
    -- TODO: cases on PlanarStep
    -- swapAtRoot case: use cutListSummandsP_proj_perm + projSummand_node_factors
    -- recurse case: use cutListSummandsP_proj_componentwise on the singleton
    --   List.Forall₂ chain (pre eq, old↝new, post eq) + Tier 3 recursion on the
    --   sub-step (well-founded by tree weight strictly less in the child)
    sorry
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-! ### §3c: Tier 4 — Δ^p on Nonplanar via descent

These definitions inherit the Tier 3 sorry transitively (until A.7-β is
closed); the architecture is in place so consumers can target the API. -/

/-- The **Nonplanar cut-summand multiset**, defined via `Nonplanar.lift`
    using the (Tier 3) PlanarEquiv invariance. Sorry-blocked transitively
    via `cutSummandsP_proj_planarEquiv`. -/
noncomputable def cutSummandsN :
    Nonplanar α → Multiset (Forest (Nonplanar α) × Nonplanar α) :=
  Nonplanar.lift (fun T => (cutSummandsP T).map projSummand)
    (fun _ _ h => cutSummandsP_proj_planarEquiv h)

@[simp] theorem cutSummandsN_mk (T : Planar α) :
    cutSummandsN (Nonplanar.mk T) = (cutSummandsP T).map projSummand := rfl

/-- The **nonplanar tree-level Δ^p**: explicit `T ⊗ 1` term plus the
    sum of cut-summand tensors at the Nonplanar level. -/
noncomputable def comulTreeN (T : Nonplanar α) :
    ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) :=
  ofTree T ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α))
  + ((cutSummandsN T).map
      (fun p => of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)).sum

/-- The **nonplanar forest-level Δ^p**: multiplicative product of
    tree-level coproducts over the components of the forest. -/
noncomputable def comulForestN (F : Forest (Nonplanar α)) :
    ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) :=
  (F.map (comulTreeN (R := R))).prod

@[simp] theorem comulForestN_zero :
    comulForestN (R := R) (0 : Forest (Nonplanar α)) = 1 := by
  simp only [comulForestN, Multiset.map_zero, Multiset.prod_zero]

@[simp] theorem comulForestN_add (F G : Forest (Nonplanar α)) :
    comulForestN (R := R) (F + G) =
      comulForestN (R := R) F * comulForestN (R := R) G := by
  unfold comulForestN
  rw [Multiset.map_add, Multiset.prod_add]

/-- `comulForestN` packaged as a `MonoidHom` from
    `Multiplicative (Forest (Nonplanar α))`. -/
noncomputable def comulMonoidHomN :
    Multiplicative (Forest (Nonplanar α)) →*
      (ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) where
  toFun F := comulForestN (R := R) F.toAdd
  map_one' := comulForestN_zero
  map_mul' F G := comulForestN_add F.toAdd G.toAdd

/-- The **Δ^p coproduct on `ConnesKreimer R (Nonplanar α)`** as an
    algebra hom. -/
noncomputable def comulAlgHomN :
    ConnesKreimer R (Nonplanar α) →ₐ[R]
      ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) :=
  AddMonoidAlgebra.lift R
    ((ConnesKreimer R (Nonplanar α)) ⊗[R] (ConnesKreimer R (Nonplanar α)))
    (Forest (Nonplanar α)) comulMonoidHomN

@[simp] theorem comulAlgHomN_apply_of' (F : Forest (Nonplanar α)) :
    comulAlgHomN (R := R) (α := α) (of' F) = comulForestN F := by
  show AddMonoidAlgebra.lift R _ _ comulMonoidHomN (Finsupp.single F 1) = _
  rw [AddMonoidAlgebra.lift_single, one_smul]
  rfl

@[simp] theorem comulAlgHomN_apply_ofTree (T : Nonplanar α) :
    comulAlgHomN (R := R) (α := α) (ofTree T) = comulTreeN T := by
  unfold ofTree
  rw [comulAlgHomN_apply_of']
  unfold comulForestN
  simp only [Multiset.map_singleton, Multiset.prod_singleton]

/-! ## §4: Phase A.7-γ — Hochschild 1-cocycle (TO STATE & PROVE)

`B+_a : Multiset (Nonplanar α) → Nonplanar α` is the smart constructor
`Nonplanar.node a`. The Hochschild 1-cocycle property is
`Δ^p ∘ B+_a = B+_a ⊗ 1 + (id ⊗ B+_a) ∘ Δ^p` (Foissy §3 / MCB §1.2.11).

Statement and proof deferred — the precise tensor/linear-map shape
depends on the chosen Bialgebra encoding for the Nonplanar carrier
(mathlib's `Bialgebra.comul` vs. our `comulAlgHomN`), so it's cleaner
to state alongside the Bialgebra instance in §5. -/

/-- The **B+_a** operator: graft an unordered forest of Nonplanar trees
    under a new root labeled `a`. Identical to the smart constructor. -/
noncomputable def bPlus (a : α) (F : Forest (Nonplanar α)) :
    Nonplanar α :=
  Nonplanar.node a F

@[simp] theorem bPlus_def (a : α) (F : Forest (Nonplanar α)) :
    bPlus a F = Nonplanar.node a F := rfl

/-! ## §5: Phase A.7-δ — Foissy clean coassoc + Bialgebra instance (PENDING)

Foissy's 5-line proof: define `A := {x : Δ ⊗ id (Δ x) = id ⊗ Δ (Δ x)}`.
Both sides are algebra homs (Δ by construction; tensoring with id and
composition preserve algebra-hom), so `A` is a subalgebra. By the §4
cocycle, `A` is closed under `B+_a`. By induction (every Nonplanar tree
is either a leaf or `B+_a (children)`), `A` contains every tree. Since
`A` is a subalgebra containing all generators, `A` = entire algebra.

Once §3 sorries close (Tier 2.1, 2.2, 3) and §4 cocycle proven, the
`Bialgebra (ConnesKreimer R (Nonplanar α))` instance lands sorry-free
with `comul := comulAlgHomN`, `counit := counit` (already in
`ConnesKreimer.lean`), and the four Bialgebra laws (comul_one,
comul_mul, counit_one, counit_mul) following from algebra-hom-ness +
the Foissy coassoc. -/

end ConnesKreimer

end RootedTree
