import Linglib.Core.Algebra.RootedTree.Coproduct
import Linglib.Core.Combinatorics.RootedTree.Nonplanar
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.TensorProduct.Basic

set_option autoImplicit false

/-!
# Δ^p on `ConnesKreimer R (Nonplanar α)` via projection from `Planar`
@cite{marcolli-chomsky-berwick-2025} @cite{foissy-introduction-hopf-algebras-trees}

The Nonplanar Δ^p is obtained by descending the planar Δ^p
(`Coproduct.lean`) through the projection `mk : Planar α → Nonplanar α`.
The descent requires showing that the projected cut summands
(`(cutSummandsP T).map projSummand`) depend on `T : Planar α` only
through `mk T`, i.e., are invariant under `Planar.PlanarEquiv`. Once
established, `Nonplanar.lift` produces `cutSummandsN`, which extends to
`comulTreeN`, `comulForestN`, and the algebra hom `comulAlgHomN`.

## Status

`[UPSTREAM]` candidate. Sorry-free for the descent (`comulAlgHomN`).
Hochschild cocycle for `B+`, Foissy clean coassoc, and the
`Bialgebra (ConnesKreimer R (Nonplanar α))` instance are deferred —
see `## Phase A.7-γ` and `## Phase A.7-δ` sections below.

## Architecture

- **Projection algebra hom** (`planarToNonplanarAlg`): directly on top of
  mathlib's `AddMonoidAlgebra.mapDomainAlgHom`, applied to the additive
  monoid hom `Multiset.mapAddMonoidHom Nonplanar.mk`. The universal
  property of `AddMonoidAlgebra` does the heavy lifting.
- **Cut-summand descent** (§3): pointwise projection
  (`projSummand`/`projForest`/`projAugAction`) plus a clean factoring of
  the `cutListSummandsP` cons case as a Nonplanar-level cartesian
  product (`cutListSummandsP_cons_proj`); structural induction on
  `PlanarStep` for the headline invariance, with pure `EqvGen`/`Forall₂`
  lifts for `PlanarEquiv` and `List.Forall₂` versions.
-/

namespace RootedTree

namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α : Type*}

/-! ## Projection algebra hom `Planar → Nonplanar`

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

/-! ## API lemmas — action on `of'` and `ofTree` -/

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

/-! ## Phase A.7-β — projection of cut summands, descent of Δ^p

To descend Δ^p from `Planar` to `Nonplanar`, we need a Nonplanar-side
cut-summand multiset that is `PlanarEquiv`-invariant. The strategy:
project each planar cut summand through `mk` componentwise, then prove
the resulting multiset depends on `T : Planar α` only through `mk T`.

The proof factors through three layers:
- **Pointwise projection** (`projSummand`, `projForest`, `projAugAction`):
  the per-element `Nonplanar.mk` lifts.
- **Combine factoring** (`cutListSummandsP_cons_proj`): the cons case of
  `cutListSummandsP` distributes over the projection, giving a clean
  cartesian-product recursion at the `Nonplanar` level.
- **Headline lifts** (`cutSummandsP_proj_planarStep`,
  `cutSummandsP_proj_planarEquiv`, `cutListSummandsP_proj_componentwise`):
  structural induction on `PlanarStep` for the substantive content;
  pure `EqvGen` / `Forall₂` lifts for the rest. -/

/-! ### Pointwise projection -/

/-- Project a planar cut summand to a nonplanar one. -/
def projSummand : Forest (Planar α) × Planar α →
    Forest (Nonplanar α) × Nonplanar α :=
  fun p => (p.1.map Nonplanar.mk, Nonplanar.mk p.2)

/-- Project a `cutListSummandsP` summand to nonplanar level, discarding
    the list-order of the remainder children. The discarded order doesn't
    affect the eventual `mk (.node a remainder)`, since `mk` is invariant
    under children-list permutation (`Planar.planarEquiv_root_perm`). -/
def projForest : Forest (Planar α) × List (Planar α) →
    Forest (Nonplanar α) × Multiset (Nonplanar α) :=
  fun p => (p.1.map Nonplanar.mk, Multiset.ofList (p.2.map Nonplanar.mk))

/-- Project an `augActionP` summand to nonplanar level (per-child decision). -/
def projAugAction : Forest (Planar α) × Option (Planar α) →
    Forest (Nonplanar α) × Option (Nonplanar α) :=
  fun p => (p.1.map Nonplanar.mk, p.2.map Nonplanar.mk)

/-- Bridge: applying `cutSummandsP_node`'s wrapper `(p.1, .node a p.2)`
    then `projSummand` factors through `projForest` followed by the
    `Nonplanar.node a` smart constructor. -/
theorem projSummand_node_factors (a : α) (p : Forest (Planar α) × List (Planar α)) :
    projSummand (p.1, .node a p.2) =
      ((projForest p).1, Nonplanar.node a (projForest p).2) := by
  show (p.1.map Nonplanar.mk, Nonplanar.mk (.node a p.2)) =
       (p.1.map Nonplanar.mk, Nonplanar.node a (Multiset.ofList (p.2.map Nonplanar.mk)))
  congr 1
  exact (Nonplanar.node_mk_planar_list a p.2).symm

/-! ### Combine factoring through projection

The cons case of `cutListSummandsP` combines a per-child decision
(`augActionP`) with the cut-summands of the remaining children. This
combination distributes over the `Nonplanar` projection: the "projected
combiner" `innerCombinerProj` operates on
`(Forest × Option) × (Forest × Multiset)` and matches `projForest` of
the inline planar combiner. The headline result is
`cutListSummandsP_cons_proj`, which expresses the cons case of the
projected `cutListSummandsP` as a clean cartesian product at the
Nonplanar level. -/

/-- The Nonplanar-level combiner: given a per-child decision and the
    accumulated cuts of the remaining children, produce the merged
    (cut forest, remainder multiset) pair. Mirrors the inline lambda in
    `cutListSummandsP`'s cons case but operates on `Multiset` remainders. -/
private def innerCombinerProj :
    (Forest (Nonplanar α) × Option (Nonplanar α)) ×
    (Forest (Nonplanar α) × Multiset (Nonplanar α)) →
    Forest (Nonplanar α) × Multiset (Nonplanar α)
  | ((F, Option.none), (G, ms)) => (F + G, ms)
  | ((F, Option.some r), (G, ms)) => (F + G, r ::ₘ ms)

/-- Pointwise: `projForest` of an applied planar combiner equals
    `innerCombinerProj` applied to the projected pair-of-pairs. -/
private theorem projForest_innerCombiner_apply
    (p : (Forest (Planar α) × Option (Planar α)) ×
         (Forest (Planar α) × List (Planar α))) :
    projForest (match p.1.2 with
                | Option.none => (p.1.1 + p.2.1, p.2.2)
                | Option.some r => (p.1.1 + p.2.1, r :: p.2.2)) =
      innerCombinerProj (projAugAction p.1, projForest p.2) := by
  obtain ⟨⟨F, dec⟩, ⟨G, list⟩⟩ := p
  cases dec with
  | none =>
    show ((F + G).map Nonplanar.mk, Multiset.ofList (list.map Nonplanar.mk)) =
         (F.map Nonplanar.mk + G.map Nonplanar.mk, Multiset.ofList (list.map Nonplanar.mk))
    rw [Multiset.map_add]
  | some r =>
    show ((F + G).map Nonplanar.mk, Multiset.ofList ((r :: list).map Nonplanar.mk)) =
         (F.map Nonplanar.mk + G.map Nonplanar.mk,
          Nonplanar.mk r ::ₘ Multiset.ofList (list.map Nonplanar.mk))
    rw [Multiset.map_add]
    rfl

/-- Pointwise: `projAugAction` of `augActionP old` is determined by the
    Nonplanar projection of the cut summands plus the equality of the
    `Nonplanar.mk`-projection of the trees themselves (needed for the
    extract-whole element of `augActionP`). -/
private theorem augActionP_proj_eq_of_step_data
    {old new : Planar α}
    (h_mk : Nonplanar.mk old = Nonplanar.mk new)
    (h_proj : (cutSummandsP old).map projSummand =
              (cutSummandsP new).map projSummand) :
    (augActionP old).map projAugAction =
      (augActionP new).map projAugAction := by
  rw [augActionP_eq, augActionP_eq, Multiset.map_cons, Multiset.map_cons]
  congr 1
  · -- First element (extract-whole): projAugAction ({old}, none) = ({mk old}, none)
    show (({old} : Forest (Planar α)).map Nonplanar.mk,
          (Option.none : Option (Planar α)).map Nonplanar.mk) =
         (({new} : Forest (Planar α)).map Nonplanar.mk,
          (Option.none : Option (Planar α)).map Nonplanar.mk)
    rw [Multiset.map_singleton, Multiset.map_singleton, h_mk]
  · -- Tail: projAugAction-of-projection = (s.1, some s.2) ∘ projSummand
    rw [Multiset.map_map, Multiset.map_map]
    -- Both sides now: (cutSummandsP _).map (projAugAction ∘ (fun p => (p.1, some p.2)))
    -- Rewrite this composed function as (fun s => (s.1, some s.2)) ∘ projSummand
    have eq_fn : (projAugAction (α := α)) ∘
        (fun (p : Forest (Planar α) × Planar α) => (p.1, Option.some p.2)) =
        (fun (s : Forest (Nonplanar α) × Nonplanar α) => (s.1, Option.some s.2)) ∘
        (projSummand (α := α)) := by
      funext p
      rfl
    rw [eq_fn]
    -- Now: (cutSummandsP old).map (g ∘ projSummand) = (cutSummandsP new).map (g ∘ projSummand)
    -- = ((cutSummandsP old).map projSummand).map g = ((cutSummandsP new).map projSummand).map g
    rw [← Multiset.map_map, ← Multiset.map_map, h_proj]

/-! ### Cartesian-product distributivity

The pair-componentwise `Prod.map` distributes over `Multiset.product`
(`×ˢ`). Mathlib has the bind-side analogues but not this exact form for
multiset products; the proof is one inductive line via `cons_product`. -/

private theorem map_prodMap_product {α β γ δ : Type*}
    (f : α → γ) (g : β → δ)
    (s : Multiset α) (t : Multiset β) :
    (s ×ˢ t).map (Prod.map f g) = s.map f ×ˢ t.map g := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.cons_product, Multiset.map_add, Multiset.map_map,
               Multiset.map_cons, ih]
    rfl

/-! ### Headline factoring: cons case of projected `cutListSummandsP` -/

/-- The projected `cutListSummandsP` on a cons list factors as a clean
    cartesian product at the Nonplanar level. This is the key lemma
    enabling all subsequent invariance proofs. -/
private theorem cutListSummandsP_cons_proj (t : Planar α) (ts : List (Planar α)) :
    (cutListSummandsP (t :: ts)).map projForest =
      ((augActionP t).map projAugAction ×ˢ
       (cutListSummandsP ts).map projForest).map innerCombinerProj := by
  rw [cutListSummandsP_cons, Multiset.map_map, ← map_prodMap_product,
      Multiset.map_map]
  apply Multiset.map_congr rfl
  intro p _
  exact projForest_innerCombiner_apply p

/-! ### List-side projection invariants

These three theorems establish that the projected `cutListSummandsP` is
invariant under (1) substituting an "augAction-projection-equal" child,
(2) substituting a "projForest-equal" tail, and (3) any list permutation. -/

/-- Substituting `old` with `new` in `cutListSummandsP` is invariant
    under `projForest` if `(augActionP old).map projAugAction =
    (augActionP new).map projAugAction`. -/
private theorem cutListSummandsP_proj_at_via_augAction
    {pre post : List (Planar α)} {old new : Planar α}
    (h : (augActionP old).map projAugAction =
         (augActionP new).map projAugAction) :
    (cutListSummandsP (pre ++ old :: post)).map projForest =
    (cutListSummandsP (pre ++ new :: post)).map projForest := by
  induction pre with
  | nil =>
    show (cutListSummandsP (old :: post)).map projForest =
         (cutListSummandsP (new :: post)).map projForest
    rw [cutListSummandsP_cons_proj, cutListSummandsP_cons_proj, h]
  | cons p pre' ih =>
    show (cutListSummandsP (p :: (pre' ++ old :: post))).map projForest =
         (cutListSummandsP (p :: (pre' ++ new :: post))).map projForest
    rw [cutListSummandsP_cons_proj, cutListSummandsP_cons_proj, ih]

/-- Tail lift: `cutListSummandsP` is invariant under `projForest`-equal
    tails when consed with a fixed head. -/
private theorem cutListSummandsP_proj_tail_lift (d : Planar α)
    {cs ds : List (Planar α)}
    (h : (cutListSummandsP cs).map projForest =
         (cutListSummandsP ds).map projForest) :
    (cutListSummandsP (d :: cs)).map projForest =
      (cutListSummandsP (d :: ds)).map projForest := by
  rw [cutListSummandsP_cons_proj, cutListSummandsP_cons_proj, h]

/-- Triple-combiner symmetry: combining three pieces (two decisions plus
    the accumulated rest) at the projected level is symmetric in the
    first two decision arguments. -/
private theorem innerCombinerProj_swap_args
    (a b : Forest (Nonplanar α) × Option (Nonplanar α))
    (c : Forest (Nonplanar α) × Multiset (Nonplanar α)) :
    innerCombinerProj (a, innerCombinerProj (b, c)) =
    innerCombinerProj (b, innerCombinerProj (a, c)) := by
  obtain ⟨Fa, da⟩ := a
  obtain ⟨Fb, db⟩ := b
  obtain ⟨Fc, mc⟩ := c
  cases da with
  | none =>
    cases db with
    | none =>
      show (Fa + (Fb + Fc), mc) = (Fb + (Fa + Fc), mc)
      rw [← add_assoc, ← add_assoc, add_comm Fa Fb]
    | some rb =>
      show (Fa + (Fb + Fc), rb ::ₘ mc) = (Fb + (Fa + Fc), rb ::ₘ mc)
      rw [← add_assoc, ← add_assoc, add_comm Fa Fb]
  | some ra =>
    cases db with
    | none =>
      show (Fa + (Fb + Fc), ra ::ₘ mc) = (Fb + (Fa + Fc), ra ::ₘ mc)
      rw [← add_assoc, ← add_assoc, add_comm Fa Fb]
    | some rb =>
      show (Fa + (Fb + Fc), ra ::ₘ rb ::ₘ mc) =
           (Fb + (Fa + Fc), rb ::ₘ ra ::ₘ mc)
      have hF : Fa + (Fb + Fc) = Fb + (Fa + Fc) := by
        rw [← add_assoc, ← add_assoc, add_comm Fa Fb]
      have hM : (ra ::ₘ rb ::ₘ mc : Multiset (Nonplanar α)) = rb ::ₘ ra ::ₘ mc :=
        Multiset.cons_swap ra rb mc
      rw [hF, hM]

/-- Doubly-applied `innerCombinerProj` over a triple cartesian product
    is symmetric in the first two factors. The substantive content of
    `cutListSummandsP_proj_perm`'s `swap` case. -/
private theorem swap_double_combinerProj
    (A B : Multiset (Forest (Nonplanar α) × Option (Nonplanar α)))
    (C : Multiset (Forest (Nonplanar α) × Multiset (Nonplanar α))) :
    (A ×ˢ (B ×ˢ C).map innerCombinerProj).map innerCombinerProj =
    (B ×ˢ (A ×ˢ C).map innerCombinerProj).map innerCombinerProj := by
  -- Convert both sides to triple-bind form, swap outer two binds via
  -- `bind_bind`, then close pointwise via `innerCombinerProj_swap_args`.
  have lhs :
      (A ×ˢ (B ×ˢ C).map innerCombinerProj).map innerCombinerProj =
        A.bind (fun a => B.bind (fun b => C.map (fun c =>
          innerCombinerProj (a, innerCombinerProj (b, c))))) := by
    show ((A.bind fun a => ((B ×ˢ C).map innerCombinerProj).map (Prod.mk a))
          ).map innerCombinerProj = _
    rw [Multiset.map_bind]
    apply Multiset.bind_congr; intro a _
    show ((((B.bind fun b => C.map (Prod.mk b)) : Multiset _).map innerCombinerProj).map
            (Prod.mk a)).map innerCombinerProj = _
    rw [Multiset.map_bind, Multiset.map_bind, Multiset.map_bind]
    apply Multiset.bind_congr; intro b _
    rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
    rfl
  have rhs :
      (B ×ˢ (A ×ˢ C).map innerCombinerProj).map innerCombinerProj =
        B.bind (fun b => A.bind (fun a => C.map (fun c =>
          innerCombinerProj (b, innerCombinerProj (a, c))))) := by
    show ((B.bind fun b => ((A ×ˢ C).map innerCombinerProj).map (Prod.mk b))
          ).map innerCombinerProj = _
    rw [Multiset.map_bind]
    apply Multiset.bind_congr; intro b _
    show ((((A.bind fun a => C.map (Prod.mk a)) : Multiset _).map innerCombinerProj).map
            (Prod.mk b)).map innerCombinerProj = _
    rw [Multiset.map_bind, Multiset.map_bind, Multiset.map_bind]
    apply Multiset.bind_congr; intro a _
    rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
    rfl
  rw [lhs, rhs, Multiset.bind_bind]
  apply Multiset.bind_congr; intro b _
  apply Multiset.bind_congr; intro a _
  apply Multiset.map_congr rfl; intro c _
  exact innerCombinerProj_swap_args a b c

/-- The projected `cutListSummandsP` is `List.Perm`-invariant: two
    permutation-related child lists yield the same projected
    cut-summand multiset. -/
theorem cutListSummandsP_proj_perm
    {cs ds : List (Planar α)} (h : cs.Perm ds) :
    (cutListSummandsP cs).map projForest =
      (cutListSummandsP ds).map projForest := by
  induction h with
  | nil => rfl
  | cons c _ ih => exact cutListSummandsP_proj_tail_lift c ih
  | swap c d cs =>
    rw [cutListSummandsP_cons_proj, cutListSummandsP_cons_proj,
        cutListSummandsP_cons_proj, cutListSummandsP_cons_proj]
    exact (swap_double_combinerProj _ _ _).symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ### Headline: PlanarStep + EqvGen lift

Substantive content: `cutSummandsP_proj_planarStep` proves projection
invariance under a single elementary step (`PlanarStep`). The
`PlanarEquiv` (`EqvGen`) and `Forall₂` versions follow as straightforward
lifts. The structural induction on `PlanarStep` handles the recursion:
the `recurse` case calls itself on a strictly smaller child tree. -/

/-- Projection invariance under a single `PlanarStep`. Structural
    induction on the step constructor: `swapAtRoot` uses
    `cutListSummandsP_proj_perm`; `recurse` uses the inductive
    hypothesis combined with `cutListSummandsP_proj_at_via_augAction`. -/
theorem cutSummandsP_proj_planarStep
    {t s : Planar α} (h : Planar.PlanarStep t s) :
    (cutSummandsP t).map projSummand =
      (cutSummandsP s).map projSummand := by
  induction h with
  | @swapAtRoot a l r pre post =>
    -- t = .node a (pre ++ l :: r :: post), s = .node a (pre ++ r :: l :: post)
    -- Use cutSummandsP_node + projSummand_node_factors + cutListSummandsP_proj_perm
    rw [cutSummandsP_node, cutSummandsP_node, Multiset.map_map, Multiset.map_map]
    have hperm : (pre ++ l :: r :: post).Perm (pre ++ r :: l :: post) :=
      List.Perm.append_left pre (List.Perm.swap r l post)
    have hL : (cutListSummandsP (pre ++ l :: r :: post)).map projForest =
              (cutListSummandsP (pre ++ r :: l :: post)).map projForest :=
      cutListSummandsP_proj_perm hperm
    -- LHS: (cutListSummandsP _).map ((projSummand) ∘ (fun p => (p.1, .node a p.2)))
    --    = (cutListSummandsP _).map (fun p => ((projForest p).1, Nonplanar.node a (projForest p).2))
    --    = ((cutListSummandsP _).map projForest).map (fun pf => (pf.1, Nonplanar.node a pf.2))
    have eq_fn :
        (projSummand (α := α)) ∘
          (fun (p : Forest (Planar α) × List (Planar α)) => (p.1, .node a p.2)) =
        (fun (pf : Forest (Nonplanar α) × Multiset (Nonplanar α)) =>
          (pf.1, Nonplanar.node a pf.2)) ∘ (projForest (α := α)) := by
      funext p
      exact projSummand_node_factors a p
    rw [eq_fn, ← Multiset.map_map, ← Multiset.map_map, hL]
  | @recurse a pre old new post hsub ih =>
    -- t = .node a (pre ++ old :: post), s = .node a (pre ++ new :: post)
    -- ih : (cutSummandsP old).map projSummand = (cutSummandsP new).map projSummand
    -- We need: (cutSummandsP t).map projSummand = (cutSummandsP s).map projSummand
    rw [cutSummandsP_node, cutSummandsP_node, Multiset.map_map, Multiset.map_map]
    have h_mk : Nonplanar.mk old = Nonplanar.mk new :=
      Nonplanar.mk_eq_mk_iff.mpr (Planar.PlanarEquiv.of_step hsub)
    have h_aug : (augActionP old).map projAugAction =
                 (augActionP new).map projAugAction :=
      augActionP_proj_eq_of_step_data h_mk ih
    have hL : (cutListSummandsP (pre ++ old :: post)).map projForest =
              (cutListSummandsP (pre ++ new :: post)).map projForest :=
      cutListSummandsP_proj_at_via_augAction h_aug
    have eq_fn :
        (projSummand (α := α)) ∘
          (fun (p : Forest (Planar α) × List (Planar α)) => (p.1, .node a p.2)) =
        (fun (pf : Forest (Nonplanar α) × Multiset (Nonplanar α)) =>
          (pf.1, Nonplanar.node a pf.2)) ∘ (projForest (α := α)) := by
      funext p
      exact projSummand_node_factors a p
    rw [eq_fn, ← Multiset.map_map, ← Multiset.map_map, hL]

/-- Projection invariance under `PlanarEquiv`. Pure `EqvGen` lift of
    `cutSummandsP_proj_planarStep`. -/
theorem cutSummandsP_proj_planarEquiv
    {t s : Planar α} (h : Planar.PlanarEquiv t s) :
    (cutSummandsP t).map projSummand =
      (cutSummandsP s).map projSummand := by
  induction h with
  | rel _ _ hstep => exact cutSummandsP_proj_planarStep hstep
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- Componentwise `PlanarEquiv` invariance for child lists. Pure
    `Forall₂` induction using `cutListSummandsP_proj_at_via_augAction`
    on the head and the IH on the tail. -/
theorem cutListSummandsP_proj_componentwise
    {cs ds : List (Planar α)}
    (h : List.Forall₂ Planar.PlanarEquiv cs ds) :
    (cutListSummandsP cs).map projForest =
      (cutListSummandsP ds).map projForest := by
  induction h with
  | nil => rfl
  | @cons c d cs' ds' hcd _ ih =>
    -- Replace c with d at head, then push cs' → ds' under d via ih.
    have h_mk : Nonplanar.mk c = Nonplanar.mk d :=
      Nonplanar.mk_eq_mk_iff.mpr hcd
    have h_proj : (cutSummandsP c).map projSummand =
                  (cutSummandsP d).map projSummand :=
      cutSummandsP_proj_planarEquiv hcd
    have h_aug : (augActionP c).map projAugAction =
                 (augActionP d).map projAugAction :=
      augActionP_proj_eq_of_step_data h_mk h_proj
    have step1 : (cutListSummandsP (c :: cs')).map projForest =
                 (cutListSummandsP (d :: cs')).map projForest := by
      have := cutListSummandsP_proj_at_via_augAction (pre := []) (post := cs') h_aug
      simpa using this
    have step2 : (cutListSummandsP (d :: cs')).map projForest =
                 (cutListSummandsP (d :: ds')).map projForest :=
      cutListSummandsP_proj_tail_lift d ih
    exact step1.trans step2

/-! ### Δ^p on Nonplanar via descent

The `cutSummandsP_proj_planarEquiv` invariance lifts `cutSummandsP`
through `Nonplanar.lift`, giving a well-defined `cutSummandsN`. The
tree-level coproduct `comulTreeN` then extends multiplicatively to a
forest-level monoid hom and finally to the algebra hom `comulAlgHomN`. -/

/-- The **Nonplanar cut-summand multiset**, defined via `Nonplanar.lift`
    using the `cutSummandsP_proj_planarEquiv` invariance. -/
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

/-- Recursive formula: `comulForestN (T ::ₘ F) = comulTreeN T * comulForestN F`. -/
@[simp] theorem comulForestN_cons (T : Nonplanar α) (F : Forest (Nonplanar α)) :
    comulForestN (R := R) (T ::ₘ F) =
      comulTreeN (R := R) T * comulForestN (R := R) F := by
  show comulForestN (R := R) (({T} : Multiset (Nonplanar α)) + F) = _
  rw [comulForestN_add]
  congr 1
  show ((({T} : Multiset (Nonplanar α)).map (comulTreeN (R := R))).prod : _) = _
  rw [Multiset.map_singleton, Multiset.prod_singleton]

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

/-! ## Phase A.7-γ — Hochschild 1-cocycle for `B+_a`

`B+_a : Forest (Nonplanar α) → Nonplanar α` is the smart constructor
`Nonplanar.node a`. Linearly extended to `bPlusLin a : H →ₗ[R] H` (sending
basis element `of' F` to `ofTree (Nonplanar.node a F)`), it satisfies
the **Hochschild 1-cocycle** property (Foissy / MCB §1.2.11):

  Δ^p ∘ B+_a = (·) ⊗ 1 ∘ B+_a + (id ⊗ B+_a) ∘ Δ^p

i.e., for every `x : H`:

  Δ^p (B+_a x) = (B+_a x) ⊗ 1 + (id ⊗ B+_a)(Δ^p x).

This is the algebraic input to Foissy's clean inductive proof of
coassociativity (§A.7-δ): the subalgebra `A := {x | (Δ ⊗ id)(Δ x) =
(id ⊗ Δ)(Δ x)}` is closed under `B+_a`, contains all leaves (which are
`B+_a 1`), hence equals the whole algebra. -/

/-! ### B+_a as a function, smart constructor, and linear map -/

/-- The **B+_a** operator: graft an unordered forest of Nonplanar trees
    under a new root labeled `a`. Identical to the smart constructor. -/
noncomputable def bPlus (a : α) (F : Forest (Nonplanar α)) :
    Nonplanar α :=
  Nonplanar.node a F

@[simp] theorem bPlus_def (a : α) (F : Forest (Nonplanar α)) :
    bPlus a F = Nonplanar.node a F := rfl

/-- The **B+_a linear map**: linearly extend the smart constructor `bPlus a`
    to an `R`-linear endomorphism of `ConnesKreimer R (Nonplanar α)`,
    sending the basis element `of' F` to `ofTree (Nonplanar.node a F)`. -/
noncomputable def bPlusLin (a : α) :
    ConnesKreimer R (Nonplanar α) →ₗ[R] ConnesKreimer R (Nonplanar α) :=
  Finsupp.lift _ R (Forest (Nonplanar α))
    (fun F => ofTree (Nonplanar.node a F))

@[simp] theorem bPlusLin_of' (a : α) (F : Forest (Nonplanar α)) :
    bPlusLin (R := R) a (of' F) = ofTree (Nonplanar.node a F) := by
  show Finsupp.lift _ R _ _ (Finsupp.single F 1) = _
  rw [Finsupp.lift_apply, Finsupp.sum_single_index] <;> simp

@[simp] theorem bPlusLin_one (a : α) :
    bPlusLin (R := R) a (1 : ConnesKreimer R (Nonplanar α)) =
      ofTree (Nonplanar.leaf a) := by
  show bPlusLin (R := R) a (of' 0) = _
  rw [bPlusLin_of']
  show ofTree (Nonplanar.node a 0) = ofTree (Nonplanar.leaf a)
  rfl

/-! ### The cocycle theorem (basis-level) -/

/-- For the empty forest: `Nonplanar.node a 0 = Nonplanar.leaf a`. -/
@[simp] theorem Nonplanar_node_zero (a : α) :
    (Nonplanar.node a (0 : Multiset (Nonplanar α)) : Nonplanar α) =
      Nonplanar.leaf a := rfl

/-- The cut summands of a leaf: only one summand `(0, leaf a)`,
    corresponding to the empty cut. -/
theorem cutSummandsN_leaf (a : α) :
    cutSummandsN (Nonplanar.leaf a : Nonplanar α) =
      ({((0 : Forest (Nonplanar α)), Nonplanar.leaf a)} : Multiset _) := by
  show (cutSummandsP (Planar.leaf a)).map (projSummand (α := α)) = _
  rw [show Planar.leaf a = Planar.node a [] from rfl, cutSummandsP_node,
      cutListSummandsP_nil, Multiset.map_singleton, Multiset.map_singleton]
  rfl

/-- The tree-level coproduct on a leaf:
    `comulTreeN (leaf a) = ofTree (leaf a) ⊗ 1 + 1 ⊗ ofTree (leaf a)`. -/
theorem comulTreeN_leaf (a : α) :
    comulTreeN (R := R) (Nonplanar.leaf a) =
      ofTree (Nonplanar.leaf a) ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)) +
      (1 : ConnesKreimer R (Nonplanar α)) ⊗ₜ[R] ofTree (Nonplanar.leaf a) := by
  unfold comulTreeN
  rw [cutSummandsN_leaf, Multiset.map_singleton, Multiset.sum_singleton, of'_zero]

/-- The **Hochschild 1-cocycle property of B+_a**, on basis elements:
    for every forest `F`, the coproduct of the grafted tree
    `Nonplanar.node a F` decomposes as the explicit primitive term plus
    the right-channel B+ application of `comulForestN F`. -/
theorem comulTreeN_node_cocycle (a : α) (F : Forest (Nonplanar α)) :
    comulTreeN (R := R) (Nonplanar.node a F) =
      ofTree (Nonplanar.node a F) ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)) +
      (LinearMap.lTensor _ (bPlusLin (R := R) a)) (comulForestN F) := by
  induction F using Multiset.induction with
  | empty =>
    rw [Nonplanar_node_zero, comulForestN_zero, comulTreeN_leaf]
    -- Goal: ofTree (leaf a) ⊗ 1 + 1 ⊗ ofTree (leaf a) =
    --       ofTree (leaf a) ⊗ 1 + (id ⊗ bPlusLin a)(1)
    congr 1
    show (1 : ConnesKreimer R (Nonplanar α)) ⊗ₜ[R] ofTree (Nonplanar.leaf a) =
         (LinearMap.lTensor _ (bPlusLin (R := R) a))
           (1 : ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α))
    show _ = (LinearMap.lTensor _ (bPlusLin (R := R) a))
              ((1 : ConnesKreimer R (Nonplanar α)) ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)))
    rw [LinearMap.lTensor_tmul, bPlusLin_one]
  | cons T F' ih =>
    -- TODO Phase A.7-γ cons case (~200-300 LOC of tensor algebra).
    -- Strategy:
    --   1. comulForestN_cons: comulForestN (T ::ₘ F') = comulTreeN T * comulForestN F'
    --   2. Decompose comulTreeN T = ofTree T ⊗ 1 + (cuts sum). Distribute multiplication.
    --   3. (id ⊗ bPlus) is linear; distributes over sum.
    --   4. (ofTree T ⊗ 1) commutes with (id ⊗ bPlus) (verify by TensorProduct.ext).
    --      Use IH to rewrite (id ⊗ bPlus)(comulForestN F') = cuts sum of (node a F').
    --      First half: (ofTree T ⊗ 1) * cuts sum of (node a F') matches "extract T whole"
    --                  branch of cuts of node a (T ::ₘ F').
    --   5. Second half: (id ⊗ bPlus)(cuts(T) * comulForestN F') matches "recurse cut"
    --      branch of cuts of node a (T ::ₘ F'). Uses cutListSummandsP_cons-style
    --      enumeration.
    --   6. Sum of both halves matches the full cuts sum of node a (T ::ₘ F') (via
    --      cutListSummandsP_cons_proj at the projected level).
    sorry

/-- The cocycle, lifted to the algebra-hom level on tree basis elements. -/
theorem comulAlgHomN_bPlusLin_cocycle (a : α) (F : Forest (Nonplanar α)) :
    comulAlgHomN (R := R) (bPlusLin (R := R) a (of' F)) =
      bPlusLin (R := R) a (of' F) ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)) +
      (LinearMap.lTensor _ (bPlusLin (R := R) a)) (comulAlgHomN (of' F)) := by
  rw [bPlusLin_of', comulAlgHomN_apply_ofTree, comulAlgHomN_apply_of']
  exact comulTreeN_node_cocycle a F

/-! ## Phase A.7-δ — Foissy clean coassoc + Bialgebra instance (PENDING)

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
