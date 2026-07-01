import Linglib.Core.Algebra.RootedTree.Coproduct.Pruning
import Linglib.Core.Algebra.RootedTree.Coproduct.TraceNonplanar
import Linglib.Core.Combinatorics.RootedTree.Nonplanar
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.TensorProduct.Maps

set_option autoImplicit false

/-!
# Δ^ρ on `ConnesKreimer R (Nonplanar α)` via projection from `RoseTree`
[marcolli-chomsky-berwick-2025] [foissy-introduction-hopf-algebras-trees]

The Nonplanar Δ^ρ is obtained by descending the tree-level Δ^ρ
(`Coproduct.lean`) through the projection `mk : RoseTree α → Nonplanar α`.
The descent requires showing that the projected cut summands
(`(cutSummandsP T).map projSummand`) depend on `T : RoseTree α` only
through `mk T`, i.e., are invariant under `RoseTree.PermEquiv`. Once
established, `Nonplanar.lift` produces `cutSummandsN`, which extends to
`comulTreeN`, `comulForestN`, and the algebra hom `comulAlgHomN`.

## Status

`[UPSTREAM]` candidate. Sorry-free. Covers: the descent
(`comulAlgHomN`), the Hochschild 1-cocycle (`comulTreeN_node_cocycle`,
`comulAlgHomN_bPlusLin_cocycle`), and the counit laws
(`counit_rTensor_comulAlgHomN`, `counit_lTensor_comulAlgHomN`).

The GL/CK duality theorem (`pairing_gl_eq_pairing_coproduct_Rho`,
classical result of [foissy-2002]), coassociativity
(`comulRhoN_coassoc` → `comulAlgHomN_coassoc_algHom`), and the
`Bialgebra (ConnesKreimer R (Nonplanar α))` instance live downstream in
`Coproduct/PruningDuality.lean` (the duality proof needs the B⁻
calculus of `BMinus.lean`, which imports this file). The full
`HopfAlgebra` instance (with antipode) lives in the sibling
`HopfAlgebraNonplanar.lean` (Phase A.8).

## Architecture

- **Projection algebra hom** (`planarToNonplanarAlg`): directly on top of
  mathlib's `AddMonoidAlgebra.mapDomainAlgHom`, applied to the additive
  monoid hom `Multiset.mapAddMonoidHom Nonplanar.mk`. The universal
  property of `AddMonoidAlgebra` does the heavy lifting.
- **Cut-summand descent** (§3): pointwise projection
  (`projSummand`/`projForest`/`projAugAction`) plus a clean factoring of
  the `cutListSummandsP` cons case as a Nonplanar-level cartesian
  product (`cutListSummandsP_cons_proj`); structural induction on
  `PermStep` for the headline invariance, with pure `EqvGen`/`Forall₂`
  lifts for `PermEquiv` and `List.Forall₂` versions.
-/

namespace RootedTree

namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α : Type*}

/-! ## Projection algebra hom `RoseTree → Nonplanar`

`Nonplanar.mk : RoseTree α → Nonplanar α` extends to an algebra hom on
`ConnesKreimer R` via `AddMonoidAlgebra.mapDomainAlgHom`. Surjective at
the carrier level; the kernel encodes PermEquiv-equivalence of forests
of trees, which is what subsequent sub-phases will need to factor through. -/

/-- The additive monoid hom from forests of tree-level trees to forests of
    nonplanar trees, given by mapping `Nonplanar.mk` componentwise. -/
noncomputable def forestProjAddHom :
    Forest (RoseTree α) →+ Forest (Nonplanar α) :=
  Multiset.mapAddMonoidHom Nonplanar.mk

/-- The **projection algebra hom** `ConnesKreimer R (RoseTree α) →ₐ[R]
    ConnesKreimer R (Nonplanar α)` induced by `Nonplanar.mk`. -/
noncomputable def planarToNonplanarAlg :
    ConnesKreimer R (RoseTree α) →ₐ[R] ConnesKreimer R (Nonplanar α) :=
  AddMonoidAlgebra.mapDomainAlgHom R R (forestProjAddHom (α := α))

/-! ## API lemmas — action on `of'` and `ofTree` -/

@[simp] theorem planarToNonplanarAlg_of' (F : Forest (RoseTree α)) :
    planarToNonplanarAlg (R := R) (of' F) =
      of' (R := R) (F.map Nonplanar.mk) := by
  show Finsupp.mapDomain (forestProjAddHom (α := α)) (Finsupp.single F 1) =
       Finsupp.single (F.map Nonplanar.mk) 1
  rw [Finsupp.mapDomain_single]
  rfl

@[simp] theorem planarToNonplanarAlg_ofTree (t : RoseTree α) :
    planarToNonplanarAlg (R := R) (ofTree t) =
      ofTree (Nonplanar.mk t) := by
  unfold ofTree
  rw [planarToNonplanarAlg_of', Multiset.map_singleton]

@[simp] theorem planarToNonplanarAlg_one :
    planarToNonplanarAlg (R := R) (1 : ConnesKreimer R (RoseTree α)) = 1 :=
  map_one _

@[simp] theorem planarToNonplanarAlg_mul
    (x y : ConnesKreimer R (RoseTree α)) :
    planarToNonplanarAlg (R := R) (x * y) =
      planarToNonplanarAlg x * planarToNonplanarAlg y :=
  map_mul _ _ _

/-! ## Phase A.7-β — projection of cut summands, descent of Δ^ρ

To descend Δ^ρ from `RoseTree` to `Nonplanar`, we need a Nonplanar-side
cut-summand multiset that is `PermEquiv`-invariant. The strategy:
project each tree-level cut summand through `mk` componentwise, then prove
the resulting multiset depends on `T : RoseTree α` only through `mk T`.

The proof factors through three layers:
- **Pointwise projection** (`projSummand`, `projForest`, `projAugAction`):
  the per-element `Nonplanar.mk` lifts.
- **Combine factoring** (`cutListSummandsP_cons_proj`): the cons case of
  `cutListSummandsP` distributes over the projection, giving a clean
  cartesian-product recursion at the `Nonplanar` level.
- **Headline lifts** (`cutSummandsP_proj_permStep`,
  `cutSummandsP_proj_permEquiv`, `cutListSummandsP_proj_componentwise`):
  structural induction on `PermStep` for the substantive content;
  pure `EqvGen` / `Forall₂` lifts for the rest. -/

/-! ### Pointwise projection -/

/-- Project a tree-level cut summand to a nonplanar one. -/
def projSummand : Forest (RoseTree α) × RoseTree α →
    Forest (Nonplanar α) × Nonplanar α :=
  fun p => (p.1.map Nonplanar.mk, Nonplanar.mk p.2)

/-- Project a `cutListSummandsP` summand to nonplanar level, discarding
    the list-order of the remainder children. The discarded order doesn't
    affect the eventual `mk (.node a remainder)`, since `mk` is invariant
    under children-list permutation (`RoseTree.permEquiv_root_perm`). -/
def projForest : Forest (RoseTree α) × List (RoseTree α) →
    Forest (Nonplanar α) × Multiset (Nonplanar α) :=
  fun p => (p.1.map Nonplanar.mk, Multiset.ofList (p.2.map Nonplanar.mk))

/-- Project an `augActionP` summand to nonplanar level (per-child decision). -/
def projAugAction : Forest (RoseTree α) × Option (RoseTree α) →
    Forest (Nonplanar α) × Option (Nonplanar α) :=
  fun p => (p.1.map Nonplanar.mk, p.2.map Nonplanar.mk)

/-- Bridge: applying `cutSummandsP_node`'s wrapper `(p.1, .node a p.2)`
    then `projSummand` factors through `projForest` followed by the
    `Nonplanar.node a` smart constructor. -/
theorem projSummand_node_factors (a : α) (p : Forest (RoseTree α) × List (RoseTree α)) :
    projSummand (p.1, .node a p.2) =
      ((projForest p).1, Nonplanar.node a (projForest p).2) := by
  show (p.1.map Nonplanar.mk, Nonplanar.mk (.node a p.2)) =
       (p.1.map Nonplanar.mk, Nonplanar.node a (Multiset.ofList (p.2.map Nonplanar.mk)))
  congr 1
  exact (Nonplanar.node_mk_tree_list a p.2).symm

/-! ### Combine factoring through projection

The cons case of `cutListSummandsP` combines a per-child decision
(`augActionP`) with the cut-summands of the remaining children. This
combination distributes over the `Nonplanar` projection: the "projected
combiner" `innerCombinerProj` operates on
`(Forest × Option) × (Forest × Multiset)` and matches `projForest` of
the inline tree-level combiner. The headline result is
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

/-- Pointwise: `projForest` of an applied tree-level combiner equals
    `innerCombinerProj` applied to the projected pair-of-pairs. -/
private theorem projForest_innerCombiner_apply
    (p : (Forest (RoseTree α) × Option (RoseTree α)) ×
         (Forest (RoseTree α) × List (RoseTree α))) :
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
    {old new : RoseTree α}
    (h_mk : Nonplanar.mk old = Nonplanar.mk new)
    (h_proj : (cutSummandsP old).map projSummand =
              (cutSummandsP new).map projSummand) :
    (augActionP old).map projAugAction =
      (augActionP new).map projAugAction := by
  rw [augActionP_eq, augActionP_eq, Multiset.map_cons, Multiset.map_cons]
  congr 1
  · -- First element (extract-whole): projAugAction ({old}, none) = ({mk old}, none)
    show (({old} : Forest (RoseTree α)).map Nonplanar.mk,
          (Option.none : Option (RoseTree α)).map Nonplanar.mk) =
         (({new} : Forest (RoseTree α)).map Nonplanar.mk,
          (Option.none : Option (RoseTree α)).map Nonplanar.mk)
    rw [Multiset.map_singleton, Multiset.map_singleton, h_mk]
  · -- Tail: projAugAction-of-projection = (s.1, some s.2) ∘ projSummand
    rw [Multiset.map_map, Multiset.map_map]
    -- Both sides now: (cutSummandsP _).map (projAugAction ∘ (fun p => (p.1, some p.2)))
    -- Rewrite this composed function as (fun s => (s.1, some s.2)) ∘ projSummand
    have eq_fn : (projAugAction (α := α)) ∘
        (fun (p : Forest (RoseTree α) × RoseTree α) => (p.1, Option.some p.2)) =
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
private theorem cutListSummandsP_cons_proj (t : RoseTree α) (ts : List (RoseTree α)) :
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
    {pre post : List (RoseTree α)} {old new : RoseTree α}
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
private theorem cutListSummandsP_proj_tail_lift (d : RoseTree α)
    {cs ds : List (RoseTree α)}
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
    {cs ds : List (RoseTree α)} (h : cs.Perm ds) :
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

/-! ### Headline: PermStep + EqvGen lift

Substantive content: `cutSummandsP_proj_permStep` proves projection
invariance under a single elementary step (`PermStep`). The
`PermEquiv` (`EqvGen`) and `Forall₂` versions follow as straightforward
lifts. The structural induction on `PermStep` handles the recursion:
the `recurse` case calls itself on a strictly smaller child tree. -/

/-- Projection invariance under a single `PermStep`. Structural
    induction on the step constructor: `swapAtRoot` uses
    `cutListSummandsP_proj_perm`; `recurse` uses the inductive
    hypothesis combined with `cutListSummandsP_proj_at_via_augAction`. -/
theorem cutSummandsP_proj_permStep
    {t s : RoseTree α} (h : RoseTree.PermStep t s) :
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
          (fun (p : Forest (RoseTree α) × List (RoseTree α)) => (p.1, .node a p.2)) =
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
      Nonplanar.mk_eq_mk_iff.mpr (RoseTree.PermEquiv.of_step hsub)
    have h_aug : (augActionP old).map projAugAction =
                 (augActionP new).map projAugAction :=
      augActionP_proj_eq_of_step_data h_mk ih
    have hL : (cutListSummandsP (pre ++ old :: post)).map projForest =
              (cutListSummandsP (pre ++ new :: post)).map projForest :=
      cutListSummandsP_proj_at_via_augAction h_aug
    have eq_fn :
        (projSummand (α := α)) ∘
          (fun (p : Forest (RoseTree α) × List (RoseTree α)) => (p.1, .node a p.2)) =
        (fun (pf : Forest (Nonplanar α) × Multiset (Nonplanar α)) =>
          (pf.1, Nonplanar.node a pf.2)) ∘ (projForest (α := α)) := by
      funext p
      exact projSummand_node_factors a p
    rw [eq_fn, ← Multiset.map_map, ← Multiset.map_map, hL]

/-- Projection invariance under `PermEquiv`. Pure `EqvGen` lift of
    `cutSummandsP_proj_permStep`. -/
theorem cutSummandsP_proj_permEquiv
    {t s : RoseTree α} (h : RoseTree.PermEquiv t s) :
    (cutSummandsP t).map projSummand =
      (cutSummandsP s).map projSummand := by
  induction h with
  | rel _ _ hstep => exact cutSummandsP_proj_permStep hstep
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- Componentwise `PermEquiv` invariance for child lists. Pure
    `Forall₂` induction using `cutListSummandsP_proj_at_via_augAction`
    on the head and the IH on the tail. -/
theorem cutListSummandsP_proj_componentwise
    {cs ds : List (RoseTree α)}
    (h : List.Forall₂ RoseTree.PermEquiv cs ds) :
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
      cutSummandsP_proj_permEquiv hcd
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

/-! ### Δ^ρ on Nonplanar via descent

The `cutSummandsP_proj_permEquiv` invariance lifts `cutSummandsP`
through `Nonplanar.lift`, giving a well-defined `cutSummandsN`. The
tree-level coproduct `comulTreeN` then extends multiplicatively to a
forest-level monoid hom and finally to the algebra hom `comulAlgHomN`. -/

/-- The **Nonplanar cut-summand multiset**, defined via `Nonplanar.lift`
    using the `cutSummandsP_proj_permEquiv` invariance. -/
noncomputable def cutSummandsN :
    Nonplanar α → Multiset (Forest (Nonplanar α) × Nonplanar α) :=
  Nonplanar.lift (fun T => (cutSummandsP T).map projSummand)
    (fun _ _ h => cutSummandsP_proj_permEquiv h)

@[simp] theorem cutSummandsN_mk (T : RoseTree α) :
    cutSummandsN (Nonplanar.mk T) = (cutSummandsP T).map projSummand := rfl

/-- The **nonplanar tree-level Δ^ρ**: explicit `T ⊗ 1` term plus the
    sum of cut-summand tensors at the Nonplanar level. -/
noncomputable def comulTreeN (T : Nonplanar α) :
    ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) :=
  ofTree T ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α))
  + ((cutSummandsN T).map
      (fun p => of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)).sum

/-- A **filtered nonplanar tree-level Δ^ρ**: the `T ⊗ 1` primitive term plus
    the cut-summand sum restricted to summands satisfying `pred`. Generalizes
    `comulTreeN` (the `pred = always-true` case); used to carve phase-restricted
    sub-coproducts (e.g. the phase coproduct Δ^c_Φ of
    [marcolli-chomsky-berwick-2025] §1.14). -/
noncomputable def comulTreeNFiltered (T : Nonplanar α)
    (pred : Forest (Nonplanar α) × Nonplanar α → Prop) [DecidablePred pred] :
    ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) :=
  ofTree T ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α))
  + (((cutSummandsN T).filter pred).map
      (fun p => of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)).sum

/-- The filter drops nothing when every cut summand satisfies `pred`, recovering
    the full `comulTreeN`. -/
theorem comulTreeNFiltered_eq_comulTreeN (T : Nonplanar α)
    (pred : Forest (Nonplanar α) × Nonplanar α → Prop) [DecidablePred pred]
    (hAll : ∀ p ∈ cutSummandsN T, pred p) :
    comulTreeNFiltered (R := R) T pred = comulTreeN (R := R) T := by
  unfold comulTreeNFiltered comulTreeN
  rw [Multiset.filter_eq_self.mpr hAll]

/-- The **nonplanar forest-level Δ^ρ**: multiplicative product of
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

/-- The **Δ^ρ coproduct on `ConnesKreimer R (Nonplanar α)`** as an
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

  Δ^ρ ∘ B+_a = (·) ⊗ 1 ∘ B+_a + (id ⊗ B+_a) ∘ Δ^ρ

i.e., for every `x : H`:

  Δ^ρ (B+_a x) = (B+_a x) ⊗ 1 + (id ⊗ B+_a)(Δ^ρ x).

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

/-! ### `augActionN` and `cutForestSummandsN` substrate

`cutForestSummandsN F` is the Nonplanar-level multiset of
`(cut_forest, remainder_forest)` pairs ranging over per-tree decisions
on the forest `F`. Each per-tree decision (`augActionN T`) is either
"extract `T` whole" (pair `({T}, none)`) or "recurse with a cut summand
of `T`" (pair `(s.1, some s.2)` for `s ∈ cutSummandsN T`).

Defined recursively at the Nonplanar level via `Multiset.foldr`, with
the `LeftCommutative` obligation discharged by `swap_double_combinerProj`
(the per-tree-decision swap symmetry, established for the tree-level
projection in §3 above and reused here verbatim). -/

/-- Per-tree decision multiset at the Nonplanar level: extract this tree
    whole (`({T}, none)`), or recurse into a cut summand. -/
noncomputable def augActionN (T : Nonplanar α) :
    Multiset (Forest (Nonplanar α) × Option (Nonplanar α)) :=
  (({T} : Forest (Nonplanar α)), Option.none) ::ₘ
    (cutSummandsN T).map (fun s => (s.1, Option.some s.2))

/-- Bridge to the tree-level `augActionP`: at a tree-level lift, `augActionN`
    agrees with `(augActionP T).map projAugAction`. -/
private theorem augActionN_mk (T : RoseTree α) :
    augActionN (Nonplanar.mk T) = (augActionP T).map projAugAction := by
  unfold augActionN
  simp only [cutSummandsN_mk, augActionP_eq, Multiset.map_cons, Multiset.map_map]
  rfl

/-- Multiset.foldr combiner for `cutForestSummandsN`: combine a per-tree
    decision with the accumulated cuts of the remaining trees via the
    cartesian product and `innerCombinerProj`. -/
private noncomputable def cutForestCombinerN (T : Nonplanar α)
    (acc : Multiset (Forest (Nonplanar α) × Forest (Nonplanar α))) :
    Multiset (Forest (Nonplanar α) × Forest (Nonplanar α)) :=
  (augActionN T ×ˢ acc).map innerCombinerProj

/-- The combiner is left-commutative — discharged by `swap_double_combinerProj`,
    the per-tree-decision swap symmetry of `innerCombinerProj`. -/
private instance : LeftCommutative (cutForestCombinerN (α := α)) where
  left_comm _ _ _ := swap_double_combinerProj _ _ _

/-- The **forest cut summand multiset**: every per-tree decision tuple on
    `F : Forest (Nonplanar α)` produces a pair `(cut_forest, remainder_forest)`,
    and `cutForestSummandsN F` enumerates them all (as a multiset). The
    public Nonplanar-level analog of `(cutListSummandsP ps).map projForest`,
    independent of the tree-level list representation. -/
noncomputable def cutForestSummandsN (F : Forest (Nonplanar α)) :
    Multiset (Forest (Nonplanar α) × Forest (Nonplanar α)) :=
  Multiset.foldr cutForestCombinerN
    ({((0 : Forest (Nonplanar α)), (0 : Forest (Nonplanar α)))} : Multiset _) F

@[simp] theorem cutForestSummandsN_zero :
    cutForestSummandsN (0 : Forest (Nonplanar α)) =
      ({((0 : Forest (Nonplanar α)), (0 : Forest (Nonplanar α)))} : Multiset _) := rfl

@[simp] theorem cutForestSummandsN_cons (T : Nonplanar α) (F : Forest (Nonplanar α)) :
    cutForestSummandsN (T ::ₘ F) =
      (augActionN T ×ˢ cutForestSummandsN F).map innerCombinerProj := by
  show Multiset.foldr cutForestCombinerN _ (T ::ₘ F) = _
  rw [Multiset.foldr_cons]
  rfl

/-! ### Bridges to the tree-level list representation

The tree-level substrate `cutListSummandsP` (defined on `List (RoseTree α)`)
is reused to evaluate `cutForestSummandsN` on a tree-level list rep, and
to characterize cuts of a Nonplanar node. These bridges are private —
the public `cutSummandsN_node` and `comulForestN_eq_sum` are stated
purely at the Nonplanar level. -/

/-- Witness: every `F : Forest (Nonplanar α)` has a tree-level list
    representative. Used internally to lift tree-level-side characterizations
    to the Nonplanar level. -/
private theorem exists_planar_list_rep (F : Forest (Nonplanar α)) :
    ∃ ps : List (RoseTree α), F = Multiset.ofList (ps.map Nonplanar.mk) := by
  refine ⟨F.toList.map Quotient.out, ?_⟩
  conv_lhs => rw [← Multiset.coe_toList F]
  congr 1
  rw [List.map_map]
  conv_lhs => rw [show F.toList = F.toList.map id from (List.map_id _).symm]
  apply List.map_congr_left
  intro x _
  exact (Quotient.out_eq x).symm

/-- `cutForestSummandsN` evaluated on a tree-level list rep agrees with the
    tree-level `cutListSummandsP` projected through `projForest`. By
    induction on `ps` using `cutListSummandsP_cons_proj` and
    `augActionN_mk`. -/
private theorem cutForestSummandsN_via_planar_list (ps : List (RoseTree α)) :
    cutForestSummandsN (Multiset.ofList (ps.map Nonplanar.mk)) =
      (cutListSummandsP ps).map projForest := by
  induction ps with
  | nil =>
    show cutForestSummandsN (0 : Forest (Nonplanar α)) = _
    rw [cutForestSummandsN_zero, cutListSummandsP_nil, Multiset.map_singleton]
    rfl
  | cons p ps' ih =>
    show cutForestSummandsN (Nonplanar.mk p ::ₘ Multiset.ofList (ps'.map Nonplanar.mk)) = _
    rw [cutForestSummandsN_cons, ih, augActionN_mk]
    exact (cutListSummandsP_cons_proj p ps').symm

/-- Cuts of a node decompose via the tree-level `cutListSummandsP` projected
    through `projForest` — the tree-level-list-rep form of `cutSummandsN_node`.
    The map `(p ↦ (p.1, Nonplanar.node a p.2))` re-grafts the remainder
    children onto a fresh root with label `a`. -/
private theorem cutSummandsN_node_planar_list (a : α) (ps : List (RoseTree α)) :
    cutSummandsN (Nonplanar.node a (Multiset.ofList (ps.map Nonplanar.mk))) =
      ((cutListSummandsP ps).map projForest).map
        (fun pf => (pf.1, Nonplanar.node a pf.2)) := by
  rw [Nonplanar.node_mk_tree_list]
  show (cutSummandsP (RoseTree.node a ps)).map (projSummand (α := α)) = _
  rw [cutSummandsP_node, Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro p _
  show (p.1.map Nonplanar.mk, Nonplanar.mk (.node a p.2)) =
       ((projForest p).1, Nonplanar.node a (projForest p).2)
  rw [← Nonplanar.node_mk_tree_list]
  rfl

/-! ### Tensor-algebra and multiset distributivity helpers -/

/-- The fundamental distributivity in `H ⊗ H` for basis-vector tensors:
    `(of' a ⊗ of' b) * (of' c ⊗ of' d) = of' (a + c) ⊗ of' (b + d)`.
    Combines `Algebra.TensorProduct.tmul_mul_tmul` with `of'_add` on
    both channels. -/
private theorem of'_tmul_mul_of'_tmul (a b c d : Forest (Nonplanar α)) :
    (of' (R := R) a ⊗ₜ[R] of' (R := R) b) * (of' (R := R) c ⊗ₜ[R] of' (R := R) d) =
      of' (R := R) (a + c) ⊗ₜ[R] of' (R := R) (b + d) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, ← of'_add, ← of'_add]

/-- Cartesian product distributes the head map: `(s.map f) ×ˢ t = s.bind (a ↦ t.map (Prod.mk (f a)))`.
    Pure `Multiset.product`/`Multiset.bind_map` algebra; included locally because mathlib
    doesn't ship this exact form. -/
private theorem map_first_product {β γ δ : Type*}
    (f : β → γ) (s : Multiset β) (t : Multiset δ) :
    (s.map f) ×ˢ t = s.bind (fun a => t.map (Prod.mk (f a))) :=
  Multiset.bind_map s _ f

/-! ### Public API

The two structural facts that drive the cocycle: cuts of a node
decompose along `cutForestSummandsN`, and `comulForestN` expands as the
multiset sum over `cutForestSummandsN`. Both are pure Nonplanar-level
statements; tree-level substrate is invisible to consumers. -/

/-- Cuts of `Nonplanar.node a F` decompose along the per-tree decisions
    of `F`: each pair `(cf, rem) ∈ cutForestSummandsN F` gives a cut
    summand `(cf, Nonplanar.node a rem)`. The Nonplanar-level form. -/
@[simp] theorem cutSummandsN_node (a : α) (F : Forest (Nonplanar α)) :
    cutSummandsN (Nonplanar.node a F) =
      (cutForestSummandsN F).map (fun pf => (pf.1, Nonplanar.node a pf.2)) := by
  obtain ⟨ps, hps⟩ := exists_planar_list_rep F
  subst hps
  rw [cutSummandsN_node_planar_list, ← cutForestSummandsN_via_planar_list]

/-- Extract-branch of the `comulForestN_eq_sum` cons step: `(ofTree T ⊗ 1)`
    times the forest-cuts sum collapses into the "extract T whole"
    summand of `cutForestSummandsN_cons` (the `({T}, none)` decision). -/
private theorem comulForestN_cons_extract_branch (T : Nonplanar α)
    (P : Multiset (Forest (Nonplanar α) × Forest (Nonplanar α))) :
    (ofTree T ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α))) *
        (P.map (fun p => of' (R := R) p.1 ⊗ₜ[R] of' (R := R) p.2)).sum =
      (((P.map (Prod.mk
          (({T}, Option.none) : Forest (Nonplanar α) × Option (Nonplanar α)))).map
        innerCombinerProj).map
        (fun p => of' (R := R) p.1 ⊗ₜ[R] of' (R := R) p.2)).sum := by
  rw [← of'_singleton, ← of'_zero (R := R) (T := Nonplanar α),
      ← Multiset.sum_map_mul_left]
  simp only [Multiset.map_map]
  refine congr_arg Multiset.sum (Multiset.map_congr rfl (fun p _ => ?_))
  show (of' (R := R) ({T} : Forest (Nonplanar α)) ⊗ₜ[R] of' (R := R) 0) *
        (of' (R := R) p.1 ⊗ₜ[R] of' (R := R) p.2) =
       ((fun p => of' (R := R) p.1 ⊗ₜ[R] of' (R := R) p.2) ∘ innerCombinerProj ∘
          Prod.mk (({T}, Option.none) :
            Forest (Nonplanar α) × Option (Nonplanar α))) p
  rw [of'_tmul_mul_of'_tmul, zero_add]
  rfl

/-- Recurse-branch of the `comulForestN_eq_sum` cons step: the
    `cutSummandsN T`-indexed sum part of `comulTreeN T` times the
    forest-cuts sum collapses into the cartesian product of
    "recurse-with-cut" decisions on `T` against the rest. -/
private theorem comulForestN_cons_recurse_branch (T : Nonplanar α)
    (P : Multiset (Forest (Nonplanar α) × Forest (Nonplanar α))) :
    (((cutSummandsN T).map (fun s => of' (R := R) s.1 ⊗ₜ[R] ofTree s.2)).sum) *
        (P.map (fun p => of' (R := R) p.1 ⊗ₜ[R] of' (R := R) p.2)).sum =
      (((((cutSummandsN T).map (fun s => (s.1, Option.some s.2))) ×ˢ P).map
        innerCombinerProj).map
        (fun p => of' (R := R) p.1 ⊗ₜ[R] of' (R := R) p.2)).sum := by
  rw [← Multiset.sum_map_mul_right,
      show (cutSummandsN T).map (fun s =>
        (of' (R := R) s.1 ⊗ₜ[R] ofTree s.2) *
        (P.map (fun p => of' (R := R) p.1 ⊗ₜ[R] of' (R := R) p.2)).sum) =
      (cutSummandsN T).map (fun s =>
        (P.map (fun p => of' (R := R) (s.1 + p.1) ⊗ₜ[R]
          of' (R := R) (s.2 ::ₘ p.2))).sum) from
        Multiset.map_congr rfl (fun s _ => by
          rw [← of'_singleton (R := R) s.2, ← Multiset.sum_map_mul_left]
          refine congr_arg Multiset.sum
            (Multiset.map_congr rfl (fun p _ => ?_))
          rw [of'_tmul_mul_of'_tmul, Multiset.singleton_add]),
      ← Multiset.sum_bind, map_first_product]
  simp only [Multiset.map_bind, Multiset.map_map]
  refine congr_arg Multiset.sum (Multiset.bind_congr (fun s _ => ?_))
  apply Multiset.map_congr rfl
  intro p _
  rfl

/-- The forest coproduct `comulForestN F` expands as a multiset sum of
    `of' cf ⊗ of' rem` over `(cf, rem) ∈ cutForestSummandsN F`. -/
theorem comulForestN_eq_sum (F : Forest (Nonplanar α)) :
    comulForestN (R := R) F = ((cutForestSummandsN F).map
      (fun pf => of' (R := R) pf.1 ⊗ₜ[R] of' (R := R) pf.2)).sum := by
  induction F using Multiset.induction with
  | empty =>
    rw [comulForestN_zero, cutForestSummandsN_zero,
        Multiset.map_singleton, Multiset.sum_singleton, of'_zero]
    rfl
  | cons T F' ih =>
    rw [comulForestN_cons, ih, cutForestSummandsN_cons]
    unfold comulTreeN augActionN
    rw [add_mul, Multiset.cons_product, Multiset.map_add, Multiset.map_add, Multiset.sum_add,
        comulForestN_cons_extract_branch, comulForestN_cons_recurse_branch]

/-! ### The cocycle theorem (basis-level) -/

/-- For the empty forest: `Nonplanar.node a 0 = Nonplanar.leaf a`. -/
@[simp] theorem node_zero_eq_leaf (a : α) :
    (Nonplanar.node a (0 : Multiset (Nonplanar α)) : Nonplanar α) =
      Nonplanar.leaf a := rfl

/-- The cut summands of a leaf: only one summand `(0, leaf a)`,
    corresponding to the empty cut. -/
theorem cutSummandsN_leaf (a : α) :
    cutSummandsN (Nonplanar.leaf a : Nonplanar α) =
      ({((0 : Forest (Nonplanar α)), Nonplanar.leaf a)} : Multiset _) := by
  show (cutSummandsP (RoseTree.leaf a)).map (projSummand (α := α)) = _
  rw [show RoseTree.leaf a = RoseTree.node a [] from rfl, cutSummandsP_node,
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
    the right-channel B+ application of `comulForestN F`. Proven via
    the substrate `cutSummandsN_node` (cuts of a node decompose along
    `cutForestSummandsN F`) and `comulForestN_eq_sum` (forest coproduct
    expands as the matching multiset sum); the `LinearMap.lTensor`
    distributes over the sum via `map_multiset_sum`, and the per-summand
    check reduces to `LinearMap.lTensor_tmul` + `bPlusLin_of'`. -/
theorem comulTreeN_node_cocycle (a : α) (F : Forest (Nonplanar α)) :
    comulTreeN (R := R) (Nonplanar.node a F) =
      ofTree (Nonplanar.node a F) ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)) +
      (LinearMap.lTensor _ (bPlusLin (R := R) a)) (comulForestN F) := by
  unfold comulTreeN
  rw [cutSummandsN_node, comulForestN_eq_sum,
      map_multiset_sum (LinearMap.lTensor (ConnesKreimer R (Nonplanar α))
        (bPlusLin (R := R) a))]
  simp only [Multiset.map_map]
  refine congr_arg (_ + ·) (congr_arg Multiset.sum
    (Multiset.map_congr rfl (fun pf _ => ?_)))
  show of' (R := R) pf.1 ⊗ₜ[R] ofTree (Nonplanar.node a pf.2) =
       (LinearMap.lTensor (ConnesKreimer R (Nonplanar α)) (bPlusLin (R := R) a))
         (of' (R := R) pf.1 ⊗ₜ[R] of' (R := R) pf.2)
  rw [LinearMap.lTensor_tmul, bPlusLin_of']

/-- The cocycle, lifted to the algebra-hom level on tree basis elements. -/
theorem comulAlgHomN_bPlusLin_cocycle (a : α) (F : Forest (Nonplanar α)) :
    comulAlgHomN (R := R) (bPlusLin (R := R) a (of' F)) =
      bPlusLin (R := R) a (of' F) ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)) +
      (LinearMap.lTensor _ (bPlusLin (R := R) a)) (comulAlgHomN (of' F)) := by
  rw [bPlusLin_of', comulAlgHomN_apply_ofTree, comulAlgHomN_apply_of']
  exact comulTreeN_node_cocycle a F

/-! ## Phase A.7-δ — Counit laws + coassoc via GL/CK duality + `Bialgebra`

Counit laws follow by reducing to the tree case via
`AddMonoidAlgebra.algHom_ext` + multiplicativity (the empty-cut summand
contributes `1 ⊗ of' F`; all others are killed by `counit`).

Coassociativity uses GL/CK duality: `comulRhoN_coassoc` (LinearMap form)
is derived from `pairing_gl_eq_pairing_coproduct_Rho` (Foissy axiom) +
`GrossmanLarson.mul_assoc` via `pairing₃_unique`; the AlgHom form
`comulAlgHomN_coassoc_algHom` is a one-line lift. This replaces the
earlier direct Foissy-clean proof (≈ 350 LOC, deleted in R.8 Phase 2):
both Δ^ρ and Δ^c coassoc now use a single GL-duality framework.

The final `Bialgebra` instance is assembled via `Bialgebra.ofAlgHom`. -/

/-! ### Empty cut existence (substrate for counit laws)

The empty cut `(0, T)` is always a cut summand of `T`. The tree-level
substrate `cutSummandsP T` always contains `(0, T)`, by mutual structural
induction with `cutListSummandsP`; the nonplanar `cutForestSummandsN F`
contains `(0, F)` by descent. These witnesses split the `(counit ⊗ id)`
sum into a single non-vanishing summand `1 ⊗ of' F`. -/

mutual

/-- The empty cut `(0, T)` is a cut summand of every tree-level tree `T`. -/
private theorem mem_cutSummandsP_zero : ∀ (T : RoseTree α),
    ((0 : Forest (RoseTree α)), T) ∈ cutSummandsP T
  | .node a children => by
    rw [cutSummandsP_node, Multiset.mem_map]
    exact ⟨(0, children), mem_cutListSummandsP_zero children, rfl⟩

/-- The empty cut `(0, ps)` is a list cut summand of every tree-level list `ps`. -/
private theorem mem_cutListSummandsP_zero : ∀ (ps : List (RoseTree α)),
    ((0 : Forest (RoseTree α)), ps) ∈ cutListSummandsP ps
  | [] => by
    rw [cutListSummandsP_nil]; exact Multiset.mem_singleton.mpr rfl
  | t :: ts => by
    rw [cutListSummandsP_cons, Multiset.mem_map]
    refine ⟨((0, Option.some t), (0, ts)), ?_, ?_⟩
    · rw [Multiset.mem_product, augActionP_eq, Multiset.mem_cons]
      refine ⟨Or.inr ?_, mem_cutListSummandsP_zero ts⟩
      rw [Multiset.mem_map]
      exact ⟨(0, t), mem_cutSummandsP_zero t, rfl⟩
    · -- The cons combiner with `(0, some t)` and `(0, ts)` gives `(0, t :: ts)`
      -- via `0 + 0 = 0`.
      show (((0 : Forest (RoseTree α)) + (0 : Forest (RoseTree α))), t :: ts) =
           ((0 : Forest (RoseTree α)), t :: ts)
      rw [zero_add]

end

/-- The empty cut `(0, F)` is a forest cut summand of every nonplanar forest `F`. -/
private theorem cutForestSummandsN_zero_mem (F : Forest (Nonplanar α)) :
    ((0 : Forest (Nonplanar α)), F) ∈ cutForestSummandsN F := by
  obtain ⟨ps, rfl⟩ := exists_planar_list_rep F
  rw [cutForestSummandsN_via_planar_list, Multiset.mem_map]
  refine ⟨(0, ps), mem_cutListSummandsP_zero ps, ?_⟩
  show ((0 : Forest (RoseTree α)).map Nonplanar.mk,
        Multiset.ofList (ps.map Nonplanar.mk)) =
       ((0 : Forest (Nonplanar α)), Multiset.ofList (ps.map Nonplanar.mk))
  rw [Multiset.map_zero]

/-! ### Tree-depth induction substrate -/

/-- A tree's depth is strictly less than the depth of any node containing
    it as a child. -/
theorem Nonplanar.depth_lt_of_mem (T : Nonplanar α) (F : Forest (Nonplanar α))
    (hT : T ∈ F) (a : α) : T.depth < (Nonplanar.node a F).depth := by
  obtain ⟨ps, hps⟩ := exists_planar_list_rep F
  subst hps
  rw [Nonplanar.node_mk_tree_list]
  show T.depth < (RoseTree.node a ps).depth
  rw [RoseTree.depth_node]
  rw [show (Multiset.ofList (ps.map Nonplanar.mk) : Forest (Nonplanar α)) =
        ((ps.map Nonplanar.mk : List (Nonplanar α)) : Multiset _) from rfl,
      Multiset.mem_coe, List.mem_map] at hT
  obtain ⟨c, hc, rfl⟩ := hT
  show (Nonplanar.mk c).depth < 1 + (ps.map RoseTree.depth).foldr max 0
  rw [Nonplanar.depth_mk, Nat.add_comm]
  exact Nat.lt_succ_of_le (RoseTree.depth_le_foldr_max hc)

/-! ### Counit ⊗ id commutation with `lTensor (bPlusLin a)`

The factor-wise commutation `(counit ⊗ id) ∘ (id ⊗ B+_a) = (id ⊗ B+_a) ∘ (counit ⊗ id)`
(where the right `id` is on different domains: `H` on the left, `R` on the right).
Pure `TensorProduct.induction_on` calculation; both sides reduce to
`counit x ⊗ B+_a y` on simple tensors. Used in the tree-level counit law and
in the bPlus closure proof. -/

private theorem counit_rTensor_lTensor_bPlus_apply (a : α)
    (z : ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) :
    (Algebra.TensorProduct.map (counit (R := R))
        (AlgHom.id R (ConnesKreimer R (Nonplanar α))))
      ((LinearMap.lTensor _ (bPlusLin (R := R) a)) z) =
    (LinearMap.lTensor R (bPlusLin (R := R) a))
      ((Algebra.TensorProduct.map (counit (R := R))
        (AlgHom.id R (ConnesKreimer R (Nonplanar α)))) z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul x y =>
    rw [LinearMap.lTensor_tmul, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply,
        LinearMap.lTensor_tmul]
  | add z₁ z₂ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂, map_add, map_add]

/-! ### Symmetric: id ⊗ counit commutation with `lTensor (bPlusLin a)`

Mirror of `counit_rTensor_lTensor_bPlus_apply`. Acting on the right factor with
counit and on the left factor with B+_a — they don't interact. -/

private theorem counit_lTensor_lTensor_bPlus_apply (a : α)
    (z : ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) :
    (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
        (counit (R := R)))
      ((LinearMap.rTensor _ (bPlusLin (R := R) a)) z) =
    (LinearMap.rTensor R (bPlusLin (R := R) a))
      ((Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
        (counit (R := R))) z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul x y =>
    rw [LinearMap.rTensor_tmul, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply,
        LinearMap.rTensor_tmul]
  | add z₁ z₂ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂, map_add, map_add]

/-! ### Tree-level counit law (depth induction)

`(counit ⊗ id)(Δ T) = 1 ⊗ T` for every nonplanar tree `T`. Strong induction
on `T.depth`: leaves close directly via `comulTreeN_leaf`; nodes use the
cocycle `comulTreeN_node_cocycle`, the commutation
`counit_rTensor_lTensor_bPlus_apply`, and the forest law on the children. -/

private theorem comulForestN_counit_rTensor (F : Forest (Nonplanar α))
    (hF : ∀ T ∈ F, (Algebra.TensorProduct.map (counit (R := R))
        (AlgHom.id R (ConnesKreimer R (Nonplanar α)))) (comulTreeN T) =
      (1 : R) ⊗ₜ ofTree T) :
    (Algebra.TensorProduct.map (counit (R := R))
        (AlgHom.id R (ConnesKreimer R (Nonplanar α))))
      (comulForestN F) = (1 : R) ⊗ₜ of' F := by
  induction F using Multiset.induction with
  | empty =>
    rw [comulForestN_zero, map_one, of'_zero, Algebra.TensorProduct.one_def]
  | cons T F' ih =>
    have ih' := ih (fun T' hT' => hF T' (Multiset.mem_cons_of_mem hT'))
    have hT := hF T (Multiset.mem_cons_self T F')
    rw [comulForestN_cons, map_mul, hT, ih',
        Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        show (ofTree T : ConnesKreimer R (Nonplanar α)) * of' F' =
              of' (T ::ₘ F') from by
          rw [show (T ::ₘ F' : Forest (Nonplanar α)) = {T} + F' from
                (Multiset.singleton_add T F').symm,
              of'_add, of'_singleton]]

private theorem comulForestN_counit_lTensor (F : Forest (Nonplanar α))
    (hF : ∀ T ∈ F, (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
        (counit (R := R))) (comulTreeN T) =
      ofTree T ⊗ₜ (1 : R)) :
    (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
        (counit (R := R)))
      (comulForestN F) = of' F ⊗ₜ (1 : R) := by
  induction F using Multiset.induction with
  | empty =>
    rw [comulForestN_zero, map_one, of'_zero, Algebra.TensorProduct.one_def]
  | cons T F' ih =>
    have ih' := ih (fun T' hT' => hF T' (Multiset.mem_cons_of_mem hT'))
    have hT := hF T (Multiset.mem_cons_self T F')
    rw [comulForestN_cons, map_mul, hT, ih',
        Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        show (ofTree T : ConnesKreimer R (Nonplanar α)) * of' F' =
              of' (T ::ₘ F') from by
          rw [show (T ::ₘ F' : Forest (Nonplanar α)) = {T} + F' from
                (Multiset.singleton_add T F').symm,
              of'_add, of'_singleton]]

private theorem comulTreeN_counit_rTensor (T : Nonplanar α) :
    (Algebra.TensorProduct.map (counit (R := R))
        (AlgHom.id R (ConnesKreimer R (Nonplanar α))))
      (comulTreeN T) = (1 : R) ⊗ₜ ofTree T := by
  -- Strong induction on T.depth.
  suffices aux : ∀ n : ℕ, ∀ T : Nonplanar α, T.depth = n →
      (Algebra.TensorProduct.map (counit (R := R))
          (AlgHom.id R (ConnesKreimer R (Nonplanar α))))
        (comulTreeN T) = (1 : R) ⊗ₜ ofTree T by
    exact aux T.depth T rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro T hT
    -- Pick a tree-level rep T = mk (.node a children).
    obtain ⟨T₀, rfl⟩ : ∃ T₀ : RoseTree α, T = Nonplanar.mk T₀ :=
      ⟨Quotient.out T, (Quotient.out_eq T).symm⟩
    obtain ⟨a, children⟩ := T₀
    rw [show (Nonplanar.mk (RoseTree.node a children) : Nonplanar α) =
        Nonplanar.node a (Multiset.ofList (children.map Nonplanar.mk))
        from (Nonplanar.node_mk_tree_list a children).symm]
    -- Use cocycle.
    rw [comulTreeN_node_cocycle, map_add]
    -- First summand vanishes via counit_ofTree.
    rw [show (Algebra.TensorProduct.map (counit (R := R))
            (AlgHom.id R (ConnesKreimer R (Nonplanar α))))
          (ofTree (Nonplanar.node a (Multiset.ofList (children.map Nonplanar.mk))) ⊗ₜ
            (1 : ConnesKreimer R (Nonplanar α))) = 0 from by
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, counit_ofTree,
          TensorProduct.zero_tmul], zero_add]
    -- Second summand: commutation + forest law.
    rw [counit_rTensor_lTensor_bPlus_apply,
        comulForestN_counit_rTensor (R := R)
          (Multiset.ofList (children.map Nonplanar.mk))
          (fun T' hT' => by
            apply IH T'.depth ?_ T' rfl
            have hlt := Nonplanar.depth_lt_of_mem T' _ hT' a
            rw [show (Nonplanar.node a (Multiset.ofList (children.map Nonplanar.mk)) :
                  Nonplanar α) =
                Nonplanar.mk (RoseTree.node a children) from
                Nonplanar.node_mk_tree_list a children] at hlt
            rw [hT] at hlt
            exact hlt),
        LinearMap.lTensor_tmul, bPlusLin_of']

/-- `counit ∘ B+_a = 0` as a linear map. The image of `B+_a` lies in the
    span of `ofTree`s on non-leaf trees, all of which have card-1 forests
    so counit kills them. Proven by reducing the linear-map equality to
    basis vectors via `Finsupp.lhom_ext`, then computing on `of' F`. -/
private theorem counit_bPlusLin (a : α) (y : ConnesKreimer R (Nonplanar α)) :
    counit (R := R) (bPlusLin (R := R) a y) = 0 := by
  -- Both maps are R-linear; reduce to checking equality of the composite with 0
  -- as a LinearMap, then evaluate at y.
  have h : ((counit (R := R)).toLinearMap.comp (bPlusLin (R := R) a) :
           ConnesKreimer R (Nonplanar α) →ₗ[R] R) = 0 := by
    apply Finsupp.lhom_ext
    intro F r
    show counit (bPlusLin a (Finsupp.single F r)) = (0 : R)
    -- Convert `single F r` to `r • of' F`, then push through linearity.
    have hr : (Finsupp.single F r : ConnesKreimer R (Nonplanar α))
              = (r : R) • (of' F : ConnesKreimer R (Nonplanar α)) := by
      show Finsupp.single F r = r • Finsupp.single F (1 : R)
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hr]
    -- Force re-elaboration through Module-flavored smul.
    change counit (R := R) (bPlusLin a ((r : R) • (of' F : ConnesKreimer R (Nonplanar α)))) =
           (0 : R)
    rw [(bPlusLin (R := R) a).map_smul, bPlusLin_of',
        _root_.map_smul (counit (R := R)) r, counit_ofTree, smul_zero]
  -- Apply h pointwise to y.
  have := congrFun (congrArg DFunLike.coe h) y
  simpa using this

private theorem comulTreeN_counit_lTensor (T : Nonplanar α) :
    (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
        (counit (R := R)))
      (comulTreeN T) = ofTree T ⊗ₜ (1 : R) := by
  -- Strong induction on T.depth.
  suffices aux : ∀ n : ℕ, ∀ T : Nonplanar α, T.depth = n →
      (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
          (counit (R := R)))
        (comulTreeN T) = ofTree T ⊗ₜ (1 : R) by
    exact aux T.depth T rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n _IH =>
    intro T _hT
    obtain ⟨T₀, rfl⟩ : ∃ T₀ : RoseTree α, T = Nonplanar.mk T₀ :=
      ⟨Quotient.out T, (Quotient.out_eq T).symm⟩
    obtain ⟨a, children⟩ := T₀
    rw [show (Nonplanar.mk (RoseTree.node a children) : Nonplanar α) =
        Nonplanar.node a (Multiset.ofList (children.map Nonplanar.mk))
        from (Nonplanar.node_mk_tree_list a children).symm]
    -- Use cocycle: comulTreeN T = ofTree T ⊗ 1 + (id ⊗ bPlusLin a)(comulForestN F).
    rw [comulTreeN_node_cocycle, map_add]
    -- First summand: (id ⊗ counit)(ofTree T ⊗ 1) = ofTree T ⊗ counit(1) = ofTree T ⊗ 1.
    rw [show (Algebra.TensorProduct.map
              (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
              (counit (R := R)))
          (ofTree (Nonplanar.node a (Multiset.ofList (children.map Nonplanar.mk))) ⊗ₜ
            (1 : ConnesKreimer R (Nonplanar α))) =
        ofTree (Nonplanar.node a (Multiset.ofList (children.map Nonplanar.mk))) ⊗ₜ
          (1 : R) from by
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]]
    -- Second summand: (id ⊗ counit) ∘ (lTensor (bPlusLin a)) z is zero,
    -- because counit ∘ bPlusLin a = 0 (any tree from B+_a has counit 0).
    rw [show (Algebra.TensorProduct.map
              (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
              (counit (R := R)))
          ((LinearMap.lTensor _ (bPlusLin (R := R) a))
            (comulForestN (Multiset.ofList (children.map Nonplanar.mk)))) = 0 from by
      generalize comulForestN (R := R)
        (Multiset.ofList (children.map Nonplanar.mk)) = z
      induction z using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | tmul x y =>
        rw [LinearMap.lTensor_tmul, Algebra.TensorProduct.map_tmul,
            AlgHom.id_apply, counit_bPlusLin, TensorProduct.tmul_zero]
      | add z₁ z₂ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂, add_zero]]
    rw [add_zero]

/-! ### Counit laws (algebra-hom level)

Strategy: reduce to `of' F` via `AddMonoidAlgebra.algHom_ext`. For each `F`, expand
`comulAlgHomN (of' F) = comulForestN F` via `comulForestN_eq_sum`, then identify
the unique cut summand `(0, F) ∈ cutForestSummandsN F` (the "all empty cuts"
tuple). Other summands have `pf.1.card > 0`, so `counit (of' pf.1) = 0` and
`(counit ⊗ id)` kills them. The surviving `(0, F)` summand contributes
`1 ⊗ of' F = (lid).symm (of' F)`.

Helper lemmas needed (substantive):
* `mem_cutSummandsN_zero (T : Nonplanar α) : (0, T) ∈ cutSummandsN T` — the empty
  cut exists at every tree.
* `cutForestSummandsN_zero_mem (F : Forest (Nonplanar α)) : (0, F) ∈ cutForestSummandsN F`.
* `cutForestSummandsN_pos_pi : ∀ pf ∈ cutForestSummandsN F, pf ≠ (0, F) → pf.1.card > 0`. -/

theorem counit_rTensor_comulAlgHomN :
    (Algebra.TensorProduct.map (counit (R := R)) (AlgHom.id R _)).comp comulAlgHomN =
      (Algebra.TensorProduct.lid R (ConnesKreimer R (Nonplanar α))).symm.toAlgHom := by
  apply AddMonoidAlgebra.algHom_ext
  intro F
  show (Algebra.TensorProduct.map (counit (R := R))
          (AlgHom.id R (ConnesKreimer R (Nonplanar α)))) (comulAlgHomN (of' F)) =
       (Algebra.TensorProduct.lid R (ConnesKreimer R (Nonplanar α))).symm (of' F)
  rw [comulAlgHomN_apply_of', Algebra.TensorProduct.lid_symm_apply]
  exact comulForestN_counit_rTensor F (fun T _ => comulTreeN_counit_rTensor T)

theorem counit_lTensor_comulAlgHomN :
    (Algebra.TensorProduct.map (AlgHom.id R _) (counit (R := R))).comp comulAlgHomN =
      (Algebra.TensorProduct.rid R R (ConnesKreimer R (Nonplanar α))).symm.toAlgHom := by
  apply AddMonoidAlgebra.algHom_ext
  intro F
  show (Algebra.TensorProduct.map (AlgHom.id R (ConnesKreimer R (Nonplanar α)))
          (counit (R := R))) (comulAlgHomN (of' F)) =
       (Algebra.TensorProduct.rid R R (ConnesKreimer R (Nonplanar α))).symm (of' F)
  rw [comulAlgHomN_apply_of', Algebra.TensorProduct.rid_symm_apply]
  exact comulForestN_counit_lTensor F (fun T _ => comulTreeN_counit_lTensor T)
/-! ### Δ^ρ coassoc and Bialgebra instance: moved

The GL/CK duality theorem (`pairing_gl_eq_pairing_coproduct_Rho`), the
coassociativity of `comulAlgHomN`, and the `Bialgebra` instance live in
`Coproduct/PruningDuality.lean`, downstream of `BMinus.lean` (whose B⁻
calculus drives the duality proof). -/

end ConnesKreimer

end RootedTree
