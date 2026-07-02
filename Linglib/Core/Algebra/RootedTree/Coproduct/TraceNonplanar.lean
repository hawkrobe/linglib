/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.Coproduct.Trace
import Linglib.Core.Algebra.RootedTree.Coproduct.TraceCoassoc
import Linglib.Core.Algebra.RootedTree.GrossmanLarson
import Linglib.Core.Algebra.RootedTree.GrossmanLarsonMonoid
import Linglib.Core.Algebra.RootedTree.GrossmanLarsonPairing
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis

set_option autoImplicit false
-- The structure-wrapped `ConnesKreimer` needs one extra pending step when
-- synthesizing instances on nested tensor squares `CK ⊗ (CK ⊗ CK)` (the
-- def-synonym's fall-through to `AddMonoidAlgebra` instances is gone).
set_option maxSynthPendingDepth 2

/-!
# Δ^c on `ConnesKreimer R (Nonplanar (α ⊕ β))` via descent + duality
[marcolli-chomsky-berwick-2025]
[foissy-typed-decorated-rooted-trees-2018]

The decorated coproduct Δ^c (contraction-extraction with trace
placeholders) descended from the tree-level version `comulCAlgHomP` in
`Coproduct/Trace.lean` to `Nonplanar` trees. Coassociativity is
proved via Foissy 2018 §4.2 GL-CK duality: GL associativity (`product`
in `GrossmanLarson.lean`) ⇔ Δ^c coassociativity, transported through
the symmetry-weighted pairing in `GrossmanLarsonPairing.lean`.

## MCB target: Lemma 1.2.10

`comulCN_coassoc` + `Bialgebra` instance closes MCB Lemma 1.2.10 (the
graded bialgebra structure of `(V(F_{SO_0}), ⊔, Δ^c)`). The GL/duality
route is the **unification approach** that also enables Δ^d (Def 1.2.5,
via different extraction policy + projection) and Δ^ρ (Lemma 1.2.11,
currently parallel — to be unified at R.8). See
`memory/project_mcb_unification_rationale.md` for why this matters
architecturally (avoids ~thousands of LOC of duplication).

The descent layer mirrors `Coproduct/PruningNonplanar.lean`'s descent
of Δ^ρ. The duality-based coassoc proof is the *new* technique that
handles Δ^c — for which Foissy clean coassoc (used for Δ^ρ) does NOT
work (B+ is not a Hochschild 1-cocycle for Δ^c; see CHANGELOG entry
0.230.944 R.0 patch and `project_phase_e3_db_plan.md`).

## Construction

1. **Descent of `cutSummandsCP`** through `Nonplanar.mk`. Mirrors the
   `Pruning` descent but threads the trace-encoder `τ`.
2. **`comulCTreeN`, `comulCForestN`, `comulCAlgHomN`** — Nonplanar
   tree/forest-level Δ^c, packaged as algebra hom.
3. **Coassoc via duality** (Foissy 2018 §4.2): the duality theorem
   `pairing (gl x y) z = pairing x (Δ^c z) (after suitable
   ⊗-evaluation)` lets us transport `gl_assoc` (R.5.5) to Δ^c coassoc.
4. **Bialgebra instance**: counit + counit-multiplicativity from CK,
   coassoc from duality.

## Status

`[UPSTREAM]` candidate. Sorry-free. MCB Lemma 1.2.10 is fully proved: both
its grading content (`mcb_lemma_1_2_10`) and Δ^c coassociativity
(`comulCN_coassoc`), the latter under the `TraceCoherent` hypothesis. The
coassoc proof is the direct double-cut bijection `doubleCut_eq`, descended
from the tree-level `DoubleCut.coassT` (`Coproduct/TraceCoassoc.lean`) through
`Nonplanar.mk`. The earlier plan to derive it from a GL/Δ^c pairing duality
was abandoned: that duality is **false** (GL grafting never removes trace
markers, so no orientation of `⟨x ⋆ y, z⟩ = pairing₂ (… ) (Δ^c z)` can hold;
counterexamples in `scratch/validate_duality.lean` V4). The duality route
works for the deletion variant Δ^ρ — see `Coproduct/PruningDuality.lean`.
-/

namespace RootedTree

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α β : Type*}

/-! ## Descent of cut-summand enumeration

Mirrors `Coproduct/PruningNonplanar.lean`'s descent of `cutSummandsP`,
but for the generic `cutSummandsG` (which uses a `List`-shaped per-cut
remainder rather than `Option`). The descent applies whenever the
`extract` policy is invariant under `RoseTree.PermEquiv` modulo
`Nonplanar.mk`. For Δ^c (`extractC (τ ∘ Nonplanar.mk)`) this follows
from `value_permEquiv`. -/

namespace ConnesKreimer

/-! ### Pointwise projection for the G-form -/

/-- Project a tree-level cut summand to a nonplanar one. -/
private def projSummand : Forest (RoseTree α) × RoseTree α →
    Forest (Nonplanar α) × Nonplanar α :=
  fun p => (p.1.map Nonplanar.mk, Nonplanar.mk p.2)

/-- Project a `cutListSummandsG` summand to nonplanar level, discarding
    the list-order of the remainder by sending to `Multiset`. -/
private def projForestG : Forest (RoseTree α) × List (RoseTree α) →
    Forest (Nonplanar α) × Multiset (Nonplanar α) :=
  fun p => (p.1.map Nonplanar.mk, Multiset.ofList (p.2.map Nonplanar.mk))

/-! ### Bridge: `projSummand` factors through `projForestG` + `node` -/

/-- Applying the `cutSummandsG_node` wrapper `(p.1, .node a p.2)` then
    `projSummand` factors through `projForestG` followed by the
    `Nonplanar.node a` smart constructor. -/
private theorem projSummand_node_factors (a : α)
    (p : Forest (RoseTree α) × List (RoseTree α)) :
    projSummand (α := α) (p.1, .node a p.2) =
      ((projForestG p).1, Nonplanar.node a (projForestG p).2) := by
  show (p.1.map Nonplanar.mk, Nonplanar.mk (.node a p.2)) =
       (p.1.map Nonplanar.mk,
        Nonplanar.node a (Multiset.ofList (p.2.map Nonplanar.mk)))
  congr 1
  exact (Nonplanar.node_mk_tree_list a p.2).symm

/-! ### Combiner factoring

The cons case of `cutListSummandsG` adds the cut forest and concatenates
the remainder lists. At the Nonplanar level (via `projForestG`), the
remainder concatenation becomes multiset addition. -/

/-- The Nonplanar-level combiner: clean addition on both components. -/
private def combinerProjG :
    (Forest (Nonplanar α) × Multiset (Nonplanar α)) ×
    (Forest (Nonplanar α) × Multiset (Nonplanar α)) →
    Forest (Nonplanar α) × Multiset (Nonplanar α)
  | ((F1, m1), (F2, m2)) => (F1 + F2, m1 + m2)

/-- Pointwise: `projForestG` of an applied tree-level combiner equals
    `combinerProjG` applied to the projected pair-of-pairs. -/
private theorem projForestG_combine_apply
    (p : (Forest (RoseTree α) × List (RoseTree α)) ×
         (Forest (RoseTree α) × List (RoseTree α))) :
    projForestG (p.1.1 + p.2.1, p.1.2 ++ p.2.2) =
      combinerProjG (projForestG p.1, projForestG p.2) := by
  obtain ⟨⟨F1, l1⟩, ⟨F2, l2⟩⟩ := p
  show ((F1 + F2).map Nonplanar.mk,
        Multiset.ofList ((l1 ++ l2).map Nonplanar.mk)) =
       (F1.map Nonplanar.mk + F2.map Nonplanar.mk,
        Multiset.ofList (l1.map Nonplanar.mk) +
        Multiset.ofList (l2.map Nonplanar.mk))
  rw [Multiset.map_add]
  congr 1
  show Multiset.ofList ((l1 ++ l2).map Nonplanar.mk) = _
  rw [List.map_append]
  rfl

/-! ### Cartesian-product distributivity (G-form copy) -/

private theorem map_prodMap_product_G {α' β' γ δ : Type*}
    (f : α' → γ) (g : β' → δ)
    (s : Multiset α') (t : Multiset β') :
    (s ×ˢ t).map (Prod.map f g) = s.map f ×ˢ t.map g := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.cons_product, Multiset.map_add, Multiset.map_map,
               Multiset.map_cons, ih]
    rfl

/-! ### Headline factoring: cons case of projected `cutListSummandsG` -/

/-- The projected `cutListSummandsG` on a cons list factors as a clean
    cartesian product at the Nonplanar level via `combinerProjG`. -/
private theorem cutListSummandsG_cons_proj
    (extract : RoseTree α → Option (List (RoseTree α)))
    (t : RoseTree α) (ts : List (RoseTree α)) :
    (cutListSummandsG extract (t :: ts)).map projForestG =
      ((augActionG extract t).map projForestG ×ˢ
       (cutListSummandsG extract ts).map projForestG).map combinerProjG := by
  rw [cutListSummandsG_cons, Multiset.map_map, ← map_prodMap_product_G,
      Multiset.map_map]
  apply Multiset.map_congr rfl
  intro p _
  exact projForestG_combine_apply p

/-! ### Extract-policy invariance

The hypothesis on the `extract` policy: its return value, projected
component-wise through `Nonplanar.mk`, is the same on `PermEquiv`-equal
inputs. For Δ^c (`extractC (τ ∘ Nonplanar.mk)`) this holds because the
root label and the τ value are both `PermEquiv`-invariant. -/

/-- An extract policy is **`Nonplanar.mk`-invariant** if its return
    value, projected componentwise through `Nonplanar.mk`, depends on
    its input only through `Nonplanar.mk`. -/
def ExtractInvariant (extract : RoseTree α → Option (List (RoseTree α))) : Prop :=
  ∀ t s : RoseTree α, Nonplanar.mk t = Nonplanar.mk s →
    (extract t).map (List.map (Nonplanar.mk (α := α))) =
      (extract s).map (List.map (Nonplanar.mk (α := α)))

/-- `augActionG`-projection invariance under the descent hypothesis. -/
private theorem augActionG_proj_eq_of_step_data
    {extract : RoseTree α → Option (List (RoseTree α))}
    (hExt : ExtractInvariant extract)
    {old new : RoseTree α}
    (h_mk : Nonplanar.mk old = Nonplanar.mk new)
    (h_proj : (cutSummandsG extract old).map projSummand =
              (cutSummandsG extract new).map projSummand) :
    (augActionG extract old).map projForestG =
      (augActionG extract new).map projForestG := by
  rw [augActionG_eq, augActionG_eq, Multiset.map_add, Multiset.map_add]
  congr 1
  · -- Extract-whole sentinel branch: invariance from hExt + h_mk.
    have hExtEq := hExt old new h_mk
    -- Branch on extract old / extract new; rewrite into goal directly.
    rcases hOld : extract old with _ | rOld
    · -- extract old = none
      rw [hOld] at hExtEq
      simp only [Option.map_none] at hExtEq
      rcases hNew : extract new with _ | rNew
      · -- both none: both sentinel branches reduce to 0
        show Multiset.map projForestG
              (match (none : Option (List (RoseTree α))) with
               | none => 0
               | some r => {((({old} : Forest (RoseTree α))), r)}) =
             Multiset.map projForestG
              (match (none : Option (List (RoseTree α))) with
               | none => 0
               | some r => {((({new} : Forest (RoseTree α))), r)})
        simp
      · -- new is some, but old is none — contradiction with hExtEq.
        rw [hNew] at hExtEq
        simp at hExtEq
    · -- extract old = some rOld
      rw [hOld] at hExtEq
      simp only [Option.map_some] at hExtEq
      rcases hNew : extract new with _ | rNew
      · -- old is some, new is none — contradiction.
        rw [hNew] at hExtEq
        simp at hExtEq
      · -- both some: pure equality on the singleton sentinel.
        rw [hNew] at hExtEq
        simp only [Option.map_some, Option.some.injEq] at hExtEq
        -- hExtEq : rOld.map mk = rNew.map mk
        show Multiset.map projForestG
              (match (some rOld : Option (List (RoseTree α))) with
               | none => 0
               | some r => {((({old} : Forest (RoseTree α))), r)}) =
             Multiset.map projForestG
              (match (some rNew : Option (List (RoseTree α))) with
               | none => 0
               | some r => {((({new} : Forest (RoseTree α))), r)})
        show Multiset.map projForestG
                ({(({old} : Forest (RoseTree α)), rOld)} : Multiset _) =
             Multiset.map projForestG
                ({(({new} : Forest (RoseTree α)), rNew)} : Multiset _)
        rw [Multiset.map_singleton, Multiset.map_singleton]
        show ({(({old} : Forest (RoseTree α)).map Nonplanar.mk,
                Multiset.ofList (rOld.map Nonplanar.mk))} :
              Multiset (Forest (Nonplanar α) × Multiset (Nonplanar α))) =
             {(({new} : Forest (RoseTree α)).map Nonplanar.mk,
                Multiset.ofList (rNew.map Nonplanar.mk))}
        rw [Multiset.map_singleton, Multiset.map_singleton, h_mk, hExtEq]
  · -- Inherited branch: projForestG of (p.1, [p.2]) = ((projSummand p).1, ↑[(projSummand p).2])
    rw [Multiset.map_map, Multiset.map_map]
    have eq_fn :
        (projForestG (α := α)) ∘
          (fun (p : Forest (RoseTree α) × RoseTree α) => (p.1, [p.2])) =
        (fun (s : Forest (Nonplanar α) × Nonplanar α) =>
          (s.1, (Multiset.ofList [s.2] : Multiset (Nonplanar α)))) ∘
        (projSummand (α := α)) := by
      funext p
      rfl
    rw [eq_fn, ← Multiset.map_map, ← Multiset.map_map, h_proj]

/-! ### List-side projection invariants

Three theorems parallel to `cutListSummandsP_proj_at_via_augAction`,
`cutListSummandsP_proj_tail_lift`, and `cutListSummandsP_proj_perm`. -/

/-- Substituting `old` with `new` in `cutListSummandsG` is invariant
    under `projForestG` if the `augActionG`-projections agree. -/
private theorem cutListSummandsG_proj_at_via_augAction
    (extract : RoseTree α → Option (List (RoseTree α)))
    {pre post : List (RoseTree α)} {old new : RoseTree α}
    (h : (augActionG extract old).map projForestG =
         (augActionG extract new).map projForestG) :
    (cutListSummandsG extract (pre ++ old :: post)).map projForestG =
    (cutListSummandsG extract (pre ++ new :: post)).map projForestG := by
  induction pre with
  | nil =>
    show (cutListSummandsG extract (old :: post)).map projForestG =
         (cutListSummandsG extract (new :: post)).map projForestG
    rw [cutListSummandsG_cons_proj, cutListSummandsG_cons_proj, h]
  | cons p pre' ih =>
    show (cutListSummandsG extract (p :: (pre' ++ old :: post))).map projForestG =
         (cutListSummandsG extract (p :: (pre' ++ new :: post))).map projForestG
    rw [cutListSummandsG_cons_proj, cutListSummandsG_cons_proj, ih]

/-- Tail lift: `cutListSummandsG` is invariant under `projForestG`-equal
    tails when consed with a fixed head. -/
private theorem cutListSummandsG_proj_tail_lift
    (extract : RoseTree α → Option (List (RoseTree α)))
    (d : RoseTree α) {cs ds : List (RoseTree α)}
    (h : (cutListSummandsG extract cs).map projForestG =
         (cutListSummandsG extract ds).map projForestG) :
    (cutListSummandsG extract (d :: cs)).map projForestG =
      (cutListSummandsG extract (d :: ds)).map projForestG := by
  rw [cutListSummandsG_cons_proj, cutListSummandsG_cons_proj, h]

/-! ### Swap symmetry for `combinerProjG` -/

/-- Triple-combiner symmetry: combining three projected pieces at the
    Nonplanar level is symmetric in the first two factors. -/
private theorem combinerProjG_swap_args
    (a b : Forest (Nonplanar α) × Multiset (Nonplanar α))
    (c : Forest (Nonplanar α) × Multiset (Nonplanar α)) :
    combinerProjG (a, combinerProjG (b, c)) =
    combinerProjG (b, combinerProjG (a, c)) := by
  obtain ⟨Fa, ma⟩ := a
  obtain ⟨Fb, mb⟩ := b
  obtain ⟨Fc, mc⟩ := c
  show (Fa + (Fb + Fc), ma + (mb + mc)) = (Fb + (Fa + Fc), mb + (ma + mc))
  rw [← add_assoc, ← add_assoc, add_comm Fa Fb,
      ← add_assoc, ← add_assoc, add_comm ma mb]

/-- Doubly-applied `combinerProjG` over a triple cartesian product is
    symmetric in the first two factors. The substantive content of
    `cutListSummandsG_proj_perm`'s `swap` case. -/
private theorem swap_double_combinerProjG
    (A B : Multiset (Forest (Nonplanar α) × Multiset (Nonplanar α)))
    (C : Multiset (Forest (Nonplanar α) × Multiset (Nonplanar α))) :
    (A ×ˢ (B ×ˢ C).map combinerProjG).map combinerProjG =
    (B ×ˢ (A ×ˢ C).map combinerProjG).map combinerProjG := by
  have lhs :
      (A ×ˢ (B ×ˢ C).map combinerProjG).map combinerProjG =
        A.bind (fun a => B.bind (fun b => C.map (fun c =>
          combinerProjG (a, combinerProjG (b, c))))) := by
    show ((A.bind fun a => ((B ×ˢ C).map combinerProjG).map (Prod.mk a))
          ).map combinerProjG = _
    rw [Multiset.map_bind]
    apply Multiset.bind_congr; intro a _
    show ((((B.bind fun b => C.map (Prod.mk b)) : Multiset _).map combinerProjG).map
            (Prod.mk a)).map combinerProjG = _
    rw [Multiset.map_bind, Multiset.map_bind, Multiset.map_bind]
    apply Multiset.bind_congr; intro b _
    rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
    rfl
  have rhs :
      (B ×ˢ (A ×ˢ C).map combinerProjG).map combinerProjG =
        B.bind (fun b => A.bind (fun a => C.map (fun c =>
          combinerProjG (b, combinerProjG (a, c))))) := by
    show ((B.bind fun b => ((A ×ˢ C).map combinerProjG).map (Prod.mk b))
          ).map combinerProjG = _
    rw [Multiset.map_bind]
    apply Multiset.bind_congr; intro b _
    show ((((A.bind fun a => C.map (Prod.mk a)) : Multiset _).map combinerProjG).map
            (Prod.mk b)).map combinerProjG = _
    rw [Multiset.map_bind, Multiset.map_bind, Multiset.map_bind]
    apply Multiset.bind_congr; intro a _
    rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
    rfl
  rw [lhs, rhs, Multiset.bind_bind]
  apply Multiset.bind_congr; intro b _
  apply Multiset.bind_congr; intro a _
  apply Multiset.map_congr rfl; intro c _
  exact combinerProjG_swap_args a b c

/-- The projected `cutListSummandsG` is `List.Perm`-invariant. -/
private theorem cutListSummandsG_proj_perm
    (extract : RoseTree α → Option (List (RoseTree α)))
    {cs ds : List (RoseTree α)} (h : cs.Perm ds) :
    (cutListSummandsG extract cs).map projForestG =
      (cutListSummandsG extract ds).map projForestG := by
  induction h with
  | nil => rfl
  | cons c _ ih => exact cutListSummandsG_proj_tail_lift extract c ih
  | swap c d cs =>
    rw [cutListSummandsG_cons_proj, cutListSummandsG_cons_proj,
        cutListSummandsG_cons_proj, cutListSummandsG_cons_proj]
    exact (swap_double_combinerProjG _ _ _).symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ### Headline: PermStep + EqvGen lift

Structural induction on `PermStep`. The `swapAtRoot` case uses
`cutListSummandsG_proj_perm`; the `recurse` case uses the inductive
hypothesis combined with `cutListSummandsG_proj_at_via_augAction`. -/

/-- Projection invariance under a single `PermStep`. -/
theorem cutSummandsG_proj_permStep
    {extract : RoseTree α → Option (List (RoseTree α))}
    (hExt : ExtractInvariant extract)
    {t s : RoseTree α} (h : RoseTree.PermStep t s) :
    (cutSummandsG extract t).map projSummand =
      (cutSummandsG extract s).map projSummand := by
  induction h with
  | @swapAtRoot a l r pre post =>
    rw [cutSummandsG_node, cutSummandsG_node,
        Multiset.map_map, Multiset.map_map]
    have hperm : (pre ++ l :: r :: post).Perm (pre ++ r :: l :: post) :=
      List.Perm.append_left pre (List.Perm.swap r l post)
    have hL : (cutListSummandsG extract (pre ++ l :: r :: post)).map projForestG =
              (cutListSummandsG extract (pre ++ r :: l :: post)).map projForestG :=
      cutListSummandsG_proj_perm extract hperm
    have eq_fn :
        (projSummand (α := α)) ∘
          (fun (p : Forest (RoseTree α) × List (RoseTree α)) => (p.1, .node a p.2)) =
        (fun (pf : Forest (Nonplanar α) × Multiset (Nonplanar α)) =>
          (pf.1, Nonplanar.node a pf.2)) ∘ (projForestG (α := α)) := by
      funext p
      exact projSummand_node_factors a p
    rw [eq_fn, ← Multiset.map_map, ← Multiset.map_map, hL]
  | @recurse a pre old new post hsub ih =>
    rw [cutSummandsG_node, cutSummandsG_node,
        Multiset.map_map, Multiset.map_map]
    have h_mk : Nonplanar.mk old = Nonplanar.mk new :=
      Nonplanar.mk_eq_mk_iff.mpr (RoseTree.PermEquiv.of_step hsub)
    have h_aug : (augActionG extract old).map projForestG =
                 (augActionG extract new).map projForestG :=
      augActionG_proj_eq_of_step_data hExt h_mk ih
    have hL : (cutListSummandsG extract (pre ++ old :: post)).map projForestG =
              (cutListSummandsG extract (pre ++ new :: post)).map projForestG :=
      cutListSummandsG_proj_at_via_augAction extract h_aug
    have eq_fn :
        (projSummand (α := α)) ∘
          (fun (p : Forest (RoseTree α) × List (RoseTree α)) => (p.1, .node a p.2)) =
        (fun (pf : Forest (Nonplanar α) × Multiset (Nonplanar α)) =>
          (pf.1, Nonplanar.node a pf.2)) ∘ (projForestG (α := α)) := by
      funext p
      exact projSummand_node_factors a p
    rw [eq_fn, ← Multiset.map_map, ← Multiset.map_map, hL]

/-- Projection invariance under `PermEquiv`. Pure `EqvGen` lift. -/
theorem cutSummandsG_proj_permEquiv
    {extract : RoseTree α → Option (List (RoseTree α))}
    (hExt : ExtractInvariant extract)
    {t s : RoseTree α} (h : RoseTree.PermEquiv t s) :
    (cutSummandsG extract t).map projSummand =
      (cutSummandsG extract s).map projSummand := by
  induction h with
  | rel _ _ hstep => exact cutSummandsG_proj_permStep hExt hstep
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-! ### Trace specialization

The Δ^c policy `extractC (τ ∘ Nonplanar.mk)` is `ExtractInvariant`:
- For `Sum.inl _`-rooted inputs, `extractC` returns `some [traceLeaf (τ (mk t))]`.
- For `Sum.inr _`-rooted inputs, `extractC` returns `none`.

Both cases are determined by the root label and the τ value, both of
which are `PermEquiv`-invariant. -/

/-- The Δ^c extract policy is `ExtractInvariant`. -/
theorem extractC_mkComp_invariant (τ : Nonplanar (α ⊕ β) → β) :
    ExtractInvariant (extractC (τ ∘ Nonplanar.mk)) := by
  intro t s hmk
  -- Root labels match (permEquiv-invariant), so the extractC branches match.
  have hlabel : t.value = s.value := by
    have heq : RoseTree.PermEquiv t s := Nonplanar.mk_eq_mk_iff.mp hmk
    exact RoseTree.value_permEquiv heq
  -- Destructure both trees as nodes; rewrite root labels via hlabel.
  obtain ⟨at_, cs_t⟩ := t
  obtain ⟨as, cs_s⟩ := s
  simp only [RoseTree.value] at hlabel
  subst hlabel
  -- Now both have root label at_. Case-split on at_.
  cases at_ with
  | inl a =>
    show (extractC (τ ∘ Nonplanar.mk) (RoseTree.node (Sum.inl a) cs_t)).map _ =
         (extractC (τ ∘ Nonplanar.mk) (RoseTree.node (Sum.inl a) cs_s)).map _
    simp only [extractC_inl, Option.map_some]
    -- Goal: some [mk (traceLeaf (τ (mk t)))] = some [mk (traceLeaf (τ (mk s)))]
    -- Reduces to: τ (mk t) = τ (mk s), which is congrArg τ hmk.
    have : (τ ∘ Nonplanar.mk) (RoseTree.node (Sum.inl a) cs_t) =
           (τ ∘ Nonplanar.mk) (RoseTree.node (Sum.inl a) cs_s) := by
      show τ (Nonplanar.mk _) = τ (Nonplanar.mk _)
      exact congrArg τ hmk
    rw [this]
  | inr b =>
    show (extractC (τ ∘ Nonplanar.mk) (RoseTree.node (Sum.inr b) cs_t)).map _ =
         (extractC (τ ∘ Nonplanar.mk) (RoseTree.node (Sum.inr b) cs_s)).map _
    simp only [extractC_inr, Option.map_none]

/-- Δ^c cut-summand-projection invariance under `PermEquiv`. -/
theorem cutSummandsCP_proj_permEquiv (τ : Nonplanar (α ⊕ β) → β)
    {t s : RoseTree (α ⊕ β)} (h : RoseTree.PermEquiv t s) :
    (cutSummandsCP (τ ∘ Nonplanar.mk) t).map projSummand =
      (cutSummandsCP (τ ∘ Nonplanar.mk) s).map projSummand :=
  cutSummandsG_proj_permEquiv (extractC_mkComp_invariant τ) h

end ConnesKreimer

/-! ### Descent of `cutSummandsCP` through `Nonplanar.mk` -/

/-- The Nonplanar Δ^c cut summands, descended from `cutSummandsCP` via
    `Nonplanar.lift` using the descent invariance
    `cutSummandsCP_proj_permEquiv`. -/
noncomputable def cutSummandsCN (τ : Nonplanar (α ⊕ β) → β) :
    Nonplanar (α ⊕ β) → Multiset (Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) :=
  Nonplanar.lift
    (fun T => (ConnesKreimer.cutSummandsCP (τ ∘ Nonplanar.mk) T).map
      ConnesKreimer.projSummand)
    (fun _ _ h => ConnesKreimer.cutSummandsCP_proj_permEquiv τ h)

@[simp] theorem cutSummandsCN_mk (τ : Nonplanar (α ⊕ β) → β) (T : RoseTree (α ⊕ β)) :
    cutSummandsCN τ (Nonplanar.mk T) =
      (ConnesKreimer.cutSummandsCP (τ ∘ Nonplanar.mk) T).map
        ConnesKreimer.projSummand := rfl

/-! ### Nonplanar tree- and forest-level Δ^c -/

/-- The Nonplanar tree-level Δ^c coproduct. -/
noncomputable def comulCTreeN (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) :
    ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R] ConnesKreimer R (Nonplanar (α ⊕ β)) :=
  ConnesKreimer.ofTree T ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar (α ⊕ β)))
  + ((cutSummandsCN τ T).map
      (fun p => ConnesKreimer.of' (R := R) p.1 ⊗ₜ[R] ConnesKreimer.ofTree p.2)).sum

/-- The Nonplanar forest-level Δ^c (multiplicative extension). -/
noncomputable def comulCForestN (τ : Nonplanar (α ⊕ β) → β)
    (F : Forest (Nonplanar (α ⊕ β))) :
    ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R] ConnesKreimer R (Nonplanar (α ⊕ β)) :=
  (F.map (comulCTreeN (R := R) τ)).prod

@[simp] theorem comulCForestN_zero (τ : Nonplanar (α ⊕ β) → β) :
    comulCForestN (R := R) τ (0 : Forest (Nonplanar (α ⊕ β))) = 1 := by
  simp only [comulCForestN, Multiset.map_zero, Multiset.prod_zero]

@[simp] theorem comulCForestN_add (τ : Nonplanar (α ⊕ β) → β)
    (F G : Forest (Nonplanar (α ⊕ β))) :
    comulCForestN (R := R) τ (F + G) =
      comulCForestN (R := R) τ F * comulCForestN (R := R) τ G := by
  unfold comulCForestN
  rw [Multiset.map_add, Multiset.prod_add]

/-- Forest-level Δ^c as a `MonoidHom` from `Multiplicative (Forest ...)`. -/
noncomputable def comulCMonoidHomN (τ : Nonplanar (α ⊕ β) → β) :
    Multiplicative (Forest (Nonplanar (α ⊕ β))) →*
      (ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R]
        ConnesKreimer R (Nonplanar (α ⊕ β))) where
  toFun F := comulCForestN (R := R) τ F.toAdd
  map_one' := comulCForestN_zero τ
  map_mul' F G := comulCForestN_add τ F.toAdd G.toAdd

/-- The **Δ^c coproduct on `ConnesKreimer R (Nonplanar (α ⊕ β))`** as
    an algebra hom, parameterized by the trace encoder `τ`. -/
noncomputable def comulCAlgHomN (τ : Nonplanar (α ⊕ β) → β) :
    ConnesKreimer R (Nonplanar (α ⊕ β)) →ₐ[R]
      ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R]
        ConnesKreimer R (Nonplanar (α ⊕ β)) :=
  ConnesKreimer.lift (comulCMonoidHomN τ)

@[simp] theorem comulCAlgHomN_apply_of' (τ : Nonplanar (α ⊕ β) → β)
    (F : Forest (Nonplanar (α ⊕ β))) :
    comulCAlgHomN (R := R) τ (ConnesKreimer.of' F) = comulCForestN τ F := by
  rw [comulCAlgHomN, ConnesKreimer.lift_of']
  rfl

@[simp] theorem comulCAlgHomN_apply_ofTree (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) :
    comulCAlgHomN (R := R) τ (ConnesKreimer.ofTree T) = comulCTreeN τ T := by
  rw [show (ConnesKreimer.ofTree T : ConnesKreimer R (Nonplanar (α ⊕ β)))
        = ConnesKreimer.of' {T} from rfl, comulCAlgHomN_apply_of']
  show comulCForestN τ {T} = _
  unfold comulCForestN
  rw [Multiset.map_singleton, Multiset.prod_singleton]

/-! ### Tensor-extended pairings

The pairing `⟨·, ·⟩` from `GrossmanLarsonPairing.lean` extends to the
tensor square (`pairing₂`) and cube (`pairing₃`). These power the GL/CK
duality for the deletion coproduct Δ^ρ (`Coproduct/PruningDuality.lean`:
`⟨x ⋆ y, z⟩ = pairing₂ (y ⊗ x) (Δ^ρ z)`). For the trace variant Δ^c no
such duality holds — the trunk of a proper cut contains trace-marker
leaves that GL grafting can never produce — so Δ^c coassociativity
(`comulCN_coassoc` below) is a separate combinatorial statement. -/

/-- The **tensor-extended pairing** `H ⊗ H →ₗ H ⊗ H →ₗ R`, defined by
    `pairing₂ (x ⊗ y) (w ⊗ z) = pairing x w * pairing y z` and extended
    bilinearly.

    Implementation: reshuffle `(x⊗y)⊗(w⊗z)` to `(x⊗w)⊗(y⊗z)` via
    `tensorTensorTensorComm`; apply `TP.map pair pair` where
    `pair = TP.lift pairing : H ⊗ H →ₗ R`; contract via `mul' R R`;
    curry the result.

    Decoration-free: works on `ConnesKreimer R (Nonplanar α)` for any
    `α`. Consumed by the Δ^ρ duality (`Coproduct/PruningDuality.lean`). -/
noncomputable def pairing₂ :
    (ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) →ₗ[R]
    (ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) →ₗ[R] R :=
  let pair : ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)
                →ₗ[R] R :=
    TensorProduct.lift GrossmanLarson.pairing
  TensorProduct.curry <|
    LinearMap.mul' R R ∘ₗ
      TensorProduct.map pair pair ∘ₗ
      (TensorProduct.tensorTensorTensorComm R
        (ConnesKreimer R (Nonplanar α))
        (ConnesKreimer R (Nonplanar α))
        (ConnesKreimer R (Nonplanar α))
        (ConnesKreimer R (Nonplanar α))).toLinearMap

/-- Evaluation of `pairing₂` on pure tensors: `pairing₂ (x ⊗ y) (w ⊗ z) =
    pairing x w * pairing y z`. -/
@[simp] theorem pairing₂_tmul_tmul
    (x y w z : ConnesKreimer R (Nonplanar α)) :
    pairing₂ (R := R) (x ⊗ₜ y) (w ⊗ₜ z) =
      GrossmanLarson.pairing x w * GrossmanLarson.pairing y z := by
  rfl

/-- The **triple-tensor pairing** `H ⊗ (H ⊗ H) →ₗ H ⊗ (H ⊗ H) →ₗ R`,
    defined on pure tensors by
    `pairing₃ (a ⊗ (b ⊗ c)) (x ⊗ (y ⊗ z)) = pairing a x · pairing b y · pairing c z`.

    Used in the duality-based proof of `comulCN_coassoc`: equating
    LHS and RHS coassoc expressions via pairing against arbitrary
    `x ⊗ (y ⊗ z)` triple tensors.

    Implementation: pairing on the first factor times `pairing₂` on the
    second factor; both extended bilinearly. -/
noncomputable def pairing₃ :
    (ConnesKreimer R (Nonplanar α) ⊗[R]
      (ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α))) →ₗ[R]
    (ConnesKreimer R (Nonplanar α) ⊗[R]
      (ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α))) →ₗ[R] R :=
  let pair1 : ConnesKreimer R (Nonplanar α) ⊗[R]
                ConnesKreimer R (Nonplanar α) →ₗ[R] R :=
    TensorProduct.lift GrossmanLarson.pairing
  let pair2 : (ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α))
                ⊗[R] (ConnesKreimer R (Nonplanar α) ⊗[R]
                      ConnesKreimer R (Nonplanar α)) →ₗ[R] R :=
    TensorProduct.lift pairing₂
  TensorProduct.curry <|
    LinearMap.mul' R R ∘ₗ
      TensorProduct.map pair1 pair2 ∘ₗ
      (TensorProduct.tensorTensorTensorComm R
        (ConnesKreimer R (Nonplanar α))
        (ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α))
        (ConnesKreimer R (Nonplanar α))
        (ConnesKreimer R (Nonplanar α) ⊗[R]
          ConnesKreimer R (Nonplanar α))).toLinearMap

/-- Evaluation of `pairing₃` on pure tensors. -/
@[simp] theorem pairing₃_tmul_tmul_tmul
    (a b c x y z : ConnesKreimer R (Nonplanar α)) :
    pairing₃ (R := R) (a ⊗ₜ (b ⊗ₜ c)) (x ⊗ₜ (y ⊗ₜ z)) =
      GrossmanLarson.pairing a x *
        (GrossmanLarson.pairing b y * GrossmanLarson.pairing c z) := by
  rfl

/-! ### Trace coherence

There is **no** GL/Δ^c pairing duality: for any marker-free `z` with a
proper admissible cut, the trunk side of `Δ^c z` carries trace-marker
leaves, while every forest in the support of a GL product `x ⋆ y` has at
least as many markers as `x` and `y` combined (grafting never removes
vertices) — so `⟨x ⋆ y, z⟩ = 0` against any cut summand that would make
the right side nonzero, in either slot orientation. Checked
computationally in `scratch/validate_duality.lean` (V4). An earlier
sorry-fenced duality statement here was false and has been removed; the
duality (with crossed slots) is true for the deletion variant Δ^ρ and is
proved in `Coproduct/PruningDuality.lean`.

Δ^c coassociativity itself is **not τ-generic** either: iterating Δ^c
re-encodes already-cut subtrees, so the marker written by a second-stage
cut is `τ` of a tree *containing markers*, while the opposite cut order
writes `τ` of the original subtree. For `τ` sensitive to that difference
coassociativity fails (counterexample: `τ` = count of `Sum.inl`
vertices, `z` an inl-labeled 3-chain; `scratch/validate_duality.lean`
V5). [marcolli-chomsky-berwick-2025]'s proof of Lemma 1.2.10 (book
p. 37–38) silently uses that their trace labels compose under
contraction ("the accessible terms of accessible terms … are themselves
accessible terms"); `TraceCoherent` is that hypothesis made explicit. -/

/-- **Trace coherence**: `τ` does not distinguish a cut trunk (with its
    trace markers) from the tree it was cut from. This is the condition
    under which iterated Δ^c cuts commute (coassociativity): second-stage
    markers computed on marked trunks agree with markers computed on the
    original tree. Constant encoders satisfy it (`traceCoherent_const`);
    [marcolli-chomsky-berwick-2025]'s identity trace satisfies it in
    spirit via label expansion (their marker labels denote subtrees of
    the *original* tree). -/
def TraceCoherent (τ : Nonplanar (α ⊕ β) → β) : Prop :=
  ∀ T : Nonplanar (α ⊕ β), ∀ p ∈ cutSummandsCN τ T, τ p.2 = τ T

/-- Constant trace encoders are coherent. -/
theorem traceCoherent_const (b : β) :
    TraceCoherent (fun _ : Nonplanar (α ⊕ β) => b) :=
  fun _ _ _ => rfl

/-! ### Auxiliary: `pairing₃` reduction helpers

Generic reduction lemmas for `pairing₃` on shifted tensor shapes,
consumed by the Δ^ρ duality chain in `Coproduct/PruningDuality.lean`. -/

section CoassocChain
variable (τ : Nonplanar (α ⊕ β) → β)

/-! ### Helpers: `pairing₃` on shifted-tensor forms

Two reduction lemmas that express `pairing₃ (x ⊗ (y ⊗ z'))` evaluated on
shifted tensor forms in terms of `pairing₂` and binary `pairing`. Both
are proved by `TensorProduct.induction_on`, reducing to the pure-tensor
case where `pairing₃_tmul_tmul_tmul` and `pairing₂_tmul_tmul` agree. -/

/-- `pairing₃ (x ⊗ (y ⊗ z')) ∘ assoc` on a `(U ⊗ c)`-shape tensor:
    factors as `pairing₂ (x ⊗ y) U * pairing z' c`. Generic in `α`
    (the trace decoration is irrelevant). -/
lemma pairing₃_assoc_tmul
    (x y z' : ConnesKreimer R (Nonplanar α))
    (U : ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α))
    (c : ConnesKreimer R (Nonplanar α)) :
    pairing₃ (R := R) (x ⊗ₜ[R] (y ⊗ₜ[R] z'))
        ((TensorProduct.assoc R _ _ _) (U ⊗ₜ[R] c)) =
      pairing₂ (R := R) (x ⊗ₜ[R] y) U * GrossmanLarson.pairing z' c := by
  induction U using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [TensorProduct.assoc_tmul, pairing₃_tmul_tmul_tmul,
               pairing₂_tmul_tmul, mul_assoc]
  | add U₁ U₂ ih₁ ih₂ =>
    rw [TensorProduct.add_tmul, map_add, map_add, ih₁, ih₂, map_add, add_mul]

/-- `pairing₃ (x ⊗ (y ⊗ z'))` on a `(a ⊗ S)`-shape tensor: factors as
    `pairing x a * pairing₂ (y ⊗ z') S`. Generic in `α`. -/
lemma pairing₃_tmul_apply
    (x y z' a : ConnesKreimer R (Nonplanar α))
    (S : ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) :
    pairing₃ (R := R) (x ⊗ₜ[R] (y ⊗ₜ[R] z')) (a ⊗ₜ[R] S) =
      GrossmanLarson.pairing x a * pairing₂ (R := R) (y ⊗ₜ[R] z') S := by
  induction S using TensorProduct.induction_on with
  | zero => simp
  | tmul b c =>
    simp only [pairing₃_tmul_tmul_tmul, pairing₂_tmul_tmul]
  | add S₁ S₂ ih₁ ih₂ =>
    rw [TensorProduct.tmul_add, map_add, ih₁, ih₂, map_add, mul_add]

/-! ### Chain lemmas: pairing₃ against `coassocLHSLin/RHSLin`

These compose two applications of `pairing_gl_eq_pairing_coproduct_C`
(Foissy 2018 §4.2) through the helper lemmas above. The intermediate
`pairing₃_assoc_rTensor_comul` / `pairing₃_lTensor_comul` lemmas
generalize over the inner Δ^c-image, enabling a clean specialization
to `V = Δ^c z`. -/

end CoassocChain

/-! ### Nondegeneracy of `pairing₂` and `pairing₃` (lifted from binary)

`pairing₂` and `pairing₃` are nondegenerate over `[CharZero R]
[NoZeroDivisors R]`, lifted from binary `pairing_nondegenerate` via the
natural basis of `CK = (Forest T) →₀ R`. -/

/-- Bilinear extension: `pairing₃ (of' F ⊗ s) (of' G ⊗ t) = pairing (of' F)
    (of' G) * pairing₂ s t` for arbitrary `s, t ∈ CK ⊗ CK`. Proven via
    `TensorProduct.induction_on` on `s` and `t`, reducing to the pure-tensor
    case where `pairing₃_tmul_tmul_tmul` and `pairing₂_tmul_tmul` agree. -/
private theorem pairing₃_of'_tmul_of'_tmul (F G : Forest (Nonplanar α))
    (s t : ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) :
    pairing₃ (R := R)
        (ConnesKreimer.of' F ⊗ₜ[R] s)
        (ConnesKreimer.of' G ⊗ₜ[R] t) =
      GrossmanLarson.pairing (ConnesKreimer.of' (R := R) F)
                              (ConnesKreimer.of' G) *
        pairing₂ (R := R) s t := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul b c =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul y z =>
      simp only [pairing₃_tmul_tmul_tmul, pairing₂_tmul_tmul]
    | add t₁ t₂ ih₁ ih₂ =>
      -- pairing₃ is linear in 2nd arg (map_add); also `of' G ⊗ ·` distributes.
      rw [TensorProduct.tmul_add, map_add, ih₁, ih₂, map_add, mul_add]
  | add s₁ s₂ ih₁ ih₂ =>
    -- pairing₃ is linear in 1st arg, via map_add at the outer; same for pairing₂.
    rw [TensorProduct.tmul_add, map_add, LinearMap.add_apply, ih₁, ih₂,
        map_add, LinearMap.add_apply, mul_add]

/-- **Nondegeneracy of `pairing₂`** (lifted from binary): if
    `U ∈ CK ⊗ CK` pairs to zero against every pure tensor `x ⊗ y`,
    then `U = 0`.

    Proof: decompose `U` via the natural basis of `CK = (Forest T) →₀ R`
    as `U = c.sum (fun F U_F => of' F ⊗ U_F)`. Pairing against
    `of' F ⊗ y` extracts `autF · pairing y (c F)`. Over `CharZero`
    (so `autF ≠ 0`), each `c F = 0` by `pairing_nondegenerate` +
    `pairing_symm`, hence `c = 0` and `U = 0`. -/
private theorem pairing₂_nondegenerate
    [CharZero R] [NoZeroDivisors R]
    (U : ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α))
    (h : ∀ x y : ConnesKreimer R (Nonplanar α),
      pairing₂ (R := R) (x ⊗ₜ[R] y) U = 0) : U = 0 := by
  classical
  let ℬ : Module.Basis (Forest (Nonplanar α)) R (ConnesKreimer R (Nonplanar α)) :=
    ConnesKreimer.basisSingleOne
  obtain ⟨c, hc⟩ : ∃ c : Forest (Nonplanar α) →₀ ConnesKreimer R (Nonplanar α),
      c.sum (fun F U_F => ℬ F ⊗ₜ[R] U_F) = U :=
    TensorProduct.eq_repr_basis_left ℬ U
  have hℬ : ∀ G : Forest (Nonplanar α),
      (ℬ G : ConnesKreimer R (Nonplanar α)) = ConnesKreimer.of' G := fun _ =>
    ConnesKreimer.basisSingleOne_apply _
  have hc_zero : ∀ F, c F = 0 := by
    intro F
    apply GrossmanLarson.pairing_nondegenerate (c F)
    intro y
    rw [GrossmanLarson.pairing_symm]
    have h_aut_ne : (Nonplanar.forestAutCard F : R) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nonplanar.forestAutCard_pos F).ne'
    have h_eval := h (ConnesKreimer.of' F) y
    rw [← hc] at h_eval
    rw [map_finsuppSum (pairing₂ (R := R) (ConnesKreimer.of' F ⊗ₜ[R] y))] at h_eval
    simp only [hℬ, pairing₂_tmul_tmul, GrossmanLarson.pairing_of'_of'] at h_eval
    rw [Finsupp.sum_eq_single F
          (fun G _ hGF => by rw [if_neg (fun heq => hGF heq.symm), zero_mul])
          (fun _ => by rw [LinearMap.map_zero, mul_zero])] at h_eval
    rw [if_pos rfl] at h_eval
    rcases mul_eq_zero.mp h_eval with h' | h'
    · exact absurd h' h_aut_ne
    · exact h'
  have hc_zero' : c = 0 := Finsupp.ext hc_zero
  rw [← hc, hc_zero', Finsupp.sum_zero_index]

/-- **Nondegeneracy of `pairing₃`**: if `U ∈ CK ⊗ (CK ⊗ CK)` pairs to
    zero against every test triple tensor, then `U = 0`.

    Proof: decompose `U` via the basis on the outer factor as
    `U = c.sum (fun F U_F => of' F ⊗ U_F)` where `U_F ∈ CK ⊗ CK`.
    Pairing against `of' F ⊗ (x ⊗ y)` extracts `autF · pairing₂ (x ⊗ y)
    (c F)` via `pairing₃_of'_tmul_of'_tmul`. Over `CharZero` (so
    `autF ≠ 0`), each `pairing₂ (x ⊗ y) (c F) = 0` for all `x, y`; by
    `pairing₂_nondegenerate`, `c F = 0`. Hence `c = 0` and `U = 0`. -/
theorem pairing₃_nondegenerate
    [CharZero R] [NoZeroDivisors R]
    (U : ConnesKreimer R (Nonplanar α) ⊗[R]
          (ConnesKreimer R (Nonplanar α) ⊗[R]
            ConnesKreimer R (Nonplanar α)))
    (h : ∀ t, pairing₃ (R := R) t U = 0) : U = 0 := by
  classical
  let ℬ : Module.Basis (Forest (Nonplanar α)) R
        (ConnesKreimer R (Nonplanar α)) :=
    ConnesKreimer.basisSingleOne
  obtain ⟨c, hc⟩ : ∃ c : Forest (Nonplanar α) →₀
        (ConnesKreimer R (Nonplanar α) ⊗[R]
          ConnesKreimer R (Nonplanar α)),
      c.sum (fun F U_F => ℬ F ⊗ₜ[R] U_F) = U :=
    TensorProduct.eq_repr_basis_left ℬ U
  have hℬ : ∀ G : Forest (Nonplanar α),
      (ℬ G : ConnesKreimer R (Nonplanar α)) = ConnesKreimer.of' G :=
    fun _ => ConnesKreimer.basisSingleOne_apply _
  have hc_zero : ∀ F, c F = 0 := by
    intro F
    apply pairing₂_nondegenerate (c F)
    intro x y
    have h_aut_ne : (Nonplanar.forestAutCard F : R) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nonplanar.forestAutCard_pos F).ne'
    have h_eval := h (ConnesKreimer.of' F ⊗ₜ[R] (x ⊗ₜ[R] y))
    rw [← hc] at h_eval
    rw [map_finsuppSum
          (pairing₃ (R := R) (ConnesKreimer.of' F ⊗ₜ[R] (x ⊗ₜ[R] y)))] at h_eval
    simp only [hℬ, pairing₃_of'_tmul_of'_tmul, GrossmanLarson.pairing_of'_of'] at h_eval
    rw [Finsupp.sum_eq_single F
          (fun G _ hGF => by rw [if_neg (fun heq => hGF heq.symm), zero_mul])
          (fun _ => by rw [LinearMap.map_zero, mul_zero])] at h_eval
    rw [if_pos rfl] at h_eval
    rcases mul_eq_zero.mp h_eval with h' | h'
    · exact absurd h' h_aut_ne
    · exact h'
  have hc_zero' : c = 0 := Finsupp.ext hc_zero
  rw [← hc, hc_zero', Finsupp.sum_zero_index]

/-! ### Equality form of nondegeneracy

`pairing₃_unique`: two tensors that pair the same against every test
vector are equal. Follows from `pairing₃_nondegenerate` via
`U = V ↔ U - V = 0`, requiring `AddCommGroup` on the triple tensor.

**Single ring hypothesis**: this theorem lives in its own section with
`[CommRing R₁]` only (NOT [CommSemiring R] from the file's top section +
[CommRing R] added on top — those create two CommSemiring R instances
that don't unify). The `AddCommGroup` on the wrapper comes from the
global `ConnesKreimer.instCommRing`. -/

section PairingUnique
variable {R₁ : Type*} [CommRing R₁] {α₁ : Type*}

theorem pairing₃_unique [CharZero R₁] [NoZeroDivisors R₁]
    (U V : ConnesKreimer R₁ (Nonplanar α₁) ⊗[R₁]
          (ConnesKreimer R₁ (Nonplanar α₁) ⊗[R₁]
            ConnesKreimer R₁ (Nonplanar α₁)))
    (h : ∀ t, pairing₃ (R := R₁) t U = pairing₃ (R := R₁) t V) : U = V := by
  rw [← sub_eq_zero]
  apply pairing₃_nondegenerate
  intro t
  rw [map_sub, h t, sub_self]

end PairingUnique

/-! ### Double-cut enumeration — substrate for the direct coassoc proof

The combinatorial core of Δ^c coassociativity (`comulCN_coassoc_tree`),
following the [marcolli-chomsky-berwick-2025] Lemma 1.2.10 argument
("the accessible terms of accessible terms … are themselves accessible
terms"). Both `(Δ^c ⊗ id) ∘ Δ^c` and `(id ⊗ Δ^c) ∘ Δ^c` enumerate
ordered pairs of nested admissible cuts of a tree; the two enumerations
biject under `TraceCoherent`.

The plan (validated computationally, `scratch/validate_duality.lean` V7):
1. `comulCTreeN`/`comulCForestN` as multiset sums over cut enumerators
   `treeCutsN`/`forestCutsN` (this section).
2. Each composite expands to a sum over a double-cut enumerator
   `dcLHS`/`dcRHS` (`lhsExpand`/`rhsExpand`).
3. `dcLHS = dcRHS` as Nonplanar multisets under coherence
   (`doubleCut_eq`, the bijection). -/

section DoubleCut
variable {R : Type*} [CommSemiring R] {α β : Type*}

/-- Tensor-product factor of a (crown, trunk) cut pair. -/
private noncomputable def cutTensor
    (p : Forest (Nonplanar (α ⊕ β)) × Forest (Nonplanar (α ⊕ β))) :
    ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R] ConnesKreimer R (Nonplanar (α ⊕ β)) :=
  ConnesKreimer.of' (R := R) p.1 ⊗ₜ[R] ConnesKreimer.of' p.2

/-- Triple-tensor factor for the coassoc target `CK ⊗ (CK ⊗ CK)`. -/
private noncomputable def tripleTensor
    (q : Forest (Nonplanar (α ⊕ β)) × Forest (Nonplanar (α ⊕ β)) ×
         Forest (Nonplanar (α ⊕ β))) :
    ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R]
      (ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R] ConnesKreimer R (Nonplanar (α ⊕ β))) :=
  ConnesKreimer.of' (R := R) q.1 ⊗ₜ[R]
    (ConnesKreimer.of' q.2.1 ⊗ₜ[R] ConnesKreimer.of' q.2.2)

/-- Product of two multiset-sums equals the sum over their cartesian
    product. The combinatorial backbone of `comulCForestN_eq_sum`. -/
private theorem sum_product_map_mul {A B M : Type*} [NonUnitalNonAssocSemiring M]
    (s : Multiset A) (t : Multiset B) (f : A → M) (g : B → M) :
    ((s ×ˢ t).map (fun p => f p.1 * g p.2)).sum =
      (s.map f).sum * (t.map g).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.cons_product, Multiset.map_add, Multiset.sum_add, ih,
        Multiset.map_cons, Multiset.sum_cons, add_mul]
    congr 1
    rw [Multiset.map_map,
        show (fun p => f p.1 * g p.2) ∘ (Prod.mk a) = (fun b => f a * g b) from rfl,
        ← Multiset.sum_map_mul_left]

/-- Convolution-of-cuts is left-commutative (it is the symmetric
    `combinerProjG` of the descent layer); needed for `Multiset.foldr`. -/
instance instLeftCommConvCut : LeftCommutative
    (fun (s acc : Multiset (Forest (Nonplanar (α ⊕ β)) × Forest (Nonplanar (α ⊕ β)))) =>
      (s ×ˢ acc).map ConnesKreimer.combinerProjG) :=
  ⟨fun a b c => ConnesKreimer.swap_double_combinerProjG a b c⟩

/-- All cut summands of a tree as (crown forest, trunk forest) pairs:
    full cut `({T}, ∅)`, plus `cutSummandsCN` (which already includes the
    empty cut `(∅, {T})` and all proper cuts, each with a single-tree
    trunk). -/
private noncomputable def treeCutsN (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) :
    Multiset (Forest (Nonplanar (α ⊕ β)) × Forest (Nonplanar (α ⊕ β))) :=
  ({T}, 0) ::ₘ (cutSummandsCN τ T).map (fun p => (p.1, {p.2}))

/-- `comulCTreeN` as a single multiset sum over `treeCutsN`. -/
private theorem comulCTreeN_eq_sum (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) :
    comulCTreeN (R := R) τ T = ((treeCutsN τ T).map (cutTensor (R := R))).sum := by
  unfold comulCTreeN treeCutsN
  rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_map]
  congr 1

/-- Forest-level cut enumeration via convolution over the component trees. -/
private noncomputable def forestCutsN (τ : Nonplanar (α ⊕ β) → β)
    (F : Forest (Nonplanar (α ⊕ β))) :
    Multiset (Forest (Nonplanar (α ⊕ β)) × Forest (Nonplanar (α ⊕ β))) :=
  (F.map (treeCutsN τ)).foldr
    (fun s acc => (s ×ˢ acc).map ConnesKreimer.combinerProjG) {(0, 0)}

private theorem forestCutsN_zero (τ : Nonplanar (α ⊕ β) → β) :
    forestCutsN τ (0 : Forest (Nonplanar (α ⊕ β))) = {(0, 0)} := by
  unfold forestCutsN; simp

private theorem forestCutsN_cons (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) (F : Forest (Nonplanar (α ⊕ β))) :
    forestCutsN τ (T ::ₘ F) =
      (treeCutsN τ T ×ˢ forestCutsN τ F).map ConnesKreimer.combinerProjG := by
  unfold forestCutsN
  rw [Multiset.map_cons, Multiset.foldr_cons]

/-- `comulCForestN` as a single multiset sum over `forestCutsN`. -/
private theorem comulCForestN_eq_sum (τ : Nonplanar (α ⊕ β) → β)
    (F : Forest (Nonplanar (α ⊕ β))) :
    comulCForestN (R := R) τ F = ((forestCutsN τ F).map (cutTensor (R := R))).sum := by
  induction F using Multiset.induction with
  | empty =>
    rw [comulCForestN_zero, forestCutsN_zero, Multiset.map_singleton,
        Multiset.sum_singleton]
    show (1 : _) = ConnesKreimer.of' (R := R) (0 : Forest (Nonplanar (α ⊕ β))) ⊗ₜ[R]
      ConnesKreimer.of' 0
    rw [ConnesKreimer.of'_zero, Algebra.TensorProduct.one_def]
  | cons T F ih =>
    rw [show (T ::ₘ F : Forest (Nonplanar (α ⊕ β))) = {T} + F from
          (Multiset.singleton_add T F).symm, comulCForestN_add]
    rw [show comulCForestN (R := R) τ {T} = comulCTreeN τ T from by
          unfold comulCForestN; rw [Multiset.map_singleton, Multiset.prod_singleton],
        comulCTreeN_eq_sum, ih]
    rw [show ({T} + F : Forest (Nonplanar (α ⊕ β))) = T ::ₘ F from
          (Multiset.singleton_add T F), forestCutsN_cons, Multiset.map_map]
    rw [show (cutTensor (R := R) ∘ ConnesKreimer.combinerProjG) =
          (fun p => cutTensor (R := R) p.1 * cutTensor p.2) from ?_]
    · rw [sum_product_map_mul]
    · funext p
      obtain ⟨⟨F1, m1⟩, ⟨F2, m2⟩⟩ := p
      show cutTensor (R := R) (F1 + F2, m1 + m2) =
        cutTensor (R := R) (F1, m1) * cutTensor (F2, m2)
      unfold cutTensor
      simp only [ConnesKreimer.of'_add, Algebra.TensorProduct.tmul_mul_tmul]

/-- LHS double-cut enumerator: outer cut of `T`, then re-cut its crown. -/
private noncomputable def dcLHS (τ : Nonplanar (α ⊕ β) → β) (T : Nonplanar (α ⊕ β)) :
    Multiset (Forest (Nonplanar (α ⊕ β)) × Forest (Nonplanar (α ⊕ β)) ×
              Forest (Nonplanar (α ⊕ β))) :=
  (treeCutsN τ T).bind (fun AB =>
    (forestCutsN τ AB.1).map (fun A12 => (A12.1, A12.2, AB.2)))

/-- RHS double-cut enumerator: outer cut of `T`, then re-cut its trunk. -/
private noncomputable def dcRHS (τ : Nonplanar (α ⊕ β) → β) (T : Nonplanar (α ⊕ β)) :
    Multiset (Forest (Nonplanar (α ⊕ β)) × Forest (Nonplanar (α ⊕ β)) ×
              Forest (Nonplanar (α ⊕ β))) :=
  (treeCutsN τ T).bind (fun AB =>
    (forestCutsN τ AB.2).map (fun B12 => (AB.1, B12.1, B12.2)))

/-- Per-cut-pair LHS: reassociating `comulCForestN`-of-crown ⊗ trunk
    enumerates the crown's forest cuts. -/
private theorem lhs_per_pair (τ : Nonplanar (α ⊕ β) → β)
    (A B : Forest (Nonplanar (α ⊕ β))) :
    (TensorProduct.assoc R (ConnesKreimer R (Nonplanar (α ⊕ β)))
        (ConnesKreimer R (Nonplanar (α ⊕ β))) (ConnesKreimer R (Nonplanar (α ⊕ β))))
        (comulCForestN (R := R) τ A ⊗ₜ[R] ConnesKreimer.of' B) =
      ((forestCutsN τ A).map
        (fun A12 => tripleTensor (R := R) (A12.1, A12.2, B))).sum := by
  rw [comulCForestN_eq_sum]
  let φ : (ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R] ConnesKreimer R (Nonplanar (α ⊕ β)))
            →ₗ[R] ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R]
              (ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R]
                ConnesKreimer R (Nonplanar (α ⊕ β))) :=
    (TensorProduct.assoc R _ _ _).toLinearMap ∘ₗ
      ((TensorProduct.mk R _ _).flip (ConnesKreimer.of' B))
  show φ ((Multiset.map (cutTensor (R := R)) (forestCutsN τ A)).sum) = _
  rw [map_multiset_sum, Multiset.map_map]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro p _
  show (TensorProduct.assoc R _ _ _)
      ((ConnesKreimer.of' (R := R) p.1 ⊗ₜ[R] ConnesKreimer.of' p.2) ⊗ₜ[R]
        ConnesKreimer.of' B) = _
  rw [TensorProduct.assoc_tmul]
  rfl

/-- Per-cut-pair RHS: crown ⊗ `comulCForestN`-of-trunk enumerates the
    trunk's forest cuts. -/
private theorem rhs_per_pair (τ : Nonplanar (α ⊕ β) → β)
    (A B : Forest (Nonplanar (α ⊕ β))) :
    ConnesKreimer.of' (R := R) A ⊗ₜ[R] comulCForestN (R := R) τ B =
      ((forestCutsN τ B).map
        (fun B12 => tripleTensor (R := R) (A, B12.1, B12.2))).sum := by
  rw [comulCForestN_eq_sum]
  let ψ : (ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R] ConnesKreimer R (Nonplanar (α ⊕ β)))
            →ₗ[R] ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R]
              (ConnesKreimer R (Nonplanar (α ⊕ β)) ⊗[R]
                ConnesKreimer R (Nonplanar (α ⊕ β))) :=
    (TensorProduct.mk R _ _) (ConnesKreimer.of' A)
  show ψ ((Multiset.map (cutTensor (R := R)) (forestCutsN τ B)).sum) = _
  rw [map_multiset_sum, Multiset.map_map]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro p _
  rfl

/-- **LHS expansion**: `assoc ∘ (Δ^c ⊗ id) ∘ Δ^c` on a tree enumerates
    `dcLHS`. -/
private theorem lhsExpand (τ : Nonplanar (α ⊕ β) → β) (T : Nonplanar (α ⊕ β)) :
    (TensorProduct.assoc R (ConnesKreimer R (Nonplanar (α ⊕ β)))
        (ConnesKreimer R (Nonplanar (α ⊕ β))) (ConnesKreimer R (Nonplanar (α ⊕ β))))
        ((comulCAlgHomN (R := R) τ).toLinearMap.rTensor _ (comulCTreeN τ T)) =
      ((dcLHS τ T).map (tripleTensor (R := R))).sum := by
  rw [comulCTreeN_eq_sum]
  let Λ := (TensorProduct.assoc R (ConnesKreimer R (Nonplanar (α ⊕ β)))
        (ConnesKreimer R (Nonplanar (α ⊕ β)))
        (ConnesKreimer R (Nonplanar (α ⊕ β)))).toLinearMap ∘ₗ
      (comulCAlgHomN (R := R) τ).toLinearMap.rTensor
        (ConnesKreimer R (Nonplanar (α ⊕ β)))
  show Λ ((Multiset.map (cutTensor (R := R)) (treeCutsN τ T)).sum) = _
  rw [map_multiset_sum, Multiset.map_map]
  unfold dcLHS
  rw [Multiset.map_bind, Multiset.sum_bind]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  rintro ⟨A, B⟩ _
  show Λ (cutTensor (R := R) (A, B)) =
    (Multiset.map (tripleTensor (R := R))
      ((forestCutsN τ A).map (fun A12 => (A12.1, A12.2, B)))).sum
  rw [Multiset.map_map]
  show (TensorProduct.assoc R _ _ _)
      ((comulCAlgHomN (R := R) τ).toLinearMap.rTensor _
        ((ConnesKreimer.of' (R := R) A) ⊗ₜ[R] ConnesKreimer.of' B)) = _
  rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, comulCAlgHomN_apply_of',
      lhs_per_pair]
  rfl

/-- **RHS expansion**: `(id ⊗ Δ^c) ∘ Δ^c` on a tree enumerates `dcRHS`. -/
private theorem rhsExpand (τ : Nonplanar (α ⊕ β) → β) (T : Nonplanar (α ⊕ β)) :
    (comulCAlgHomN (R := R) τ).toLinearMap.lTensor _ (comulCTreeN τ T) =
      ((dcRHS τ T).map (tripleTensor (R := R))).sum := by
  rw [comulCTreeN_eq_sum]
  show (comulCAlgHomN (R := R) τ).toLinearMap.lTensor _
        ((Multiset.map (cutTensor (R := R)) (treeCutsN τ T)).sum) = _
  rw [map_multiset_sum, Multiset.map_map]
  unfold dcRHS
  rw [Multiset.map_bind, Multiset.sum_bind]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  rintro ⟨A, B⟩ _
  show (comulCAlgHomN (R := R) τ).toLinearMap.lTensor _ (cutTensor (R := R) (A, B)) =
    (Multiset.map (tripleTensor (R := R))
      ((forestCutsN τ B).map (fun B12 => (A, B12.1, B12.2)))).sum
  rw [Multiset.map_map]
  show (comulCAlgHomN (R := R) τ).toLinearMap.lTensor _
        ((ConnesKreimer.of' (R := R) A) ⊗ₜ[R] ConnesKreimer.of' B) = _
  rw [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, comulCAlgHomN_apply_of',
      rhs_per_pair]
  rfl

/-! ### Descent of the double-cut enumerators through `Nonplanar.mk`

The Nonplanar `dcLHS`/`dcRHS` are the projections (via `Nonplanar.mk`) of the
tree-level `DoubleCut.dcLHSP`/`dcRHSP`; `DoubleCut.coassT` then gives the bijection. -/

/-- Project a tree-level (crown, trunk) pair to Nonplanar. -/
private def projPair (p : Forest (RoseTree (α ⊕ β)) × Forest (RoseTree (α ⊕ β))) :
    Forest (Nonplanar (α ⊕ β)) × Forest (Nonplanar (α ⊕ β)) :=
  (p.1.map Nonplanar.mk, p.2.map Nonplanar.mk)

private theorem treeCutsN_mk (τ : Nonplanar (α ⊕ β) → β) (t : RoseTree (α ⊕ β)) :
    treeCutsN τ (Nonplanar.mk t)
      = (DoubleCut.treeCutsP (τ ∘ Nonplanar.mk) t).map projPair := by
  unfold treeCutsN DoubleCut.treeCutsP
  rw [cutSummandsCN_mk, Multiset.map_cons, Multiset.map_map, Multiset.map_map]
  congr 1

/-- Naturality of the cut combiner under `projPair`. -/
private theorem combinerProjG_nat
    (A B : Multiset (Forest (RoseTree (α ⊕ β)) × Forest (RoseTree (α ⊕ β)))) :
    ((A.map projPair) ×ˢ (B.map projPair)).map ConnesKreimer.combinerProjG
      = ((A ×ˢ B).map (fun pq => (pq.1.1 + pq.2.1, pq.1.2 + pq.2.2))).map projPair := by
  rw [← ConnesKreimer.map_prodMap_product_G, Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl; rintro ⟨⟨F1, m1⟩, ⟨F2, m2⟩⟩ _
  show ConnesKreimer.combinerProjG
      ((F1.map Nonplanar.mk, m1.map Nonplanar.mk), (F2.map Nonplanar.mk, m2.map Nonplanar.mk))
    = projPair (F1 + F2, m1 + m2)
  show (F1.map Nonplanar.mk + F2.map Nonplanar.mk, m1.map Nonplanar.mk + m2.map Nonplanar.mk)
      = ((F1 + F2).map Nonplanar.mk, (m1 + m2).map Nonplanar.mk)
  rw [Multiset.map_add, Multiset.map_add]

private theorem forestCutsN_mk (τ : Nonplanar (α ⊕ β) → β)
    (F : Forest (RoseTree (α ⊕ β))) :
    forestCutsN τ (F.map Nonplanar.mk)
      = (DoubleCut.forestCutsP (τ ∘ Nonplanar.mk) F).map projPair := by
  induction F using Multiset.induction with
  | empty =>
    rw [Multiset.map_zero, forestCutsN_zero, DoubleCut.forestCutsP_zero,
        Multiset.map_singleton]; rfl
  | cons t F ih =>
    rw [Multiset.map_cons, forestCutsN_cons, treeCutsN_mk, ih, DoubleCut.forestCutsP_cons,
        DoubleCut.convFP_eq, combinerProjG_nat]

private theorem dcLHS_mk (τ : Nonplanar (α ⊕ β) → β) (t : RoseTree (α ⊕ β)) :
    dcLHS τ (Nonplanar.mk t) = (DoubleCut.dcLHSP (τ ∘ Nonplanar.mk) t).map DoubleCut.proj3 := by
  unfold dcLHS DoubleCut.dcLHSP
  rw [treeCutsN_mk, Multiset.bind_map, Multiset.map_bind]
  apply Multiset.bind_congr; rintro ⟨F, G⟩ _
  show (forestCutsN τ (F.map Nonplanar.mk)).map (fun A12 => (A12.1, A12.2, G.map Nonplanar.mk))
      = ((DoubleCut.forestCutsP (τ ∘ Nonplanar.mk) F).map
          (fun A12 => (A12.1, A12.2, G))).map DoubleCut.proj3
  rw [forestCutsN_mk, Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl; rintro ⟨A1, A2⟩ _; rfl

private theorem dcRHS_mk (τ : Nonplanar (α ⊕ β) → β) (t : RoseTree (α ⊕ β)) :
    dcRHS τ (Nonplanar.mk t) = (DoubleCut.dcRHSP (τ ∘ Nonplanar.mk) t).map DoubleCut.proj3 := by
  unfold dcRHS DoubleCut.dcRHSP
  rw [treeCutsN_mk, Multiset.bind_map, Multiset.map_bind]
  apply Multiset.bind_congr; rintro ⟨F, G⟩ _
  show (forestCutsN τ (G.map Nonplanar.mk)).map (fun B12 => (F.map Nonplanar.mk, B12.1, B12.2))
      = ((DoubleCut.forestCutsP (τ ∘ Nonplanar.mk) G).map
          (fun B12 => (F, B12.1, B12.2))).map DoubleCut.proj3
  rw [forestCutsN_mk, Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl; rintro ⟨B1, B2⟩ _; rfl

/-- The tree-level trace coherence descends from the Nonplanar one. -/
private theorem traceCoherentP_of_coherent (τ : Nonplanar (α ⊕ β) → β)
    (hτ : TraceCoherent τ) : DoubleCut.TraceCoherentP (τ ∘ Nonplanar.mk) := by
  intro t p hp
  have hmem : ConnesKreimer.projSummand p ∈ cutSummandsCN τ (Nonplanar.mk t) := by
    rw [cutSummandsCN_mk]; exact Multiset.mem_map.mpr ⟨p, hp, rfl⟩
  exact hτ (Nonplanar.mk t) (ConnesKreimer.projSummand p) hmem

/-- **The double-cut bijection** (MCB Lemma 1.2.10's combinatorial core):
    the LHS and RHS double-cut enumerators of a tree agree as Nonplanar
    multisets, under trace coherence. Proved by descending through
    `Nonplanar.mk` to the tree-level `DoubleCut.coassT`. -/
private theorem doubleCut_eq (τ : Nonplanar (α ⊕ β) → β)
    (hτ : TraceCoherent τ) (T : Nonplanar (α ⊕ β)) :
    dcLHS τ T = dcRHS τ T := by
  induction T using Quotient.inductionOn with
  | _ t =>
    show dcLHS τ (Nonplanar.mk t) = dcRHS τ (Nonplanar.mk t)
    rw [dcLHS_mk, dcRHS_mk,
        DoubleCut.coassT (τ ∘ Nonplanar.mk) (traceCoherentP_of_coherent τ hτ) t]

end DoubleCut

/-! ### Coassociativity of Δ^c on Nonplanar (direct double-cut bijection)

Specialized to `[CommRing R]` (rather than `[CommSemiring R]`) only for
uniformity with the `Bialgebra` consumers; the double-cut proof itself is
`CommSemiring`-generic. -/

section CoassocCommRing
variable {R' : Type*} [CommRing R'] {α' β' : Type*}

/-- **Per-tree Δ^c coassociativity** (LinearMap-applied form on a single
    tree's coproduct `comulCTreeN τ T`). The combinatorial heart of
    coassociativity: both sides enumerate ordered pairs of nested
    admissible cuts of `T`, and `TraceCoherent τ` makes the trunk-marker
    labels written by the two cut orders agree.

    Reduced by the two expansion lemmas (`lhsExpand`, `rhsExpand`) to the
    double-cut bijection `doubleCut_eq`. The headline `comulCN_coassoc`
    reduces to this by multiplicativity (forest = product of trees). -/
theorem comulCN_coassoc_tree
    (τ : Nonplanar (α' ⊕ β') → β') (hτ : TraceCoherent τ)
    (T : Nonplanar (α' ⊕ β')) :
    TensorProduct.assoc R'
        (ConnesKreimer R' (Nonplanar (α' ⊕ β')))
        (ConnesKreimer R' (Nonplanar (α' ⊕ β')))
        (ConnesKreimer R' (Nonplanar (α' ⊕ β')))
        ((comulCAlgHomN (R := R') τ).toLinearMap.rTensor _ (comulCTreeN τ T)) =
      (comulCAlgHomN (R := R') τ).toLinearMap.lTensor _ (comulCTreeN τ T) := by
  rw [lhsExpand, rhsExpand, doubleCut_eq τ hτ T]

/-- **Coassociativity of `comulCAlgHomN` (Δ^c on Nonplanar)**, under
    trace coherence.

    NOT τ-generic: without `TraceCoherent τ`, iterating Δ^c writes
    second-stage markers computed on marked trunks, and the two cut
    orders disagree (counterexample: `τ` = inl-vertex count on an
    inl-labeled 3-chain; validated in `scratch/validate_duality.lean`
    V5). Under coherence the double-cut enumerations agree — this is
    [marcolli-chomsky-berwick-2025] Lemma 1.2.10's coassociativity
    (book p. 37–38, the quotient-composition argument "the accessible
    terms of accessible terms … are themselves accessible terms").

    Proved by the double-cut bijection on each tree
    (`comulCN_coassoc_tree`), lifted to forests by multiplicativity
    (both composites are algebra homs, so they agree on a product
    `of' F = ∏ ofTree Tᵢ` once they agree on each `ofTree Tᵢ`). The
    earlier plan to transport `GrossmanLarson.mul_assoc` through a
    GL/Δ^c pairing duality is dead — that duality is false (see the
    Trace coherence section above); the duality route works only for
    Δ^ρ (`Coproduct/PruningDuality.lean`). -/
theorem comulCN_coassoc
    (τ : Nonplanar (α' ⊕ β') → β') (hτ : TraceCoherent τ) :
    TensorProduct.assoc R'
        (ConnesKreimer R' (Nonplanar (α' ⊕ β')))
        (ConnesKreimer R' (Nonplanar (α' ⊕ β')))
        (ConnesKreimer R' (Nonplanar (α' ⊕ β'))) ∘ₗ
      (comulCAlgHomN (R := R') τ).toLinearMap.rTensor _ ∘ₗ
      (comulCAlgHomN (R := R') τ).toLinearMap =
    (comulCAlgHomN (R := R') τ).toLinearMap.lTensor _ ∘ₗ
      (comulCAlgHomN (R := R') τ).toLinearMap := by
  -- Package both composites as algebra homs (defeq to the LinearMap
  -- composites in the statement) and prove the AlgHom equality.
  let CK := ConnesKreimer R' (Nonplanar (α' ⊕ β'))
  let Δ := comulCAlgHomN (R := R') τ
  let L : CK →ₐ[R'] CK ⊗[R'] (CK ⊗[R'] CK) :=
    (Algebra.TensorProduct.assoc R' R' R' CK CK CK).toAlgHom.comp
      ((Algebra.TensorProduct.map Δ (AlgHom.id R' CK)).comp Δ)
  let Rr : CK →ₐ[R'] CK ⊗[R'] (CK ⊗[R'] CK) :=
    (Algebra.TensorProduct.map (AlgHom.id R' CK) Δ).comp Δ
  suffices hLR : L = Rr by
    -- L.toLinearMap and Rr.toLinearMap are defeq to the two composites.
    exact congrArg AlgHom.toLinearMap hLR
  -- Both AlgHoms agree on every basis forest `of' G`, by induction on
  -- `G` using multiplicativity and the per-tree statement.
  have key : ∀ G : Forest (Nonplanar (α' ⊕ β')),
      L (ConnesKreimer.of' G) = Rr (ConnesKreimer.of' G) := by
    intro G
    induction G using Multiset.induction with
    | empty => rw [ConnesKreimer.of'_zero, map_one, map_one]
    | cons T G ihG =>
      rw [show (T ::ₘ G : Forest (Nonplanar (α' ⊕ β'))) = {T} + G from
            (Multiset.singleton_add T G).symm,
          ConnesKreimer.of'_add, map_mul, map_mul, ihG, ConnesKreimer.of'_singleton]
      congr 1
      -- L (ofTree T) = Rr (ofTree T): the per-tree statement (the AlgHom
      -- applications are defeq to the LinearMap-applied per-tree form).
      show TensorProduct.assoc R' CK CK CK
          ((comulCAlgHomN (R := R') τ).toLinearMap.rTensor _
            (comulCAlgHomN (R := R') τ (ConnesKreimer.ofTree T))) =
        (comulCAlgHomN (R := R') τ).toLinearMap.lTensor _
          (comulCAlgHomN (R := R') τ (ConnesKreimer.ofTree T))
      rw [comulCAlgHomN_apply_ofTree]
      exact comulCN_coassoc_tree τ hτ T
  exact ConnesKreimer.algHom_ext (fun F => key F)

end CoassocCommRing

/-! ### Empty-cut uniqueness — combinatorial substrate for the per-tree counit law

For any extract policy and tree `T`, the unique cut summand of
`cutSummandsG extract T` with empty cut forest (`p.1.card = 0`) is the
empty cut `(0, T)`. By mutual structural induction with the list and
per-child cases. This is the substrate for the Δ^c per-tree counit law:
under `(counit ⊗ id)`, only this summand survives, contributing
`1 ⊗ ofTree T`. -/

namespace ConnesKreimer

/-- Helper: filter of `(s ×ˢ t)` by a conjunction predicate distributes
    into a product of filters. Used to factor the cardinality-zero
    condition on `(p.1.1 + p.2.1)` into independent conditions on each
    factor of the cartesian product. -/
private lemma filter_product_split {α₁ β₁ : Type*}
    (s : Multiset α₁) (t : Multiset β₁)
    (p : α₁ → Prop) [DecidablePred p] (q : β₁ → Prop) [DecidablePred q] :
    (s ×ˢ t).filter (fun pr => p pr.1 ∧ q pr.2) = (s.filter p) ×ˢ (t.filter q) := by
  show ((s.bind fun a => t.map (Prod.mk a)).filter (fun pr => p pr.1 ∧ q pr.2)) =
       (s.filter p).bind (fun a => (t.filter q).map (Prod.mk a))
  rw [Multiset.filter_bind, Multiset.bind_filter]
  apply Multiset.bind_congr
  intro a _
  rw [Multiset.filter_map]
  by_cases h : p a
  · rw [if_pos h]
    apply congrArg
    apply Multiset.filter_congr
    intro b _
    show (p a ∧ q b) ↔ q b
    simp [h]
  · rw [if_neg h]
    apply Multiset.eq_zero_of_forall_notMem
    intro pr hpr
    rw [Multiset.mem_map] at hpr
    obtain ⟨b, hb_mem, _hb_eq⟩ := hpr
    rw [Multiset.mem_filter] at hb_mem
    -- hb_mem.2 : ((fun pr => p pr.1 ∧ q pr.2) ∘ Prod.mk a) b = (p a ∧ q b) after β
    have hpa : p a := hb_mem.2.1
    exact h hpa

variable {α : Type*}

mutual

/-- The unique cut summand of `cutSummandsG extract T` with empty cut
    forest is the empty cut `(0, T)`. -/
private theorem cutSummandsG_filter_empty
    (extract : RoseTree α → Option (List (RoseTree α))) :
    ∀ (T : RoseTree α),
      (cutSummandsG extract T).filter (fun p => p.1.card = 0) =
        ({((0 : Forest (RoseTree α)), T)} : Multiset _)
  | .node a cs => by
    rw [cutSummandsG_node, Multiset.filter_map]
    -- After filter_map the inner predicate is `(·.1.card = 0) ∘ (fun p => (p.1, .node a p.2))`,
    -- which is definitionally `fun p => p.1.card = 0`. Use Multiset.filter_congr to
    -- rewrite the predicate to the form the IH expects.
    have hcongr :
        Multiset.filter
            ((fun p : Forest (RoseTree α) × RoseTree α => p.1.card = 0) ∘
              fun p : Forest (RoseTree α) × List (RoseTree α) => (p.1, RoseTree.node a p.2))
            (cutListSummandsG extract cs) =
        Multiset.filter (fun p => p.1.card = 0) (cutListSummandsG extract cs) := by
      apply Multiset.filter_congr
      intro p _
      rfl
    rw [hcongr, cutListSummandsG_filter_empty extract cs, Multiset.map_singleton]

/-- The unique list-cut summand of `cutListSummandsG extract cs` with
    empty cut forest is `(0, cs)`. -/
private theorem cutListSummandsG_filter_empty
    (extract : RoseTree α → Option (List (RoseTree α))) :
    ∀ (cs : List (RoseTree α)),
      (cutListSummandsG extract cs).filter (fun p => p.1.card = 0) =
        ({((0 : Forest (RoseTree α)), cs)} : Multiset _)
  | [] => by
    rw [cutListSummandsG_nil, Multiset.filter_singleton]
    rw [if_pos (show (0 : Forest (RoseTree α)).card = 0 from Multiset.card_zero)]
  | t :: ts => by
    rw [cutListSummandsG_cons, Multiset.filter_map]
    -- Convert composed predicate to a conjunction form using card_add.
    have hcongr :
        Multiset.filter
            ((fun p : Forest (RoseTree α) × List (RoseTree α) => p.1.card = 0) ∘
              fun p : (Forest (RoseTree α) × List (RoseTree α)) ×
                       (Forest (RoseTree α) × List (RoseTree α)) =>
                (p.1.1 + p.2.1, p.1.2 ++ p.2.2))
            (augActionG extract t ×ˢ cutListSummandsG extract ts) =
        Multiset.filter
            (fun p : (Forest (RoseTree α) × List (RoseTree α)) ×
                     (Forest (RoseTree α) × List (RoseTree α)) =>
              (fun q : Forest (RoseTree α) × List (RoseTree α) => q.1.card = 0) p.1 ∧
              (fun q : Forest (RoseTree α) × List (RoseTree α) => q.1.card = 0) p.2)
            (augActionG extract t ×ˢ cutListSummandsG extract ts) := by
      apply Multiset.filter_congr
      intro p _
      show (p.1.1 + p.2.1).card = 0 ↔ p.1.1.card = 0 ∧ p.2.1.card = 0
      rw [Multiset.card_add, Nat.add_eq_zero_iff]
    rw [hcongr,
        filter_product_split (augActionG extract t) (cutListSummandsG extract ts)
          (fun q : Forest (RoseTree α) × List (RoseTree α) => q.1.card = 0)
          (fun q : Forest (RoseTree α) × List (RoseTree α) => q.1.card = 0),
        augActionG_filter_empty extract t,
        cutListSummandsG_filter_empty extract ts,
        Multiset.product_singleton, Multiset.map_singleton]
    show ({((0 : Forest (RoseTree α)) + (0 : Forest (RoseTree α)),
            ([t] : List (RoseTree α)) ++ ts)} : Multiset _) = _
    rw [zero_add]
    rfl

/-- The unique per-child decision of `augActionG extract t` with empty
    cut forest is `(0, [t])` (the "recurse with empty cut" branch). -/
private theorem augActionG_filter_empty
    (extract : RoseTree α → Option (List (RoseTree α))) :
    ∀ (t : RoseTree α),
      (augActionG extract t).filter (fun p => p.1.card = 0) =
        ({((0 : Forest (RoseTree α)), [t])} : Multiset _)
  | t => by
    -- Case-split on extract t up-front using the specialized augActionG_eq_*
    -- lemmas (which avoid the inline match expression).
    cases h_ext : extract t with
    | none =>
      rw [augActionG_eq_none extract t h_ext, Multiset.filter_map]
      have hcongr :
          Multiset.filter
              ((fun p : Forest (RoseTree α) × List (RoseTree α) => p.1.card = 0) ∘
                fun p : Forest (RoseTree α) × RoseTree α => (p.1, [p.2]))
              (cutSummandsG extract t) =
          Multiset.filter (fun p => p.1.card = 0) (cutSummandsG extract t) := by
        apply Multiset.filter_congr
        intro p _
        rfl
      rw [hcongr, cutSummandsG_filter_empty extract t, Multiset.map_singleton]
    | some r =>
      rw [augActionG_eq_some extract t r h_ext, Multiset.filter_cons]
      -- filter cons: if pred (({t}, r)) then {({t},r)} else 0, plus filter of the tail
      rw [if_neg (by
        show ¬ ({t} : Forest (RoseTree α)).card = 0
        rw [Multiset.card_singleton]
        decide)]
      rw [Multiset.zero_add, Multiset.filter_map]
      have hcongr :
          Multiset.filter
              ((fun p : Forest (RoseTree α) × List (RoseTree α) => p.1.card = 0) ∘
                fun p : Forest (RoseTree α) × RoseTree α => (p.1, [p.2]))
              (cutSummandsG extract t) =
          Multiset.filter (fun p => p.1.card = 0) (cutSummandsG extract t) := by
        apply Multiset.filter_congr
        intro p _
        rfl
      rw [hcongr, cutSummandsG_filter_empty extract t, Multiset.map_singleton]

end

/-- Nonplanar-level descent: the unique cut summand of `cutSummandsCN τ T`
    with empty cut forest is `(0, T)`. -/
private theorem cutSummandsCN_filter_empty {α β : Type*}
    (τ : Nonplanar (α ⊕ β) → β) (T : Nonplanar (α ⊕ β)) :
    (cutSummandsCN τ T).filter (fun p => p.1.card = 0) =
      ({((0 : Forest (Nonplanar (α ⊕ β))), T)} : Multiset _) := by
  obtain ⟨T₀, rfl⟩ : ∃ T₀ : RoseTree (α ⊕ β), T = Nonplanar.mk T₀ :=
    ⟨Quotient.out T, (Quotient.out_eq T).symm⟩
  rw [cutSummandsCN_mk, Multiset.filter_map]
  -- `(projSummand p).1.card = (p.1.map Nonplanar.mk).card = p.1.card`; use filter_congr.
  have hcongr :
      Multiset.filter
          ((fun p : Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β) => p.1.card = 0) ∘
            projSummand (α := α ⊕ β))
          (cutSummandsCP (τ ∘ Nonplanar.mk) T₀) =
      Multiset.filter (fun p : Forest (RoseTree (α ⊕ β)) × RoseTree (α ⊕ β) => p.1.card = 0)
          (cutSummandsCP (τ ∘ Nonplanar.mk) T₀) := by
    apply Multiset.filter_congr
    intro p _
    show (p.1.map Nonplanar.mk).card = 0 ↔ p.1.card = 0
    rw [Multiset.card_map]
  rw [hcongr]
  show Multiset.map projSummand
        (Multiset.filter (fun p : Forest (RoseTree (α ⊕ β)) × RoseTree (α ⊕ β) => p.1.card = 0)
          (cutSummandsG (extractC (τ ∘ Nonplanar.mk)) T₀)) = _
  rw [cutSummandsG_filter_empty (extractC (τ ∘ Nonplanar.mk)) T₀,
      Multiset.map_singleton]
  show ((((0 : Forest (RoseTree (α ⊕ β))).map Nonplanar.mk : Forest (Nonplanar (α ⊕ β))),
         Nonplanar.mk T₀) : Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) ::ₘ 0 = _
  rw [Multiset.map_zero]
  rfl

end ConnesKreimer

/-- Sum-of-conditional helper: sum of a multiset map where each entry is
    conditionally zero equals the sum over the filtered subset. -/
private lemma sum_map_ite_zero {ι M : Type*} [AddCommMonoid M]
    (s : Multiset ι) (p : ι → Prop) [DecidablePred p] (g : ι → M) :
    (s.map (fun a => if p a then g a else (0 : M))).sum =
      ((s.filter p).map g).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih]
    by_cases hpa : p a
    · rw [if_pos hpa, Multiset.filter_cons_of_pos _ hpa,
          Multiset.map_cons, Multiset.sum_cons]
    · rw [if_neg hpa, Multiset.filter_cons_of_neg _ hpa, zero_add]

/-! ### Counit laws + Bialgebra instance

With `comulCN_coassoc` structurally closed (modulo 4 deferred substrate
sorries), the remaining inputs to `Bialgebra.ofAlgHom` are:
1. The AlgHom-form coassoc (`comulCAlgHomN_coassoc_algHom`).
2. The right counit law (`counit_rTensor_comulCAlgHomN`).
3. The left counit law (`counit_lTensor_comulCAlgHomN`).

Each lands here. The per-tree counit laws are derived from the empty-cut
uniqueness substrate (`cutSummandsCN_filter_empty`) above. -/

section BialgebraInst
variable {R' : Type*} [CommRing R'] {α' β' : Type*}

/-- **AlgHom-form coassoc** of `comulCAlgHomN` under trace coherence.
    Follows from `comulCN_coassoc` by AlgHom extensionality. -/
theorem comulCAlgHomN_coassoc_algHom
    (τ : Nonplanar (α' ⊕ β') → β') (hτ : TraceCoherent τ) :
    (Algebra.TensorProduct.assoc R' R' R'
        (ConnesKreimer R' (Nonplanar (α' ⊕ β')))
        (ConnesKreimer R' (Nonplanar (α' ⊕ β')))
        (ConnesKreimer R' (Nonplanar (α' ⊕ β')))).toAlgHom.comp
      ((Algebra.TensorProduct.map (comulCAlgHomN (R := R') τ) (AlgHom.id R' _)).comp
        (comulCAlgHomN (R := R') τ)) =
    (Algebra.TensorProduct.map (AlgHom.id R' _) (comulCAlgHomN (R := R') τ)).comp
      (comulCAlgHomN (R := R') τ) := by
  apply AlgHom.toLinearMap_injective
  -- The .toLinearMap of both AlgHom expressions equals the corresponding
  -- LinearMap composition. `comulCN_coassoc` gives the equality.
  exact comulCN_coassoc τ hτ

/-! ### Counit laws — factored via per-tree + forest helpers

Mirrors the Δ^ρ proof structure in `PruningNonplanar.lean` (lines
1049-1598). The headline theorems are CLOSED structurally from two
per-tree sorries that capture the `cutSummandsCN` substrate work
(the (0, T) summand + non-zero-p₁ killing under `counit ⊗ id`). -/

/-- **Per-tree right counit law**: under `(counit ⊗ id)`, only the `(0, T)`
    cut summand of `cutSummandsCN τ T` survives, contributing `1 ⊗ ofTree T`.

    Proof: expand `comulCTreeN τ T = ofTree T ⊗ 1 + Σ (of' p₁ ⊗ ofTree p₂)`.
    Apply `(counit ⊗ id)`: the first summand vanishes via `counit_ofTree`;
    each cut-summand contribution becomes `(if p₁.card = 0 then 1 else 0) ⊗
    ofTree p₂`. Extract the filtered sum via `sum_map_ite_zero`, then use
    `cutSummandsCN_filter_empty` to show the filter yields exactly `{(0, T)}`. -/
private theorem counit_rTensor_comulCTreeN (τ : Nonplanar (α' ⊕ β') → β')
    (T : Nonplanar (α' ⊕ β')) :
    (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R')
        (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β')))))
      (comulCTreeN τ T) = (1 : R') ⊗ₜ ConnesKreimer.ofTree T := by
  -- Expand comulCTreeN τ T.
  unfold comulCTreeN
  rw [map_add]
  -- First summand: (counit ⊗ id)(ofTree T ⊗ 1) = counit(ofTree T) ⊗ 1 = 0 ⊗ 1 = 0.
  rw [show (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R')
              (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β')))))
            (ConnesKreimer.ofTree T ⊗ₜ[R']
              (1 : ConnesKreimer R' (Nonplanar (α' ⊕ β')))) = 0 from by
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ConnesKreimer.counit_ofTree,
        TensorProduct.zero_tmul]]
  rw [zero_add]
  -- Distribute (counit ⊗ id) through the multiset sum.
  rw [map_multiset_sum
        (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R')
          (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β')))))]
  simp only [Multiset.map_map]
  -- Each summand: (counit ⊗ id)(of' p.1 ⊗ ofTree p.2) =
  --   (if p.1.card = 0 then 1 else 0) ⊗ ofTree p.2.
  rw [show ((Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R')
              (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β'))))) ∘
            (fun p : Forest (Nonplanar (α' ⊕ β')) × Nonplanar (α' ⊕ β') =>
              ConnesKreimer.of' (R := R') p.1 ⊗ₜ[R'] ConnesKreimer.ofTree p.2)) =
            (fun p => (if p.1.card = 0 then (1 : R') else 0) ⊗ₜ[R']
                       ConnesKreimer.ofTree p.2) from by
    funext p
    show (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R')
            (AlgHom.id R' _))
          (ConnesKreimer.of' (R := R') p.1 ⊗ₜ[R'] ConnesKreimer.ofTree p.2) = _
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ConnesKreimer.counit_of']]
  -- Pull the if outside the tensor product: (if h then 1 else 0) ⊗ y = if h then 1 ⊗ y else 0.
  rw [show (fun p : Forest (Nonplanar (α' ⊕ β')) × Nonplanar (α' ⊕ β') =>
              (if p.1.card = 0 then (1 : R') else 0) ⊗ₜ[R']
                ConnesKreimer.ofTree p.2) =
            (fun p =>
              if p.1.card = 0 then
                ((1 : R') ⊗ₜ[R'] ConnesKreimer.ofTree p.2 :
                  R' ⊗[R'] ConnesKreimer R' (Nonplanar (α' ⊕ β')))
              else 0) from by
    funext p
    by_cases hp : p.1.card = 0
    · rw [if_pos hp, if_pos hp]
    · rw [if_neg hp, if_neg hp, TensorProduct.zero_tmul]]
  -- Extract the filter via sum_map_ite_zero.
  rw [sum_map_ite_zero]
  -- Filter equals {(0, T)} by cutSummandsCN_filter_empty.
  rw [ConnesKreimer.cutSummandsCN_filter_empty τ T,
      Multiset.map_singleton, Multiset.sum_singleton]

/-- **Per-tree left counit law**: mirror of the right counit. Same
    `cutSummandsCN` substrate, with `counit` on the right factor. -/
private theorem counit_lTensor_comulCTreeN (τ : Nonplanar (α' ⊕ β') → β')
    (T : Nonplanar (α' ⊕ β')) :
    (Algebra.TensorProduct.map (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β'))))
        ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R'))
      (comulCTreeN τ T) = ConnesKreimer.ofTree T ⊗ₜ (1 : R') := by
  unfold comulCTreeN
  rw [map_add]
  -- First summand: (id ⊗ counit)(ofTree T ⊗ 1) = ofTree T ⊗ counit(1) = ofTree T ⊗ 1.
  rw [show (Algebra.TensorProduct.map
              (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β'))))
              ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R'))
            (ConnesKreimer.ofTree T ⊗ₜ[R']
              (1 : ConnesKreimer R' (Nonplanar (α' ⊕ β')))) =
          ConnesKreimer.ofTree T ⊗ₜ[R'] (1 : R') from by
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]]
  -- Second summand: distribute via map_multiset_sum, then show the entire sum is 0.
  rw [map_multiset_sum
        (Algebra.TensorProduct.map (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β'))))
          ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R'))]
  simp only [Multiset.map_map]
  -- Each summand: (id ⊗ counit)(of' p.1 ⊗ ofTree p.2) = of' p.1 ⊗ counit(ofTree p.2)
  --              = of' p.1 ⊗ 0 = 0.
  rw [show ((Algebra.TensorProduct.map
              (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β'))))
              ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R')) ∘
            (fun p : Forest (Nonplanar (α' ⊕ β')) × Nonplanar (α' ⊕ β') =>
              ConnesKreimer.of' (R := R') p.1 ⊗ₜ[R'] ConnesKreimer.ofTree p.2)) =
            (fun _ => (0 : ConnesKreimer R' (Nonplanar (α' ⊕ β')) ⊗[R'] R')) from by
    funext p
    show (Algebra.TensorProduct.map
            (AlgHom.id R' _) ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R'))
          (ConnesKreimer.of' (R := R') p.1 ⊗ₜ[R'] ConnesKreimer.ofTree p.2) = _
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ConnesKreimer.counit_ofTree,
        TensorProduct.tmul_zero]]
  -- The sum of all zeros over a multiset is 0.
  rw [show ((cutSummandsCN τ T).map (fun _ : Forest (Nonplanar (α' ⊕ β')) × Nonplanar (α' ⊕ β') =>
              (0 : ConnesKreimer R' (Nonplanar (α' ⊕ β')) ⊗[R'] R'))).sum = 0 from by
    induction (cutSummandsCN τ T) using Multiset.induction with
    | empty => simp
    | cons _ _ ih => rw [Multiset.map_cons, Multiset.sum_cons, ih, add_zero]]
  rw [add_zero]

/-- **Forest right counit law**: lift per-tree to forest via `Multiset.induction`
    + multiplicativity of `comulCForestN` and `(counit ⊗ id)` as AlgHom.
    Mirrors `PruningNonplanar.comulForestN_counit_rTensor`. -/
private theorem counit_rTensor_comulCForestN (τ : Nonplanar (α' ⊕ β') → β')
    (F : Forest (Nonplanar (α' ⊕ β')))
    (hF : ∀ T ∈ F, (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R')
        (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β')))))
        (comulCTreeN τ T) = (1 : R') ⊗ₜ ConnesKreimer.ofTree T) :
    (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R')
        (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β')))))
      (comulCForestN (R := R') τ F) = (1 : R') ⊗ₜ ConnesKreimer.of' F := by
  induction F using Multiset.induction with
  | empty =>
    rw [comulCForestN_zero, map_one, ConnesKreimer.of'_zero,
        Algebra.TensorProduct.one_def]
  | cons T F' ih =>
    have ih' := ih (fun T' hT' => hF T' (Multiset.mem_cons_of_mem hT'))
    have hT := hF T (Multiset.mem_cons_self T F')
    have hForest : (ConnesKreimer.ofTree T : ConnesKreimer R' (Nonplanar (α' ⊕ β')))
                    * ConnesKreimer.of' F' = ConnesKreimer.of' (T ::ₘ F') := by
      rw [show (T ::ₘ F' : Forest (Nonplanar (α' ⊕ β'))) = {T} + F' from
            (Multiset.singleton_add T F').symm,
          ConnesKreimer.of'_add, ConnesKreimer.of'_singleton]
    -- comulCForestN (T ::ₘ F') = comulCTreeN τ T * comulCForestN τ F'
    have hCons : comulCForestN (R := R') τ (T ::ₘ F') =
        comulCTreeN (R := R') τ T * comulCForestN (R := R') τ F' := by
      unfold comulCForestN
      rw [Multiset.map_cons, Multiset.prod_cons]
    rw [hCons, map_mul, hT, ih',
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, hForest]

/-- **Forest left counit law**: mirror. -/
private theorem counit_lTensor_comulCForestN (τ : Nonplanar (α' ⊕ β') → β')
    (F : Forest (Nonplanar (α' ⊕ β')))
    (hF : ∀ T ∈ F, (Algebra.TensorProduct.map
        (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β'))))
        ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R'))
        (comulCTreeN τ T) = ConnesKreimer.ofTree T ⊗ₜ (1 : R')) :
    (Algebra.TensorProduct.map (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β'))))
        ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R'))
      (comulCForestN (R := R') τ F) = ConnesKreimer.of' F ⊗ₜ (1 : R') := by
  induction F using Multiset.induction with
  | empty =>
    rw [comulCForestN_zero, map_one, ConnesKreimer.of'_zero,
        Algebra.TensorProduct.one_def]
  | cons T F' ih =>
    have ih' := ih (fun T' hT' => hF T' (Multiset.mem_cons_of_mem hT'))
    have hT := hF T (Multiset.mem_cons_self T F')
    have hForest : (ConnesKreimer.ofTree T : ConnesKreimer R' (Nonplanar (α' ⊕ β')))
                    * ConnesKreimer.of' F' = ConnesKreimer.of' (T ::ₘ F') := by
      rw [show (T ::ₘ F' : Forest (Nonplanar (α' ⊕ β'))) = {T} + F' from
            (Multiset.singleton_add T F').symm,
          ConnesKreimer.of'_add, ConnesKreimer.of'_singleton]
    have hCons : comulCForestN (R := R') τ (T ::ₘ F') =
        comulCTreeN (R := R') τ T * comulCForestN (R := R') τ F' := by
      unfold comulCForestN
      rw [Multiset.map_cons, Multiset.prod_cons]
    rw [hCons, map_mul, hT, ih',
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, hForest]

/-- **Right counit law** (CLOSED via per-tree + forest helpers): `(counit ⊗ id) ∘ Δ^c = lid⁻¹`. -/
theorem counit_rTensor_comulCAlgHomN (τ : Nonplanar (α' ⊕ β') → β') :
    (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R')
        (AlgHom.id R' _)).comp (comulCAlgHomN (R := R') τ) =
      (Algebra.TensorProduct.lid R'
        (ConnesKreimer R' (Nonplanar (α' ⊕ β')))).symm.toAlgHom := by
  apply ConnesKreimer.algHom_ext
  intro F
  show (Algebra.TensorProduct.map ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R')
          (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β')))))
        (comulCAlgHomN (R := R') τ (ConnesKreimer.of' F)) =
       (Algebra.TensorProduct.lid R'
        (ConnesKreimer R' (Nonplanar (α' ⊕ β')))).symm (ConnesKreimer.of' F)
  rw [comulCAlgHomN_apply_of', Algebra.TensorProduct.lid_symm_apply]
  exact counit_rTensor_comulCForestN τ F (fun T _ => counit_rTensor_comulCTreeN τ T)

/-- **Left counit law** (CLOSED via per-tree + forest helpers): `(id ⊗ counit) ∘ Δ^c = rid⁻¹`. -/
theorem counit_lTensor_comulCAlgHomN (τ : Nonplanar (α' ⊕ β') → β') :
    (Algebra.TensorProduct.map (AlgHom.id R' _)
        ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R')).comp (comulCAlgHomN (R := R') τ) =
      (Algebra.TensorProduct.rid R' R'
        (ConnesKreimer R' (Nonplanar (α' ⊕ β')))).symm.toAlgHom := by
  apply ConnesKreimer.algHom_ext
  intro F
  show (Algebra.TensorProduct.map (AlgHom.id R' (ConnesKreimer R' (Nonplanar (α' ⊕ β'))))
          ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R'))
        (comulCAlgHomN (R := R') τ (ConnesKreimer.of' F)) =
       (Algebra.TensorProduct.rid R' R'
        (ConnesKreimer R' (Nonplanar (α' ⊕ β')))).symm (ConnesKreimer.of' F)
  rw [comulCAlgHomN_apply_of', Algebra.TensorProduct.rid_symm_apply]
  exact counit_lTensor_comulCForestN τ F (fun T _ => counit_lTensor_comulCTreeN τ T)

/-- **`Bialgebra` structure** on `ConnesKreimer R' (Nonplanar (α' ⊕ β'))`
    with Δ^c as the coproduct, for a trace-coherent encoder.

    The graded bialgebra structure of MCB Lemma 1.2.10. Built via
    `Bialgebra.ofAlgHom` with `comulCAlgHomN τ` as the coproduct and the
    inherited `counit` from CK. A `def`, not an `instance`: coassociativity
    needs `TraceCoherent τ` (it is false for arbitrary `τ` — see
    `comulCN_coassoc`), which instance resolution cannot synthesize.
    Depends on:
    * `comulCAlgHomN_coassoc_algHom` (sorried, under trace coherence).
    * `counit_rTensor_comulCAlgHomN` (proved).
    * `counit_lTensor_comulCAlgHomN` (proved). -/
@[reducible] noncomputable def bialgebraC
    (τ : Nonplanar (α' ⊕ β') → β')
    (hτ : TraceCoherent τ) :
    Bialgebra R' (ConnesKreimer R' (Nonplanar (α' ⊕ β'))) :=
  Bialgebra.ofAlgHom (comulCAlgHomN (R := R') τ) ((ConnesKreimer.counit (R := R')) :
          ConnesKreimer R' (Nonplanar (α' ⊕ β')) →ₐ[R'] R')
    (comulCAlgHomN_coassoc_algHom τ hτ)
    (counit_rTensor_comulCAlgHomN τ)
    (counit_lTensor_comulCAlgHomN τ)

end BialgebraInst

/-! ## MCB Lemma 1.2.10 — graded bialgebra structure

Per `marcolli-chomsky-berwick-2025` p. 37, Lemma 1.2.10:

> Let V^c(𝔉_{SO_0}) denote the vector space (over ℚ) spanned by the
> workspaces F ∈ 𝔉_{SO_0}, endowed with the product given by the
> disjoint union ⊔ and the coproduct Δ^c of (1.2.8). The space
> V(𝔉_{SO_0}) is graded by the number of edges. Then
> (V^c(𝔉_{SO_0}), ⊔, Δ^c) is a graded bialgebra.

This section formalizes the statement: defines edge-count grading on
forests, sets up the graded subspaces, and packages MCB Lemma 1.2.10
as a theorem combining the Δ^c bialgebra structure (`bialgebraC`, for
trace-coherent encoders) with grading compatibility. Both grading
halves are fully proved (edge conservation through the trace cut
machinery: `cutSummandsCN_numNodes`). -/

section MCBLemma1_2_10
variable {R'' : Type*} [CommRing R''] {α'' β'' : Type*}

/-- **Edge count of a forest**: total edges across all trees.

    A tree with `n` vertices has `n - 1` edges. For a forest
    `F = {T_1, ..., T_k}`: total edges = `Σ (weight(T_i) - 1)`.

    Defined as a per-tree sum (avoiding global subtraction) to make
    additivity (`edgeCount (F + G) = edgeCount F + edgeCount G`)
    immediate from `Multiset.map_add` + `Multiset.sum_add`.

    Per MCB Lemma 1.2.10, this is the grading on V^c(𝔉_{SO_0}). -/
def Forest.edgeCount {X : Type*} (F : Forest (Nonplanar X)) : ℕ :=
  (F.map (fun T => T.numNodes - 1)).sum

/-- **Graded piece V_n**: the subspace of `ConnesKreimer R'' (Nonplanar X)`
    spanned by forests with exactly `n` edges. -/
noncomputable def gradedPiece (X : Type*) (n : ℕ) :
    Submodule R'' (ConnesKreimer R'' (Nonplanar X)) :=
  Submodule.span R''
    {x | ∃ F : Forest (Nonplanar X), F.edgeCount = n ∧ x = ConnesKreimer.of' F}

/-! ### Edge bookkeeping for `edgeCount` -/

private theorem edgeCount_add {X : Type*} (F G : Forest (Nonplanar X)) :
    Forest.edgeCount (F + G) = Forest.edgeCount F + Forest.edgeCount G := by
  show ((F + G).map (fun T => T.numNodes - 1)).sum = _
  rw [Multiset.map_add, Multiset.sum_add]
  rfl

private theorem edgeCount_singleton {X : Type*} (T : Nonplanar X) :
    Forest.edgeCount ({T} : Forest (Nonplanar X)) = T.numNodes - 1 := by
  show (({T} : Multiset (Nonplanar X)).map (fun T => T.numNodes - 1)).sum = _
  rw [Multiset.map_singleton, Multiset.sum_singleton]

/-- `Σ (wᵢ − 1) + card = Σ wᵢ` for tree-level forests (each `wᵢ ≥ 1`). -/
private theorem sum_map_numNodes_sub_one_add_card {γ : Type*}
    (F : Multiset (RoseTree γ)) :
    ((F.map (fun t => RoseTree.numNodes t - 1)).sum + Multiset.card F =
      (F.map RoseTree.numNodes).sum) := by
  induction F using Multiset.induction_on with
  | empty => rfl
  | cons a F ih =>
    have h1 : 1 ≤ RoseTree.numNodes a := RoseTree.numNodes_pos a
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons,
        Multiset.sum_cons, Multiset.card_cons]
    omega

/-- **Edge conservation for Δ^c cut summands**: the trace marker replaces
    the cut subtree by a unit-weight leaf, so crown edges plus trunk
    weight recover the tree weight exactly. Descends
    `cutSummandsG_numNodes` (`Coproduct/Defs.lean`) through `Nonplanar.mk`. -/
private theorem cutSummandsCN_numNodes (τ : Nonplanar (α'' ⊕ β'') → β'')
    (T : Nonplanar (α'' ⊕ β'')) :
    ∀ p ∈ cutSummandsCN τ T,
      Forest.edgeCount p.1 + p.2.numNodes = T.numNodes := by
  obtain ⟨T₀, rfl⟩ : ∃ T₀ : RoseTree (α'' ⊕ β''), T = Nonplanar.mk T₀ :=
    ⟨T.out, (Quotient.out_eq T).symm⟩
  intro p hp
  rw [cutSummandsCN_mk] at hp
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
  rw [ConnesKreimer.cutSummandsCP_def] at hq
  have hext : ∀ (t : RoseTree (α'' ⊕ β'')) r,
      ConnesKreimer.extractC (τ ∘ Nonplanar.mk) t = some r →
      (r.map RoseTree.numNodes).sum = 1 := by
    intro t r h
    cases t with
    | node x cs =>
      cases x with
      | inl a =>
        rw [ConnesKreimer.extractC_inl] at h
        obtain rfl := (Option.some.injEq _ _ ▸ h :
          [ConnesKreimer.traceLeaf ((τ ∘ Nonplanar.mk)
            (RoseTree.node (Sum.inl a) cs))] = r)
        simp [ConnesKreimer.traceLeaf]
      | inr b =>
        rw [ConnesKreimer.extractC_inr] at h
        exact absurd h (by simp)
  have h := ConnesKreimer.cutSummandsG_numNodes _ hext T₀ q hq
  have hsub := sum_map_numNodes_sub_one_add_card q.1
  show Forest.edgeCount (q.1.map Nonplanar.mk) +
      (Nonplanar.mk q.2).numNodes = (Nonplanar.mk T₀).numNodes
  rw [Nonplanar.numNodes_mk, Nonplanar.numNodes_mk]
  rw [show Forest.edgeCount (q.1.map Nonplanar.mk) =
      ((q.1.map (fun t => RoseTree.numNodes t - 1)).sum) from by
    show ((q.1.map Nonplanar.mk).map
        (fun T => Nonplanar.numNodes T - 1)).sum = _
    rw [Multiset.map_map]
    rfl]
  omega

/-! ### Homogeneous tensor span at fixed total edge degree -/

/-- The span of basis tensors `of' F₁ ⊗ of' F₂` with total edge count
    `n` — the homogeneous degree-`n` piece of the tensor square through
    which Δ^c factors. -/
private noncomputable def gradedTensorSpan (n : ℕ) :
    Submodule R'' (ConnesKreimer R'' (Nonplanar (α'' ⊕ β'')) ⊗[R'']
      ConnesKreimer R'' (Nonplanar (α'' ⊕ β''))) :=
  Submodule.span R'' {y | ∃ F₁ F₂ : Forest (Nonplanar (α'' ⊕ β'')),
    Forest.edgeCount F₁ + Forest.edgeCount F₂ = n ∧
    y = ConnesKreimer.of' F₁ ⊗ₜ[R''] ConnesKreimer.of' F₂}

/-- Multiplicativity of the graded tensor spans: degrees add. -/
private theorem gradedTensorSpan_mul {m k : ℕ}
    {u v : ConnesKreimer R'' (Nonplanar (α'' ⊕ β'')) ⊗[R'']
      ConnesKreimer R'' (Nonplanar (α'' ⊕ β''))}
    (hu : u ∈ gradedTensorSpan (R'' := R'') (α'' := α'') (β'' := β'') m)
    (hv : v ∈ gradedTensorSpan (R'' := R'') (α'' := α'') (β'' := β'') k) :
    u * v ∈ gradedTensorSpan (R'' := R'') (α'' := α'') (β'' := β'') (m + k) := by
  have hle : gradedTensorSpan (R'' := R'') (α'' := α'') (β'' := β'') m *
      gradedTensorSpan (R'' := R'') (α'' := α'') (β'' := β'') k ≤
      gradedTensorSpan (R'' := R'') (α'' := α'') (β'' := β'') (m + k) := by
    rw [gradedTensorSpan, gradedTensorSpan, Submodule.span_mul_span]
    refine Submodule.span_le.mpr ?_
    rintro w ⟨a, ⟨F₁, F₂, hab, rfl⟩, b, ⟨G₁, G₂, hgk, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨F₁ + G₁, F₂ + G₂, ?_, ?_⟩
    · rw [edgeCount_add, edgeCount_add]
      omega
    · show (ConnesKreimer.of' F₁ ⊗ₜ[R''] ConnesKreimer.of' F₂) *
        (ConnesKreimer.of' G₁ ⊗ₜ[R''] ConnesKreimer.of' G₂) =
        ConnesKreimer.of' (F₁ + G₁) ⊗ₜ[R''] ConnesKreimer.of' (F₂ + G₂)
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← ConnesKreimer.of'_add,
        ← ConnesKreimer.of'_add]
  exact hle (Submodule.mul_mem_mul hu hv)

/-- Tree-level membership: `Δ^c` of a single tree is homogeneous of
    degree the tree's edge count. -/
private theorem comulCTreeN_mem (τ : Nonplanar (α'' ⊕ β'') → β'')
    (T : Nonplanar (α'' ⊕ β'')) :
    comulCTreeN (R := R'') τ T ∈
      gradedTensorSpan (R'' := R'') (α'' := α'') (β'' := β'') (T.numNodes - 1) := by
  unfold comulCTreeN
  refine Submodule.add_mem _ ?_ ?_
  · refine Submodule.subset_span ⟨{T}, 0, ?_, ?_⟩
    · rw [edgeCount_singleton]
      show T.numNodes - 1 + Forest.edgeCount (0 : Forest (Nonplanar (α'' ⊕ β''))) =
        T.numNodes - 1
      show T.numNodes - 1 + 0 = T.numNodes - 1
      omega
    · rw [ConnesKreimer.of'_zero]
      rfl
  · refine multiset_sum_mem _ ?_
    intro c hc
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hc
    have hcons := cutSummandsCN_numNodes τ T p hp
    have hpos := Nonplanar.numNodes_pos p.2
    refine Submodule.subset_span ⟨p.1, {p.2}, ?_, rfl⟩
    rw [edgeCount_singleton]
    omega

/-- Forest-level membership: `Δ^c` of a forest is homogeneous of degree
    its edge count. -/
private theorem comulCForestN_mem (τ : Nonplanar (α'' ⊕ β'') → β'')
    (F : Forest (Nonplanar (α'' ⊕ β''))) :
    comulCForestN (R := R'') τ F ∈
      gradedTensorSpan (R'' := R'') (α'' := α'') (β'' := β'')
        (Forest.edgeCount F) := by
  induction F using Multiset.induction_on with
  | empty =>
    rw [comulCForestN_zero]
    refine Submodule.subset_span
      ⟨0, 0, rfl, ?_⟩
    rw [Algebra.TensorProduct.one_def, ConnesKreimer.of'_zero]
  | cons T F ih =>
    have hcons : comulCForestN (R := R'') τ (T ::ₘ F) =
        comulCTreeN (R := R'') τ T * comulCForestN (R := R'') τ F := by
      show comulCForestN (R := R'') τ (({T} : Multiset (Nonplanar (α'' ⊕ β''))) + F) = _
      rw [comulCForestN_add]
      congr 1
      show ((({T} : Multiset (Nonplanar (α'' ⊕ β''))).map
          (comulCTreeN (R := R'') τ)).prod) = _
      rw [Multiset.map_singleton, Multiset.prod_singleton]
    rw [hcons,
        show Forest.edgeCount (T ::ₘ F) =
          (T.numNodes - 1) + Forest.edgeCount F from by
        show ((T ::ₘ F).map (fun T => T.numNodes - 1)).sum = _
        rw [Multiset.map_cons, Multiset.sum_cons]
        rfl]
    exact gradedTensorSpan_mul (comulCTreeN_mem τ T) ih

/-- **MCB Lemma 1.2.10** — the graded bialgebra structure.

    States that:
    1. The bialgebra structure `bialgebraC` (from `comulCAlgHomN`, for
       trace-coherent encoders).
    2. The space `V^c(𝔉_{SO_0})` is graded by `edgeCount`.
    3. The product (⊔ = disjoint union) preserves grading additively:
       `V_n ⊗ V_m → V_{n+m}` (because `edgeCount(F + G) = edgeCount(F) + edgeCount(G)`).
    4. The coproduct (Δ^c) preserves grading: for `x ∈ V_n`,
       `Δ^c(x) ∈ Σ_{i+j=n} V_i ⊗ V_j`.

    **Status**: statement packaged. The grading-compatibility proofs are
    sorry'd (substrate work).

    **Hopf structure** (corollary, deferred):
    > induces a Hopf algebra structure on the complement in V^c(𝔉_{SO_0})
    > of the span of the lexical items and features.

    Antipode emerges via the graded connected bialgebra construction
    (inductive formula `S(x) = -x - Σ S(x_(1)) · x_(2)`) after quotienting
    by the (1 - α) ideal for α a lexical-item generator. Deferred to
    sibling file. -/
theorem mcb_lemma_1_2_10
    (τ : Nonplanar (α'' ⊕ β'') → β'') :
    -- (1) Bialgebra structure: `bialgebraC` (for trace-coherent τ).
    -- (2) Edge-count grading: each gradedPiece is a Submodule.
    -- (3) Product preserves grading: of'(F+G).edgeCount = F.edgeCount + G.edgeCount.
    (∀ F G : Forest (Nonplanar (α'' ⊕ β'')),
      Forest.edgeCount (F + G) = Forest.edgeCount F + Forest.edgeCount G) ∧
    -- (4) Coproduct preserves grading: for basis x = of' F with edge count n,
    -- comulCAlgHomN τ x ∈ ⊕_{i+j=n} V_i ⊗ V_j.
    (∀ (n : ℕ) (F : Forest (Nonplanar (α'' ⊕ β''))),
      Forest.edgeCount F = n →
      comulCAlgHomN (R := R'') τ (ConnesKreimer.of' F) ∈
        Submodule.span R'' {y | ∃ (i j : ℕ) (_hi : i + j = n)
          (xi yi : ConnesKreimer R'' (Nonplanar (α'' ⊕ β''))),
          xi ∈ gradedPiece (α'' ⊕ β'') i ∧
          yi ∈ gradedPiece (α'' ⊕ β'') j ∧
          y = xi ⊗ₜ[R''] yi}) := by
  refine ⟨edgeCount_add, ?_⟩
  · -- Δ^c preserves grading exactly: each cut summand splits the edges
    -- (the trace marker replaces the cut subtree by a unit-weight leaf,
    -- `cutSummandsCN_numNodes`), and the homogeneous tensor spans multiply
    -- additively (`gradedTensorSpan_mul`).
    intro n F hF
    rw [comulCAlgHomN_apply_of']
    have hmem := comulCForestN_mem (R'' := R'') τ F
    rw [hF] at hmem
    refine SetLike.le_def.mp (Submodule.span_le.mpr ?_) hmem
    rintro y ⟨F₁, F₂, hsum, rfl⟩
    exact Submodule.subset_span
      ⟨Forest.edgeCount F₁, Forest.edgeCount F₂, hsum,
        ConnesKreimer.of' F₁, ConnesKreimer.of' F₂,
        Submodule.subset_span ⟨F₁, rfl, rfl⟩,
        Submodule.subset_span ⟨F₂, rfl, rfl⟩, rfl⟩

end MCBLemma1_2_10

end RootedTree
