/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.Coproduct.Trace
import Linglib.Core.Algebra.RootedTree.GrossmanLarson
import Linglib.Core.Algebra.RootedTree.GrossmanLarsonPairing
import Mathlib.RingTheory.Bialgebra.Basic

set_option autoImplicit false

/-!
# Δ^c on `ConnesKreimer R (Nonplanar (α ⊕ β))` via descent + duality
@cite{marcolli-chomsky-berwick-2025}
@cite{foissy-typed-decorated-rooted-trees-2018}

The decorated coproduct Δ^c (contraction-extraction with trace
placeholders) descended from the planar version `comulCAlgHomP` in
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

`[UPSTREAM]` candidate. Skeleton API only. All proofs `sorry`. Builds
on R.5 GL substrate (sorry'd `mul_assoc`) and R.6 pairing substrate
(sorry'd everywhere). Proper proofs land once R.5 + R.6 are sorry-free.
-/

namespace RootedTree

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α β : Type*}

/-! ## Descent of cut-summand enumeration

Mirrors `Coproduct/PruningNonplanar.lean`'s descent of `cutSummandsP`,
but for the generic `cutSummandsG` (which uses a `List`-shaped per-cut
remainder rather than `Option`). The descent applies whenever the
`extract` policy is invariant under `Planar.PlanarEquiv` modulo
`Nonplanar.mk`. For Δ^c (`extractC (τ ∘ Nonplanar.mk)`) this follows
from `planarEquiv_label_eq`. -/

namespace ConnesKreimer

/-! ### Pointwise projection for the G-form -/

/-- Project a planar cut summand to a nonplanar one. -/
private def projSummand : Forest (Planar α) × Planar α →
    Forest (Nonplanar α) × Nonplanar α :=
  fun p => (p.1.map Nonplanar.mk, Nonplanar.mk p.2)

/-- Project a `cutListSummandsG` summand to nonplanar level, discarding
    the list-order of the remainder by sending to `Multiset`. -/
private def projForestG : Forest (Planar α) × List (Planar α) →
    Forest (Nonplanar α) × Multiset (Nonplanar α) :=
  fun p => (p.1.map Nonplanar.mk, Multiset.ofList (p.2.map Nonplanar.mk))

/-! ### Bridge: `projSummand` factors through `projForestG` + `node` -/

/-- Applying the `cutSummandsG_node` wrapper `(p.1, .node a p.2)` then
    `projSummand` factors through `projForestG` followed by the
    `Nonplanar.node a` smart constructor. -/
private theorem projSummand_node_factors (a : α)
    (p : Forest (Planar α) × List (Planar α)) :
    projSummand (α := α) (p.1, .node a p.2) =
      ((projForestG p).1, Nonplanar.node a (projForestG p).2) := by
  show (p.1.map Nonplanar.mk, Nonplanar.mk (.node a p.2)) =
       (p.1.map Nonplanar.mk,
        Nonplanar.node a (Multiset.ofList (p.2.map Nonplanar.mk)))
  congr 1
  exact (Nonplanar.node_mk_planar_list a p.2).symm

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

/-- Pointwise: `projForestG` of an applied planar combiner equals
    `combinerProjG` applied to the projected pair-of-pairs. -/
private theorem projForestG_combine_apply
    (p : (Forest (Planar α) × List (Planar α)) ×
         (Forest (Planar α) × List (Planar α))) :
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
    (extract : Planar α → Option (List (Planar α)))
    (t : Planar α) (ts : List (Planar α)) :
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
component-wise through `Nonplanar.mk`, is the same on `PlanarEquiv`-equal
inputs. For Δ^c (`extractC (τ ∘ Nonplanar.mk)`) this holds because the
root label and the τ value are both `PlanarEquiv`-invariant. -/

/-- An extract policy is **`Nonplanar.mk`-invariant** if its return
    value, projected componentwise through `Nonplanar.mk`, depends on
    its input only through `Nonplanar.mk`. -/
def ExtractInvariant (extract : Planar α → Option (List (Planar α))) : Prop :=
  ∀ t s : Planar α, Nonplanar.mk t = Nonplanar.mk s →
    (extract t).map (List.map (Nonplanar.mk (α := α))) =
      (extract s).map (List.map (Nonplanar.mk (α := α)))

/-- `augActionG`-projection invariance under the descent hypothesis. -/
private theorem augActionG_proj_eq_of_step_data
    {extract : Planar α → Option (List (Planar α))}
    (hExt : ExtractInvariant extract)
    {old new : Planar α}
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
              (match (none : Option (List (Planar α))) with
               | none => 0
               | some r => {((({old} : Forest (Planar α))), r)}) =
             Multiset.map projForestG
              (match (none : Option (List (Planar α))) with
               | none => 0
               | some r => {((({new} : Forest (Planar α))), r)})
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
              (match (some rOld : Option (List (Planar α))) with
               | none => 0
               | some r => {((({old} : Forest (Planar α))), r)}) =
             Multiset.map projForestG
              (match (some rNew : Option (List (Planar α))) with
               | none => 0
               | some r => {((({new} : Forest (Planar α))), r)})
        show Multiset.map projForestG
                ({(({old} : Forest (Planar α)), rOld)} : Multiset _) =
             Multiset.map projForestG
                ({(({new} : Forest (Planar α)), rNew)} : Multiset _)
        rw [Multiset.map_singleton, Multiset.map_singleton]
        show ({(({old} : Forest (Planar α)).map Nonplanar.mk,
                Multiset.ofList (rOld.map Nonplanar.mk))} :
              Multiset (Forest (Nonplanar α) × Multiset (Nonplanar α))) =
             {(({new} : Forest (Planar α)).map Nonplanar.mk,
                Multiset.ofList (rNew.map Nonplanar.mk))}
        rw [Multiset.map_singleton, Multiset.map_singleton, h_mk, hExtEq]
  · -- Inherited branch: projForestG of (p.1, [p.2]) = ((projSummand p).1, ↑[(projSummand p).2])
    rw [Multiset.map_map, Multiset.map_map]
    have eq_fn :
        (projForestG (α := α)) ∘
          (fun (p : Forest (Planar α) × Planar α) => (p.1, [p.2])) =
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
    (extract : Planar α → Option (List (Planar α)))
    {pre post : List (Planar α)} {old new : Planar α}
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
    (extract : Planar α → Option (List (Planar α)))
    (d : Planar α) {cs ds : List (Planar α)}
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
    (extract : Planar α → Option (List (Planar α)))
    {cs ds : List (Planar α)} (h : cs.Perm ds) :
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

/-! ### Headline: PlanarStep + EqvGen lift

Structural induction on `PlanarStep`. The `swapAtRoot` case uses
`cutListSummandsG_proj_perm`; the `recurse` case uses the inductive
hypothesis combined with `cutListSummandsG_proj_at_via_augAction`. -/

/-- Projection invariance under a single `PlanarStep`. -/
theorem cutSummandsG_proj_planarStep
    {extract : Planar α → Option (List (Planar α))}
    (hExt : ExtractInvariant extract)
    {t s : Planar α} (h : Planar.PlanarStep t s) :
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
          (fun (p : Forest (Planar α) × List (Planar α)) => (p.1, .node a p.2)) =
        (fun (pf : Forest (Nonplanar α) × Multiset (Nonplanar α)) =>
          (pf.1, Nonplanar.node a pf.2)) ∘ (projForestG (α := α)) := by
      funext p
      exact projSummand_node_factors a p
    rw [eq_fn, ← Multiset.map_map, ← Multiset.map_map, hL]
  | @recurse a pre old new post hsub ih =>
    rw [cutSummandsG_node, cutSummandsG_node,
        Multiset.map_map, Multiset.map_map]
    have h_mk : Nonplanar.mk old = Nonplanar.mk new :=
      Nonplanar.mk_eq_mk_iff.mpr (Planar.PlanarEquiv.of_step hsub)
    have h_aug : (augActionG extract old).map projForestG =
                 (augActionG extract new).map projForestG :=
      augActionG_proj_eq_of_step_data hExt h_mk ih
    have hL : (cutListSummandsG extract (pre ++ old :: post)).map projForestG =
              (cutListSummandsG extract (pre ++ new :: post)).map projForestG :=
      cutListSummandsG_proj_at_via_augAction extract h_aug
    have eq_fn :
        (projSummand (α := α)) ∘
          (fun (p : Forest (Planar α) × List (Planar α)) => (p.1, .node a p.2)) =
        (fun (pf : Forest (Nonplanar α) × Multiset (Nonplanar α)) =>
          (pf.1, Nonplanar.node a pf.2)) ∘ (projForestG (α := α)) := by
      funext p
      exact projSummand_node_factors a p
    rw [eq_fn, ← Multiset.map_map, ← Multiset.map_map, hL]

/-- Projection invariance under `PlanarEquiv`. Pure `EqvGen` lift. -/
theorem cutSummandsG_proj_planarEquiv
    {extract : Planar α → Option (List (Planar α))}
    (hExt : ExtractInvariant extract)
    {t s : Planar α} (h : Planar.PlanarEquiv t s) :
    (cutSummandsG extract t).map projSummand =
      (cutSummandsG extract s).map projSummand := by
  induction h with
  | rel _ _ hstep => exact cutSummandsG_proj_planarStep hExt hstep
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-! ### Trace specialization

The Δ^c policy `extractC (τ ∘ Nonplanar.mk)` is `ExtractInvariant`:
- For `Sum.inl _`-rooted inputs, `extractC` returns `some [traceLeaf (τ (mk t))]`.
- For `Sum.inr _`-rooted inputs, `extractC` returns `none`.

Both cases are determined by the root label and the τ value, both of
which are `PlanarEquiv`-invariant. -/

/-- The Δ^c extract policy is `ExtractInvariant`. -/
theorem extractC_mkComp_invariant (τ : Nonplanar (α ⊕ β) → β) :
    ExtractInvariant (extractC (τ ∘ Nonplanar.mk)) := by
  intro t s hmk
  -- Root labels match (planarEquiv-invariant), so the extractC branches match.
  have hlabel : t.label = s.label := by
    have heq : Planar.PlanarEquiv t s := Nonplanar.mk_eq_mk_iff.mp hmk
    exact Planar.planarEquiv_label_eq heq
  -- Destructure both trees as nodes; rewrite root labels via hlabel.
  obtain ⟨at_, cs_t⟩ := t
  obtain ⟨as, cs_s⟩ := s
  simp only [Planar.label] at hlabel
  subst hlabel
  -- Now both have root label at_. Case-split on at_.
  cases at_ with
  | inl a =>
    show (extractC (τ ∘ Nonplanar.mk) (Planar.node (Sum.inl a) cs_t)).map _ =
         (extractC (τ ∘ Nonplanar.mk) (Planar.node (Sum.inl a) cs_s)).map _
    simp only [extractC_inl, Option.map_some]
    -- Goal: some [mk (traceLeaf (τ (mk t)))] = some [mk (traceLeaf (τ (mk s)))]
    -- Reduces to: τ (mk t) = τ (mk s), which is congrArg τ hmk.
    have : (τ ∘ Nonplanar.mk) (Planar.node (Sum.inl a) cs_t) =
           (τ ∘ Nonplanar.mk) (Planar.node (Sum.inl a) cs_s) := by
      show τ (Nonplanar.mk _) = τ (Nonplanar.mk _)
      exact congrArg τ hmk
    rw [this]
  | inr b =>
    show (extractC (τ ∘ Nonplanar.mk) (Planar.node (Sum.inr b) cs_t)).map _ =
         (extractC (τ ∘ Nonplanar.mk) (Planar.node (Sum.inr b) cs_s)).map _
    simp only [extractC_inr, Option.map_none]

/-- Δ^c cut-summand-projection invariance under `PlanarEquiv`. -/
theorem cutSummandsCP_proj_planarEquiv (τ : Nonplanar (α ⊕ β) → β)
    {t s : Planar (α ⊕ β)} (h : Planar.PlanarEquiv t s) :
    (cutSummandsCP (τ ∘ Nonplanar.mk) t).map projSummand =
      (cutSummandsCP (τ ∘ Nonplanar.mk) s).map projSummand :=
  cutSummandsG_proj_planarEquiv (extractC_mkComp_invariant τ) h

end ConnesKreimer

/-! ### Descent of `cutSummandsCP` through `Nonplanar.mk` -/

/-- The Nonplanar Δ^c cut summands, descended from `cutSummandsCP` via
    `Nonplanar.lift` using the descent invariance
    `cutSummandsCP_proj_planarEquiv`. -/
noncomputable def cutSummandsCN (τ : Nonplanar (α ⊕ β) → β) :
    Nonplanar (α ⊕ β) → Multiset (Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) :=
  Nonplanar.lift
    (fun T => (ConnesKreimer.cutSummandsCP (τ ∘ Nonplanar.mk) T).map
      ConnesKreimer.projSummand)
    (fun _ _ h => ConnesKreimer.cutSummandsCP_proj_planarEquiv τ h)

@[simp] theorem cutSummandsCN_mk (τ : Nonplanar (α ⊕ β) → β) (T : Planar (α ⊕ β)) :
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
  AddMonoidAlgebra.lift R
    ((ConnesKreimer R (Nonplanar (α ⊕ β))) ⊗[R]
      (ConnesKreimer R (Nonplanar (α ⊕ β))))
    (Forest (Nonplanar (α ⊕ β))) (comulCMonoidHomN τ)

@[simp] theorem comulCAlgHomN_apply_of' (τ : Nonplanar (α ⊕ β) → β)
    (F : Forest (Nonplanar (α ⊕ β))) :
    comulCAlgHomN (R := R) τ (ConnesKreimer.of' F) = comulCForestN τ F := by
  show AddMonoidAlgebra.lift R _ _ (comulCMonoidHomN τ)
        (Finsupp.single F 1) = _
  rw [AddMonoidAlgebra.lift_single, one_smul]
  rfl

/-! ### Duality bridge: GL associativity ↔ Δ^c coassociativity

The headline of R.6+R.7. The pairing `⟨·, ·⟩` from
`GrossmanLarsonPairing.lean` realizes a non-degenerate bilinear form on
`H × H → R`. By extending to `H ⊗ H → R` via `pairing₂ x⊗y w⊗z =
pairing x w · pairing y z`, the GL product `⋆` and Δ^c are paired:
```
pairing (product x y) z = pairing₂ (x ⊗ y) (Δ^c z)
```
This identity makes GL associativity equivalent to Δ^c coassociativity.
The Δ^c coassoc theorem (`comulCN_coassoc` below) follows from GL
associativity (`GrossmanLarson.mul_assoc`) by transporting through this
duality. **TODO**: state + prove. -/

/-- The **tensor-extended pairing** `H ⊗ H →ₗ H ⊗ H →ₗ R`, defined by
    `pairing₂ (x ⊗ y) (w ⊗ z) = pairing x w * pairing y z` and extended
    bilinearly.

    Implementation: reshuffle `(x⊗y)⊗(w⊗z)` to `(x⊗w)⊗(y⊗z)` via
    `tensorTensorTensorComm`; apply `TP.map pair pair` where
    `pair = TP.lift pairing : H ⊗ H →ₗ R`; contract via `mul' R R`;
    curry the result.

    Decoration-free: works on `ConnesKreimer R (Nonplanar α)` for any `α`.
    The trace-aware `pairing_gl_eq_pairing_coproduct_C` instantiates at
    `α := α ⊕ β`. -/
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

/-- **The duality theorem**: `pairing (product x y) z = pairing₂ (x ⊗ y)
    (Δ^c z)`. The bridge that transports GL associativity to Δ^c
    coassociativity. **TODO**: proof. Uses the Foissy 2018 §4.2
    combinatorial identity relating cut summands of `z` to grafting
    sites of `x ⋆ y`. Blocked on `cutSummandsCN` being non-sorry (requires
    `cutSummandsCP_proj_planarEquiv` descent invariance lemma; parallel
    to `cutSummandsP_proj_planarEquiv` for Δ^ρ in `PruningNonplanar.lean`). -/
theorem pairing_gl_eq_pairing_coproduct_C
    (τ : Nonplanar (α ⊕ β) → β)
    (x y z : ConnesKreimer R (Nonplanar (α ⊕ β))) :
    GrossmanLarson.pairing
        (GrossmanLarson.product x y) z =
      pairing₂ (R := R)
        (x ⊗ₜ[R] y)
        (comulCAlgHomN (R := R) τ z) := by
  sorry

/-! ### Coassociativity of Δ^c on Nonplanar (via duality) -/

/-- **Coassociativity of `comulCAlgHomN`**. Proved by transporting
    `GrossmanLarson.mul_assoc` through `pairing_gl_eq_pairing_coproduct_C`
    + `pairing_nondegenerate`. **TODO**: proof. -/
theorem comulCN_coassoc (τ : Nonplanar (α ⊕ β) → β) :
    TensorProduct.assoc R
        (ConnesKreimer R (Nonplanar (α ⊕ β)))
        (ConnesKreimer R (Nonplanar (α ⊕ β)))
        (ConnesKreimer R (Nonplanar (α ⊕ β))) ∘ₗ
      (comulCAlgHomN (R := R) τ).toLinearMap.rTensor _ ∘ₗ
      (comulCAlgHomN (R := R) τ).toLinearMap =
    (comulCAlgHomN (R := R) τ).toLinearMap.lTensor _ ∘ₗ
      (comulCAlgHomN (R := R) τ).toLinearMap := by
  sorry

/-! ### Counit + Bialgebra instance (deferred)

The counit on `ConnesKreimer R (Nonplanar (α ⊕ β))` is inherited from
`ConnesKreimer.counit` (extracts the empty-forest coefficient). Together
with `comulCAlgHomN` and `comulCN_coassoc`, this would give a
`CoalgebraStruct`/`Coalgebra` and ultimately a `Bialgebra` instance.

**The `Bialgebra` / `Coalgebra` typeclass instances are NOT registered
here** — they would close over all the open `sorry`s (`cutSummandsCN`,
`comulCN_coassoc`, ...), which is the typeclass-poisoning anti-pattern
flagged by the auditor for R.5's `Semigroup`/`Monoid`. They land once
the underlying `comulCN_coassoc` is sorry-free. -/

end RootedTree
