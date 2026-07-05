/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.Coproduct.PruningNonplanar
import Linglib.Core.Algebra.RootedTree.Coproduct.TraceNonplanar

set_option autoImplicit false

/-!
# Δ^d on `ConnesKreimer R (Nonplanar (α ⊕ β))` via projection from Δ^c
[marcolli-chomsky-berwick-2025]

The **deletion variant** of the Connes-Kreimer admissible-cut coproduct,
derived from Δ^c (`Coproduct/TraceNonplanar.lean`) by stripping
trace-placeholder leaves from the right channel — MCB Lemma 1.3.10
(p. 44):

  Δ^d = (id ⊗ Π_{d,c}) ∘ Δ^c = (id ⊗ Π_{d,p}) ∘ Δ^ρ

where Π_{c,p} deletes trace-placeholder leaves and Π_{d,p} is the
binary-rebinarize step.

## In our n-ary substrate

MCB works with binary trees throughout. Their Π_{d,p} (the "rebinarize"
step) contracts degree-1 vertices to recover binary structure. In our
`Nonplanar α` substrate trees can be arbitrary n-ary, so **Π_{d,p} is
the identity**: no degree-1 smoothing needed, no rebinarization step.

Δ^d in our setting therefore reduces to just the trace-strip projection
from Δ^c:

  Δ^d := (Π_{d,c} ⊗ Π_{d,c}) ∘ Δ^c

This file constructs Π_{d,c} as an algebra hom `stripTraceAlgHom :
ConnesKreimer R (Nonplanar (α ⊕ β)) →ₐ[R] ConnesKreimer R (Nonplanar α)`
and defines `comulDN` as the composition above.

## Relationship to Δ^ρ

The Sum.inl embedding `embedInlAlgHom : ConnesKreimer R (Nonplanar α) →ₐ
ConnesKreimer R (Nonplanar (α ⊕ β))` (induced by `Sum.inl : α → α ⊕ β`)
lets us compare:

  `comulDN ∘ embedInlAlgHom = comulAlgHomN`  (the equivalence theorem)

i.e., starting from a trace-free tree, applying Δ^c then stripping
gives the same result as Δ^ρ directly. This is the n-ary specialization
of MCB's `Δ^d = (id ⊗ Π_{d,p}) ∘ Δ^ρ` (since Π_{d,p} is identity here).

## Bialgebra structure

Δ^d does **not** have a separate Bialgebra structure in this file. By
the equivalence theorem, consumers wanting a Bialgebra should compose
through `embedInlAlgHom` and use the Δ^ρ structure
(`PruningDuality.instBialgebraRho`). MCB's Lemma 1.2.12 (Δ^d weak
coassoc with distance-≤-1 multiplicity discrepancy) is specific to the
binary `Π_{d,p}` step which is identity in our setting; in our n-ary
substrate Δ^d ≡ Δ^ρ (modulo the embedding) has strict coassoc.

## Status

`[UPSTREAM]` candidate. **Sorry-free** as of MCB Phase F.1 R.9 closure:
`comulDN_embedInl_eq_comulAlgHomN` is now proven via tree-level mutual
structural induction on tree / children-list, factoring the wrapper
`bPlusLin a` out of the per-summand tensors so the head and tail
induction hypotheses apply cleanly. The left-channel half uses
`stripTraceAlgHom_comp_embedInlAlgHom` (strip inverts the Sum.inl
embedding); the right-channel trace-removal uses
`strip_cutSummandsCP_sum_eq` + `strip_cutListSummandsG_unwrap_sum_eq`.
-/

namespace RootedTree

namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α β : Type*}

/-! ## Tree-level trace-strip projection

Strip trace-placeholder subtrees (`Sum.inr`-rooted subtrees) from a
`RoseTree (α ⊕ β)` tree, yielding `Option (RoseTree α)` — the result is
`none` only if the root itself is a trace placeholder.

The strip recurses into children via `filterMap`: each child is
stripped, and `none` results are dropped. -/

/-- The children-list functor action `mapList f = List.map (RoseTree.map f)`,
    named so the node-expansion of `RoseTree.map` reads structurally below. -/
def RoseTree.mapList (f : α → β) (cs : List (RoseTree α)) : List (RoseTree β) :=
  cs.map (RoseTree.map f)

/-- `RoseTree.map` on a node, expressed through `RoseTree.mapList`. -/
theorem RoseTree.map_node_mapList (f : α → β) (a : α) (cs : List (RoseTree α)) :
    RoseTree.map f (RoseTree.node a cs) = RoseTree.node (f a) (RoseTree.mapList f cs) :=
  RoseTree.map_node f a cs

mutual

/-- Strip trace-placeholder subtrees from a tree-level tree. Returns `none`
    if the root is a trace placeholder (`Sum.inr`-labeled). -/
def RoseTree.stripTrace : RoseTree (α ⊕ β) → Option (RoseTree α)
  | .node (Sum.inr _) _ => none
  | .node (Sum.inl a) cs => some (.node a (RoseTree.stripTraceList cs))

/-- Auxiliary: strip each tree in a children list, dropping `none`s. -/
def RoseTree.stripTraceList : List (RoseTree (α ⊕ β)) → List (RoseTree α)
  | [] => []
  | c :: cs =>
    match RoseTree.stripTrace c with
    | none => RoseTree.stripTraceList cs
    | some t => t :: RoseTree.stripTraceList cs

end

@[simp] theorem RoseTree.stripTrace_inr (b : β) (cs : List (RoseTree (α ⊕ β))) :
    RoseTree.stripTrace (RoseTree.node (Sum.inr b) cs) = none := rfl

@[simp] theorem RoseTree.stripTrace_inl (a : α) (cs : List (RoseTree (α ⊕ β))) :
    RoseTree.stripTrace (RoseTree.node (Sum.inl a) cs) =
      some (.node a (RoseTree.stripTraceList cs)) := rfl

@[simp] theorem RoseTree.stripTraceList_nil :
    RoseTree.stripTraceList ([] : List (RoseTree (α ⊕ β))) = [] := rfl

/-! ## Descent to `Nonplanar`

Lift `RoseTree.stripTrace` through the quotient. The lift requires that
`stripTrace ∘ Nonplanar.mk` be well-defined modulo `Perm`, which
holds because:
* `Perm` permutes children; `stripTraceList` commutes with
  permutations up to `List.Perm` on the resulting list.
* At the `Nonplanar.mk` level, child-list order collapses, so
  Perm-related stripped trees become equal.
-/

/-- The Perm-invariant strip-then-mk composition. Used to lift
    `RoseTree.stripTrace` through the Nonplanar quotient. -/
private def stripTraceQuotient (t : RoseTree (α ⊕ β)) : Option (Nonplanar α) :=
  (RoseTree.stripTrace t).map Nonplanar.mk

/-- `RoseTree.stripTraceList` agrees with `List.filterMap RoseTree.stripTrace`
    (by structural induction on the list — both pattern-match the same
    way on the optional strip result). -/
private theorem stripTraceList_eq_filterMap (cs : List (RoseTree (α ⊕ β))) :
    RoseTree.stripTraceList cs = cs.filterMap RoseTree.stripTrace := by
  induction cs with
  | nil => rfl
  | cons head tail ih =>
    show (match RoseTree.stripTrace head with
            | none => RoseTree.stripTraceList tail
            | some t => t :: RoseTree.stripTraceList tail) =
         (head :: tail).filterMap RoseTree.stripTrace
    cases h : RoseTree.stripTrace head with
    | none => simp [List.filterMap_cons_none h, ih]
    | some t => simp [List.filterMap_cons_some h, ih]

mutual
/-- **Perm invariance** of the strip-then-mk composition. The `node` case is
    by root-label: an `inr` root strips to `none` on both sides, an `inl` root
    lifts the companion's `PermList` on the stripped children through `mk`. -/
private theorem stripTraceQuotient_perm :
    ∀ {t t' : RoseTree (α ⊕ β)}, RoseTree.Perm t t' →
      stripTraceQuotient t = stripTraceQuotient t'
  | _, _, @RoseTree.Perm.node _ a cs ds h => by
    cases a with
    | inl a' =>
      show ((RoseTree.stripTrace (RoseTree.node (Sum.inl a') cs)).map Nonplanar.mk) =
           ((RoseTree.stripTrace (RoseTree.node (Sum.inl a') ds)).map Nonplanar.mk)
      simp only [RoseTree.stripTrace_inl, Option.map_some]
      congr 1
      exact Nonplanar.mk_eq_mk_iff.mpr (RoseTree.Perm.node (stripTraceList_permList h))
    | inr b =>
      show ((RoseTree.stripTrace (RoseTree.node (Sum.inr b) cs)).map Nonplanar.mk) =
           ((RoseTree.stripTrace (RoseTree.node (Sum.inr b) ds)).map Nonplanar.mk)
      simp only [RoseTree.stripTrace_inr, Option.map_none]
  | _, _, .trans h₁ h₂ => (stripTraceQuotient_perm h₁).trans (stripTraceQuotient_perm h₂)

/-- Companion: `stripTraceList` sends `PermList`-related children to
    `PermList`-related stripped lists. `cons` case-splits on whether the
    `Perm`-related heads survive the strip (both drop, or both survive with
    `Perm`-related results via the sibling); `swap` filters through the plain
    `List.Perm`. -/
private theorem stripTraceList_permList :
    ∀ {cs ds : List (RoseTree (α ⊕ β))}, RoseTree.PermList cs ds →
      RoseTree.PermList (RoseTree.stripTraceList cs) (RoseTree.stripTraceList ds)
  | _, _, .nil => .nil
  | _, _, @RoseTree.PermList.cons _ c d cs' ds' hcd hs => by
    have hq : (RoseTree.stripTrace c).map Nonplanar.mk =
              (RoseTree.stripTrace d).map Nonplanar.mk :=
      stripTraceQuotient_perm hcd
    rw [stripTraceList_eq_filterMap, stripTraceList_eq_filterMap]
    cases hc : RoseTree.stripTrace c with
    | none =>
      have hd : RoseTree.stripTrace d = none := by
        have h2 := hq.symm; rw [hc] at h2; simpa using h2
      rw [List.filterMap_cons_none hc, List.filterMap_cons_none hd,
          ← stripTraceList_eq_filterMap, ← stripTraceList_eq_filterMap]
      exact stripTraceList_permList hs
    | some t_c =>
      cases hd : RoseTree.stripTrace d with
      | none => rw [hc, hd] at hq; simp at hq
      | some t_d =>
        rw [hc, hd] at hq
        simp only [Option.map_some, Option.some.injEq] at hq
        rw [List.filterMap_cons_some hc, List.filterMap_cons_some hd,
            ← stripTraceList_eq_filterMap, ← stripTraceList_eq_filterMap]
        exact RoseTree.PermList.cons (Nonplanar.mk_eq_mk_iff.mp hq)
          (stripTraceList_permList hs)
  | _, _, .swap c d cs => by
    rw [stripTraceList_eq_filterMap, stripTraceList_eq_filterMap]
    exact RoseTree.PermList.of_perm
      (List.Perm.filterMap RoseTree.stripTrace (List.Perm.swap c d cs))
  | _, _, .trans h₁ h₂ =>
    (stripTraceList_permList h₁).trans (stripTraceList_permList h₂)
end

/-- Strip trace-placeholder subtrees from a `Nonplanar` tree. -/
noncomputable def Nonplanar.stripTrace : Nonplanar (α ⊕ β) → Option (Nonplanar α) :=
  Quotient.lift stripTraceQuotient (fun _ _ h => stripTraceQuotient_perm h)

@[simp] theorem Nonplanar.stripTrace_mk (t : RoseTree (α ⊕ β)) :
    Nonplanar.stripTrace (Nonplanar.mk t) =
      (RoseTree.stripTrace t).map Nonplanar.mk := rfl

/-! ## Forest-level strip

Map `Nonplanar.stripTrace` over each tree in the forest, dropping the
`none` results via `Multiset.filterMap`. The result is a forest in
`Nonplanar α`. -/

/-- The additive monoid hom from forests in `Nonplanar (α ⊕ β)` to
    forests in `Nonplanar α`, given by stripping each tree componentwise
    and dropping the trace-rooted ones. -/
noncomputable def stripTraceForestAddHom :
    Forest (Nonplanar (α ⊕ β)) →+ Forest (Nonplanar α) where
  toFun F := F.filterMap Nonplanar.stripTrace
  map_zero' := Multiset.filterMap_zero _
  map_add' F G := Multiset.filterMap_add _ F G

/-! ## AlgHom lift — Π_{d,c}

The trace-strip algebra hom `Π_{d,c}` in MCB's notation. -/

/-- The **trace-strip algebra hom** `Π_{d,c}` —
    `ConnesKreimer R (Nonplanar (α ⊕ β)) →ₐ[R] ConnesKreimer R (Nonplanar α)`
    induced by `stripTraceForestAddHom` via `ConnesKreimer.mapDomainAlgHom`. -/
noncomputable def stripTraceAlgHom :
    ConnesKreimer R (Nonplanar (α ⊕ β)) →ₐ[R] ConnesKreimer R (Nonplanar α) :=
  ConnesKreimer.mapDomainAlgHom (stripTraceForestAddHom (α := α) (β := β))

@[simp] theorem stripTraceAlgHom_of' (F : Forest (Nonplanar (α ⊕ β))) :
    stripTraceAlgHom (R := R) (of' F) =
      of' (R := R) (F.filterMap Nonplanar.stripTrace) := by
  rw [stripTraceAlgHom, ConnesKreimer.mapDomainAlgHom_of']
  rfl

/-! ## Sum.inl embedding

The embedding `α → α ⊕ β` lifts componentwise to trees and forests via
`RoseTree.map` / `Nonplanar.map` / `Multiset.map`. -/

/-- Embed a `Nonplanar α` tree into `Nonplanar (α ⊕ β)` via `Sum.inl`. -/
def Nonplanar.embedInl : Nonplanar α → Nonplanar (α ⊕ β) :=
  Nonplanar.map (Sum.inl : α → α ⊕ β)

/-- Embed a forest of `Nonplanar α` trees into a forest of
    `Nonplanar (α ⊕ β)` trees, componentwise. -/
noncomputable def embedInlForestAddHom :
    Forest (Nonplanar α) →+ Forest (Nonplanar (α ⊕ β)) :=
  Multiset.mapAddMonoidHom Nonplanar.embedInl

/-- The **Sum.inl embedding algebra hom**
    `ConnesKreimer R (Nonplanar α) →ₐ[R] ConnesKreimer R (Nonplanar (α ⊕ β))`
    induced by `Nonplanar.embedInl` via `ConnesKreimer.mapDomainAlgHom`. -/
noncomputable def embedInlAlgHom :
    ConnesKreimer R (Nonplanar α) →ₐ[R] ConnesKreimer R (Nonplanar (α ⊕ β)) :=
  ConnesKreimer.mapDomainAlgHom (embedInlForestAddHom (α := α) (β := β))

@[simp] theorem embedInlAlgHom_of' (F : Forest (Nonplanar α)) :
    embedInlAlgHom (R := R) (β := β) (of' F) =
      of' (R := R) (F.map Nonplanar.embedInl) := by
  rw [embedInlAlgHom, ConnesKreimer.mapDomainAlgHom_of']
  rfl

/-! ### Strip inverts embed

`RoseTree.stripTrace (RoseTree.map Sum.inl p) = some p` — embedding via
`Sum.inl` then stripping recovers the original. Proven by mutual
structural induction on the tree-level tree / its child list. Descends to
the Nonplanar level via `Quotient.inductionOn`, and lifts to the
algebra-hom level: `stripTraceAlgHom ∘ embedInlAlgHom = id`. -/

mutual

private theorem RoseTree.stripTrace_map_inl :
    ∀ (p : RoseTree α), RoseTree.stripTrace (RoseTree.map (Sum.inl : α → α ⊕ β) p) = some p
  | .node a cs => by
    rw [RoseTree.map_node_mapList]
    show RoseTree.stripTrace (.node (Sum.inl a) (RoseTree.mapList Sum.inl cs)) = _
    rw [RoseTree.stripTrace_inl]
    congr 1
    show RoseTree.node a (RoseTree.stripTraceList (RoseTree.mapList Sum.inl cs)) =
         RoseTree.node a cs
    rw [RoseTree.stripTraceList_mapList_inl]

private theorem RoseTree.stripTraceList_mapList_inl :
    ∀ (cs : List (RoseTree α)),
      RoseTree.stripTraceList (RoseTree.mapList (Sum.inl : α → α ⊕ β) cs) = cs
  | [] => rfl
  | c :: cs => by
    show (match RoseTree.stripTrace (RoseTree.map Sum.inl c) with
           | none => RoseTree.stripTraceList (RoseTree.mapList Sum.inl cs)
           | some t => t :: RoseTree.stripTraceList (RoseTree.mapList Sum.inl cs)) =
         c :: cs
    rw [RoseTree.stripTrace_map_inl c, RoseTree.stripTraceList_mapList_inl cs]

end

theorem Nonplanar.stripTrace_embedInl (T : Nonplanar α) :
    Nonplanar.stripTrace (Nonplanar.embedInl (β := β) T) = some T := by
  refine Quotient.inductionOn T ?_
  intro p
  show Nonplanar.stripTrace (Nonplanar.map Sum.inl (Nonplanar.mk p)) = some (Nonplanar.mk p)
  rw [Nonplanar.map_mk]
  show ((RoseTree.stripTrace (RoseTree.map Sum.inl p)).map Nonplanar.mk : Option (Nonplanar α)) =
       some (Nonplanar.mk p)
  rw [RoseTree.stripTrace_map_inl]
  rfl

/-- `stripTrace ∘ embedInl = some` (as forest-level filterMap = identity).
    This is the multiset-level version of `Nonplanar.stripTrace_embedInl`. -/
theorem stripTrace_embedInl_filterMap (F : Forest (Nonplanar α)) :
    (F.map (Nonplanar.embedInl (β := β))).filterMap Nonplanar.stripTrace = F := by
  rw [Multiset.filterMap_map]
  have h : (Nonplanar.stripTrace ∘ (Nonplanar.embedInl (α := α) (β := β))) = some := by
    funext T
    exact Nonplanar.stripTrace_embedInl T
  rw [h, Multiset.filterMap_some]

/-- `stripTraceAlgHom ∘ embedInlAlgHom = id`. The strip inverts the
    Sum.inl embedding at the AlgHom level: trace-free trees survive a
    round-trip through embedding + stripping. -/
theorem stripTraceAlgHom_comp_embedInlAlgHom :
    (stripTraceAlgHom (R := R) (α := α) (β := β)).comp embedInlAlgHom =
      AlgHom.id R (ConnesKreimer R (Nonplanar α)) := by
  apply AlgHom.ext
  intro x
  show stripTraceAlgHom (embedInlAlgHom x) = x
  refine ConnesKreimer.induction_linear x ?_ ?_ ?_
  · show stripTraceAlgHom (embedInlAlgHom (0 : ConnesKreimer R (Nonplanar α))) = 0
    rw [map_zero, map_zero]
  · intro a b ha hb
    let a' : ConnesKreimer R (Nonplanar α) := a
    let b' : ConnesKreimer R (Nonplanar α) := b
    have ha' : stripTraceAlgHom (embedInlAlgHom a') = a' := ha
    have hb' : stripTraceAlgHom (embedInlAlgHom b') = b' := hb
    show stripTraceAlgHom (embedInlAlgHom (a' + b')) = a' + b'
    rw [map_add, map_add, ha', hb']
  · intro F r
    show stripTraceAlgHom (embedInlAlgHom (ConnesKreimer.single F r)) = ConnesKreimer.single F r
    have hsingle : (ConnesKreimer.single F r : ConnesKreimer R (Nonplanar α)) =
        r • (of' (R := R) F : ConnesKreimer R (Nonplanar α)) :=
      ConnesKreimer.smul_single_one F r
    rw [hsingle, map_smul, map_smul, embedInlAlgHom_of', stripTraceAlgHom_of',
        stripTrace_embedInl_filterMap]

/-! ## Δ^d definition

`comulDN := (Π_{d,c} ⊗ Π_{d,c}) ∘ Δ^c` — MCB Lemma 1.3.10 by
construction. Target carrier is `Nonplanar α` (trace-stripped). -/

/-- The **Δ^d coproduct on `ConnesKreimer R (Nonplanar (α ⊕ β))`** as an
    algebra hom, with trace-stripping applied to both channels of
    `comulCAlgHomN τ`. -/
noncomputable def comulDN (τ : Nonplanar (α ⊕ β) → β) :
    ConnesKreimer R (Nonplanar (α ⊕ β)) →ₐ[R]
      ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) :=
  (Algebra.TensorProduct.map (stripTraceAlgHom (R := R) (α := α) (β := β))
    stripTraceAlgHom).comp (comulCAlgHomN τ)

/-- **MCB Lemma 1.3.10** (definitional in our construction):
    `Δ^d = (Π_{d,c} ⊗ Π_{d,c}) ∘ Δ^c`. -/
theorem comulDN_eq_strip_comp_comulCAlgHomN (τ : Nonplanar (α ⊕ β) → β) :
    comulDN (R := R) τ =
      (Algebra.TensorProduct.map (stripTraceAlgHom (R := R) (α := α) (β := β))
        stripTraceAlgHom).comp (comulCAlgHomN τ) := rfl

/-! ## Equivalence with Δ^ρ via embedding

The substantive MCB-correspondence: starting from a trace-free
`T : Nonplanar α` and embedding into `Nonplanar (α ⊕ β)` via `Sum.inl`,
applying `comulDN` (= Δ^c then strip) gives the same result as applying
`comulAlgHomN` (Δ^ρ) directly.

In MCB's binary substrate this requires the additional `Π_{d,p}`
rebinarize step on the right channel; in our n-ary substrate, the
strip is enough. -/

/-- `stripTraceAlgHom` applied to `ofTree (embedInl T)` returns `ofTree T`.
    Forest-level lift of `Nonplanar.stripTrace_embedInl`. -/
private theorem stripTraceAlgHom_ofTree_embedInl
    (T : Nonplanar α) :
    stripTraceAlgHom (R := R) (β := β)
        (ofTree (Nonplanar.embedInl T)) =
      ofTree T := by
  show stripTraceAlgHom (of' ({Nonplanar.embedInl T} : Forest (Nonplanar (α ⊕ β)))) =
       of' ({T} : Forest (Nonplanar α))
  rw [stripTraceAlgHom_of']
  congr 1
  rw [show ({Nonplanar.embedInl T} : Forest (Nonplanar (α ⊕ β))) =
        ({T} : Forest (Nonplanar α)).map Nonplanar.embedInl from
      (Multiset.map_singleton _ _).symm]
  exact stripTrace_embedInl_filterMap _

/-- `RoseTree.stripTraceList` distributes over list concatenation.
    Follows from `stripTraceList_eq_filterMap` + `List.filterMap_append`. -/
private theorem stripTraceList_append
    (l1 l2 : List (RoseTree (α ⊕ β))) :
    RoseTree.stripTraceList (l1 ++ l2) =
      RoseTree.stripTraceList l1 ++ RoseTree.stripTraceList l2 := by
  rw [stripTraceList_eq_filterMap, stripTraceList_eq_filterMap,
      stripTraceList_eq_filterMap, List.filterMap_append]

/-! ### RoseTree-level cut-tensor builders

The tensors that arise when applying `(S ⊗ S)` to `comulCTreeN`'s cut
summands on the LHS, and to `comulTreeN`'s cut summands on the RHS,
both viewed at the `Nonplanar α` level. -/

/-- LHS tensor builder: a Δ^c cut summand pair `(F_C, T_C)` lifted to
    `Nonplanar α ⊗ Nonplanar α` via `stripTraceAlgHom` on both channels. -/
private noncomputable def cutTensorC_planar
    (p : Forest (RoseTree (α ⊕ β)) × RoseTree (α ⊕ β)) :
    ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) :=
  stripTraceAlgHom (of' (p.1.map Nonplanar.mk)) ⊗ₜ[R]
    stripTraceAlgHom (ofTree (Nonplanar.mk p.2))

/-- RHS tensor builder: a Δ^ρ cut summand pair `(F, T')` directly at
    the `Nonplanar α` level. -/
private noncomputable def cutTensorP_planar
    (p : Forest (RoseTree α) × RoseTree α) :
    ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) :=
  (of' (p.1.map Nonplanar.mk) : ConnesKreimer R (Nonplanar α)) ⊗ₜ[R]
    ofTree (Nonplanar.mk p.2)

/-- Unwrapped LHS tensor builder for **list-level** cut summands:
    `(F, l)` is mapped to a tensor where the right channel is `of'`
    applied to the forest of stripped survivors (no `.node a`-wrapping). -/
private noncomputable def cutTensorC_planar_unwrap
    (p : Forest (RoseTree (α ⊕ β)) × List (RoseTree (α ⊕ β))) :
    ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) :=
  stripTraceAlgHom (of' (p.1.map Nonplanar.mk)) ⊗ₜ[R]
    (of' (Multiset.ofList ((RoseTree.stripTraceList p.2).map Nonplanar.mk)) :
      ConnesKreimer R (Nonplanar α))

/-- Unwrapped RHS tensor builder for **list-level** cut summands. -/
private noncomputable def cutTensorP_planar_unwrap
    (p : Forest (RoseTree α) × List (RoseTree α)) :
    ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) :=
  (of' (p.1.map Nonplanar.mk) : ConnesKreimer R (Nonplanar α)) ⊗ₜ[R]
    (of' (Multiset.ofList (p.2.map Nonplanar.mk)) :
      ConnesKreimer R (Nonplanar α))

/-- Per-tree-augmentation tensor builder for `augActionP`: handles the
    `Option`-shaped remainder by mapping `none ↦ 1` and `some r ↦ ofTree r`. -/
private noncomputable def cutTensorP_augAction
    (p : Forest (RoseTree α) × Option (RoseTree α)) :
    ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α) :=
  (of' (p.1.map Nonplanar.mk) : ConnesKreimer R (Nonplanar α)) ⊗ₜ[R]
    (match p.2 with
     | none => (1 : ConnesKreimer R (Nonplanar α))
     | some r => ofTree (Nonplanar.mk r))

/-! ### Multiplicativity of cut-tensor builders under `combine`

Both unwrapped builders factor through the cons combiners as products. -/

/-- `cutTensorC_planar_unwrap` is multiplicative under `combine_G`. -/
private theorem cutTensorC_planar_unwrap_combine_G
    (p : (Forest (RoseTree (α ⊕ β)) × List (RoseTree (α ⊕ β))) ×
         (Forest (RoseTree (α ⊕ β)) × List (RoseTree (α ⊕ β)))) :
    cutTensorC_planar_unwrap (R := R) (p.1.1 + p.2.1, p.1.2 ++ p.2.2) =
      cutTensorC_planar_unwrap (R := R) p.1 *
        cutTensorC_planar_unwrap (R := R) p.2 := by
  unfold cutTensorC_planar_unwrap
  obtain ⟨⟨F1, l1⟩, ⟨F2, l2⟩⟩ := p
  show (stripTraceAlgHom (of' ((F1 + F2).map Nonplanar.mk))) ⊗ₜ[R]
        (of' (Multiset.ofList ((RoseTree.stripTraceList (l1 ++ l2)).map Nonplanar.mk))
          : ConnesKreimer R (Nonplanar α))
       = (stripTraceAlgHom (of' (F1.map Nonplanar.mk)) ⊗ₜ[R]
          (of' (Multiset.ofList ((RoseTree.stripTraceList l1).map Nonplanar.mk))
            : ConnesKreimer R (Nonplanar α))) *
         (stripTraceAlgHom (of' (F2.map Nonplanar.mk)) ⊗ₜ[R]
          (of' (Multiset.ofList ((RoseTree.stripTraceList l2).map Nonplanar.mk))
            : ConnesKreimer R (Nonplanar α)))
  rw [Algebra.TensorProduct.tmul_mul_tmul]
  rw [Multiset.map_add, of'_add, map_mul]
  rw [stripTraceList_append, List.map_append]
  rw [show (((RoseTree.stripTraceList l1).map Nonplanar.mk ++
              (RoseTree.stripTraceList l2).map Nonplanar.mk : List (Nonplanar α)) :
            Multiset (Nonplanar α)) =
          (Multiset.ofList ((RoseTree.stripTraceList l1).map Nonplanar.mk) +
            Multiset.ofList ((RoseTree.stripTraceList l2).map Nonplanar.mk)) from
        (Multiset.coe_add _ _).symm]
  rw [of'_add]

/-- Named version of the combine_P function (extracted to avoid Lean's
    "inline match generates fresh matchers" issue when this is reused
    across proofs via rewrite). -/
private def combineP_fn :
    (Forest (RoseTree α) × Option (RoseTree α)) ×
        (Forest (RoseTree α) × List (RoseTree α)) →
      Forest (RoseTree α) × List (RoseTree α) :=
  fun p => match p.1.2 with
    | none => (p.1.1 + p.2.1, p.2.2)
    | some r => (p.1.1 + p.2.1, r :: p.2.2)

theorem cutListSummandsP_cons' (t : RoseTree α) (ts : List (RoseTree α)) :
    cutListSummandsP (t :: ts) =
      (augActionP t ×ˢ cutListSummandsP ts).map combineP_fn := by
  rw [cutListSummandsP_cons]; rfl

/-- `cutTensorP_planar_unwrap` factors via `cutTensorP_augAction` and
    `cutTensorP_planar_unwrap` under `combineP_fn`. -/
private theorem cutTensorP_planar_unwrap_combine_P
    (p : (Forest (RoseTree α) × Option (RoseTree α)) ×
         (Forest (RoseTree α) × List (RoseTree α))) :
    cutTensorP_planar_unwrap (R := R) (combineP_fn p) =
      cutTensorP_augAction (R := R) p.1 *
        cutTensorP_planar_unwrap (R := R) p.2 := by
  show cutTensorP_planar_unwrap (R := R)
        (match p.1.2 with
         | none => (p.1.1 + p.2.1, p.2.2)
         | some r => (p.1.1 + p.2.1, r :: p.2.2)) =
      cutTensorP_augAction (R := R) p.1 *
        cutTensorP_planar_unwrap (R := R) p.2
  unfold cutTensorP_planar_unwrap cutTensorP_augAction
  obtain ⟨⟨F1, opt⟩, ⟨F2, l2⟩⟩ := p
  cases opt with
  | none =>
    show ((of' ((F1 + F2).map Nonplanar.mk) :
            ConnesKreimer R (Nonplanar α)) ⊗ₜ[R]
          (of' (Multiset.ofList (l2.map Nonplanar.mk))
            : ConnesKreimer R (Nonplanar α)))
       = ((of' (F1.map Nonplanar.mk) : ConnesKreimer R (Nonplanar α)) ⊗ₜ[R]
          (1 : ConnesKreimer R (Nonplanar α))) *
         ((of' (F2.map Nonplanar.mk) : ConnesKreimer R (Nonplanar α)) ⊗ₜ[R]
          (of' (Multiset.ofList (l2.map Nonplanar.mk))
            : ConnesKreimer R (Nonplanar α)))
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Multiset.map_add, of'_add]
  | some r =>
    show ((of' ((F1 + F2).map Nonplanar.mk) :
            ConnesKreimer R (Nonplanar α)) ⊗ₜ[R]
          (of' (Multiset.ofList ((r :: l2).map Nonplanar.mk))
            : ConnesKreimer R (Nonplanar α)))
       = ((of' (F1.map Nonplanar.mk) : ConnesKreimer R (Nonplanar α)) ⊗ₜ[R]
          ofTree (Nonplanar.mk r)) *
         ((of' (F2.map Nonplanar.mk) : ConnesKreimer R (Nonplanar α)) ⊗ₜ[R]
          (of' (Multiset.ofList (l2.map Nonplanar.mk))
            : ConnesKreimer R (Nonplanar α)))
    rw [Algebra.TensorProduct.tmul_mul_tmul, Multiset.map_add, of'_add,
        List.map_cons,
        show ((Nonplanar.mk r :: l2.map Nonplanar.mk : List (Nonplanar α)) :
              Multiset (Nonplanar α)) =
              (Nonplanar.mk r ::ₘ (Multiset.ofList (l2.map Nonplanar.mk))) from
          (Multiset.cons_coe _ _).symm,
        ← Multiset.singleton_add, of'_add, of'_singleton]

/-! ### Sum-of-product over cartesian product

Standard distributivity: when the integrand factors as `f a * g b` over
`s ×ˢ t`, the sum equals `(s.map f).sum * (t.map g).sum`. -/

/-- Sum of `f a * g b` over `s ×ˢ t` factors as a product of sums. -/
private theorem sum_map_product_mul
    {A : Type*} [NonUnitalNonAssocSemiring A]
    {γ δ : Type*} (s : Multiset γ) (t : Multiset δ)
    (f : γ → A) (g : δ → A) :
    ((s ×ˢ t).map (fun p => f p.1 * g p.2)).sum =
      ((s.map f).sum) * ((t.map g).sum) := by
  rw [show ((s ×ˢ t).map (fun p => f p.1 * g p.2)) =
        s.bind (fun a => t.map (fun b => f a * g b)) from by
    show (s.bind (fun a => t.map (Prod.mk a))).map _ = _
    rw [Multiset.map_bind]
    apply Multiset.bind_congr
    intro a _
    rw [Multiset.map_map]
    rfl]
  rw [Multiset.sum_bind]
  -- Goal: (s.map (fun a => (t.map (fun b => f a * g b)).sum)).sum =
  --       (s.map f).sum * (t.map g).sum
  rw [show (s.map (fun a => (t.map (fun b => f a * g b)).sum)) =
        s.map (fun a => f a * (t.map g).sum) from
      Multiset.map_congr rfl (fun a _ => Multiset.sum_map_mul_left)]
  exact Multiset.sum_map_mul_right

/-! ### Universal identity: unwrapped tensor for singleton-remainder

For any `t_c : RoseTree (α ⊕ β)` (regardless of root), the unwrapped
cutTensor for `(F, [t_c])` equals `cutTensorC_planar (F, t_c)`. This
holds for both `Sum.inl`-rooted `t_c` (where strip succeeds, yielding
the stripped tree) and `Sum.inr`-rooted `t_c` (where both sides reduce
to `... ⊗ 1`). -/

private theorem cutTensorC_planar_unwrap_singleton
    (F : Forest (RoseTree (α ⊕ β))) (t_c : RoseTree (α ⊕ β)) :
    cutTensorC_planar_unwrap (R := R) (F, [t_c]) =
      cutTensorC_planar (R := R) (F, t_c) := by
  unfold cutTensorC_planar_unwrap cutTensorC_planar
  congr 1
  -- Right channel: of'(Multiset.ofList (stripTraceList [t_c] .map mk)) = S(ofTree (mk t_c))
  show (of' (Multiset.ofList ((RoseTree.stripTraceList [t_c]).map Nonplanar.mk))
          : ConnesKreimer R (Nonplanar α))
       = stripTraceAlgHom (ofTree (Nonplanar.mk t_c))
  show (of' (Multiset.ofList ((RoseTree.stripTraceList [t_c]).map Nonplanar.mk))
          : ConnesKreimer R (Nonplanar α))
       = stripTraceAlgHom (of' ({Nonplanar.mk t_c} : Forest (Nonplanar (α ⊕ β))))
  rw [stripTraceAlgHom_of']
  -- Case-split on RoseTree.stripTrace t_c.
  cases h : RoseTree.stripTrace t_c with
  | none =>
    show (of' (Multiset.ofList ((RoseTree.stripTraceList [t_c]).map Nonplanar.mk))
          : ConnesKreimer R (Nonplanar α))
         = of' (({Nonplanar.mk t_c} : Forest (Nonplanar (α ⊕ β))).filterMap
            Nonplanar.stripTrace)
    rw [show RoseTree.stripTraceList [t_c] = [] from by
      show (match RoseTree.stripTrace t_c with
              | none => RoseTree.stripTraceList []
              | some t => t :: RoseTree.stripTraceList []) = []
      rw [h]; rfl]
    rw [show ({Nonplanar.mk t_c} : Forest (Nonplanar (α ⊕ β))).filterMap
              Nonplanar.stripTrace = 0 from by
      rw [show ({Nonplanar.mk t_c} : Forest (Nonplanar (α ⊕ β))) =
            Nonplanar.mk t_c ::ₘ 0 from rfl,
          Multiset.filterMap_cons]
      show ((Nonplanar.stripTrace (Nonplanar.mk t_c)).map (fun x => ({x} : Multiset
              (Nonplanar α)))).getD 0 + (0 : Multiset (Nonplanar (α ⊕ β))).filterMap
              Nonplanar.stripTrace = 0
      rw [Multiset.filterMap_zero]
      show ((Nonplanar.stripTrace (Nonplanar.mk t_c)).map (fun x => ({x} : Multiset
              (Nonplanar α)))).getD 0 + 0 = 0
      rw [add_zero]
      show ((Nonplanar.stripTrace (Nonplanar.mk t_c)).map (fun x => ({x} : Multiset
              (Nonplanar α)))).getD 0 = 0
      show (((RoseTree.stripTrace t_c).map Nonplanar.mk).map (fun x => ({x} : Multiset
              (Nonplanar α)))).getD 0 = 0
      rw [h]
      rfl]
    rfl
  | some t' =>
    show (of' (Multiset.ofList ((RoseTree.stripTraceList [t_c]).map Nonplanar.mk))
          : ConnesKreimer R (Nonplanar α))
         = of' (({Nonplanar.mk t_c} : Forest (Nonplanar (α ⊕ β))).filterMap
            Nonplanar.stripTrace)
    rw [show RoseTree.stripTraceList [t_c] = [t'] from by
      show (match RoseTree.stripTrace t_c with
              | none => RoseTree.stripTraceList []
              | some t => t :: RoseTree.stripTraceList []) = [t']
      rw [h]; rfl]
    rw [show ({Nonplanar.mk t_c} : Forest (Nonplanar (α ⊕ β))).filterMap
              Nonplanar.stripTrace = ({Nonplanar.mk t'} : Multiset (Nonplanar α)) from by
      rw [show ({Nonplanar.mk t_c} : Forest (Nonplanar (α ⊕ β))) =
            Nonplanar.mk t_c ::ₘ 0 from rfl,
          Multiset.filterMap_cons, Multiset.filterMap_zero]
      show ((Nonplanar.stripTrace (Nonplanar.mk t_c)).map (fun x => ({x} : Multiset
              (Nonplanar α)))).getD 0 + 0 = {Nonplanar.mk t'}
      rw [add_zero]
      show (((RoseTree.stripTrace t_c).map Nonplanar.mk).map (fun x => ({x} : Multiset
              (Nonplanar α)))).getD 0 = {Nonplanar.mk t'}
      rw [h]
      rfl]
    rfl

/-! ### Mutual tree-level lemmas

The tree-level lemma uses the unwrapped list-level lemma (applied to
children of the tree, with the root wrapped via `bPlusLin` on the right
channel). The list-level lemma's cons case uses the tree-level lemma
for the head child (via mutual call) + the unwrapped list-level lemma
for the tail (via direct call). -/

mutual

/-- **Tree-level**: sum of Δ^c-stripped cut tensors of `embed t` equals
    sum of Δ^ρ cut tensors of `t`. -/
private theorem strip_cutSummandsCP_sum_eq
    (τ : Nonplanar (α ⊕ β) → β) :
    ∀ (t : RoseTree α),
      ((cutSummandsCP (τ ∘ Nonplanar.mk) (RoseTree.map Sum.inl t)).map
        (cutTensorC_planar (R := R))).sum
      = ((cutSummandsP t).map (cutTensorP_planar (R := R))).sum
  | .node a cs => by
    rw [RoseTree.map_node_mapList]
    show ((cutSummandsCP (τ ∘ Nonplanar.mk)
              (RoseTree.node (Sum.inl a) (RoseTree.mapList Sum.inl cs))).map
              (cutTensorC_planar (R := R))).sum
       = ((cutSummandsP (RoseTree.node a cs)).map (cutTensorP_planar (R := R))).sum
    rw [cutSummandsCP_node, cutSummandsP_node,
        Multiset.map_map, Multiset.map_map]
    -- The wrapped tensor builder `(p ↦ cutTensorC_planar (p.1, .node (Sum.inl a) p.2))`
    -- factors as `(TP.map id (bPlusLin a)) ∘ cutTensorC_planar_unwrap`.
    -- Convert both LHS / RHS maps to (lTensor (bPlusLin a)) ∘ unwrap.
    have hLHS_factor :
        ∀ (p : Forest (RoseTree (α ⊕ β)) × List (RoseTree (α ⊕ β))),
          cutTensorC_planar (R := R) (p.1, RoseTree.node (Sum.inl a) p.2) =
            (LinearMap.lTensor (ConnesKreimer R (Nonplanar α))
                (bPlusLin (R := R) a)) (cutTensorC_planar_unwrap (R := R) p) := by
      intro p
      unfold cutTensorC_planar cutTensorC_planar_unwrap
      rw [LinearMap.lTensor_tmul, bPlusLin_of']
      congr 1
      show stripTraceAlgHom (ofTree (Nonplanar.mk (RoseTree.node (Sum.inl a) p.2))) =
            ofTree (Nonplanar.node a (Multiset.ofList ((RoseTree.stripTraceList p.2).map
              Nonplanar.mk)))
      show stripTraceAlgHom (of' ({Nonplanar.mk (RoseTree.node (Sum.inl a) p.2)}
            : Forest (Nonplanar (α ⊕ β)))) = _
      rw [stripTraceAlgHom_of']
      rw [show ({Nonplanar.mk (RoseTree.node (Sum.inl a) p.2)}
                : Forest (Nonplanar (α ⊕ β))).filterMap Nonplanar.stripTrace =
                ({Nonplanar.mk (RoseTree.node a (RoseTree.stripTraceList p.2))}
                : Forest (Nonplanar α)) from by
        rw [show ({Nonplanar.mk (RoseTree.node (Sum.inl a) p.2)} : Forest
              (Nonplanar (α ⊕ β))) = Nonplanar.mk (RoseTree.node (Sum.inl a) p.2) ::ₘ 0
              from rfl,
            Multiset.filterMap_cons, Multiset.filterMap_zero, add_zero]
        show ((Nonplanar.stripTrace (Nonplanar.mk (RoseTree.node (Sum.inl a) p.2))).map
                (fun x => ({x} : Multiset (Nonplanar α)))).getD 0 =
              {Nonplanar.mk (RoseTree.node a (RoseTree.stripTraceList p.2))}
        show (((RoseTree.stripTrace (RoseTree.node (Sum.inl a) p.2)).map Nonplanar.mk).map
                (fun x => ({x} : Multiset (Nonplanar α)))).getD 0 =
              {Nonplanar.mk (RoseTree.node a (RoseTree.stripTraceList p.2))}
        rw [RoseTree.stripTrace_inl]
        rfl]
      rw [of'_singleton]
      congr 1
      exact (Nonplanar.node_mk_tree_list a _).symm
    have hRHS_factor :
        ∀ (p : Forest (RoseTree α) × List (RoseTree α)),
          cutTensorP_planar (R := R) (p.1, RoseTree.node a p.2) =
            (LinearMap.lTensor (ConnesKreimer R (Nonplanar α))
                (bPlusLin (R := R) a)) (cutTensorP_planar_unwrap (R := R) p) := by
      intro p
      unfold cutTensorP_planar cutTensorP_planar_unwrap
      rw [LinearMap.lTensor_tmul, bPlusLin_of']
      congr 1
      show ofTree (Nonplanar.mk (RoseTree.node a p.2)) =
            ofTree (Nonplanar.node a (Multiset.ofList (p.2.map Nonplanar.mk)))
      congr 1
      exact (Nonplanar.node_mk_tree_list a _).symm
    rw [show (Multiset.map ((cutTensorC_planar (R := R)) ∘
              (fun p : Forest (RoseTree (α ⊕ β)) × List (RoseTree (α ⊕ β)) =>
                (p.1, RoseTree.node (Sum.inl a) p.2)))
              (cutListSummandsG (extractC (τ ∘ Nonplanar.mk))
                  (RoseTree.mapList Sum.inl cs)))
            = (Multiset.map ((LinearMap.lTensor (ConnesKreimer R (Nonplanar α))
                  (bPlusLin (R := R) a)) ∘ (cutTensorC_planar_unwrap (R := R)))
                (cutListSummandsG (extractC (τ ∘ Nonplanar.mk))
                  (RoseTree.mapList Sum.inl cs))) from
            Multiset.map_congr rfl (fun p _ => hLHS_factor p)]
    rw [show (Multiset.map ((cutTensorP_planar (R := R)) ∘
              (fun p : Forest (RoseTree α) × List (RoseTree α) =>
                (p.1, RoseTree.node a p.2)))
              (cutListSummandsP cs))
            = (Multiset.map ((LinearMap.lTensor (ConnesKreimer R (Nonplanar α))
                  (bPlusLin (R := R) a)) ∘ (cutTensorP_planar_unwrap (R := R)))
                (cutListSummandsP cs)) from
            Multiset.map_congr rfl (fun p _ => hRHS_factor p)]
    rw [← Multiset.map_map, ← Multiset.map_map,
        ← map_multiset_sum (LinearMap.lTensor (ConnesKreimer R (Nonplanar α))
          (bPlusLin (R := R) a)),
        ← map_multiset_sum (LinearMap.lTensor (ConnesKreimer R (Nonplanar α))
          (bPlusLin (R := R) a))]
    -- Apply unwrapped list IH.
    congr 1
    exact strip_cutListSummandsG_unwrap_sum_eq τ cs

/-- **List-level (unwrapped)**: sum of unwrapped Δ^c-stripped tensors of
    cut summands of `(embed cs)` equals sum of unwrapped Δ^ρ tensors of
    cut summands of `cs`. The tree-level wrapper `bPlusLin a` is factored
    out, so this lemma is parameter-free in `a`. -/
private theorem strip_cutListSummandsG_unwrap_sum_eq
    (τ : Nonplanar (α ⊕ β) → β) :
    ∀ (cs : List (RoseTree α)),
      ((cutListSummandsG (extractC (τ ∘ Nonplanar.mk))
          (RoseTree.mapList Sum.inl cs)).map
        (cutTensorC_planar_unwrap (R := R))).sum
      = ((cutListSummandsP cs).map (cutTensorP_planar_unwrap (R := R))).sum
  | [] => by
    show ((cutListSummandsG (extractC (τ ∘ Nonplanar.mk))
            (RoseTree.mapList Sum.inl ([] : List (RoseTree α)))).map _).sum
       = ((cutListSummandsP ([] : List (RoseTree α))).map _).sum
    rw [show RoseTree.mapList Sum.inl ([] : List (RoseTree α)) = [] from rfl,
        cutListSummandsG_nil, cutListSummandsP_nil,
        Multiset.map_singleton, Multiset.map_singleton,
        Multiset.sum_singleton, Multiset.sum_singleton]
    show cutTensorC_planar_unwrap (R := R)
            ((0 : Forest (RoseTree (α ⊕ β))), ([] : List (RoseTree (α ⊕ β))))
       = cutTensorP_planar_unwrap (R := R)
            ((0 : Forest (RoseTree α)), ([] : List (RoseTree α)))
    unfold cutTensorC_planar_unwrap cutTensorP_planar_unwrap
    simp only [Multiset.map_zero, of'_zero, map_one, List.map_nil,
               Multiset.coe_nil]
    show (1 : ConnesKreimer R (Nonplanar α)) ⊗ₜ[R]
            (of' (0 : Forest (Nonplanar α)) : ConnesKreimer R (Nonplanar α))
       = (1 : ConnesKreimer R (Nonplanar α)) ⊗ₜ[R]
            (of' (0 : Forest (Nonplanar α)) : ConnesKreimer R (Nonplanar α))
    rfl
  | c :: cs' => by
    show ((cutListSummandsG (extractC (τ ∘ Nonplanar.mk))
            (RoseTree.mapList Sum.inl (c :: cs'))).map
            (cutTensorC_planar_unwrap (R := R))).sum
       = ((cutListSummandsP (c :: cs')).map
            (cutTensorP_planar_unwrap (R := R))).sum
    -- Unfold cons (using cutListSummandsP_cons' with named combine_P_fn).
    rw [show RoseTree.mapList Sum.inl (c :: cs') =
          RoseTree.map Sum.inl c :: RoseTree.mapList Sum.inl cs' from rfl,
        cutListSummandsG_cons, cutListSummandsP_cons']
    -- LHS: the integrand factors as gC c * gC tail via combine_G multiplicativity.
    rw [show (Multiset.map (cutTensorC_planar_unwrap (R := R))
              ((Multiset.map (fun (p : (Forest (RoseTree (α ⊕ β)) × List (RoseTree (α ⊕ β))) ×
                  (Forest (RoseTree (α ⊕ β)) × List (RoseTree (α ⊕ β)))) =>
                  (p.1.1 + p.2.1, p.1.2 ++ p.2.2))
                ((augActionG (extractC (τ ∘ Nonplanar.mk)) (RoseTree.map Sum.inl c)) ×ˢ
                  (cutListSummandsG (extractC (τ ∘ Nonplanar.mk))
                    (RoseTree.mapList Sum.inl cs')))))).sum =
            (Multiset.map
              (fun p => cutTensorC_planar_unwrap (R := R) p.1 *
                        cutTensorC_planar_unwrap (R := R) p.2)
              ((augActionG (extractC (τ ∘ Nonplanar.mk)) (RoseTree.map Sum.inl c)) ×ˢ
                (cutListSummandsG (extractC (τ ∘ Nonplanar.mk))
                  (RoseTree.mapList Sum.inl cs')))).sum from by
      congr 1
      rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro p _
      exact cutTensorC_planar_unwrap_combine_G p]
    rw [sum_map_product_mul]
    -- RHS: simplify by composing maps and using cutTensorP_planar_unwrap_combine_P.
    simp only [Multiset.map_map]
    rw [show ((cutTensorP_planar_unwrap (R := R)) ∘ (combineP_fn : _ → _)) =
            (fun p => cutTensorP_augAction (R := R) p.1 *
                      cutTensorP_planar_unwrap (R := R) p.2) from by
      funext p
      exact cutTensorP_planar_unwrap_combine_P p]
    rw [sum_map_product_mul]
    -- Now both sides are products of sums.
    -- Tail equality via mutual IH.
    have ih_tail :
        ((cutListSummandsG (extractC (τ ∘ Nonplanar.mk))
            (RoseTree.mapList Sum.inl cs')).map
          (cutTensorC_planar_unwrap (R := R))).sum
        = ((cutListSummandsP cs').map (cutTensorP_planar_unwrap (R := R))).sum :=
      strip_cutListSummandsG_unwrap_sum_eq τ cs'
    -- Head equality via mutual IH (per-tree on c). Convert to cutSummandsG-form
    -- so it matches the goal after augActionG unfolds via cutSummandsG.
    have ih_head_cp :
        ((cutSummandsCP (τ ∘ Nonplanar.mk) (RoseTree.map Sum.inl c)).map
          (cutTensorC_planar (R := R))).sum
        = ((cutSummandsP c).map (cutTensorP_planar (R := R))).sum :=
      strip_cutSummandsCP_sum_eq τ c
    have ih_head :
        ((cutSummandsG (extractC (τ ∘ Nonplanar.mk)) (RoseTree.map Sum.inl c)).map
          (cutTensorC_planar (R := R))).sum
        = ((cutSummandsP c).map (cutTensorP_planar (R := R))).sum := by
      rwa [cutSummandsCP_def] at ih_head_cp
    -- Reduce head: ((augActionG ...).map gC_unwrap).sum = ofTree (mk c) ⊗ 1 + IH-LHS;
    -- ((augActionP c).map gP_augAction).sum = ofTree (mk c) ⊗ 1 + IH-RHS.
    have hextract : extractC (τ ∘ Nonplanar.mk) (RoseTree.map Sum.inl c) =
        some [traceLeaf ((τ ∘ Nonplanar.mk) (RoseTree.map Sum.inl c))] := by
      obtain ⟨a_c, cs_c⟩ := c
      rfl
    rw [augActionG_eq_some _ _ _ hextract, augActionP_eq,
        Multiset.map_cons, Multiset.sum_cons,
        Multiset.map_cons, Multiset.sum_cons,
        Multiset.map_map, Multiset.map_map]
    -- LHS-head reduces to (ofTree (mk c) ⊗ 1) + tree-IH-LHS via cutTensorC_planar_unwrap_singleton.
    rw [show (cutTensorC_planar_unwrap (R := R)
              ((({RoseTree.map Sum.inl c} : Forest (RoseTree (α ⊕ β))),
                [traceLeaf ((τ ∘ Nonplanar.mk) (RoseTree.map Sum.inl c))]))) =
          (ofTree (Nonplanar.mk c) ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α))
            : ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) from by
      unfold cutTensorC_planar_unwrap
      show stripTraceAlgHom (of' (({RoseTree.map Sum.inl c} :
              Forest (RoseTree (α ⊕ β))).map Nonplanar.mk)) ⊗ₜ[R]
            (of' (Multiset.ofList ((RoseTree.stripTraceList
              [traceLeaf ((τ ∘ Nonplanar.mk) (RoseTree.map Sum.inl c))]).map Nonplanar.mk))
              : ConnesKreimer R (Nonplanar α))
          = ofTree (Nonplanar.mk c) ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α))
      rw [show RoseTree.stripTraceList
            [traceLeaf ((τ ∘ Nonplanar.mk) (RoseTree.map Sum.inl c))] =
            ([] : List (RoseTree α)) from by
        show RoseTree.stripTraceList
              [RoseTree.node (Sum.inr ((τ ∘ Nonplanar.mk) (RoseTree.map Sum.inl c)))
                ([] : List (RoseTree (α ⊕ β)))] =
              ([] : List (RoseTree α))
        rfl]
      simp only [List.map_nil, Multiset.coe_nil, of'_zero,
                 Multiset.map_singleton]
      congr 1
      show stripTraceAlgHom (ofTree (Nonplanar.mk (RoseTree.map Sum.inl c))) =
            ofTree (Nonplanar.mk c)
      show stripTraceAlgHom (ofTree (Nonplanar.embedInl (Nonplanar.mk c))) =
            ofTree (Nonplanar.mk c)
      exact stripTraceAlgHom_ofTree_embedInl _]
    rw [show ((cutTensorC_planar_unwrap (R := R)) ∘
              (fun p : Forest (RoseTree (α ⊕ β)) × RoseTree (α ⊕ β) =>
                (p.1, [p.2]))) = (cutTensorC_planar (R := R)) from by
      funext p
      exact cutTensorC_planar_unwrap_singleton p.1 p.2]
    -- RHS: (cutTensorP_augAction ({c}, none)) = ofTree (mk c) ⊗ 1.
    rw [show cutTensorP_augAction (R := R)
          ((({c} : Forest (RoseTree α)), Option.none)) =
          (ofTree (Nonplanar.mk c) ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α))
            : ConnesKreimer R (Nonplanar α) ⊗[R] ConnesKreimer R (Nonplanar α)) from by
      unfold cutTensorP_augAction
      show (of' (({c} : Forest (RoseTree α)).map Nonplanar.mk)
              : ConnesKreimer R (Nonplanar α)) ⊗ₜ[R]
            (1 : ConnesKreimer R (Nonplanar α))
          = ofTree (Nonplanar.mk c) ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α))
      rw [Multiset.map_singleton, of'_singleton]]
    rw [show ((cutTensorP_augAction (R := R)) ∘
              (fun p : Forest (RoseTree α) × RoseTree α =>
                (p.1, Option.some p.2))) = (cutTensorP_planar (R := R)) from by
      funext p
      unfold cutTensorP_augAction cutTensorP_planar
      rfl]
    -- Now both LHS-head and RHS-head are (ofTree (mk c) ⊗ 1) + (cuts of c map).
    rw [ih_head, ih_tail]

end

/-! ### Lift from tree-level to Nonplanar -/

/-- **Per-tree**: `(S ⊗ S) (comulCTreeN τ (embedInl T)) = comulTreeN T`.
    Descent of `strip_cutSummandsCP_sum_eq` through `Quotient.inductionOn`. -/
private theorem strip_comulCTreeN_embedInl
    (τ : Nonplanar (α ⊕ β) → β) (T : Nonplanar α) :
    (Algebra.TensorProduct.map (stripTraceAlgHom (R := R) (α := α) (β := β))
        stripTraceAlgHom) (comulCTreeN τ (Nonplanar.embedInl T)) =
      comulTreeN T := by
  refine Quotient.inductionOn T ?_
  intro t
  -- Unfold both sides via comulCTreeN definition.
  show (Algebra.TensorProduct.map (stripTraceAlgHom (R := R)) stripTraceAlgHom)
        (comulCTreeN τ (Nonplanar.mk (RoseTree.map Sum.inl t))) =
       comulTreeN (Nonplanar.mk t)
  unfold comulCTreeN
  rw [map_add]
  -- First summand: (S ⊗ S) (ofTree (mk (embed t)) ⊗ 1) = ofTree (mk t) ⊗ 1.
  rw [show (Algebra.TensorProduct.map (stripTraceAlgHom (R := R)) stripTraceAlgHom)
            (ofTree (Nonplanar.mk (RoseTree.map Sum.inl t)) ⊗ₜ[R]
              (1 : ConnesKreimer R (Nonplanar (α ⊕ β)))) =
          ofTree (Nonplanar.mk t) ⊗ₜ[R] (1 : ConnesKreimer R (Nonplanar α)) from by
    rw [Algebra.TensorProduct.map_tmul, map_one]
    congr 1
    -- mk (RoseTree.map Sum.inl t) = embedInl (mk t)
    exact stripTraceAlgHom_ofTree_embedInl (Nonplanar.mk t)]
  congr 1
  -- Second summand: (S ⊗ S) (sum over cuts) = sum over Δ^ρ cuts.
  rw [map_multiset_sum
        (Algebra.TensorProduct.map (stripTraceAlgHom (R := R)) stripTraceAlgHom)]
  simp only [Multiset.map_map]
  -- Reduce sum-of-(S⊗S)-applied to sum of per-summand tensors.
  rw [show ((Algebra.TensorProduct.map (stripTraceAlgHom (R := R)) stripTraceAlgHom) ∘
            (fun p : Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β) =>
              of' (R := R) p.1 ⊗ₜ[R] ofTree p.2)) =
          (fun p : Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β) =>
            stripTraceAlgHom (of' (R := R) p.1) ⊗ₜ[R]
              stripTraceAlgHom (ofTree p.2)) from by
    funext p
    rw [Function.comp_apply, Algebra.TensorProduct.map_tmul]]
  -- Cuts descend to tree-level: cutSummandsCN τ (mk t') = (cutSummandsCP (τ ∘ mk) t').map projSummand.
  rw [show cutSummandsCN τ (Nonplanar.mk (RoseTree.map Sum.inl t)) =
        (cutSummandsCP (τ ∘ Nonplanar.mk) (RoseTree.map Sum.inl t)).map projSummand from
      cutSummandsCN_mk _ _]
  rw [show cutSummandsN (Nonplanar.mk t) =
        (cutSummandsP t).map projSummand from
      cutSummandsN_mk _]
  rw [Multiset.map_map, Multiset.map_map]
  -- Now both sums are over the tree-level cut-summand multisets.
  -- The maps compose to cutTensorC_planar / cutTensorP_planar respectively.
  rw [show ((fun p : Forest (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β) =>
              stripTraceAlgHom (of' (R := R) p.1) ⊗ₜ[R]
                stripTraceAlgHom (ofTree p.2)) ∘ projSummand) =
          cutTensorC_planar (R := R) from by
    funext p
    show stripTraceAlgHom (of' (p.1.map Nonplanar.mk)) ⊗ₜ[R]
            stripTraceAlgHom (ofTree (Nonplanar.mk p.2)) =
         cutTensorC_planar (R := R) p
    rfl]
  rw [show ((fun p : Forest (Nonplanar α) × Nonplanar α =>
              (of' (R := R) p.1 : ConnesKreimer R (Nonplanar α)) ⊗ₜ[R]
                ofTree p.2) ∘ projSummand) =
          cutTensorP_planar (R := R) from by
    funext p
    rfl]
  exact strip_cutSummandsCP_sum_eq τ t

/-- **Per-forest**: `(S ⊗ S) (comulCForestN τ (F.map embedInl)) = comulForestN F`.
    Lift per-tree via `Multiset.induction` + multiplicativity of forest coproducts
    and the AlgHom `(S ⊗ S)`. -/
private theorem strip_comulCForestN_embedInl
    (τ : Nonplanar (α ⊕ β) → β) (F : Forest (Nonplanar α)) :
    (Algebra.TensorProduct.map (stripTraceAlgHom (R := R) (α := α) (β := β))
        stripTraceAlgHom) (comulCForestN τ (F.map Nonplanar.embedInl)) =
      comulForestN F := by
  induction F using Multiset.induction with
  | empty =>
    rw [Multiset.map_zero, comulCForestN_zero, comulForestN_zero, map_one]
  | cons T F' ih =>
    rw [Multiset.map_cons, comulForestN_cons]
    -- comulCForestN τ (T_embed ::ₘ F'_embed) = comulCTreeN τ T_embed * comulCForestN τ F'_embed
    have hcons : comulCForestN (R := R) τ
        (Nonplanar.embedInl T ::ₘ F'.map Nonplanar.embedInl) =
        comulCTreeN τ (Nonplanar.embedInl T) *
          comulCForestN (R := R) τ (F'.map Nonplanar.embedInl) := by
      unfold comulCForestN
      rw [Multiset.map_cons, Multiset.prod_cons]
    rw [hcons, map_mul, strip_comulCTreeN_embedInl, ih]

/-- **MCB equivalence** (n-ary specialization): the Δ^d-via-Δ^c
    construction agrees with Δ^ρ on trace-free trees.

    `comulDN ∘ embed_{Sum.inl} = comulAlgHomN`

    Closed via: (a) AlgHom extensionality + `ConnesKreimer.induction_linear` reduces
    to per-basis `of' F`; (b) Multiset multiplicativity of `comulCForestN`,
    `comulForestN`, and `(stripTraceAlgHom ⊗ stripTraceAlgHom)` reduces to
    per-tree; (c) `Quotient.inductionOn` reduces per-tree to tree-level; (d)
    tree-level mutual structural induction on tree / children-list closes the
    cut-summand bijection via `strip_cutSummandsCP_sum_eq`. -/
theorem comulDN_embedInl_eq_comulAlgHomN (τ : Nonplanar (α ⊕ β) → β) :
    (comulDN (R := R) τ).comp (embedInlAlgHom (R := R) (β := β)) =
      comulAlgHomN := by
  apply AlgHom.ext
  intro x
  show (Algebra.TensorProduct.map (stripTraceAlgHom (R := R))
          stripTraceAlgHom) (comulCAlgHomN τ (embedInlAlgHom x)) =
       comulAlgHomN x
  refine ConnesKreimer.induction_linear x ?_ ?_ ?_
  · show (Algebra.TensorProduct.map (stripTraceAlgHom (R := R)) stripTraceAlgHom)
          (comulCAlgHomN τ (embedInlAlgHom
              (0 : ConnesKreimer R (Nonplanar α)))) =
         comulAlgHomN (0 : ConnesKreimer R (Nonplanar α))
    rw [map_zero, map_zero, map_zero, map_zero]
  · intro a b ha hb
    let a' : ConnesKreimer R (Nonplanar α) := a
    let b' : ConnesKreimer R (Nonplanar α) := b
    have ha' : (Algebra.TensorProduct.map (stripTraceAlgHom (R := R)) stripTraceAlgHom)
          (comulCAlgHomN τ (embedInlAlgHom a')) = comulAlgHomN a' := ha
    have hb' : (Algebra.TensorProduct.map (stripTraceAlgHom (R := R)) stripTraceAlgHom)
          (comulCAlgHomN τ (embedInlAlgHom b')) = comulAlgHomN b' := hb
    show (Algebra.TensorProduct.map (stripTraceAlgHom (R := R)) stripTraceAlgHom)
          (comulCAlgHomN τ (embedInlAlgHom (a' + b'))) = comulAlgHomN (a' + b')
    rw [map_add, map_add, map_add, map_add, ha', hb']
  · intro F r
    show (Algebra.TensorProduct.map (stripTraceAlgHom (R := R)) stripTraceAlgHom)
          (comulCAlgHomN τ (embedInlAlgHom (ConnesKreimer.single F r))) =
         comulAlgHomN (ConnesKreimer.single F r)
    have hsingle : (ConnesKreimer.single F r : ConnesKreimer R (Nonplanar α)) =
        r • (of' (R := R) F : ConnesKreimer R (Nonplanar α)) :=
      ConnesKreimer.smul_single_one F r
    rw [hsingle, map_smul, map_smul, map_smul, map_smul, embedInlAlgHom_of',
        comulCAlgHomN_apply_of', comulAlgHomN_apply_of']
    congr 1
    exact strip_comulCForestN_embedInl τ F

end ConnesKreimer

end RootedTree
