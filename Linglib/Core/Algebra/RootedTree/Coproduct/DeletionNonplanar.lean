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
@cite{marcolli-chomsky-berwick-2025}

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
(`PruningNonplanar.instBialgebraRho`). MCB's Lemma 1.2.12 (Δ^d weak
coassoc with distance-≤-1 multiplicity discrepancy) is specific to the
binary `Π_{d,p}` step which is identity in our setting; in our n-ary
substrate Δ^d ≡ Δ^ρ (modulo the embedding) has strict coassoc.

## Status

`[UPSTREAM]` candidate. Sorry-free except for:
* `comulDN_embedInl_eq_comulAlgHomN` — the equivalence theorem
  (sorry'd; combinatorial bijection between Δ^c cut summands of
  `embed T` and Δ^ρ cut summands of T). The left-channel half is
  handled by `stripTraceAlgHom_comp_embedInlAlgHom` (sorry-free);
  the deeper right-channel trace-removal is the remaining gap.

The PlanarEquiv invariance of trace-stripping is now sorry-free
(`stripTraceQuotient_planarEquiv`, via structural induction on
PlanarStep + `List.Perm.filterMap`). The substrate (definitions,
types, downstream API surface, strip-inverts-embed lemma) is closed.
-/

namespace RootedTree

namespace ConnesKreimer

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {α β : Type*}

/-! ## Tree-level trace-strip projection

Strip trace-placeholder subtrees (`Sum.inr`-rooted subtrees) from a
`Planar (α ⊕ β)` tree, yielding `Option (Planar α)` — the result is
`none` only if the root itself is a trace placeholder.

The strip recurses into children via `filterMap`: each child is
stripped, and `none` results are dropped. -/

mutual

/-- Strip trace-placeholder subtrees from a planar tree. Returns `none`
    if the root is a trace placeholder (`Sum.inr`-labeled). -/
def Planar.stripTrace : Planar (α ⊕ β) → Option (Planar α)
  | .node (Sum.inr _) _ => none
  | .node (Sum.inl a) cs => some (.node a (Planar.stripTraceList cs))

/-- Auxiliary: strip each tree in a children list, dropping `none`s. -/
def Planar.stripTraceList : List (Planar (α ⊕ β)) → List (Planar α)
  | [] => []
  | c :: cs =>
    match Planar.stripTrace c with
    | none => Planar.stripTraceList cs
    | some t => t :: Planar.stripTraceList cs

end

@[simp] theorem Planar.stripTrace_inr (b : β) (cs : List (Planar (α ⊕ β))) :
    Planar.stripTrace (Planar.node (Sum.inr b) cs) = none := rfl

@[simp] theorem Planar.stripTrace_inl (a : α) (cs : List (Planar (α ⊕ β))) :
    Planar.stripTrace (Planar.node (Sum.inl a) cs) =
      some (.node a (Planar.stripTraceList cs)) := rfl

@[simp] theorem Planar.stripTraceList_nil :
    Planar.stripTraceList ([] : List (Planar (α ⊕ β))) = [] := rfl

/-! ## Descent to `Nonplanar`

Lift `Planar.stripTrace` through the quotient. The lift requires that
`stripTrace ∘ Nonplanar.mk` be well-defined modulo `PlanarEquiv`, which
holds because:
* `PlanarEquiv` permutes children; `stripTraceList` commutes with
  permutations up to `List.Perm` on the resulting list.
* At the `Nonplanar.mk` level, child-list order collapses, so
  PlanarEquiv-related stripped trees become equal.
-/

/-- The PlanarEquiv-invariant strip-then-mk composition. Used to lift
    `Planar.stripTrace` through the Nonplanar quotient. -/
private def stripTraceQuotient (t : Planar (α ⊕ β)) : Option (Nonplanar α) :=
  (Planar.stripTrace t).map Nonplanar.mk

/-- `Planar.stripTraceList` agrees with `List.filterMap Planar.stripTrace`
    (by structural induction on the list — both pattern-match the same
    way on the optional strip result). -/
private theorem stripTraceList_eq_filterMap (cs : List (Planar (α ⊕ β))) :
    Planar.stripTraceList cs = cs.filterMap Planar.stripTrace := by
  induction cs with
  | nil => rfl
  | cons head tail ih =>
    show (match Planar.stripTrace head with
            | none => Planar.stripTraceList tail
            | some t => t :: Planar.stripTraceList tail) =
         (head :: tail).filterMap Planar.stripTrace
    cases h : Planar.stripTrace head with
    | none => simp [List.filterMap_cons_none h, ih]
    | some t => simp [List.filterMap_cons_some h, ih]

/-- `PlanarStep` invariance of the strip-then-mk composition. Two cases:
    swapping children permutes the strip-filtered list (`Perm.filterMap`);
    recursive step lifts via `planarEquiv_recurse_lift`. -/
private theorem stripTraceQuotient_planarStep :
    ∀ {t t' : Planar (α ⊕ β)}, Planar.PlanarStep t t' →
      stripTraceQuotient t = stripTraceQuotient t' := by
  intro t t' h
  induction h with
  | @swapAtRoot a l r pre post =>
    cases a with
    | inl a' =>
      show ((Planar.stripTrace (Planar.node (Sum.inl a') (pre ++ l :: r :: post))).map
              Nonplanar.mk) =
           ((Planar.stripTrace (Planar.node (Sum.inl a') (pre ++ r :: l :: post))).map
              Nonplanar.mk)
      simp only [Planar.stripTrace_inl, Option.map_some, stripTraceList_eq_filterMap]
      congr 1
      apply Nonplanar.mk_eq_mk_iff.mpr
      apply Planar.planarEquiv_root_perm
      exact List.Perm.filterMap _ (List.Perm.append_left pre (List.Perm.swap r l post))
    | inr b =>
      show ((Planar.stripTrace (Planar.node (Sum.inr b) (pre ++ l :: r :: post))).map
              Nonplanar.mk) =
           ((Planar.stripTrace (Planar.node (Sum.inr b) (pre ++ r :: l :: post))).map
              Nonplanar.mk)
      simp only [Planar.stripTrace_inr, Option.map_none]
  | @recurse a pre old new post _hstep ih =>
    cases a with
    | inl a' =>
      show ((Planar.stripTrace (Planar.node (Sum.inl a') (pre ++ old :: post))).map
              Nonplanar.mk) =
           ((Planar.stripTrace (Planar.node (Sum.inl a') (pre ++ new :: post))).map
              Nonplanar.mk)
      simp only [Planar.stripTrace_inl, Option.map_some, stripTraceList_eq_filterMap,
                 List.filterMap_append]
      congr 1
      apply Nonplanar.mk_eq_mk_iff.mpr
      -- ih has type stripTraceQuotient old = stripTraceQuotient new, i.e.
      --   (Planar.stripTrace old).map Nonplanar.mk = (Planar.stripTrace new).map Nonplanar.mk
      -- ih has type stripTraceQuotient old = stripTraceQuotient new.
      have ih' : (Planar.stripTrace old).map Nonplanar.mk =
                 (Planar.stripTrace new).map Nonplanar.mk := ih
      cases hold : Planar.stripTrace old with
      | none =>
        rw [hold] at ih'
        simp only [Option.map_none] at ih'
        have hnew : Planar.stripTrace new = none := by
          cases hnew' : Planar.stripTrace new with
          | none => rfl
          | some _ =>
            rw [hnew'] at ih'
            simp at ih'
        simp only [List.filterMap_cons_none hold, List.filterMap_cons_none hnew]
        exact Planar.PlanarEquiv.refl _
      | some t_old =>
        rw [hold] at ih'
        simp only [Option.map_some] at ih'
        -- ih' : some (Nonplanar.mk t_old) = (Planar.stripTrace new).map Nonplanar.mk
        cases hnew : Planar.stripTrace new with
        | none =>
          exfalso
          rw [hnew] at ih'
          simp at ih'
        | some t_new =>
          rw [hnew] at ih'
          simp only [Option.map_some, Option.some_inj] at ih'
          simp only [List.filterMap_cons_some hold, List.filterMap_cons_some hnew]
          exact Planar.planarEquiv_recurse_lift (pre.filterMap Planar.stripTrace)
                  (post.filterMap Planar.stripTrace) (Nonplanar.mk_eq_mk_iff.mp ih')
    | inr b =>
      show ((Planar.stripTrace (Planar.node (Sum.inr b) (pre ++ old :: post))).map
              Nonplanar.mk) =
           ((Planar.stripTrace (Planar.node (Sum.inr b) (pre ++ new :: post))).map
              Nonplanar.mk)
      simp only [Planar.stripTrace_inr, Option.map_none]

/-- **PlanarEquiv invariance** of the strip-then-mk composition.
    By `Relation.EqvGen` induction, reduces to `PlanarStep` invariance. -/
private theorem stripTraceQuotient_planarEquiv :
    ∀ (t t' : Planar (α ⊕ β)), t ≈ t' →
      stripTraceQuotient t = stripTraceQuotient t' := by
  intro t t' h
  induction h with
  | rel _ _ hstep => exact stripTraceQuotient_planarStep hstep
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- Strip trace-placeholder subtrees from a `Nonplanar` tree. -/
noncomputable def Nonplanar.stripTrace : Nonplanar (α ⊕ β) → Option (Nonplanar α) :=
  Quotient.lift stripTraceQuotient stripTraceQuotient_planarEquiv

@[simp] theorem Nonplanar.stripTrace_mk (t : Planar (α ⊕ β)) :
    Nonplanar.stripTrace (Nonplanar.mk t) =
      (Planar.stripTrace t).map Nonplanar.mk := rfl

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
    induced by `stripTraceForestAddHom` via `AddMonoidAlgebra.mapDomainAlgHom`. -/
noncomputable def stripTraceAlgHom :
    ConnesKreimer R (Nonplanar (α ⊕ β)) →ₐ[R] ConnesKreimer R (Nonplanar α) :=
  AddMonoidAlgebra.mapDomainAlgHom R R (stripTraceForestAddHom (α := α) (β := β))

@[simp] theorem stripTraceAlgHom_of' (F : Forest (Nonplanar (α ⊕ β))) :
    stripTraceAlgHom (R := R) (of' F) =
      of' (R := R) (F.filterMap Nonplanar.stripTrace) := by
  show Finsupp.mapDomain (stripTraceForestAddHom (α := α) (β := β))
        (Finsupp.single F 1) = Finsupp.single _ 1
  rw [Finsupp.mapDomain_single]
  rfl

/-! ## Sum.inl embedding

The embedding `α → α ⊕ β` lifts componentwise to trees and forests via
`Planar.map` / `Nonplanar.map` / `Multiset.map`. -/

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
    induced by `Nonplanar.embedInl` via `AddMonoidAlgebra.mapDomainAlgHom`. -/
noncomputable def embedInlAlgHom :
    ConnesKreimer R (Nonplanar α) →ₐ[R] ConnesKreimer R (Nonplanar (α ⊕ β)) :=
  AddMonoidAlgebra.mapDomainAlgHom R R (embedInlForestAddHom (α := α) (β := β))

@[simp] theorem embedInlAlgHom_of' (F : Forest (Nonplanar α)) :
    embedInlAlgHom (R := R) (β := β) (of' F) =
      of' (R := R) (F.map Nonplanar.embedInl) := by
  show Finsupp.mapDomain (embedInlForestAddHom (α := α) (β := β))
        (Finsupp.single F 1) = Finsupp.single _ 1
  rw [Finsupp.mapDomain_single]
  rfl

/-! ### Strip inverts embed

`Planar.stripTrace (Planar.map Sum.inl p) = some p` — embedding via
`Sum.inl` then stripping recovers the original. Proven by mutual
structural induction on the planar tree / its child list. Descends to
the Nonplanar level via `Quotient.inductionOn`, and lifts to the
algebra-hom level: `stripTraceAlgHom ∘ embedInlAlgHom = id`. -/

mutual

private theorem Planar.stripTrace_map_inl :
    ∀ (p : Planar α), Planar.stripTrace (Planar.map (Sum.inl : α → α ⊕ β) p) = some p
  | .node a cs => by
    show Planar.stripTrace (.node (Sum.inl a) (Planar.mapList Sum.inl cs)) = _
    rw [Planar.stripTrace_inl]
    congr 1
    show Planar.node a (Planar.stripTraceList (Planar.mapList Sum.inl cs)) =
         Planar.node a cs
    rw [Planar.stripTraceList_mapList_inl]

private theorem Planar.stripTraceList_mapList_inl :
    ∀ (cs : List (Planar α)),
      Planar.stripTraceList (Planar.mapList (Sum.inl : α → α ⊕ β) cs) = cs
  | [] => rfl
  | c :: cs => by
    show (match Planar.stripTrace (Planar.map Sum.inl c) with
           | none => Planar.stripTraceList (Planar.mapList Sum.inl cs)
           | some t => t :: Planar.stripTraceList (Planar.mapList Sum.inl cs)) =
         c :: cs
    rw [Planar.stripTrace_map_inl c, Planar.stripTraceList_mapList_inl cs]

end

theorem Nonplanar.stripTrace_embedInl (T : Nonplanar α) :
    Nonplanar.stripTrace (Nonplanar.embedInl (β := β) T) = some T := by
  refine Quotient.inductionOn T ?_
  intro p
  show Nonplanar.stripTrace (Nonplanar.map Sum.inl (Nonplanar.mk p)) = some (Nonplanar.mk p)
  rw [Nonplanar.map_mk]
  show ((Planar.stripTrace (Planar.map Sum.inl p)).map Nonplanar.mk : Option (Nonplanar α)) =
       some (Nonplanar.mk p)
  rw [Planar.stripTrace_map_inl]
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
  refine Finsupp.induction_linear x ?_ ?_ ?_
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
    show stripTraceAlgHom (embedInlAlgHom (Finsupp.single F r)) = Finsupp.single F r
    have hsingle : (Finsupp.single F r : ConnesKreimer R (Nonplanar α)) =
        r • (of' (R := R) F : ConnesKreimer R (Nonplanar α)) :=
      (Finsupp.smul_single_one F r).symm
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

/-- **MCB equivalence** (n-ary specialization): the Δ^d-via-Δ^c
    construction agrees with Δ^ρ on trace-free trees.

    `comulDN ∘ embed_{Sum.inl} = comulAlgHomN`

    **Sorry**: the substantive content of MCB Lemma 1.3.10 in our n-ary
    setting (with Π_{d,p} = identity). Closing requires the
    cut-bijection lemma:

    `cutSummandsCN τ (Nonplanar.embedInl T) =
        (cutSummandsN T).map (fun (F, T') => (F.map embedInl, ?embed-T'-with-traces))`

    i.e., Δ^c cuts of `embedInl T` correspond bijectively to Δ^ρ cuts
    of `T`, with the right-channel-trunk carrying traceLeaf placeholders
    in the Δ^c version. After (strip ⊗ strip): the strip on the left
    channel inverts `embedInl` (via `stripTraceAlgHom_comp_embedInlAlgHom`
    above), and the strip on the right channel removes the traceLeaf
    placeholders, recovering the Δ^ρ trunk.

    The bijection itself requires either: (a) careful structural
    induction on the planar tree at the `cutSummandsCP` vs
    `cutSummandsP` level (~200-300 LOC), or (b) an abstract argument
    via the extractC vs extractP comparison + the generic `cutSummandsG`
    naturality. Both routes are tractable but exceed this session's
    scope.

    The scaffolding `stripTraceAlgHom_comp_embedInlAlgHom` (above)
    handles the left-channel half (strip inverts embed); the
    right-channel trace-removal is the deeper part. -/
theorem comulDN_embedInl_eq_comulAlgHomN (τ : Nonplanar (α ⊕ β) → β) :
    (comulDN (R := R) τ).comp (embedInlAlgHom (R := R) (β := β)) =
      comulAlgHomN := by
  sorry

end ConnesKreimer

end RootedTree
