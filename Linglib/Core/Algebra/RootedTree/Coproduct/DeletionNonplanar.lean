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
* `Nonplanar.stripTrace_planarEquiv` — PlanarEquiv invariance of the
  tree-level strip (sorry'd; structural induction on PlanarStep).
* `comulDN_embedInl_eq_comulAlgHomN` — the equivalence theorem
  (sorry'd; combinatorial bijection between Δ^c cut summands of
  `embed T` and Δ^ρ cut summands of T).

Both sorries are statements of true mathematical facts; the proofs are
deferred. The substrate (definitions, types, downstream API surface)
is closed.
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

/-- **PlanarEquiv invariance** of the strip-then-mk composition. The
    proof reduces (by `EqvGen` induction) to `PlanarStep` invariance,
    which holds by structural induction: swapping children at the root
    produces strip-results that differ only by a child-list permutation
    (vanishing under `Nonplanar.mk`); recursive steps lift via the
    same argument on the recursive call's child.

    TODO: structural proof. Sorry-fenced for now; the statement is
    correct and matches the well-known combinatorial fact. -/
private theorem stripTraceQuotient_planarEquiv :
    ∀ (t t' : Planar (α ⊕ β)), t ≈ t' →
      stripTraceQuotient t = stripTraceQuotient t' := by
  sorry

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

    TODO: combinatorial bijection between Δ^c cut summands of
    `embedInl T` (in `Nonplanar (α ⊕ β)`) and Δ^ρ cut summands of
    `T` (in `Nonplanar α`). The strip realizes the bijection on
    remainders; cut-forest components are Sum.inl-only by construction
    (since the original tree is Sum.inl-only) so strip is identity on
    them.

    Sorry-fenced; the statement is the load-bearing API surface for
    downstream consumers wanting `Δ^d ≡ Δ^ρ`. -/
theorem comulDN_embedInl_eq_comulAlgHomN (τ : Nonplanar (α ⊕ β) → β) :
    (comulDN (R := R) τ).comp (embedInlAlgHom (R := R) (β := β)) =
      comulAlgHomN := by
  sorry

end ConnesKreimer

end RootedTree
