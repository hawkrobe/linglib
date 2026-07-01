/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.SyntacticObject.Build
import Linglib.Syntax.Minimalist.Merge.Internal

/-!
# Workspaces and Merge over syntactic objects

[marcolli-chomsky-berwick-2025] §1.2–1.4. The single-carrier program's P1b: the
**Merge and workspace layer over the `SO` syntactic objects** (`SyntacticObject.lean`).
This is additive — it does *not* touch the legacy `SyntacticObject`/`Step`/`Derivation`
(`FreeCommMagma (LIToken ⊕ Nat)`); flipping `SyntacticObject := SO` and retiring
the `⊕ Nat` index is P2.

## What this file connects

The Merge **algebra** already lives on `ConnesKreimer ℤ (Nonplanar α)` (the #424
work, `Merge/External.lean` + `Merge/Internal.lean`): `mergeOp_pair` realizes
External Merge (Lemma 1.4.1) and `mergeOp_im_composition` realizes Internal Merge
as a two-stage composition (Prop 1.4.2). This file gives the **syntactic surface**
on the carrier — workspaces, the bare-binary-node Merge primitive, the index-free
trace leaf — and relates each to the algebra by theorem.

## Bare internals, index-free traces (§1.1.3.1, §1.15, Def 1.2.1)

The carrier puts **bare `Sum.inr ()`** on internal nodes (the head comes from the
separate §1.15 head function, not the object) and on **trace leaves** (a moved
element leaves a bare vertex; chain identity is read at the workspace level, MCB
Def 1.2.1, not from a per-leaf index). So External and Internal Merge here both
build a bare binary node — distinct from the legacy head-decorated `toNonplanar`
bridges (`mergeOp_emR_matches_Step`, which graft `Sum.inl L`); those are the head
function *applied*, and P3/P4 retire them.

## Computability discipline

`Nonplanar.node`, `mergeOp`, and the coproduct are `noncomputable` (the Hopf
machinery round-trips through `Quotient.out`). So `SO.merge`/`SO.intMerge` are
`noncomputable`, and studies must **state result trees directly** (built computably
via `Nonplanar.mk ∘ RoseTree.node`, then `decide` on `IsSO`) and relate them to Merge
by theorem — never compute Merge under `decide`. `merge_mk` is the construction
bridge; the `#eval`-free `decide` examples at the end confirm the discipline holds
on this carrier (the P1 spike, now as carrier tests).
-/

namespace Minimalist

open RootedTree RootedTree.ConnesKreimer

/-! ### Workspaces (MCB Def 1.2.1)

The carrier Merge operators `SO.merge` (Lemma 1.4.1) and `SO.intMerge` (Prop 1.4.2) are
defined in `SyntacticObject/Build.lean` (they need only the bare binary node); this file
adds their **coproduct identity** on the workspace Hopf algebra. -/

/-- A **workspace** is a forest (finite multiset) of syntactic objects
    ([marcolli-chomsky-berwick-2025] Def 1.2.1). The forest **product is disjoint
    union** (`+` on `Multiset`), with unit the empty forest (`0`); a *well-formed*
    workspace is nonempty. `Forest` is the algebra's forest type, so a workspace is
    exactly what `of'` lifts into `ConnesKreimer ℤ (Nonplanar SOLabel)`. -/
abbrev Workspace : Type := Forest SO

/-- A moved element occupies **repeated isomorphic components** of the workspace; the
    number of copies is their multiplicity ([marcolli-chomsky-berwick-2025]
    Def 1.2.1: "those isomorphism classes are the chain"). Decidable now that the
    carrier has `DecidableEq SO` (#792) — this is the workspace-level chain identity
    that **replaces the legacy `⊕ Nat` trace index**. -/
def Workspace.chainMultiplicity (S : SO) (W : Workspace) : Nat := W.count S

/-! ### External Merge: bridge to the algebra (Lemma 1.4.1) -/

/-- **External Merge ↔ algebra** ([marcolli-chomsky-berwick-2025] Lemma 1.4.1,
    F̂ = ∅). The algebraic Merge `mergeOp (Sum.inr ())` on the 2-object workspace
    `{S, S'}` yields the singleton workspace of the carrier Merge `SO.merge S S'`.
    The root label is the **bare** `Sum.inr ()` — the faithful departure from the
    head-decorated legacy bridge. -/
theorem SO.merge_toForest (S S' : SO) :
    Merge.mergeOp (R := ℤ) (Sum.inr ()) S.val S'.val
        (of' ({S.val, S'.val} : Forest (Nonplanar SOLabel)))
      = of' (R := ℤ) ({(SO.merge S S').val} : Forest (Nonplanar SOLabel)) := by
  rw [Merge.mergeOp_pair, SO.merge_val]

/-! ### Internal Merge as composition (MCB Prop 1.4.2) -/

/-- **Internal Merge ↔ algebra** ([marcolli-chomsky-berwick-2025] Prop 1.4.2). Given
    the Δ^ρ cut data on `T` extracting `mover` with remainder `remainder` (the unique
    crown-`{mover}` summand `p0`, `p0.2 = remainder.val`, `T ≠ mover`), the two-stage
    composition `mergeOp (inr ()) ∘ mergeOpUnit mover` over `{T}` yields the singleton
    workspace of `SO.intMerge mover remainder`. This is `mergeOp_im_composition`
    transported to the carrier with the `IsSO`-carrying result. -/
theorem SO.intMerge_toForest (mover remainder T : SO)
    (p0 : Forest (Nonplanar SOLabel) × Nonplanar SOLabel)
    (h_filter : (cutSummandsN T.val).filter
        (fun p => p.1 = ({mover.val} : Forest (Nonplanar SOLabel))) = {p0})
    (h_remainder : p0.2 = remainder.val)
    (hT : T.val ≠ mover.val) :
    Merge.mergeOp (R := ℤ) (Sum.inr ()) remainder.val mover.val
        (Merge.mergeOpUnit (R := ℤ) mover.val
          (of' ({T.val} : Forest (Nonplanar SOLabel))))
      = of' (R := ℤ) ({(SO.intMerge mover remainder).val} : Forest (Nonplanar SOLabel)) := by
  rw [Merge.mergeOp_im_composition (Sum.inr ()) mover.val T.val remainder.val
        p0 h_filter h_remainder hT, SO.intMerge_val]

/-! ### `decide` demonstrations (the P1 computability spike, as carrier tests)

Confirms: trace/lexical leaves are well-formed; an IM-result-shaped tree — a bare
binary node over a lexical leaf and a bare trace leaf — built directly via planar
`.node` is `IsSO` and `decide`-able even though the Merge *operator* is
noncomputable; ill-formed shapes are rejected. -/

private def demoTok : LIToken := mkTraceToken 0

/-- A lexical leaf is well-formed. -/
example : IsSO (SO.lexLeaf demoTok).val := by decide

/-- The bare trace leaf is well-formed. -/
example : IsSO SO.traceLeaf.val := by decide

/-- An IM-result-shaped tree — bare binary node over a lexical leaf and a bare
    trace — is well-formed (built directly, no Merge operator). -/
example :
    IsSO (Nonplanar.mk (.node (Sum.inr ())
      [.leaf (Sum.inl demoTok), .leaf (Sum.inr ())])) := by decide

/-- A lexical item with children is **rejected** (lexical items are leaves). -/
example :
    ¬ IsSO (Nonplanar.mk (.node (Sum.inl demoTok)
      [.leaf (Sum.inr ())])) := by decide

/-- A ternary bare node is **rejected** (syntactic objects are binary). -/
example :
    ¬ IsSO (Nonplanar.mk (.node (Sum.inr ())
      [.leaf (Sum.inr ()), .leaf (Sum.inr ()), .leaf (Sum.inr ())])) := by decide

/-- Workspace chain identity is decidable: two isomorphic components ⇒ chain of 2. -/
example : Workspace.chainMultiplicity SO.traceLeaf {SO.traceLeaf, SO.traceLeaf} = 2 := by
  decide

end Minimalist
