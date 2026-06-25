/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Combinatorics.RootedTree.DecEq
import Linglib.Syntax.Minimalist.Defs

/-!
# The MCB-faithful syntactic-object carrier (skeleton)

[marcolli-chomsky-berwick-2025] §1.1. The single-carrier program
(`scratch/mcb-single-carrier-spec.md`) moves syntactic objects onto the **same**
`Nonplanar` carrier the Merge algebra already uses, exactly as the book intends
("syntactic objects… are the generators of the Hopf algebra", §1.2). This file is
P0's carrier skeleton: the well-formed subset of `Nonplanar (LIToken ⊕ Unit)`.

## Faithful labelling (§1.1.3.1: "no labels at any non-leaf vertices")

MCB's SO is a **binary, nonplanar** rooted tree with **leaves labelled by SO₀**
(lexical items + features) and **internal vertices bare** — the head is *not* on
the tree; it comes from a separate labelling algorithm (§1.15, the head function).
So on `Nonplanar (LIToken ⊕ Unit)` (the algebra's `α ⊕ β`, `β = Unit`), **role by arity**:

- a **lexical leaf** carries `Sum.inl tok` — a lexical item (`LIToken` ≈ SO₀);
- a **trace leaf** carries `Sum.inr ()` — bare (chain identity is workspace-level,
  MCB Def 1.2.1, not a per-leaf index; this replaces the legacy `⊕ Nat`);
- an **internal node** carries `Sum.inr ()` — **bare**, no head label (§1.15 supplies it).

`Sum.inr ()` is the single structural/bare marker; trace-leaf vs. internal is
childless vs. binary. `IsSO` pins this. This is the deliberate departure from the
legacy `toNonplanar` image, which decorated internal nodes with the head
(`Sum.inl headLeaf`) — that decoration is the head function applied, not the object.

## Scope

The carrier + `IsSO` + decidability + the `SO` subtype, with the faithful three-role
alphabet (lexical/trace leaves + bare internals). **Out of scope (later phases):**
workspaces + Merge on the carrier (EM + IM-via-coproduct, MCB Prop 1.4.2 — uses the
existing `comul{D,C}N`; P1 continued), the structural ops (`contains`/`subtrees` =
`Acc'`) + flip `SyntacticObject := SO` (P2), the head function + Phase API re-home
(P3), retiring `FreeCommMagma`/`toNonplanar` (P4). See `scratch/p1-spec-and-audit.md`.
-/

namespace Minimalist

open RootedTree

/-- The SO label alphabet, in the algebra's `α ⊕ β` form (`α = LIToken` lexical,
    `β = Unit` bare). Each **role is fixed by arity**, not by a third label:

    - `Sum.inl tok` on a **leaf** — a lexical item (`LIToken` ≈ SO₀);
    - `Sum.inr ()` on a **leaf** — a **trace** (bare; chain identity is workspace-level,
      MCB Def 1.2.1, not a per-leaf index — this replaces the legacy `⊕ Nat`);
    - `Sum.inr ()` on an **internal** node — **bare** (no head; §1.15 supplies it).

    `Sum.inr ()` is the single "structural/bare" marker; a trace and an internal
    vertex are the childless vs. binary occurrences of it. This is exactly the
    `Nonplanar (α ⊕ β)` (β = `Unit`) alphabet the existing `τ`-parameterised trace
    coproducts (`comul{D,C}N`) already speak. -/
abbrev SOLabel : Type := LIToken ⊕ Unit

/-! ### Well-formedness `IsSO` (binary, lexical/trace leaves, bare internals) -/

mutual
/-- Structural well-formedness of a *planar* syntactic object: a lexical node must
    be a leaf; a bare (`inr ()`) node is either a **trace leaf** (childless) or a
    **binary internal** node with well-formed children. Permutation-friendly so it
    lifts to the nonplanar quotient. -/
def isSOPlanar : Planar SOLabel → Bool
  | .node (.inl _) cs  => cs.isEmpty
  | .node (.inr ()) cs => (cs.length == 0 || cs.length == 2) && isSOPlanarList cs
/-- Auxiliary: all children well-formed. -/
def isSOPlanarList : List (Planar SOLabel) → Bool
  | []      => true
  | c :: cs => isSOPlanar c && isSOPlanarList cs
end

/-! ### `isSOPlanar` is `PlanarEquiv`-invariant (so it lifts) -/

/-- `isSOPlanarList` is a conjunction over children, hence permutation-invariant. -/
private theorem isSOPlanarList_perm (cs ds : List (Planar SOLabel)) (h : cs.Perm ds) :
    isSOPlanarList cs = isSOPlanarList ds := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [isSOPlanarList]; rw [ih]
  | swap _ _ _ => simp only [isSOPlanarList, Bool.and_left_comm]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Replacing one child by an `isSOPlanar`-equal child preserves `isSOPlanarList`. -/
private theorem isSOPlanarList_replace (pre post : List (Planar SOLabel))
    {old new : Planar SOLabel} (h : isSOPlanar old = isSOPlanar new) :
    isSOPlanarList (pre ++ old :: post) = isSOPlanarList (pre ++ new :: post) := by
  induction pre with
  | nil => simp only [List.nil_append, isSOPlanarList]; rw [h]
  | cons hd tl ih => simp only [List.cons_append, isSOPlanarList]; rw [ih]

private theorem isSOPlanar_planarStep {t s : Planar SOLabel} (h : Planar.PlanarStep t s) :
    isSOPlanar t = isSOPlanar s := by
  induction h with
  | swapAtRoot =>
    rename_i a l r pre post
    cases a with
    | inl _ => simp only [isSOPlanar]; cases pre <;> simp [List.isEmpty_cons]
    | inr u => cases u
               simp only [isSOPlanar, List.length_append, List.length_cons,
                 isSOPlanarList_perm _ _ (List.Perm.append_left pre (.swap r l post))]
  | recurse _ ih =>
    rename_i a pre old new post _hstep
    cases a with
    | inl _ => simp only [isSOPlanar]; cases pre <;> simp [List.isEmpty_cons]
    | inr u => cases u
               simp only [isSOPlanar, List.length_append, List.length_cons,
                 isSOPlanarList_replace pre post ih]

/-- `isSOPlanar` is invariant under `PlanarEquiv`, hence descends to the quotient. -/
theorem isSOPlanar_planarEquiv {t s : Planar SOLabel} (h : Planar.PlanarEquiv t s) :
    isSOPlanar t = isSOPlanar s := by
  induction h with
  | rel _ _ hstep => exact isSOPlanar_planarStep hstep
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-! ### The carrier: `IsSO` on `Nonplanar` + the `SO` subtype -/

/-- Well-formed-SO check on the nonplanar carrier, lifted from `isSOPlanar`. -/
def isSO : Nonplanar SOLabel → Bool :=
  Nonplanar.lift isSOPlanar (fun _ _ h => isSOPlanar_planarEquiv h)

@[simp] theorem isSO_mk (t : Planar SOLabel) : isSO (Nonplanar.mk t) = isSOPlanar t := rfl

/-- A tree on the carrier is a **syntactic object** ([marcolli-chomsky-berwick-2025]
    §1.1): binary, nonplanar; leaves are lexical (`Sum.inl tok`) or traces
    (`Sum.inr ()`), internal vertices bare (`Sum.inr ()`). Decidable (and
    `decide`-able, via `Core/…/DecEq`). -/
def IsSO (t : Nonplanar SOLabel) : Prop := isSO t = true

instance : DecidablePred IsSO := fun t => inferInstanceAs (Decidable (isSO t = true))

/-- The MCB-faithful **syntactic object** carrier: well-formed nonplanar trees over
    `SOLabel`. This is the target type that will become `SyntacticObject` once the
    operations (P2) and the head function / Phase API (P3) are ported onto it. -/
def SO : Type := { t : Nonplanar SOLabel // IsSO t }

instance : DecidableEq SO := Subtype.instDecidableEq

end Minimalist
