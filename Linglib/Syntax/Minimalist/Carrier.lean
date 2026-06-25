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
So on `Nonplanar (LIToken ⊕ Unit)`:

- a **leaf** carries `Sum.inl tok` — a lexical item (`LIToken` ≈ SO₀);
- an **internal node** carries `Sum.inr ()` — **bare**, no head label.

`IsSO` pins exactly this discipline (binary + leaf↔`inl`, internal↔`inr ()`).
This is the deliberate departure from the legacy `toNonplanar` image, which
decorated internal nodes with the head (`Sum.inl headLeaf`) — that decoration is
the head function applied, not part of the object.

## Scope of this skeleton

Just the carrier + `IsSO` + decidability + the `SO` subtype. **Out of scope (later
phases):** MCB-faithful traces (the `T/c`–`T/d`–`T/ρ` forms + workspace chains, P1;
`SO₀` here is `LIToken` only, no trace alphabet yet), the syntactic operations
(`contains`/`subtrees`/Merge on the carrier, P2), the head function + Phase API
re-home (P3), retiring `FreeCommMagma`/`toNonplanar` (P2/P4).
-/

namespace Minimalist

open RootedTree

/-- The SO label alphabet: a leaf carries a lexical item (`Sum.inl`), an internal
    vertex is **bare** (`Sum.inr ()`). MCB SO₀ ≈ `LIToken`; traces (a richer leaf
    alphabet, MCB Def 1.2.4) are deferred to P1. -/
abbrev SOLabel : Type := LIToken ⊕ Unit

/-! ### Well-formedness `IsSO` (binary + bare-internal discipline) -/

mutual
/-- Structural check that a *planar* tree is a well-formed syntactic object:
    a lexical-labelled node must be a leaf, a bare node must be binary with
    well-formed children. Permutation-friendly (`length`/`all`-shaped) so it lifts
    to the nonplanar quotient. -/
def isSOPlanar : Planar SOLabel → Bool
  | .node (.inl _) cs  => cs.isEmpty
  | .node (.inr ()) cs => cs.length == 2 && isSOPlanarList cs
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
    | inr u => cases u; show (decide _ && _) = (decide _ && _)
               rw [List.length_append, List.length_append,
                 isSOPlanarList_perm _ _ (List.Perm.append_left pre (.swap r l post))]
               simp
  | recurse _ ih =>
    rename_i a pre old new post _hstep
    cases a with
    | inl _ => simp only [isSOPlanar]; cases pre <;> simp [List.isEmpty_cons]
    | inr u => cases u; show (decide _ && _) = (decide _ && _)
               rw [List.length_append, List.length_append, isSOPlanarList_replace pre post ih]; rfl

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
    §1.1): binary, nonplanar, leaves lexical (`Sum.inl`), internal vertices bare
    (`Sum.inr ()`). Decidable (and `decide`-able, via `Core/…/DecEq`). -/
def IsSO (t : Nonplanar SOLabel) : Prop := isSO t = true

instance : DecidablePred IsSO := fun t => inferInstanceAs (Decidable (isSO t = true))

/-- The MCB-faithful **syntactic object** carrier: well-formed nonplanar trees over
    `SOLabel`. This is the target type that will become `SyntacticObject` once the
    operations (P2) and the head function / Phase API (P3) are ported onto it. -/
def SO : Type := { t : Nonplanar SOLabel // IsSO t }

instance : DecidableEq SO := Subtype.instDecidableEq

end Minimalist
